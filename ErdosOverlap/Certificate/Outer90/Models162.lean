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

/-! # Exact integer weighted outer models for source bin 162

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin162

def weightDenominator : ℤ := (Int.ofNat 5000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 192173749478683870)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 883094953437836000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 635216211576420650)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 232440180268934900)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 431347531509278250)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 350193207846221950)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 249392446589593380)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 183460677048586800)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 103170476437309750)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 59412081028073475)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial162.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial162.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 4585099967957758500)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1786610629284757000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 586096448305851800)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 490378230160321150)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 255208791498866825)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 96153721631957000)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 5882762206642229)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 15142422971389680)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 12153012923060620)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial162.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial162.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4585099967957758500)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1786610629284757000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 586096448305851800)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 490378230160321150)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 255208791498866825)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 96153721631957000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 5882762206642229)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 15142422971389680)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 12153012923060620)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial162.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial162.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial162.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 1969328239290798042392697969575297), (Int.ofNat 2005447735542290980758043566319554), (Int.ofNat 194618784009663777072905430400821), (Int.negOfNat 49116698257699166164935844423885), (Int.negOfNat 6083520307450498849492457428674), (Int.ofNat 866042454187636100067987695799), (Int.ofNat 104282618409636488780694943299), (Int.negOfNat 10142051711469300780120655757), (Int.negOfNat 1102383336691776129011002216), (Int.ofNat 81964466284830687958127175), (Int.ofNat 7855525844311959793474340), (Int.negOfNat 477722560795191646557573), (Int.negOfNat 40218488793137858946401), (Int.ofNat 2083827623400848832954), (Int.ofNat 155154081833635654763), (Int.negOfNat 6932986062424667878), (Int.negOfNat 488291382087430525), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1969328239290798042392697969575297/5629499534213120000000000000000000), (1002723867771145490379021783159777/2814749767106560000000000000000000), (194618784009663777072905430400821/5629499534213120000000000000000000), (-9823339651539833232987168884777/1125899906842624000000000000000000), (-3041760153725249424746228714337/2814749767106560000000000000000000), (866042454187636100067987695799/5629499534213120000000000000000000), (104282618409636488780694943299/5629499534213120000000000000000000), (-10142051711469300780120655757/5629499534213120000000000000000000), (-137797917086472016126375277/703687441776640000000000000000000), (3278578651393227518325087/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial162.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial162.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial162.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial162 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 2362628396315258422797942626155290), (Int.ofNat 2083705845741733426418306198997591), (Int.negOfNat 160113196959776678331157932627392), (Int.negOfNat 53575660063686381328974484253663), (Int.ofNat 5171100028286318487775263092220), (Int.ofNat 982838819180442507388395566227), (Int.negOfNat 88583786476940640353573525533), (Int.negOfNat 11694600357290748378194458809), (Int.ofNat 946407910043869273884699149), (Int.ofNat 94166671614842270760277008), (Int.negOfNat 6878873124455749773068678), (Int.negOfNat 541508610524451292949278), (Int.ofNat 35984500948116670987413), (Int.ofNat 2323322947202375335765), (Int.negOfNat 141555504634420920680), (Int.negOfNat 7626675302091151756), (Int.ofNat 455300568970191915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(236262839631525842279794262615529/562949953421312000000000000000000), (2083705845741733426418306198997591/5629499534213120000000000000000000), (-2501768702496510598924342697303/87960930222080000000000000000000), (-53575660063686381328974484253663/5629499534213120000000000000000000), (258555001414315924388763154611/281474976710656000000000000000000), (982838819180442507388395566227/5629499534213120000000000000000000), (-88583786476940640353573525533/5629499534213120000000000000000000), (-11694600357290748378194458809/5629499534213120000000000000000000), (946407910043869273884699149/5629499534213120000000000000000000), (5885416975927641922517313/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial162.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial162.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial162.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial162 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 5568286695609549023800200962931936), (Int.ofNat 1023345928157965044510983973978369), (Int.negOfNat 305914397073023887141408813168298), (Int.ofNat 8462597292409196545595198558895), (Int.ofNat 7739552121232530880815077436269), (Int.negOfNat 515915623082283495755428074713), (Int.negOfNat 111635269918441095134697788949), (Int.ofNat 8640293340375543313511109750), (Int.ofNat 1037223394087421639776034260), (Int.negOfNat 83421667017034136271006352), (Int.negOfNat 6721442816830114902915575), (Int.ofNat 538714406373215866611646), (Int.ofNat 32034800737116162192351), (Int.negOfNat 2504554053688522762286), (Int.negOfNat 116616277555202950385), (Int.ofNat 8799748767745348702), (Int.ofNat 322208151926270720), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(174008959237798406993756280091623/175921860444160000000000000000000), (1023345928157965044510983973978369/5629499534213120000000000000000000), (-152957198536511943570704406584149/2814749767106560000000000000000000), (1692519458481839309119039711779/1125899906842624000000000000000000), (7739552121232530880815077436269/5629499534213120000000000000000000), (-515915623082283495755428074713/5629499534213120000000000000000000), (-111635269918441095134697788949/5629499534213120000000000000000000), (34561173361502173254044439/22517998136852480000000000000000), (51861169704371081988801713/281474976710656000000000000000000), (-5213854188564633516937897/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial162.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial162.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial162.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial162 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 6560523723159314166867401523574873), (Int.ofNat 90911015348509113212821476537202), (Int.negOfNat 130235233970996148923996662220717), (Int.ofNat 38051859202290526785711233429788), (Int.negOfNat 937635663726249275840876024221), (Int.negOfNat 869197248529927007061357253468), (Int.ofNat 56097892992623992830624807225), (Int.ofNat 10116413939422021110689486565), (Int.negOfNat 826983622425827986617106751), (Int.negOfNat 75942835687862440743666036), (Int.ofNat 6937535040595576567895779), (Int.ofNat 403871323601279849481815), (Int.negOfNat 39135216310641837184879), (Int.negOfNat 1608660378264897014905), (Int.ofNat 160554352639856818493), (Int.ofNat 4844249206740029535), (Int.negOfNat 491759607739373775), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(6560523723159314166867401523574873/5629499534213120000000000000000000), (45455507674254556606410738268601/2814749767106560000000000000000000), (-130235233970996148923996662220717/5629499534213120000000000000000000), (9512964800572631696427808357447/1407374883553280000000000000000000), (-937635663726249275840876024221/5629499534213120000000000000000000), (-217299312132481751765339313367/1407374883553280000000000000000000), (2243915719704959713224992289/225179981368524800000000000000000), (2023282787884404222137897313/1125899906842624000000000000000000), (-826983622425827986617106751/5629499534213120000000000000000000), (-18985708921965610185916509/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial162.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial162.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial162.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial162 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 6487645545065471931843210746178657), (Int.negOfNat 58627544527989182778158142268890), (Int.ofNat 24555165372875428617873692975085), (Int.ofNat 8652382738101669896086996727594), (Int.negOfNat 4558635225476570891729039075518), (Int.ofNat 193730700642226071094607910592), (Int.ofNat 80817201714661569863380430048), (Int.negOfNat 6351451263112807803274527714), (Int.negOfNat 755063332604627016859261653), (Int.ofNat 75484501081650289188680226), (Int.ofNat 4587818030721380537231674), (Int.negOfNat 535518702768912981064303), (Int.negOfNat 19902463622702673880574), (Int.ofNat 2615601971165926767053), (Int.ofNat 65239237354584844088), (Int.negOfNat 9545305167836281517), (Int.negOfNat 143971908842050295), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(6487645545065471931843210746178657/5629499534213120000000000000000000), (-5862754452798918277815814226889/562949953421312000000000000000000), (4911033074575085723574738595017/1125899906842624000000000000000000), (4326191369050834948043498363797/2814749767106560000000000000000000), (-2279317612738285445864519537759/2814749767106560000000000000000000), (3027042197534782360853248603/87960930222080000000000000000000), (2525537553583174058230638439/175921860444160000000000000000000), (-3175725631556403901637263857/2814749767106560000000000000000000), (-755063332604627016859261653/5629499534213120000000000000000000), (37742250540825144594340113/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial162.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial162.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial162.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial162 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 6475299607060270592605629690603981), (Int.ofNat 25133135461171133814986698502937), (Int.negOfNat 3279755122474140934745982281495), (Int.negOfNat 11594396937133883652947865104038), (Int.negOfNat 54504694622347980736615286182), (Int.ofNat 463966698725195727108046477899), (Int.negOfNat 35023843516625138744367641626), (Int.negOfNat 6190428688889550029321331826), (Int.ofNat 677213329386034820209717044), (Int.ofNat 45395650071674823772704065), (Int.negOfNat 6345676500116728809993659), (Int.negOfNat 215788866136486739022236), (Int.ofNat 37824621110063955424561), (Int.ofNat 719983778849935847895), (Int.negOfNat 160071875061772131480), (Int.negOfNat 1699938690871547964), (Int.ofNat 528218646508555635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(6475299607060270592605629690603981/5629499534213120000000000000000000), (25133135461171133814986698502937/5629499534213120000000000000000000), (-655951024494828186949196456299/1125899906842624000000000000000000), (-5797198468566941826473932552019/2814749767106560000000000000000000), (-27252347311173990368307643091/2814749767106560000000000000000000), (463966698725195727108046477899/5629499534213120000000000000000000), (-17511921758312569372183820813/2814749767106560000000000000000000), (-3095214344444775014660665913/2814749767106560000000000000000000), (169303332346508705052429261/1407374883553280000000000000000000), (9079130014334964754540813/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial162.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial162.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial162.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial162 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 6430822467844990807100125763696433), (Int.negOfNat 100479265680314669915565572056939), (Int.negOfNat 48256422166474256598241904771888), (Int.negOfNat 1186841514892971966283692197180), (Int.ofNat 1602416686220542225725375246998), (Int.negOfNat 135051277776685629821017548658), (Int.negOfNat 37576124910895029979579393510), (Int.ofNat 4918253733336736399254409554), (Int.ofNat 365971032509184544097968694), (Int.negOfNat 64257670160127246057246674), (Int.negOfNat 1935261974159581617621558), (Int.ofNat 481234405323281898319552), (Int.ofNat 5943222504802368738925), (Int.negOfNat 2423942463165123566464), (Int.negOfNat 8329755330168798878), (Int.ofNat 9078313921519623592), (Int.negOfNat 34264334242170130), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(6430822467844990807100125763696433/5629499534213120000000000000000000), (-100479265680314669915565572056939/5629499534213120000000000000000000), (-3016026385404641037390119048243/351843720888320000000000000000000), (-59342075744648598314184609859/281474976710656000000000000000000), (801208343110271112862687623499/2814749767106560000000000000000000), (-67525638888342814910508774329/2814749767106560000000000000000000), (-3757612491089502997957939351/562949953421312000000000000000000), (2459126866668368199627204777/2814749767106560000000000000000000), (182985516254592272048984347/2814749767106560000000000000000000), (-32128835080063623028623337/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial162.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial162.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial162.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial162 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 6046945003427544412283160386088440), (Int.negOfNat 272062824165249502570875774004376), (Int.negOfNat 33085779528557715679312389134973), (Int.ofNat 3273425118891300302652404671527), (Int.negOfNat 480552997618021850623993282535), (Int.negOfNat 139974795834405375974428010177), (Int.ofNat 29533796110169201028275149731), (Int.ofNat 2098584171172028856323080655), (Int.negOfNat 551168671136766359656360377), (Int.negOfNat 12216389348242453213475819), (Int.ofNat 5330167682921391767757937), (Int.ofNat 17306303631679876339988), (Int.negOfNat 32609652259671468448963), (Int.ofNat 186863712641592677210), (Int.ofNat 139780106019078997858), (Int.negOfNat 1514420274338291957), (Int.negOfNat 505265604249664020), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(151173625085688610307079009652211/140737488355328000000000000000000), (-34007853020656187821359471750547/703687441776640000000000000000000), (-33085779528557715679312389134973/5629499534213120000000000000000000), (3273425118891300302652404671527/5629499534213120000000000000000000), (-96110599523604370124798656507/1125899906842624000000000000000000), (-139974795834405375974428010177/5629499534213120000000000000000000), (29533796110169201028275149731/5629499534213120000000000000000000), (419716834234405771264616131/1125899906842624000000000000000000), (-551168671136766359656360377/5629499534213120000000000000000000), (-12216389348242453213475819/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial162.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial162.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial162.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial162 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 5386512387976108753047060752734490), (Int.negOfNat 385655699740040427371962265282387), (Int.negOfNat 28662345198540353788407027305042), (Int.negOfNat 1243661984486950737483363213986), (Int.negOfNat 118794028901136083437837931028), (Int.ofNat 159545314105230803049533754057), (Int.ofNat 5352076207396937979409345221), (Int.negOfNat 4020159563822700872383804305), (Int.negOfNat 14991613817831728724032197), (Int.ofNat 50852859846086102851233249), (Int.negOfNat 570987310360552238881353), (Int.negOfNat 385036680251876064136038), (Int.ofNat 7155178148827158075647), (Int.ofNat 1962799301827569538120), (Int.negOfNat 44009389768524646492), (Int.negOfNat 7367233257155381833), (Int.ofNat 177394522144438320), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(538651238797610875304706075273449/562949953421312000000000000000000), (-385655699740040427371962265282387/5629499534213120000000000000000000), (-14331172599270176894203513652521/2814749767106560000000000000000000), (-621830992243475368741681606993/2814749767106560000000000000000000), (-29698507225284020859459482757/1407374883553280000000000000000000), (159545314105230803049533754057/5629499534213120000000000000000000), (5352076207396937979409345221/5629499534213120000000000000000000), (-804031912764540174476760861/1125899906842624000000000000000000), (-14991613817831728724032197/5629499534213120000000000000000000), (50852859846086102851233249/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial162.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial162.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial162.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial162 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 4493655879879759100994161215963659), (Int.negOfNat 506945414253308492569210733011142), (Int.negOfNat 27437978001672205782751187843053), (Int.ofNat 3015662546602112480463711190127), (Int.ofNat 838010893773230433788893496758), (Int.negOfNat 32802342722121979162424844702), (Int.negOfNat 25243086078428381301878350980), (Int.ofNat 848749726836208536105740826), (Int.ofNat 413246386854310306707249414), (Int.negOfNat 14991158252259079772853616), (Int.negOfNat 3927997115687020891335698), (Int.ofNat 150810553195748901976298), (Int.ofNat 24115408730915572395035), (Int.negOfNat 952308641880516234166), (Int.negOfNat 103942897084072031378), (Int.ofNat 4210282473980220098), (Int.ofNat 410747468039638310), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(4493655879879759100994161215963659/5629499534213120000000000000000000), (-253472707126654246284605366505571/2814749767106560000000000000000000), (-27437978001672205782751187843053/5629499534213120000000000000000000), (3015662546602112480463711190127/5629499534213120000000000000000000), (419005446886615216894446748379/2814749767106560000000000000000000), (-16401171361060989581212422351/2814749767106560000000000000000000), (-1262154303921419065093917549/281474976710656000000000000000000), (424374863418104268052870413/2814749767106560000000000000000000), (206623193427155153353624707/2814749767106560000000000000000000), (-936947390766192485803351/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial162.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial162.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial162.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial162 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 3405084513148786574763244146258318), (Int.negOfNat 560412903910614359329141091310486), (Int.ofNat 3287988107261572955867736679556), (Int.ofNat 5452412319574724474331090469062), (Int.negOfNat 408363800647373914602472975126), (Int.negOfNat 134688744695490003217047673883), (Int.ofNat 13030343563200728448609974684), (Int.ofNat 2796718315300335242173188076), (Int.negOfNat 228473869067502519194767216), (Int.negOfNat 33774228561970678524640495), (Int.ofNat 2439648429386539913548381), (Int.ofNat 253515241412619973739836), (Int.negOfNat 17060541000356389451099), (Int.negOfNat 1290237515359820847675), (Int.ofNat 83216804593231708670), (Int.ofNat 4748759413685288454), (Int.negOfNat 273265641941693655), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(1702542256574393287381622073129159/2814749767106560000000000000000000), (-280206451955307179664570545655243/2814749767106560000000000000000000), (821997026815393238966934169889/1407374883553280000000000000000000), (2726206159787362237165545234531/2814749767106560000000000000000000), (-204181900323686957301236487563/2814749767106560000000000000000000), (-134688744695490003217047673883/5629499534213120000000000000000000), (3257585890800182112152493671/1407374883553280000000000000000000), (699179578825083810543297019/1407374883553280000000000000000000), (-14279616816718907449672951/351843720888320000000000000000000), (-6754845712394135704928099/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial162.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial162.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial162.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial162 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 2331305174334553422645164869859483), (Int.negOfNat 502216893001500105254992929157404), (Int.ofNat 19902170593797848343871649979677), (Int.negOfNat 96074884306036841238742676877), (Int.negOfNat 541458845400275806011832410523), (Int.ofNat 111266010321703558465130359118), (Int.ofNat 14625255342392489995949082243), (Int.negOfNat 2573444641994024947753005866), (Int.negOfNat 232115099848007551582369953), (Int.ofNat 32354708412042751270407514), (Int.ofNat 2173390759381480775980064), (Int.negOfNat 260971410908954533462297), (Int.negOfNat 13230581804914903090534), (Int.ofNat 1451680405101768236927), (Int.ofNat 56537664585542130088), (Int.negOfNat 5892575012602940023), (Int.negOfNat 232511224955417885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(2331305174334553422645164869859483/5629499534213120000000000000000000), (-125554223250375026313748232289351/1407374883553280000000000000000000), (19902170593797848343871649979677/5629499534213120000000000000000000), (-96074884306036841238742676877/5629499534213120000000000000000000), (-541458845400275806011832410523/5629499534213120000000000000000000), (55633005160851779232565179559/2814749767106560000000000000000000), (14625255342392489995949082243/5629499534213120000000000000000000), (-1286722320997012473876502933/2814749767106560000000000000000000), (-232115099848007551582369953/5629499534213120000000000000000000), (16177354206021375635203757/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial162.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial162.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial162.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial162 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 1401174051521878534434928173720552), (Int.negOfNat 430686560928361484234901249979836), (Int.ofNat 16762878617978976694910119863201), (Int.ofNat 701120721620934536362484618124), (Int.ofNat 615719891651261178137036499004), (Int.ofNat 40825022131102402304166872668), (Int.negOfNat 22649124595502864005364755865), (Int.negOfNat 1081029475082587498333337015), (Int.ofNat 357690636489973305272425359), (Int.ofNat 13332296896669950246982476), (Int.negOfNat 3441527206502120010949761), (Int.negOfNat 98955559870881746036165), (Int.ofNat 22298852047353854417431), (Int.ofNat 492186503004112474635), (Int.negOfNat 103240056475282619607), (Int.negOfNat 1714213502634128625), (Int.ofNat 309724680710875515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(175146756440234816804366021715069/703687441776640000000000000000000), (-107671640232090371058725312494959/1407374883553280000000000000000000), (16762878617978976694910119863201/5629499534213120000000000000000000), (175280180405233634090621154531/1407374883553280000000000000000000), (153929972912815294534259124751/1407374883553280000000000000000000), (10206255532775600576041718167/1407374883553280000000000000000000), (-4529824919100572801072951173/1125899906842624000000000000000000), (-216205895016517499666667403/1125899906842624000000000000000000), (357690636489973305272425359/5629499534213120000000000000000000), (3333074224167487561745619/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial162.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial162.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial162.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial162 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 622126174926727407178675312473454), (Int.negOfNat 336706672956243245745285250190959), (Int.ofNat 33512170530884690590447012945866), (Int.ofNat 3688835701068717041062122380568), (Int.negOfNat 230832685572158962813976924766), (Int.negOfNat 163011492406832072657624200127), (Int.negOfNat 443631570414229721744352819), (Int.ofNat 3308526790885844861247520790), (Int.ofNat 24332703387152159611949400), (Int.negOfNat 39046469348944221636279968), (Int.negOfNat 245015067932370943198765), (Int.ofNat 300383210349466608344004), (Int.ofNat 1315276422623187124211), (Int.negOfNat 1614953969707777250594), (Int.negOfNat 4213052966871808935), (Int.ofNat 6410931956510311688), (Int.ofNat 54274981871197460), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(311063087463363703589337656236727/2814749767106560000000000000000000), (-336706672956243245745285250190959/5629499534213120000000000000000000), (16756085265442345295223506472933/2814749767106560000000000000000000), (461104462633589630132765297571/703687441776640000000000000000000), (-115416342786079481406988462383/2814749767106560000000000000000000), (-163011492406832072657624200127/5629499534213120000000000000000000), (-443631570414229721744352819/5629499534213120000000000000000000), (330852679088584486124752079/562949953421312000000000000000000), (121663516935760798059747/28147497671065600000000000000000), (-1220202167154506926133749/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial162.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial162.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial162.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial162 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 103744198990866587441911522072603), (Int.negOfNat 177485454963902772388880787795836), (Int.ofNat 39050288332725580602344155810304), (Int.negOfNat 3054192678923533319576079656776), (Int.negOfNat 1082376939366660374318164261572), (Int.ofNat 48286577029236823505306983984), (Int.ofNat 25715121324841504508499567947), (Int.negOfNat 709740224216187869709920221), (Int.negOfNat 377959602713355575161311431), (Int.ofNat 7645881159732180126582172), (Int.ofNat 3519218252606543721833862), (Int.negOfNat 58187620890596799943422), (Int.negOfNat 22294622560999607626197), (Int.ofNat 321443475463875468105), (Int.ofNat 101529174219562155270), (Int.negOfNat 1444568504822096654), (Int.negOfNat 346183719480057375), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(103744198990866587441911522072603/5629499534213120000000000000000000), (-44371363740975693097220196948959/1407374883553280000000000000000000), (76270094399854649613953429317/10995116277760000000000000000000), (-381774084865441664947009957097/703687441776640000000000000000000), (-270594234841665093579541065393/1407374883553280000000000000000000), (3017911064327301469081686499/351843720888320000000000000000000), (25715121324841504508499567947/5629499534213120000000000000000000), (-709740224216187869709920221/5629499534213120000000000000000000), (-377959602713355575161311431/5629499534213120000000000000000000), (1911470289933045031645543/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial162.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial162.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial162.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial162 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 133766484126140328899858453567698), (Int.negOfNat 84440981184290031009349177796585), (Int.ofNat 3701107719094172048163345381264), (Int.negOfNat 6651727515280931444178770690968), (Int.ofNat 394413335013348983195756597305), (Int.ofNat 167939551691230865267929502422), (Int.negOfNat 11626044012081252720197123801), (Int.negOfNat 3073998544664251026414706113), (Int.ofNat 170383013289514071044933214), (Int.ofNat 35296194999115358565297935), (Int.negOfNat 1568448400873736739216120), (Int.negOfNat 267783144699932290472627), (Int.ofNat 9904816448203812428339), (Int.ofNat 1428526690422414379976), (Int.negOfNat 45302674121616545537), (Int.negOfNat 5674011964524492362), (Int.ofNat 136114274136083585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-66883242063070164449929226783849/2814749767106560000000000000000000), (-16888196236858006201869835559317/1125899906842624000000000000000000), (231319232443385753010209086329/351843720888320000000000000000000), (-831465939410116430522346336371/703687441776640000000000000000000), (78882667002669796639151319461/1125899906842624000000000000000000), (83969775845615432633964751211/2814749767106560000000000000000000), (-11626044012081252720197123801/5629499534213120000000000000000000), (-3073998544664251026414706113/5629499534213120000000000000000000), (85191506644757035522466607/2814749767106560000000000000000000), (7059238999823071713059587/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial162.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial162.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial162.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial162 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 330451108810072422911627411708164), (Int.negOfNat 126765180576338423371670860283314), (Int.negOfNat 17720912668113775050535518715183), (Int.ofNat 100721730400287045058264989737), (Int.ofNat 817995985262058165133136375983), (Int.negOfNat 101453230665830252986157107154), (Int.negOfNat 20237135506190157803188273359), (Int.ofNat 2195095633118399934064463277), (Int.ofNat 294544025774805690976705386), (Int.negOfNat 25597881740482123672299745), (Int.negOfNat 2727191847265624864817860), (Int.ofNat 193701148395352703639283), (Int.ofNat 17275748463482113266101), (Int.negOfNat 1027721985690225629894), (Int.negOfNat 79077819721043356843), (Int.ofNat 4116088351515225638), (Int.ofNat 251665583270031665), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-82612777202518105727906852927041/1407374883553280000000000000000000), (-63382590288169211685835430141657/2814749767106560000000000000000000), (-17720912668113775050535518715183/5629499534213120000000000000000000), (100721730400287045058264989737/5629499534213120000000000000000000), (817995985262058165133136375983/5629499534213120000000000000000000), (-50726615332915126493078553577/2814749767106560000000000000000000), (-20237135506190157803188273359/5629499534213120000000000000000000), (2195095633118399934064463277/5629499534213120000000000000000000), (147272012887402845488352693/2814749767106560000000000000000000), (-5119576348096424734459949/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial162.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial162.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial162.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial162 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 645172156435724759480626358753548), (Int.negOfNat 181051468503708745635243455226632), (Int.negOfNat 8597862275062405727538539017227), (Int.ofNat 935967806344766173604211231812), (Int.negOfNat 596185637350683526045889282362), (Int.negOfNat 94478994050783059689845359282), (Int.ofNat 20728967122088932318888862333), (Int.ofNat 1924528239943944374596570289), (Int.negOfNat 318086072307125087274880009), (Int.negOfNat 22345226467470538219770018), (Int.ofNat 2967370656715142737902958), (Int.ofNat 171585445253683634502068), (Int.negOfNat 18673329217622509029753), (Int.negOfNat 929590550480395199425), (Int.ofNat 84442082153080791760), (Int.ofNat 3840662521012769996), (Int.negOfNat 279244462038351775), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-161293039108931189870156589688387/1407374883553280000000000000000000), (-22631433562963593204405431903329/703687441776640000000000000000000), (-8597862275062405727538539017227/5629499534213120000000000000000000), (233991951586191543401052807953/1407374883553280000000000000000000), (-298092818675341763022944641181/2814749767106560000000000000000000), (-47239497025391529844922679641/2814749767106560000000000000000000), (20728967122088932318888862333/5629499534213120000000000000000000), (1924528239943944374596570289/5629499534213120000000000000000000), (-318086072307125087274880009/5629499534213120000000000000000000), (-11172613233735269109885009/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial162.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial162.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial162.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial162 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 1045257667997008259146891991704513), (Int.negOfNat 226365989326815052742584626113239), (Int.negOfNat 19215932652500719491623747276084), (Int.negOfNat 3857925161021652172810481517308), (Int.negOfNat 160204635299695560515977554773), (Int.ofNat 155276720298297106084811968233), (Int.ofNat 8301269830514463686313259579), (Int.negOfNat 3161880617910704743951642390), (Int.negOfNat 127611532836503590231090940), (Int.ofNat 37382617817582912341801212), (Int.ofNat 1229363163398478525496355), (Int.negOfNat 285194308598479245777216), (Int.negOfNat 8169144236223332135131), (Int.ofNat 1514430666685020039666), (Int.ofNat 38887385889847981705), (Int.negOfNat 5982851056835906462), (Int.negOfNat 85582353108871860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-1045257667997008259146891991704513/5629499534213120000000000000000000), (-226365989326815052742584626113239/5629499534213120000000000000000000), (-4803983163125179872905936819021/1407374883553280000000000000000000), (-964481290255413043202620379327/1407374883553280000000000000000000), (-160204635299695560515977554773/5629499534213120000000000000000000), (155276720298297106084811968233/5629499534213120000000000000000000), (8301269830514463686313259579/5629499534213120000000000000000000), (-316188061791070474395164239/562949953421312000000000000000000), (-6380576641825179511554547/281474976710656000000000000000000), (9345654454395728085450303/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial162.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial162.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial162.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial162 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 1603197511589429031006858642827694), (Int.negOfNat 342093491168324857332094737838452), (Int.negOfNat 33969326684259608147698030935434), (Int.ofNat 607723201889913890707833893664), (Int.ofNat 1017132183900680938695475161932), (Int.ofNat 8660347714291192602057039934), (Int.negOfNat 25358238381166197162373029380), (Int.negOfNat 179902502592620293240174005), (Int.ofNat 390204098403856713187348881), (Int.ofNat 2700651495980237631419936), (Int.negOfNat 3702922836362832579231149), (Int.negOfNat 28693726803131869080175), (Int.ofNat 23532372252468368424059), (Int.ofNat 201546377647768789285), (Int.negOfNat 106625946960855724133), (Int.negOfNat 1058236425661647775), (Int.ofNat 315703500807533635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-801598755794714515503429321413847/2814749767106560000000000000000000), (-85523372792081214333023684459613/1407374883553280000000000000000000), (-16984663342129804073849015467717/2814749767106560000000000000000000), (18991350059059809084619809177/175921860444160000000000000000000), (254283045975170234673868790483/1407374883553280000000000000000000), (4330173857145596301028519967/2814749767106560000000000000000000), (-1267911919058309858118651469/281474976710656000000000000000000), (-35980500518524058648034801/1125899906842624000000000000000000), (390204098403856713187348881/5629499534213120000000000000000000), (84395359249382425981873/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial162.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial162.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial162.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial162 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 2403397203047248077881716518061240), (Int.negOfNat 441999353969910159293041262276951), (Int.negOfNat 10756051575969177232618758139189), (Int.ofNat 5591436555431678179874205911018), (Int.negOfNat 68246668085321395504887533518), (Int.negOfNat 158860319091314548127365283062), (Int.ofNat 6129071438190907818550155682), (Int.ofNat 3318097202197609729123498124), (Int.negOfNat 91044065811027860233677627), (Int.negOfNat 40574174298301921672793176), (Int.ofNat 718736908075578833144846), (Int.ofNat 316141157575610903727843), (Int.negOfNat 3543383401438522185606), (Int.negOfNat 1700144335865898560673), (Int.ofNat 11456051954372947552), (Int.ofNat 6728407456926839277), (Int.negOfNat 92653889975348565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-60084930076181201947042912951531/140737488355328000000000000000000), (-441999353969910159293041262276951/5629499534213120000000000000000000), (-10756051575969177232618758139189/5629499534213120000000000000000000), (2795718277715839089937102955509/2814749767106560000000000000000000), (-34123334042660697752443766759/2814749767106560000000000000000000), (-79430159545657274063682641531/2814749767106560000000000000000000), (3064535719095453909275077841/2814749767106560000000000000000000), (829524300549402432280874531/1407374883553280000000000000000000), (-91044065811027860233677627/5629499534213120000000000000000000), (-5071771787287740209099147/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial162.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial162.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial162.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial162 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 3291089850583342599020037841288600), (Int.negOfNat 430335396993633292535730716945579), (Int.ofNat 11813125166756483753268099870645), (Int.ofNat 1172075929985082797381511290294), (Int.negOfNat 603630545344876240180503782602), (Int.ofNat 85079346140025825142553233750), (Int.ofNat 21650810249760245763293039896), (Int.negOfNat 1883024002003749713479300864), (Int.negOfNat 365371567275488917459812714), (Int.ofNat 20393166803947791141700345), (Int.ofNat 3616185263081266233616779), (Int.negOfNat 138003583030300308071934), (Int.negOfNat 23575075002198757929781), (Int.ofNat 641123655973379160485), (Int.ofNat 109100146171807354160), (Int.negOfNat 2086074090206833796), (Int.negOfNat 352162539576715495), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-16455449252916712995100189206443/28147497671065600000000000000000), (-430335396993633292535730716945579/5629499534213120000000000000000000), (2362625033351296750653619974129/1125899906842624000000000000000000), (586037964992541398690755645147/2814749767106560000000000000000000), (-301815272672438120090251891301/2814749767106560000000000000000000), (68063476912020660114042587/4503599627370496000000000000000), (2706351281220030720411629987/703687441776640000000000000000000), (-7355562507827147318278519/21990232555520000000000000000000), (-182685783637744458729906357/2814749767106560000000000000000000), (4078633360789558228340069/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial162.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial162.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial162.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial162 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 4101002224430399593936283365194332), (Int.negOfNat 378525181831176752332505832487449), (Int.ofNat 14571142918919052833785016671068), (Int.ofNat 1658052462268336979829600857063), (Int.ofNat 732096259937286089633325163118), (Int.ofNat 87144647449411132183689585393), (Int.negOfNat 22996875953335053254973268340), (Int.negOfNat 2534343938085207318221053724), (Int.ofNat 328147159209655678697516516), (Int.ofNat 33983977453098197296202064), (Int.negOfNat 2810294723599902315938822), (Int.negOfNat 278530192975623448238812), (Int.ofNat 16059012789715795787415), (Int.ofNat 1546839303071278249804), (Int.negOfNat 65565132062977786202), (Int.negOfNat 6261416210610181352), (Int.ofNat 270890133059568990), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-1025250556107599898484070841298583/1407374883553280000000000000000000), (-378525181831176752332505832487449/5629499534213120000000000000000000), (3642785729729763208446254167767/1407374883553280000000000000000000), (1658052462268336979829600857063/5629499534213120000000000000000000), (366048129968643044816662581559/2814749767106560000000000000000000), (87144647449411132183689585393/5629499534213120000000000000000000), (-1149843797666752662748663417/281474976710656000000000000000000), (-633585984521301829555263431/1407374883553280000000000000000000), (82036789802413919674379129/1407374883553280000000000000000000), (2123998590818637331012629/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial162.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial162.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial162.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial162 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 4773699589438009430801113097992899), (Int.negOfNat 275098850926438703027210866930277), (Int.ofNat 42544733423695210594304851614933), (Int.ofNat 6619884669742719072433791380897), (Int.negOfNat 28354746868171863486311361853), (Int.negOfNat 215025267177544376184544559647), (Int.negOfNat 11223111447892712679914380896), (Int.ofNat 3980569764336044195184493515), (Int.ofNat 240402320256743050191544607), (Int.negOfNat 43329192008945154882453651), (Int.negOfNat 2662619285540921248939917), (Int.ofNat 303389296916021916418022), (Int.ofNat 18592087584045738068263), (Int.negOfNat 1473329684947572962150), (Int.negOfNat 89463436895518517778), (Int.ofNat 5300433055416673717), (Int.ofNat 329209497317823880), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-4773699589438009430801113097992899/5629499534213120000000000000000000), (-275098850926438703027210866930277/5629499534213120000000000000000000), (42544733423695210594304851614933/5629499534213120000000000000000000), (6619884669742719072433791380897/5629499534213120000000000000000000), (-28354746868171863486311361853/5629499534213120000000000000000000), (-215025267177544376184544559647/5629499534213120000000000000000000), (-350722232746647271247324403/175921860444160000000000000000000), (796113952867208839036898703/1125899906842624000000000000000000), (240402320256743050191544607/5629499534213120000000000000000000), (-43329192008945154882453651/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial162.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial162.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial162.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial162 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 5108265214869334508944770519234636), (Int.negOfNat 43825720709740143832452769907726), (Int.ofNat 64572905199890003656067169603762), (Int.negOfNat 1603155256931887189612569214470), (Int.negOfNat 1664116247846118486717173898044), (Int.negOfNat 6160840266697781794493988501), (Int.ofNat 38574204751594926226443666949), (Int.ofNat 913588583410217143436470095), (Int.negOfNat 543807191480679765434957983), (Int.negOfNat 17667407413501313929970809), (Int.ofNat 4738616193002446848984293), (Int.ofNat 174061174423025167114578), (Int.negOfNat 27571745263611411691227), (Int.negOfNat 1069058659523672147620), (Int.ofNat 114641122922719641772), (Int.ofNat 4550335546245939593), (Int.negOfNat 414020320961837180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-1277066303717333627236192629808659/1407374883553280000000000000000000), (-21912860354870071916226384953863/2814749767106560000000000000000000), (32286452599945001828033584801881/2814749767106560000000000000000000), (-160315525693188718961256921447/562949953421312000000000000000000), (-416029061961529621679293474511/1407374883553280000000000000000000), (-6160840266697781794493988501/5629499534213120000000000000000000), (38574204751594926226443666949/5629499534213120000000000000000000), (182717716682043428687294019/1125899906842624000000000000000000), (-543807191480679765434957983/5629499534213120000000000000000000), (-17667407413501313929970809/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial162.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial162.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial162.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial162 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 4974830767173779180512182954134544), (Int.ofNat 148726922486227371227501052061724), (Int.ofNat 23395645459315560082961583653093), (Int.negOfNat 9471707931885672391455235348115), (Int.ofNat 231514984592391162511399174206), (Int.ofNat 294567596288541420592710871191), (Int.negOfNat 4688021587040206543390423560), (Int.negOfNat 5623916926636668057736350516), (Int.negOfNat 17019050543990329248175714), (Int.ofNat 62860383497676465319110006), (Int.ofNat 909286288348941888131338), (Int.negOfNat 445238623125155858805938), (Int.negOfNat 9149598518009561297375), (Int.ofNat 2178329473400274197866), (Int.ofNat 51901533267671273498), (Int.negOfNat 7996295255058601858), (Int.negOfNat 234691361107798170), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-310926922948361198782011434633409/351843720888320000000000000000000), (37181730621556842806875263015431/1407374883553280000000000000000000), (23395645459315560082961583653093/5629499534213120000000000000000000), (-1894341586377134478291047069623/1125899906842624000000000000000000), (115757492296195581255699587103/2814749767106560000000000000000000), (294567596288541420592710871191/5629499534213120000000000000000000), (-117200539676005163584760589/140737488355328000000000000000000), (-1405979231659167014434087629/1407374883553280000000000000000000), (-8509525271995164624087857/2814749767106560000000000000000000), (31430191748838232659555003/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial162.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial162.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial162.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial162 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4647429667884714889229339024002479), (Int.ofNat 156330219671305867754739700704935), (Int.negOfNat 8960390741319966795080850574601), (Int.ofNat 565868519794205386501464386704), (Int.ofNat 1548686614508039492214733869129), (Int.negOfNat 121010187056439851226907118862), (Int.negOfNat 46658026879949166242187051424), (Int.ofNat 1694157318087416119222885154), (Int.ofNat 710779024958853124798862956), (Int.negOfNat 7437328269971328494652685), (Int.negOfNat 6287264480342492263975731), (Int.negOfNat 15252988188520666509066), (Int.ofNat 36605282341507220437359), (Int.ofNat 334201525395481374335), (Int.negOfNat 152195908194664033190), (Int.negOfNat 1931861702775846214), (Int.ofNat 509891440759092515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-4647429667884714889229339024002479/5629499534213120000000000000000000), (31266043934261173550947940140987/1125899906842624000000000000000000), (-8960390741319966795080850574601/5629499534213120000000000000000000), (35366782487137836656341524169/351843720888320000000000000000000), (1548686614508039492214733869129/5629499534213120000000000000000000), (-60505093528219925613453559431/2814749767106560000000000000000000), (-1458063339998411445068345357/175921860444160000000000000000000), (847078659043708059611442577/2814749767106560000000000000000000), (177694756239713281199715739/1407374883553280000000000000000000), (-1487465653994265698930537/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial162.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial162.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial162.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial162 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 4347774612817905813638950723304379), (Int.ofNat 159636116192774178623218225548693), (Int.ofNat 13032087244644782579913086743641), (Int.ofNat 2739020145691220919527303647119), (Int.negOfNat 1300989763522392530426839710942), (Int.negOfNat 282650252003803210303644548968), (Int.ofNat 32438798846534383438735628297), (Int.ofNat 6776478271671572830382899516), (Int.negOfNat 300536716808258471314153317), (Int.negOfNat 77960292658632875066787994), (Int.ofNat 1427676719488187107467786), (Int.ofNat 548978413298848581630657), (Int.negOfNat 3333802418422877614366), (Int.negOfNat 2664555755520982282947), (Int.negOfNat 1311283966802337648), (Int.ofNat 9678587793681321783), (Int.ofNat 56455118023577745), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-4347774612817905813638950723304379/5629499534213120000000000000000000), (159636116192774178623218225548693/5629499534213120000000000000000000), (13032087244644782579913086743641/5629499534213120000000000000000000), (2739020145691220919527303647119/5629499534213120000000000000000000), (-650494881761196265213419855471/2814749767106560000000000000000000), (-35331281500475401287955568621/703687441776640000000000000000000), (32438798846534383438735628297/5629499534213120000000000000000000), (1694119567917893207595724879/1407374883553280000000000000000000), (-300536716808258471314153317/5629499534213120000000000000000000), (-38980146329316437533393997/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial162.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial162.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial162.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial162 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 3981493344233720436636395042554492), (Int.ofNat 189179027657161814775881153723746), (Int.negOfNat 12897001180771385656841504049744), (Int.negOfNat 10903569732491652004775432431501), (Int.negOfNat 893683131022367185798039604795), (Int.ofNat 410588206920352666332234394918), (Int.ofNat 53414071109864947493354481245), (Int.negOfNat 5351358548081130944293335735), (Int.negOfNat 850861021246251095462794589), (Int.ofNat 37905179308141204553547744), (Int.ofNat 7384732131803493920186311), (Int.negOfNat 171886303259819524334125), (Int.negOfNat 42159316150437895923531), (Int.ofNat 538279115869097343345), (Int.ofNat 173252762433112121167), (Int.negOfNat 1102684208275313615), (Int.negOfNat 546350479528274375), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-995373336058430109159098760638623/1407374883553280000000000000000000), (94589513828580907387940576861873/2814749767106560000000000000000000), (-806062573798211603552594003109/351843720888320000000000000000000), (-10903569732491652004775432431501/5629499534213120000000000000000000), (-178736626204473437159607920959/1125899906842624000000000000000000), (205294103460176333166117197459/2814749767106560000000000000000000), (10682814221972989498670896249/1125899906842624000000000000000000), (-1070271709616226188858667147/1125899906842624000000000000000000), (-850861021246251095462794589/5629499534213120000000000000000000), (1184536853379412642298367/175921860444160000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial162.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial162.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial162.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial162 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3740569800859192002889873193336647), (Int.ofNat 18106412923915286109046055871950), (Int.negOfNat 58969038947875319919440989676120), (Int.ofNat 2700721685679376957714506561915), (Int.ofNat 4205547389160412527331010148335), (Int.ofNat 347814788348925082561684487582), (Int.negOfNat 71306646506642322446691027391), (Int.negOfNat 8263289783705725084080262710), (Int.ofNat 652669639211732589619066460), (Int.ofNat 89709113595862314137652538), (Int.negOfNat 3893891534976533850476835), (Int.negOfNat 606404483542996307160134), (Int.ofNat 16639801026539484641529), (Int.ofNat 2870148982874126116254), (Int.negOfNat 53970004440904300545), (Int.negOfNat 10196944737588693448), (Int.ofNat 121781125060642680), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-3740569800859192002889873193336647/5629499534213120000000000000000000), (362128258478305722180921117439/112589990684262400000000000000000), (-1474225973696882997986024741903/140737488355328000000000000000000), (540144337135875391542901312383/1125899906842624000000000000000000), (841109477832082505466202029667/1125899906842624000000000000000000), (173907394174462541280842243791/2814749767106560000000000000000000), (-71306646506642322446691027391/5629499534213120000000000000000000), (-826328978370572508408026271/562949953421312000000000000000000), (32633481960586629480953323/281474976710656000000000000000000), (44854556797931157068826269/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial162.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial162.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial162.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial162 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 3845621976637967684825046799315380), (Int.negOfNat 39502403656966706291539571589894), (Int.ofNat 64849669852904000475070364509225), (Int.ofNat 35790278668674813979674878787180), (Int.ofNat 2109401115309576876498899340174), (Int.negOfNat 775514436348178436884677462319), (Int.negOfNat 74109041293432125917731663257), (Int.ofNat 8855406092856596067214313931), (Int.ofNat 998116217255211903181304581), (Int.negOfNat 65801964463885266350139932), (Int.negOfNat 7979893180208747802545002), (Int.ofNat 348906585421198810292932), (Int.ofNat 43547607996103018924537), (Int.negOfNat 1393950472589946573405), (Int.negOfNat 174342282093202863390), (Int.ofNat 4261466215731538894), (Int.ofNat 582809518297456235), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-192281098831898384241252339965769/281474976710656000000000000000000), (-19751201828483353145769785794947/2814749767106560000000000000000000), (2593986794116160019002814580369/225179981368524800000000000000000), (1789513933433740698983743939359/281474976710656000000000000000000), (1054700557654788438249449670087/2814749767106560000000000000000000), (-775514436348178436884677462319/5629499534213120000000000000000000), (-74109041293432125917731663257/5629499534213120000000000000000000), (8855406092856596067214313931/5629499534213120000000000000000000), (998116217255211903181304581/5629499534213120000000000000000000), (-16450491115971316587534983/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial162.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial162.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial162.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial162 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 3373366871407467551745891832240662), (Int.ofNat 645412100201124162808964360473220), (Int.ofNat 257746442525683760943105698972193), (Int.ofNat 16077907866590943158025154357380), (Int.negOfNat 6847862132204362639734288848943), (Int.negOfNat 656708410818573076297554987592), (Int.ofNat 97932717951540069323188598111), (Int.ofNat 10415309227264350473394510903), (Int.negOfNat 903004223778556229346122734), (Int.negOfNat 97032043192076200093758245), (Int.ofNat 5863398191615026321528580), (Int.ofNat 608059644713929336863317), (Int.negOfNat 28201628991494874897759), (Int.negOfNat 2758127043311493797476), (Int.ofNat 104140791295796952257), (Int.ofNat 9460024745602874122), (Int.negOfNat 312170381067923725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1686683435703733775872945916120331/2814749767106560000000000000000000), (32270605010056208140448218023661/281474976710656000000000000000000), (257746442525683760943105698972193/5629499534213120000000000000000000), (803895393329547157901257717869/281474976710656000000000000000000), (-6847862132204362639734288848943/5629499534213120000000000000000000), (-82088551352321634537194373449/703687441776640000000000000000000), (97932717951540069323188598111/5629499534213120000000000000000000), (10415309227264350473394510903/5629499534213120000000000000000000), (-451502111889278114673061367/2814749767106560000000000000000000), (-19406408638415240018751649/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial162.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial162.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial162.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial162.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial162 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial162 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial162 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 4926207734107878275419107127981013), (Int.negOfNat 878235530132800251068602953787024), (Int.ofNat 303622173910225953155821927618259), (Int.negOfNat 14108680767380770920727328939705), (Int.negOfNat 7092290814457736373618237512186), (Int.ofNat 651057481792176193136410780001), (Int.ofNat 98478270676607037677563550131), (Int.negOfNat 10406864967053115396818079653), (Int.negOfNat 903672717661079099161397534), (Int.ofNat 97024271156401747744163595), (Int.ofNat 5863913568802642814326530), (Int.negOfNat 608054562984236725498117), (Int.negOfNat 28201628991494874897759), (Int.ofNat 2758127043311493797476), (Int.ofNat 104140791295796952257), (Int.negOfNat 9460024745602874122), (Int.negOfNat 312170381067923725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-4926207734107878275419107127981013/5629499534213120000000000000000000), (-54889720633300015691787684611689/351843720888320000000000000000000), (303622173910225953155821927618259/5629499534213120000000000000000000), (-2821736153476154184145465787941/1125899906842624000000000000000000), (-3546145407228868186809118756093/2814749767106560000000000000000000), (651057481792176193136410780001/5629499534213120000000000000000000), (98478270676607037677563550131/5629499534213120000000000000000000), (-10406864967053115396818079653/5629499534213120000000000000000000), (-451836358830539549580698767/2814749767106560000000000000000000), (19404854231280349548832719/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial162.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial162.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial162.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 5668908823851765865776422067201560), (Int.ofNat 5646661696016094421236566173789), (Int.ofNat 116357780639376800169160958863962), (Int.negOfNat 35911732592989105154413239786217), (Int.ofNat 1842787752089280242402217459410), (Int.ofNat 776808579305743530152629109273), (Int.negOfNat 73523574592260152398137089957), (Int.negOfNat 8858263205927166679480720931), (Int.ofNat 997404840701544520226788081), (Int.ofNat 65805075647917304888266632), (Int.negOfNat 7979346569006750057309802), (Int.negOfNat 348908491069833539554882), (Int.ofNat 43547607996103018924537), (Int.ofNat 1393950472589946573405), (Int.negOfNat 174342282093202863390), (Int.negOfNat 4261466215731538894), (Int.ofNat 582809518297456235), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-141722720596294146644410551680039/140737488355328000000000000000000), (5646661696016094421236566173789/5629499534213120000000000000000000), (58178890319688400084580479431981/2814749767106560000000000000000000), (-35911732592989105154413239786217/5629499534213120000000000000000000), (184278775208928024240221745941/562949953421312000000000000000000), (776808579305743530152629109273/5629499534213120000000000000000000), (-73523574592260152398137089957/5629499534213120000000000000000000), (-8858263205927166679480720931/5629499534213120000000000000000000), (997404840701544520226788081/5629499534213120000000000000000000), (8225634455989663111033329/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial162.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial162.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial162.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5430694797287309476010145118363716), (Int.ofNat 144295156089053662933693419891291), (Int.negOfNat 14347503191796430828205772108912), (Int.negOfNat 4812491894260104404319405730265), (Int.ofNat 3985426490857974387764155834701), (Int.negOfNat 340043149326579399040671923537), (Int.negOfNat 70836973604220968114979565041), (Int.ofNat 8250005324184873919123495710), (Int.ofNat 652107697657223240205379610), (Int.negOfNat 89696016257304227376053288), (Int.negOfNat 3893462578232405596651835), (Int.ofNat 606396225732245813691684), (Int.ofNat 16639801026539484641529), (Int.negOfNat 2870148982874126116254), (Int.negOfNat 53970004440904300545), (Int.ofNat 10196944737588693448), (Int.ofNat 121781125060642680), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-1357673699321827369002536279590929/1407374883553280000000000000000000), (144295156089053662933693419891291/5629499534213120000000000000000000), (-896718949487276926762860756807/351843720888320000000000000000000), (-962498378852020880863881146053/1125899906842624000000000000000000), (3985426490857974387764155834701/5629499534213120000000000000000000), (-340043149326579399040671923537/5629499534213120000000000000000000), (-70836973604220968114979565041/5629499534213120000000000000000000), (825000532418487391912349571/562949953421312000000000000000000), (65210769765722324020537961/562949953421312000000000000000000), (-11212002032163028422006661/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial162.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial162.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial162.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5188468241279621939762357993183683), (Int.ofNat 120028986856066522456651069244308), (Int.ofNat 14495595267114886069717738842497), (Int.ofNat 7408475883018548857007802099802), (Int.negOfNat 1012198100531539249863797444009), (Int.negOfNat 398518546739086201037553352202), (Int.ofNat 53644928991012001583308244615), (Int.ofNat 5331330851569619549415388135), (Int.negOfNat 851122775943817988437929489), (Int.negOfNat 37885708274348432202180744), (Int.ofNat 7384926058549338898370811), (Int.ofNat 171874234151799572341775), (Int.negOfNat 42159316150437895923531), (Int.negOfNat 538279115869097343345), (Int.ofNat 173252762433112121167), (Int.ofNat 1102684208275313615), (Int.negOfNat 546350479528274375), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-5188468241279621939762357993183683/5629499534213120000000000000000000), (30007246714016630614162767311077/1407374883553280000000000000000000), (14495595267114886069717738842497/5629499534213120000000000000000000), (3704237941509274428503901049901/2814749767106560000000000000000000), (-1012198100531539249863797444009/5629499534213120000000000000000000), (-199259273369543100518776676101/2814749767106560000000000000000000), (10728985798202400316661648923/1125899906842624000000000000000000), (1066266170313923909883077627/1125899906842624000000000000000000), (-851122775943817988437929489/5629499534213120000000000000000000), (-4735713534293554025272593/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial162.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial162.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial162.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 4856221701735799563244288090528547), (Int.ofNat 214409381689588553476522622546540), (Int.ofNat 17616903959109706062084852943115), (Int.negOfNat 6674087535340198453673697359444), (Int.negOfNat 1290776999203608624812922257692), (Int.ofNat 295731056660364874260231216888), (Int.ofNat 32373500526928866536405447752), (Int.negOfNat 6797771468148947471088841866), (Int.negOfNat 300430026043675620538496067), (Int.ofNat 77980800998344307189571194), (Int.ofNat 1427583667965127397108436), (Int.negOfNat 548991752839291686464307), (Int.negOfNat 3333802418422877614366), (Int.ofNat 2664555755520982282947), (Int.negOfNat 1311283966802337648), (Int.negOfNat 9678587793681321783), (Int.ofNat 56455118023577745), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-4856221701735799563244288090528547/5629499534213120000000000000000000), (10720469084479427673826131127327/281474976710656000000000000000000), (3523380791821941212416970588623/1125899906842624000000000000000000), (-1668521883835049613418424339861/1407374883553280000000000000000000), (-322694249800902156203230564423/1407374883553280000000000000000000), (36966382082545609282528902111/703687441776640000000000000000000), (4046687565866108317050680969/703687441776640000000000000000000), (-3398885734074473735544420933/2814749767106560000000000000000000), (-300430026043675620538496067/5629499534213120000000000000000000), (38990400499172153594785597/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial162.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial162.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial162.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 4420351910248985290024985422071971), (Int.ofNat 190185088477289133023282692356203), (Int.negOfNat 26724104010917519150980591487695), (Int.negOfNat 3918074052773611999428473483122), (Int.ofNat 1680027828127356770832060674752), (Int.ofNat 131606800927499554558042430871), (Int.negOfNat 46996198286700652046996100374), (Int.negOfNat 1710945943777830830623298804), (Int.ofNat 711221662760529666345657956), (Int.ofNat 7453277521749673174036685), (Int.negOfNat 6287617195837358876790981), (Int.ofNat 15242824729135443778666), (Int.ofNat 36605282341507220437359), (Int.negOfNat 334201525395481374335), (Int.negOfNat 152195908194664033190), (Int.ofNat 1931861702775846214), (Int.ofNat 509891440759092515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-4420351910248985290024985422071971/5629499534213120000000000000000000), (190185088477289133023282692356203/5629499534213120000000000000000000), (-5344820802183503830196118297539/1125899906842624000000000000000000), (-1959037026386805999714236741561/2814749767106560000000000000000000), (26250434814489949544250948043/87960930222080000000000000000000), (131606800927499554558042430871/5629499534213120000000000000000000), (-23498099143350326023498050187/2814749767106560000000000000000000), (-427736485944457707655824701/1407374883553280000000000000000000), (177805415690132416586414489/1407374883553280000000000000000000), (1490655504349934634807337/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial162.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial162.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial162.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 4150178010334817419028275606966713), (Int.ofNat 91485752014657419118117897812239), (Int.negOfNat 10572963494309646514599080678412), (Int.ofNat 7531460741796074857918555343280), (Int.ofNat 444386163089856997632110783012), (Int.negOfNat 289211947248738705678081938462), (Int.negOfNat 5202261178718560537205791860), (Int.ofNat 5616121011345109400246334016), (Int.negOfNat 16364370804203141183876964), (Int.negOfNat 62853315995023889191479156), (Int.ofNat 908771484300109280224938), (Int.ofNat 445234811827886400282038), (Int.negOfNat 9149598518009561297375), (Int.negOfNat 2178329473400274197866), (Int.ofNat 51901533267671273498), (Int.ofNat 7996295255058601858), (Int.negOfNat 234691361107798170), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-4150178010334817419028275606966713/5629499534213120000000000000000000), (91485752014657419118117897812239/5629499534213120000000000000000000), (-2643240873577411628649770169603/1407374883553280000000000000000000), (94143259272450935723981941791/70368744177664000000000000000000), (111096540772464249408027695753/1407374883553280000000000000000000), (-144605973624369352839040969231/2814749767106560000000000000000000), (-260113058935928026860289593/281474976710656000000000000000000), (87751890802267334378848969/87960930222080000000000000000000), (-4091092701050785295969241/1407374883553280000000000000000000), (-15713328998755972297869789/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial162.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial162.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial162.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 3951039941268094750044077263053310), (Int.ofNat 132019780175785260287385899374876), (Int.ofNat 24372716674480031999027992647243), (Int.ofNat 1494662530712413660821063243073), (Int.negOfNat 1429971139949553319241051272725), (Int.ofNat 4994050853187125899708747907), (Int.ofNat 38027118658160934334081544799), (Int.negOfNat 910401862078349650460268545), (Int.negOfNat 543121450506375914213356283), (Int.ofNat 17663723168744478494917859), (Int.ofNat 4738081340952299502796993), (Int.negOfNat 174057998341967285011328), (Int.negOfNat 27571745263611411691227), (Int.ofNat 1069058659523672147620), (Int.ofNat 114641122922719641772), (Int.negOfNat 4550335546245939593), (Int.negOfNat 414020320961837180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-395103994126809475004407726305331/562949953421312000000000000000000), (33004945043946315071846474843719/1407374883553280000000000000000000), (24372716674480031999027992647243/5629499534213120000000000000000000), (1494662530712413660821063243073/5629499534213120000000000000000000), (-57198845597982132769642050909/225179981368524800000000000000000), (4994050853187125899708747907/5629499534213120000000000000000000), (38027118658160934334081544799/5629499534213120000000000000000000), (-182080372415669930092053709/1125899906842624000000000000000000), (-543121450506375914213356283/5629499534213120000000000000000000), (17663723168744478494917859/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial162.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial162.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial162.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 3598080340839118176421204650059320), (Int.ofNat 208486622001858550062585176594477), (Int.ofNat 7091774586067653141159283666682), (Int.negOfNat 4986436362610290316107668329454), (Int.ofNat 162935706490171816557585991088), (Int.ofNat 207856700512176455746593027893), (Int.negOfNat 11653000826588200178893585071), (Int.negOfNat 3967435150788363674462252065), (Int.ofNat 240930929965436341321325657), (Int.ofNat 43315841710566443804835251), (Int.negOfNat 2663028085863720756658617), (Int.negOfNat 303380403889059846528922), (Int.ofNat 18592087584045738068263), (Int.ofNat 1473329684947572962150), (Int.negOfNat 89463436895518517778), (Int.negOfNat 5300433055416673717), (Int.ofNat 329209497317823880), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-89952008520977954410530116251483/140737488355328000000000000000000), (208486622001858550062585176594477/5629499534213120000000000000000000), (3545887293033826570579641833341/2814749767106560000000000000000000), (-2493218181305145158053834164727/2814749767106560000000000000000000), (10183481655635738534849124443/351843720888320000000000000000000), (207856700512176455746593027893/5629499534213120000000000000000000), (-11653000826588200178893585071/5629499534213120000000000000000000), (-793487030157672734892450413/1125899906842624000000000000000000), (240930929965436341321325657/5629499534213120000000000000000000), (43315841710566443804835251/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial162.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial162.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial162.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 3184546133054805985734076835773979), (Int.ofNat 195174160508469894927373431187972), (Int.negOfNat 7157106220798781957349797834487), (Int.ofNat 1158419495114336464772854123303), (Int.ofNat 830118487934005248191193358042), (Int.negOfNat 98161695608705306621022809778), (Int.negOfNat 23193881157282953009291591690), (Int.ofNat 2553672318354806131333567324), (Int.ofNat 328374892779203168883857916), (Int.negOfNat 34003260065422627697932214), (Int.negOfNat 2810464791047163097318522), (Int.ofNat 278542897299854976651812), (Int.ofNat 16059012789715795787415), (Int.negOfNat 1546839303071278249804), (Int.negOfNat 65565132062977786202), (Int.ofNat 6261416210610181352), (Int.ofNat 270890133059568990), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-3184546133054805985734076835773979/5629499534213120000000000000000000), (48793540127117473731843357796993/1407374883553280000000000000000000), (-7157106220798781957349797834487/5629499534213120000000000000000000), (1158419495114336464772854123303/5629499534213120000000000000000000), (415059243967002624095596679021/2814749767106560000000000000000000), (-49080847804352653310511404889/2814749767106560000000000000000000), (-2319388115728295300929159169/562949953421312000000000000000000), (638418079588701532833391831/1407374883553280000000000000000000), (82093723194800792220964479/1407374883553280000000000000000000), (-17001630032711313848966107/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial162.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial162.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial162.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 2804511298668156716552009506082528), (Int.ofNat 196095412200201863203533091710716), (Int.ofNat 8420902448832323145971994978614), (Int.ofNat 1967497335704567372032541386408), (Int.negOfNat 622011607317418334626864794894), (Int.negOfNat 96774721801027227060349722637), (Int.ofNat 21736565661316860141275765096), (Int.ofNat 1903123050830949924286700414), (Int.negOfNat 365504722643337871182262064), (Int.negOfNat 20413032093615675672248595), (Int.ofNat 3616298393644354528021579), (Int.ofNat 138016287354531836484934), (Int.negOfNat 23575075002198757929781), (Int.negOfNat 641123655973379160485), (Int.ofNat 109100146171807354160), (Int.ofNat 2086074090206833796), (Int.negOfNat 352162539576715495), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-87640978083379897392250297065079/175921860444160000000000000000000), (49023853050050465800883272927679/1407374883553280000000000000000000), (4210451224416161572985997489307/2814749767106560000000000000000000), (245937166963070921504067673301/703687441776640000000000000000000), (-311005803658709167313432397447/2814749767106560000000000000000000), (-96774721801027227060349722637/5629499534213120000000000000000000), (2717070707664607517659470637/703687441776640000000000000000000), (951561525415474962143350207/2814749767106560000000000000000000), (-22844045165208616948891379/351843720888320000000000000000000), (-4082606418723135134449719/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial162.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial162.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial162.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 2374411257569859548232543139656553), (Int.ofNat 230366821472777913611630153158514), (Int.ofNat 3346149128733730895592560797393), (Int.negOfNat 3042093614069453982655355841593), (Int.negOfNat 193035603764231387321317277287), (Int.ofNat 149783911291703861072478181142), (Int.ofNat 6468515900508499912709158107), (Int.negOfNat 3302815067927392764899315074), (Int.negOfNat 91498242004553730076072527), (Int.ofNat 40559213406738449201763426), (Int.ofNat 719102854690874542968346), (Int.negOfNat 316131629332437257418093), (Int.negOfNat 3543383401438522185606), (Int.ofNat 1700144335865898560673), (Int.ofNat 11456051954372947552), (Int.negOfNat 6728407456926839277), (Int.negOfNat 92653889975348565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-2374411257569859548232543139656553/5629499534213120000000000000000000), (115183410736388956805815076579257/2814749767106560000000000000000000), (3346149128733730895592560797393/5629499534213120000000000000000000), (-3042093614069453982655355841593/5629499534213120000000000000000000), (-193035603764231387321317277287/5629499534213120000000000000000000), (74891955645851930536239090571/2814749767106560000000000000000000), (6468515900508499912709158107/5629499534213120000000000000000000), (-1651407533963696382449657537/2814749767106560000000000000000000), (-91498242004553730076072527/5629499534213120000000000000000000), (20279606703369224600881713/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial162.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial162.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial162.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 1922936595754837797209512078876242), (Int.ofNat 212814040378895029144931149329666), (Int.negOfNat 8201257509226580509093785916321), (Int.ofNat 642232725846651756980566657586), (Int.ofNat 825661120300704168656437503016), (Int.negOfNat 12610149011392851338383458158), (Int.negOfNat 24864409774618692259522057875), (Int.ofNat 186159068142751591722906055), (Int.ofNat 389557261795946928340390781), (Int.negOfNat 2706593910876945582031936), (Int.negOfNat 3702407861816558271970249), (Int.ofNat 28697538100401327604075), (Int.ofNat 23532372252468368424059), (Int.negOfNat 201546377647768789285), (Int.negOfNat 106625946960855724133), (Int.ofNat 1058236425661647775), (Int.ofNat 315703500807533635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-961468297877418898604756039438121/2814749767106560000000000000000000), (106407020189447514572465574664833/2814749767106560000000000000000000), (-8201257509226580509093785916321/5629499534213120000000000000000000), (321116362923325878490283328793/2814749767106560000000000000000000), (103207640037588021082054687877/703687441776640000000000000000000), (-6305074505696425669191729079/2814749767106560000000000000000000), (-198915278196949538076176463/45035996273704960000000000000000), (37231813628550318344581211/1125899906842624000000000000000000), (389557261795946928340390781/5629499534213120000000000000000000), (-42290529857452274719249/87960930222080000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial162.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial162.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial162.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 1513641422505977941088866954776414), (Int.ofNat 208812172885143985927423683197739), (Int.ofNat 9262125241598927406018044748124), (Int.ofNat 3499453741044541935552412297472), (Int.negOfNat 360533529600652461840261448504), (Int.negOfNat 153072554046090693016523729423), (Int.ofNat 8808020682944305681732701929), (Int.ofNat 3157439206184071161338760190), (Int.negOfNat 128269905508834897382453490), (Int.negOfNat 37377932381546304358716512), (Int.ofNat 1229884985864352319794455), (Int.ofNat 285191132517421363673966), (Int.negOfNat 8169144236223332135131), (Int.negOfNat 1514430666685020039666), (Int.ofNat 38887385889847981705), (Int.ofNat 5982851056835906462), (Int.negOfNat 85582353108871860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-756820711252988970544433477388207/2814749767106560000000000000000000), (208812172885143985927423683197739/5629499534213120000000000000000000), (2315531310399731851504511187031/1407374883553280000000000000000000), (13669741175955241935751610537/21990232555520000000000000000000), (-45066691200081557730032681063/703687441776640000000000000000000), (-153072554046090693016523729423/5629499534213120000000000000000000), (8808020682944305681732701929/5629499534213120000000000000000000), (315743920618407116133876019/562949953421312000000000000000000), (-12826990550883489738245349/562949953421312000000000000000000), (-1168060386923322011209891/175921860444160000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial162.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial162.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial162.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 1040722114663150417037656338761993), (Int.ofNat 266968680947930475559456172717496), (Int.ofNat 13215290212471584342608821651496), (Int.negOfNat 2731457535683550776333489622104), (Int.negOfNat 746023042185346127377107176538), (Int.ofNat 102109680809089459657986905156), (Int.ofNat 21104642650849485780909157883), (Int.negOfNat 1938350596338768462569891139), (Int.negOfNat 318572294393376127548924659), (Int.ofNat 22359209053427540792649468), (Int.ofNat 2967755380899330033166058), (Int.negOfNat 171594973496857280811818), (Int.negOfNat 18673329217622509029753), (Int.ofNat 929590550480395199425), (Int.ofNat 84442082153080791760), (Int.negOfNat 3840662521012769996), (Int.negOfNat 279244462038351775), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1040722114663150417037656338761993/5629499534213120000000000000000000), (33371085118491309444932021589687/703687441776640000000000000000000), (1651911276558948042826102706437/703687441776640000000000000000000), (-341432191960443847041686202763/703687441776640000000000000000000), (-373011521092673063688553588269/2814749767106560000000000000000000), (25527420202272364914496726289/1407374883553280000000000000000000), (21104642650849485780909157883/5629499534213120000000000000000000), (-1938350596338768462569891139/5629499534213120000000000000000000), (-318572294393376127548924659/5629499534213120000000000000000000), (5589802263356885198162367/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial162.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial162.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial162.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 483409009501457422271178939045452), (Int.ofNat 274270257678959627917771269919545), (Int.negOfNat 9586270540358115047699439548874), (Int.negOfNat 2738106293972014350072984266642), (Int.ofNat 762652296140496807021611464585), (Int.ofNat 112244124595799940246009454598), (Int.negOfNat 20098885069004048433872103609), (Int.negOfNat 2214367021785687633265695177), (Int.ofNat 294365376954032038312304136), (Int.ofNat 25617258304452315311561195), (Int.negOfNat 2727050689807927045843610), (Int.negOfNat 193713852719584232052283), (Int.ofNat 17275748463482113266101), (Int.ofNat 1027721985690225629894), (Int.negOfNat 79077819721043356843), (Int.negOfNat 4116088351515225638), (Int.ofNat 251665583270031665), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-120852252375364355567794734761363/1407374883553280000000000000000000), (54854051535791925583554253983909/1125899906842624000000000000000000), (-4793135270179057523849719774437/2814749767106560000000000000000000), (-1369053146986007175036492133321/2814749767106560000000000000000000), (152530459228099361404322292917/1125899906842624000000000000000000), (56122062297899970123004727299/2814749767106560000000000000000000), (-20098885069004048433872103609/5629499534213120000000000000000000), (-2214367021785687633265695177/5629499534213120000000000000000000), (36795672119254004789038017/703687441776640000000000000000000), (5123451660890463062312239/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial162.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial162.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial162.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 19191416565574326942248658233284), (Int.ofNat 231946058287055431052141067768324), (Int.negOfNat 4433534408588743965262589983597), (Int.ofNat 4014342951707359874734793005323), (Int.ofNat 449757024135449573592126190627), (Int.negOfNat 157148657761266964712393781316), (Int.negOfNat 11764294449267362089513293551), (Int.ofNat 3054727155996963327213474213), (Int.ofNat 170561662110287723709334464), (Int.negOfNat 35276818435145166926036485), (Int.negOfNat 1568589558331434558190370), (Int.ofNat 267770440375700762059627), (Int.ofNat 9904816448203812428339), (Int.negOfNat 1428526690422414379976), (Int.negOfNat 45302674121616545537), (Int.ofNat 5674011964524492362), (Int.ofNat 136114274136083585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(4797854141393581735562164558321/1407374883553280000000000000000000), (57986514571763857763035266942081/1407374883553280000000000000000000), (-4433534408588743965262589983597/5629499534213120000000000000000000), (4014342951707359874734793005323/5629499534213120000000000000000000), (449757024135449573592126190627/5629499534213120000000000000000000), (-39287164440316741178098445329/1407374883553280000000000000000000), (-11764294449267362089513293551/5629499534213120000000000000000000), (3054727155996963327213474213/5629499534213120000000000000000000), (2665025970473245682958351/87960930222080000000000000000000), (-7055363687029033385207297/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial162.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial162.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial162.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 499294157219154946372463381954478), (Int.ofNat 263402667408493969878525929306892), (Int.ofNat 17237135845236862224455376569147), (Int.ofNat 1258702949581379123114912521108), (Int.negOfNat 932539534531750106208773425668), (Int.negOfNat 40655890270719596772372029208), (Int.ofNat 25339445796080951046479272397), (Int.ofNat 695917867821363781736599371), (Int.negOfNat 377473380627104534887266781), (Int.negOfNat 7631898573775177553702722), (Int.ofNat 3518833528422356426570762), (Int.ofNat 58178092647423153633672), (Int.negOfNat 22294622560999607626197), (Int.negOfNat 321443475463875468105), (Int.ofNat 101529174219562155270), (Int.ofNat 1444568504822096654), (Int.negOfNat 346183719480057375), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(249647078609577473186231690977239/2814749767106560000000000000000000), (65850666852123492469631482326723/1407374883553280000000000000000000), (17237135845236862224455376569147/5629499534213120000000000000000000), (314675737395344780778728130277/1407374883553280000000000000000000), (-233134883632937526552193356417/1407374883553280000000000000000000), (-5081986283839949596546503651/703687441776640000000000000000000), (25339445796080951046479272397/5629499534213120000000000000000000), (695917867821363781736599371/5629499534213120000000000000000000), (-377473380627104534887266781/5629499534213120000000000000000000), (-3815949286887588776851361/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial162.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial162.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial162.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1090509929437449222738932295714913), (Int.ofNat 319152856515074022021846047203479), (Int.ofNat 5034112636802676715188918012724), (Int.negOfNat 4047307121048742677222006046002), (Int.negOfNat 30503791270723690786938112637), (Int.ofNat 165215658659002222059873001457), (Int.negOfNat 950382422844071717163795169), (Int.negOfNat 3312968202612478443860402990), (Int.ofNat 24991076059483466763311950), (Int.ofNat 39051154784980829619364668), (Int.negOfNat 245536890398244737496865), (Int.negOfNat 300386386430524490447254), (Int.ofNat 1315276422623187124211), (Int.ofNat 1614953969707777250594), (Int.negOfNat 4213052966871808935), (Int.negOfNat 6410931956510311688), (Int.ofNat 54274981871197460), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1090509929437449222738932295714913/5629499534213120000000000000000000), (319152856515074022021846047203479/5629499534213120000000000000000000), (1258528159200669178797229503181/1407374883553280000000000000000000), (-2023653560524371338611003023001/2814749767106560000000000000000000), (-30503791270723690786938112637/5629499534213120000000000000000000), (165215658659002222059873001457/5629499534213120000000000000000000), (-950382422844071717163795169/5629499534213120000000000000000000), (-331296820261247844386040299/562949953421312000000000000000000), (499821521189669335266239/112589990684262400000000000000000), (9762788696245207404841167/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial162.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial162.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial162.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 1720913135690071222121736574140154), (Int.ofNat 301407110139462545516161237606162), (Int.negOfNat 9005190557058334250377134040126), (Int.ofNat 548835206113495508485423510326), (Int.ofNat 807190955251556213180299226058), (Int.negOfNat 44774823428222580362022785794), (Int.negOfNat 23142953202074674934061848610), (Int.ofNat 1087286040632718796816069065), (Int.ofNat 358337473097883090119383459), (Int.negOfNat 13338239311566658197594476), (Int.negOfNat 3442042181048394318210661), (Int.ofNat 98959371168151204560065), (Int.ofNat 22298852047353854417431), (Int.negOfNat 492186503004112474635), (Int.negOfNat 103240056475282619607), (Int.ofNat 1714213502634128625), (Int.ofNat 309724680710875515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(860456567845035611060868287070077/2814749767106560000000000000000000), (150703555069731272758080618803081/2814749767106560000000000000000000), (-4502595278529167125188567020063/2814749767106560000000000000000000), (274417603056747754242711755163/2814749767106560000000000000000000), (403595477625778106590149613029/2814749767106560000000000000000000), (-22387411714111290181011392897/2814749767106560000000000000000000), (-2314295320207467493406184861/562949953421312000000000000000000), (217457208126543759363213813/1125899906842624000000000000000000), (358337473097883090119383459/5629499534213120000000000000000000), (-3334559827891664549398619/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial162.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial162.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial162.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 2302319228860973867862526045925010), (Int.ofNat 290584360504848139994467709045951), (Int.ofNat 5799969889075611045520735197779), (Int.ofNat 2645417825663852015566023000252), (Int.negOfNat 416669909722729858018598798412), (Int.negOfNat 120342418121302287879824144798), (Int.ofNat 14285810880074897901790079818), (Int.ofNat 2588726776264241911977188916), (Int.negOfNat 231660923654481681739975053), (Int.negOfNat 32369669303606223741437264), (Int.ofNat 2173024812766185066156564), (Int.ofNat 260980939152128179772047), (Int.negOfNat 13230581804914903090534), (Int.negOfNat 1451680405101768236927), (Int.ofNat 56537664585542130088), (Int.ofNat 5892575012602940023), (Int.negOfNat 232511224955417885), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(230231922886097386786252604592501/562949953421312000000000000000000), (290584360504848139994467709045951/5629499534213120000000000000000000), (5799969889075611045520735197779/5629499534213120000000000000000000), (661354456415963003891505750063/1407374883553280000000000000000000), (-104167477430682464504649699603/1407374883553280000000000000000000), (-60171209060651143939912072399/2814749767106560000000000000000000), (7142905440037448950895039909/2814749767106560000000000000000000), (647181694066060477994297229/1407374883553280000000000000000000), (-231660923654481681739975053/5629499534213120000000000000000000), (-2023104331475388983839829/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial162.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial162.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial162.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 2918505961238252122346850927873900), (Int.ofNat 326172919117503388111260143711799), (Int.ofNat 6680210825123365179947137992425), (Int.negOfNat 2312839053895162380569072576644), (Int.negOfNat 389982738674110597107903266758), (Int.ofNat 122993369034519661122213516680), (Int.ofNat 12944588151644114070627249484), (Int.negOfNat 2776619266473135031365788526), (Int.negOfNat 228340713699653565472317866), (Int.ofNat 33754363272302793994092245), (Int.ofNat 2439535298823451619143581), (Int.negOfNat 253502537088388445326836), (Int.negOfNat 17060541000356389451099), (Int.ofNat 1290237515359820847675), (Int.ofNat 83216804593231708670), (Int.negOfNat 4748759413685288454), (Int.negOfNat 273265641941693655), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(29185059612382521223468509278739/56294995342131200000000000000000), (326172919117503388111260143711799/5629499534213120000000000000000000), (267208433004934607197885519697/225179981368524800000000000000000), (-578209763473790595142268144161/1407374883553280000000000000000000), (-194991369337055298553951633379/2814749767106560000000000000000000), (3074834225862991528055337917/140737488355328000000000000000000), (3236147037911028517656812371/1407374883553280000000000000000000), (-1388309633236567515682894263/2814749767106560000000000000000000), (-114170356849826782736158933/2814749767106560000000000000000000), (6750872654460558798818449/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial162.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial162.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial162.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 3577199788509118531165710014516182), (Int.ofNat 323594392930562153908138787066529), (Int.negOfNat 5709728862066733013041483875448), (Int.negOfNat 199190589223077863429973502683), (Int.ofNat 739988665776582865784911326912), (Int.ofNat 21785294562983848502316096837), (Int.negOfNat 25046080874480481547560027630), (Int.negOfNat 829421346566609722993227226), (Int.ofNat 413018653284762816520908014), (Int.ofNat 14971875639934649371123466), (Int.negOfNat 3927827048239760109955998), (Int.negOfNat 150797848871517373563298), (Int.ofNat 24115408730915572395035), (Int.ofNat 952308641880516234166), (Int.negOfNat 103942897084072031378), (Int.negOfNat 4210282473980220098), (Int.ofNat 410747468039638310), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(1788599894254559265582855007258091/2814749767106560000000000000000000), (323594392930562153908138787066529/5629499534213120000000000000000000), (-713716107758341626630185484431/703687441776640000000000000000000), (-199190589223077863429973502683/5629499534213120000000000000000000), (11562322902759107277889239483/87960930222080000000000000000000), (21785294562983848502316096837/5629499534213120000000000000000000), (-2504608087448048154756002763/562949953421312000000000000000000), (-414710673283304861496613613/2814749767106560000000000000000000), (206509326642381408260454007/2814749767106560000000000000000000), (7485937819967324685561733/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial162.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial162.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial162.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 4210893139381621576291314429462219), (Int.ofNat 319043470814953185840849086430087), (Int.ofNat 6790613638974682086705066792007), (Int.ofNat 2877110291622091515416235522003), (Int.negOfNat 310084482259292469200095449517), (Int.negOfNat 166713880770641548834860901953), (Int.ofNat 5781965586092425478388549396), (Int.ofNat 4033294177370381393106045755), (Int.negOfNat 15520223526525019853813247), (Int.negOfNat 50866210144464813928851649), (Int.negOfNat 570578510037752731162653), (Int.ofNat 385045573278838134025138), (Int.ofNat 7155178148827158075647), (Int.negOfNat 1962799301827569538120), (Int.negOfNat 44009389768524646492), (Int.ofNat 7367233257155381833), (Int.ofNat 177394522144438320), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(4210893139381621576291314429462219/5629499534213120000000000000000000), (319043470814953185840849086430087/5629499534213120000000000000000000), (6790613638974682086705066792007/5629499534213120000000000000000000), (2877110291622091515416235522003/5629499534213120000000000000000000), (-310084482259292469200095449517/5629499534213120000000000000000000), (-166713880770641548834860901953/5629499534213120000000000000000000), (1445491396523106369597137349/1407374883553280000000000000000000), (806658835474076278621209151/1125899906842624000000000000000000), (-15520223526525019853813247/5629499534213120000000000000000000), (-50866210144464813928851649/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial162.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial162.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial162.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 4889719729829273591888694158977136), (Int.ofNat 360256883630377966943921753509386), (Int.ofNat 7114408996769642443115664415948), (Int.negOfNat 3381917845105110650930497466730), (Int.negOfNat 714698105513346861086142779126), (Int.ofNat 138808006420942749270095491521), (Int.ofNat 30080882203603192920637271881), (Int.negOfNat 2095397449840161363346879105), (Int.negOfNat 551854412111070210877962077), (Int.ofNat 12212705103485617778422869), (Int.ofNat 5330702534971539113945237), (Int.negOfNat 17303127550621994236738), (Int.negOfNat 32609652259671468448963), (Int.negOfNat 186863712641592677210), (Int.ofNat 139780106019078997858), (Int.ofNat 1514420274338291957), (Int.negOfNat 505265604249664020), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(305607483114329599493043384936071/351843720888320000000000000000000), (180128441815188983471960876754693/2814749767106560000000000000000000), (1778602249192410610778916103987/1407374883553280000000000000000000), (-338191784510511065093049746673/562949953421312000000000000000000), (-357349052756673430543071389563/2814749767106560000000000000000000), (138808006420942749270095491521/5629499534213120000000000000000000), (30080882203603192920637271881/5629499534213120000000000000000000), (-419079489968032272669375821/1125899906842624000000000000000000), (-551854412111070210877962077/5629499534213120000000000000000000), (12212705103485617778422869/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial162.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial162.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial162.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 5606169711006893762186622850756544), (Int.ofNat 340691940180062201374568572139676), (Int.negOfNat 14287813212869215437914969163193), (Int.negOfNat 753405675189183148455280347975), (Int.ofNat 1389545507723135027545277034234), (Int.ofNat 140406926816338862639758183529), (Int.negOfNat 37061885319216675985764025210), (Int.negOfNat 4926049648628295056744426054), (Int.ofNat 365316352769397356033669944), (Int.ofNat 64264737662779822184877524), (Int.negOfNat 1934747170110749009715158), (Int.negOfNat 481238216620551356843452), (Int.ofNat 5943222504802368738925), (Int.ofNat 2423942463165123566464), (Int.negOfNat 8329755330168798878), (Int.negOfNat 9078313921519623592), (Int.negOfNat 34264334242170130), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(87596401734482715034165982043071/87960930222080000000000000000000), (85172985045015550343642143034919/1407374883553280000000000000000000), (-14287813212869215437914969163193/5629499534213120000000000000000000), (-30136227007567325938211213919/225179981368524800000000000000000), (694772753861567513772638517117/2814749767106560000000000000000000), (140406926816338862639758183529/5629499534213120000000000000000000), (-3706188531921667598576402521/562949953421312000000000000000000), (-2463024824314147528372213027/2814749767106560000000000000000000), (45664544096174669504208743/703687441776640000000000000000000), (16066184415694955546219381/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial162.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial162.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial162.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 6248221849423124533015124269709139), (Int.ofNat 321382172686319946287019890834935), (Int.ofNat 14483958147168348778072486976321), (Int.ofNat 8242191404162760315639693328126), (Int.negOfNat 185845908242982659333331406619), (Int.negOfNat 453370084854178074147267229708), (Int.negOfNat 34685672109873652939558592676), (Int.ofNat 6173640063199135317920918176), (Int.ofNat 676770691584358278662922044), (Int.negOfNat 45379700819896479093320065), (Int.negOfNat 6345323784621862197178409), (Int.ofNat 215778702677101516291836), (Int.ofNat 37824621110063955424561), (Int.negOfNat 719983778849935847895), (Int.negOfNat 160071875061772131480), (Int.ofNat 1699938690871547964), (Int.ofNat 528218646508555635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(6248221849423124533015124269709139/5629499534213120000000000000000000), (64276434537263989257403978166987/1125899906842624000000000000000000), (14483958147168348778072486976321/5629499534213120000000000000000000), (4121095702081380157819846664063/2814749767106560000000000000000000), (-185845908242982659333331406619/5629499534213120000000000000000000), (-113342521213544518536816807427/1407374883553280000000000000000000), (-8671418027468413234889648169/1407374883553280000000000000000000), (192926251974972978685028693/175921860444160000000000000000000), (169192672896089569665730511/1407374883553280000000000000000000), (-9075940163979295818664013/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial162.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial162.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial162.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 6996092633979991325650904596149189), (Int.ofNat 432673042409519719136823515621247), (Int.ofNat 19970348658500093536403538971619), (Int.negOfNat 12587450127749184392293511064969), (Int.negOfNat 4568847989795913017617992180348), (Int.negOfNat 180649895985743304035656264512), (Int.ofNat 80882500034242780739864489353), (Int.ofNat 6330158066635433162568585364), (Int.negOfNat 755170023369209867634918903), (Int.negOfNat 75463992741938857065897026), (Int.ofNat 4587911082244440247591024), (Int.ofNat 535505363228469876230653), (Int.negOfNat 19902463622702673880574), (Int.negOfNat 2615601971165926767053), (Int.ofNat 65239237354584844088), (Int.ofNat 9545305167836281517), (Int.negOfNat 143971908842050295), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(6996092633979991325650904596149189/5629499534213120000000000000000000), (432673042409519719136823515621247/5629499534213120000000000000000000), (19970348658500093536403538971619/5629499534213120000000000000000000), (-12587450127749184392293511064969/5629499534213120000000000000000000), (-1142211997448978254404498045087/1407374883553280000000000000000000), (-2822654624777239125557129133/87960930222080000000000000000000), (80882500034242780739864489353/5629499534213120000000000000000000), (1582539516658858290642146341/1407374883553280000000000000000000), (-755170023369209867634918903/5629499534213120000000000000000000), (-37731996370969428532948513/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial162.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial162.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial162.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 7767498620200508315491211185012132), (Int.ofNat 218296999164210194898835760755464), (Int.negOfNat 157627830418807448632394938516376), (Int.negOfNat 41546953051768624185189896193029), (Int.negOfNat 819120694218314153290899402565), (Int.ofNat 881266908711235522726394360002), (Int.ofNat 55867035111501244766517165095), (Int.negOfNat 10136441635933532505567434165), (Int.negOfNat 826721867728261093641971851), (Int.ofNat 75962306721655213095033036), (Int.ofNat 6937341113849731589711279), (Int.negOfNat 403883392709299801474165), (Int.negOfNat 39135216310641837184879), (Int.ofNat 1608660378264897014905), (Int.ofNat 160554352639856818493), (Int.negOfNat 4844249206740029535), (Int.negOfNat 491759607739373775), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1941874655050127078872802796253033/1407374883553280000000000000000000), (27287124895526274362354470094433/703687441776640000000000000000000), (-19703478802350931079049367314547/703687441776640000000000000000000), (-41546953051768624185189896193029/5629499534213120000000000000000000), (-163824138843662830658179880513/1125899906842624000000000000000000), (440633454355617761363197180001/2814749767106560000000000000000000), (11173407022300248953303433019/1125899906842624000000000000000000), (-2027288327186706501113486833/1125899906842624000000000000000000), (-826721867728261093641971851/5629499534213120000000000000000000), (18990576680413803273758259/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial162.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial162.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial162.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 7258411692032161387994525146137407), (Int.negOfNat 860944359145300565241711013897990), (Int.negOfNat 350535932829072575258877650246420), (Int.negOfNat 10574367500996072932851442788665), (Int.ofNat 7959673019535967029276523650625), (Int.ofNat 523687262104738361020018439958), (Int.negOfNat 112104942820862449466409251299), (Int.negOfNat 8653577799896394478467876750), (Int.ofNat 1037785335641930989189721110), (Int.ofNat 83434764355592223032605602), (Int.negOfNat 6721871773574243156740575), (Int.negOfNat 538722664183966360080096), (Int.ofNat 32034800737116162192351), (Int.ofNat 2504554053688522762286), (Int.negOfNat 116616277555202950385), (Int.negOfNat 8799748767745348702), (Int.ofNat 322208151926270720), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(7258411692032161387994525146137407/5629499534213120000000000000000000), (-86094435914530056524171101389799/562949953421312000000000000000000), (-17526796641453628762943882512321/281474976710656000000000000000000), (-2114873500199214586570288557733/1125899906842624000000000000000000), (12735476831257547246842437841/9007199254740992000000000000000), (261843631052369180510009219979/2814749767106560000000000000000000), (-112104942820862449466409251299/5629499534213120000000000000000000), (-34614311199585577913871507/22517998136852480000000000000000), (103778533564193098918972111/562949953421312000000000000000000), (41717382177796111516302801/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial162.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial162.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial162.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 4185915243523037442510683209291850), (Int.negOfNat 2117561587702899779446159035473546), (Int.negOfNat 211621307746218160193979528131995), (Int.ofNat 53454206139374536488203970060540), (Int.ofNat 5437713391508277953667590530036), (Int.negOfNat 981544676222943770516646104331), (Int.negOfNat 89169253178112613873168098833), (Int.ofNat 11691743244220177765928051809), (Int.ofNat 947119286597536656839215649), (Int.negOfNat 94163560430810232222150308), (Int.negOfNat 6879419735657747518303878), (Int.ofNat 541506704875816563687328), (Int.ofNat 35984500948116670987413), (Int.negOfNat 2323322947202375335765), (Int.negOfNat 141555504634420920680), (Int.ofNat 7626675302091151756), (Int.ofNat 455300568970191915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(83718304870460748850213664185837/112589990684262400000000000000000), (-1058780793851449889723079517736773/2814749767106560000000000000000000), (-42324261549243632038795905626399/1125899906842624000000000000000000), (2672710306968726824410198503027/281474976710656000000000000000000), (1359428347877069488416897632509/1407374883553280000000000000000000), (-981544676222943770516646104331/5629499534213120000000000000000000), (-89169253178112613873168098833/5629499534213120000000000000000000), (11691743244220177765928051809/5629499534213120000000000000000000), (947119286597536656839215649/5629499534213120000000000000000000), (-23540890107702558055537577/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial162.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial162.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial162.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 416487376596739525681766017472898), (Int.negOfNat 2238271165474061446183236759132860), (Int.ofNat 148743052625164023475975931758507), (Int.ofNat 51085925356912236147635276925900), (Int.negOfNat 5839091625197986182908645205077), (Int.negOfNat 871693383214129624471276867808), (Int.ofNat 103737065684593826452166112519), (Int.ofNat 10150495971680535856697087007), (Int.negOfNat 1101714842809253259195727416), (Int.negOfNat 81972238320505140307721825), (Int.ofNat 7855010467124343300676390), (Int.ofNat 477727642524884257922773), (Int.negOfNat 40218488793137858946401), (Int.negOfNat 2083827623400848832954), (Int.ofNat 155154081833635654763), (Int.ofNat 6932986062424667878), (Int.negOfNat 488291382087430525), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-208243688298369762840883008736449/2814749767106560000000000000000000), (-111913558273703072309161837956643/281474976710656000000000000000000), (148743052625164023475975931758507/5629499534213120000000000000000000), (510859253569122361476352769259/56294995342131200000000000000000), (-5839091625197986182908645205077/5629499534213120000000000000000000), (-27240418225441550764727402119/175921860444160000000000000000000), (103737065684593826452166112519/5629499534213120000000000000000000), (10150495971680535856697087007/5629499534213120000000000000000000), (-137714355351156657399465927/703687441776640000000000000000000), (-3278889532820205612308873/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial162.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial162.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial162.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial162.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial162.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial162.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial162.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial162.reflect := by
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

end Bin162
end
end ErdosOverlap.OuterNumerics
