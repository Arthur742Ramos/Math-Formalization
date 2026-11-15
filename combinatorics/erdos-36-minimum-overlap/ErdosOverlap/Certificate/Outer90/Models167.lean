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

/-! # Exact integer weighted outer models for source bin 167

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin167

def weightDenominator : ℤ := (Int.ofNat 25000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 1064925885523728000)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 4377621295721525000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 3006324737948692250)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1215593055454773000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 2158294519502363250)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1757317544964332500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1240776902511789250)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 879054104966591500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 474260907759394425)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 274402697709954500)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial167.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial167.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 22462863789186975000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 8685843658433722500)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 2861490793867259250)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 2324154977760827250)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 1168907909296048100)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 441066807983946250)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 3987088518930421)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 92668778539571140)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 90409961089798675)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial167.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial167.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 22462863789186975000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 8685843658433722500)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2861490793867259250)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 2324154977760827250)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1168907909296048100)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 441066807983946250)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 3987088518930421)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 92668778539571140)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 90409961089798675)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial167.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial167.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial167.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 10041746617804460588209188684649332), (Int.ofNat 9654279580372022563144117130185884), (Int.ofNat 981998790712579309384835634300771), (Int.negOfNat 228475132604281397844182503751165), (Int.negOfNat 30556918931077318705755401004789), (Int.ofNat 3897259755915827107835332535559), (Int.ofNat 522602347951025458118533182019), (Int.negOfNat 44401874981132756303427587002), (Int.negOfNat 5531385179347718709844411001), (Int.ofNat 351393678054942544129880365), (Int.ofNat 39544410119587997499374020), (Int.negOfNat 2017178728724743823506458), (Int.negOfNat 203261054696493397631351), (Int.ofNat 8703907908042219895859), (Int.ofNat 787217637255375940878), (Int.negOfNat 28708641969614875343), (Int.negOfNat 2481402941387530115), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2510436654451115147052297171162333/7036874417766400000000000000000000), (2413569895093005640786029282546471/7036874417766400000000000000000000), (981998790712579309384835634300771/28147497671065600000000000000000000), (-45695026520856279568836500750233/5629499534213120000000000000000000), (-30556918931077318705755401004789/28147497671065600000000000000000000), (3897259755915827107835332535559/28147497671065600000000000000000000), (522602347951025458118533182019/28147497671065600000000000000000000), (-22200937490566378151713793501/14073748835532800000000000000000000), (-5531385179347718709844411001/28147497671065600000000000000000000), (70278735610988508825976073/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial167.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial167.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial167.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial167 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 11029370856292855468697933642832975), (Int.ofNat 10250300905926738909012212493145831), (Int.negOfNat 722757130656727486271757480075842), (Int.negOfNat 265809545727356496438262804079493), (Int.ofNat 22985371410289558230098446446065), (Int.ofNat 4911281169222457197708336577997), (Int.negOfNat 388950711215783551041436377528), (Int.negOfNat 58901531536765396954858770259), (Int.ofNat 4118165897185723608728662169), (Int.ofNat 478515155823452051054958568), (Int.negOfNat 29752510899295730231096433), (Int.negOfNat 2776702239967677207413473), (Int.ofNat 155033500806910646321823), (Int.ofNat 12015098490932870944355), (Int.negOfNat 608454574641646551890), (Int.negOfNat 39758179709615329786), (Int.ofNat 1940771168830310085), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(441174834251714218747917345713319/1125899906842624000000000000000000), (10250300905926738909012212493145831/28147497671065600000000000000000000), (-361378565328363743135878740037921/14073748835532800000000000000000000), (-265809545727356496438262804079493/28147497671065600000000000000000000), (4597074282057911646019689289213/5629499534213120000000000000000000), (4911281169222457197708336577997/28147497671065600000000000000000000), (-48618838901972943880179547191/3518437208883200000000000000000000), (-58901531536765396954858770259/28147497671065600000000000000000000), (4118165897185723608728662169/28147497671065600000000000000000000), (59814394477931506381869821/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial167.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial167.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial167.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial167 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 27006226297412253584942678422675421), (Int.ofNat 5202066053184371801609638233446704), (Int.negOfNat 1496817046892518217045092072588128), (Int.ofNat 28706129090937470212680285485685), (Int.ofNat 38316594334589205566941783165714), (Int.negOfNat 2197308403957030477783426579813), (Int.negOfNat 560539515892368769445498057269), (Int.ofNat 37600427208862864225604269520), (Int.ofNat 5290879200868713454353020700), (Int.negOfNat 365609822513906657793187037), (Int.negOfNat 34848501672265567231053160), (Int.ofNat 2368957030957101679180176), (Int.ofNat 168724342997041375636001), (Int.negOfNat 11035513924033101171871), (Int.negOfNat 623249563744858525945), (Int.ofNat 38844526429008954972), (Int.ofNat 1748604809347465290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(27006226297412253584942678422675421/28147497671065600000000000000000000), (325129128324023237600602389590419/1759218604441600000000000000000000), (-46775532715391194282659127268379/879609302220800000000000000000000), (5741225818187494042536057097137/5629499534213120000000000000000000), (19158297167294602783470891582857/14073748835532800000000000000000000), (-2197308403957030477783426579813/28147497671065600000000000000000000), (-560539515892368769445498057269/28147497671065600000000000000000000), (470005340110785802820053369/351843720888320000000000000000000), (52908792008687134543530207/281474976710656000000000000000000), (-365609822513906657793187037/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial167.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial167.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial167.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial167 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 32165566246465219314560903322659958), (Int.ofNat 523266417967882467495133029662432), (Int.negOfNat 682557452994720723212604555000242), (Int.ofNat 185812380151811024853669246639918), (Int.negOfNat 2660573753585771660827857631956), (Int.negOfNat 4330113940918015343435450999778), (Int.ofNat 237871972539650736911511721295), (Int.ofNat 51522372830743636741294355490), (Int.negOfNat 3637492536145755135124650771), (Int.negOfNat 396341170750919078238189546), (Int.ofNat 30926239876560609011830809), (Int.ofNat 2162712396857595999192965), (Int.negOfNat 175666874298186894132964), (Int.negOfNat 8838923334534747160515), (Int.ofNat 723737944275920875693), (Int.ofNat 27390207151945654490), (Int.negOfNat 2212001052099706110), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(16082783123232609657280451661329979/14073748835532800000000000000000000), (16352075561496327109222907176951/879609302220800000000000000000000), (-341278726497360361606302277500121/14073748835532800000000000000000000), (92906190075905512426834623319959/14073748835532800000000000000000000), (-665143438396442915206964407989/7036874417766400000000000000000000), (-2165056970459007671717725499889/14073748835532800000000000000000000), (47574394507930147382302344259/5629499534213120000000000000000000), (5152237283074363674129435549/2814749767106560000000000000000000), (-3637492536145755135124650771/28147497671065600000000000000000000), (-198170585375459539119094773/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial167.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial167.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial167.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial167 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 31807955349065611746545021095956172), (Int.negOfNat 344468824195809252264547895442070), (Int.ofNat 105825701286999500745532187690860), (Int.ofNat 50130745772641354690989356420724), (Int.negOfNat 22452861265074640881175040009868), (Int.ofNat 717031395800641787861499945032), (Int.ofNat 409609548668171459817758474188), (Int.negOfNat 27715097427327580939997249624), (Int.negOfNat 3951241494110755599402531908), (Int.ofNat 339446922458899517982445971), (Int.ofNat 24925089223596543287739319), (Int.negOfNat 2439260756387719726035098), (Int.negOfNat 112862175842602976498109), (Int.ofNat 12000343061996262826133), (Int.ofNat 387781628650032053153), (Int.negOfNat 44038803789261667072), (Int.negOfNat 925396716217601790), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(7951988837266402936636255273989043/7036874417766400000000000000000000), (-34446882419580925226454789544207/2814749767106560000000000000000000), (5291285064349975037276609384543/1407374883553280000000000000000000), (12532686443160338672747339105181/7036874417766400000000000000000000), (-5613215316268660220293760002467/7036874417766400000000000000000000), (89628924475080223482687493129/3518437208883200000000000000000000), (102402387167042864954439618547/7036874417766400000000000000000000), (-3464387178415947617499656203/3518437208883200000000000000000000), (-987810373527688899850632977/7036874417766400000000000000000000), (339446922458899517982445971/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial167.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial167.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial167.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial167 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 31628915622658806215166915204123236), (Int.ofNat 82336604818069394430093321762177), (Int.negOfNat 517847516297122348752580834230), (Int.negOfNat 55778752096479352499598382741163), (Int.negOfNat 1300621600229236750949853622862), (Int.ofNat 2340088244297390409534750184059), (Int.negOfNat 149003418435925907886853783851), (Int.negOfNat 32453239894656617277414203556), (Int.ofNat 3062642103344088321143119414), (Int.ofNat 250107610390382994591659875), (Int.negOfNat 29272904745321904025122454), (Int.negOfNat 1271850673688841057806891), (Int.ofNat 176291983969081965882301), (Int.ofNat 4655151312798729085980), (Int.negOfNat 750920934299743593510), (Int.negOfNat 12665229977060096694), (Int.ofNat 2483230935369102135), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(7907228905664701553791728801030809/7036874417766400000000000000000000), (82336604818069394430093321762177/28147497671065600000000000000000000), (-51784751629712234875258083423/2814749767106560000000000000000000), (-55778752096479352499598382741163/28147497671065600000000000000000000), (-650310800114618375474926811431/14073748835532800000000000000000000), (2340088244297390409534750184059/28147497671065600000000000000000000), (-149003418435925907886853783851/28147497671065600000000000000000000), (-8113309973664154319353550889/7036874417766400000000000000000000), (1531321051672044160571559707/14073748835532800000000000000000000), (2000860883123063956733279/225179981368524800000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial167.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial167.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial167.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial167 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 31386550329131875093535819802215608), (Int.negOfNat 483087667325381974582515237276484), (Int.negOfNat 230487533042992315055610491924968), (Int.negOfNat 8244429376735957517599820663720), (Int.ofNat 8087847653717751729529536221528), (Int.negOfNat 552788621297766495191131141078), (Int.negOfNat 198562827140563048644021578095), (Int.ofNat 22389698807005083608982258859), (Int.ofNat 2057708628184010898709688304), (Int.negOfNat 300293996863221731875016794), (Int.negOfNat 12086679246152516914750008), (Int.ofNat 2278028979041227438931937), (Int.ofNat 45609515305204530475340), (Int.negOfNat 11567107320791147429659), (Int.negOfNat 114391474269806391453), (Int.ofNat 43564207273135691822), (Int.ofNat 102188623087738290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3923318791141484386691977475276951/3518437208883200000000000000000000), (-120771916831345493645628809319121/7036874417766400000000000000000000), (-28810941630374039381951311490621/3518437208883200000000000000000000), (-206110734418398937939995516593/703687441776640000000000000000000), (1010980956714718966191192027691/3518437208883200000000000000000000), (-276394310648883247595565570539/14073748835532800000000000000000000), (-39712565428112609728804315619/5629499534213120000000000000000000), (22389698807005083608982258859/28147497671065600000000000000000000), (128606789261500681169355519/1759218604441600000000000000000000), (-150146998431610865937508397/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial167.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial167.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial167.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial167 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 29534709017485314901404155865507470), (Int.negOfNat 1316096900076848425761951104127471), (Int.negOfNat 160448257827456507938574718842333), (Int.ofNat 17100335372791348229793478354537), (Int.negOfNat 2055519255859857649235607147765), (Int.negOfNat 767632277299346917791404318837), (Int.ofNat 136802068165398400820080969901), (Int.ofNat 12399699052309576629519294190), (Int.negOfNat 2619097198144637433406390167), (Int.negOfNat 87055495101868973872852279), (Int.ofNat 25674235719235531766754327), (Int.ofNat 296624667594578102065313), (Int.negOfNat 158489247640251824738788), (Int.negOfNat 203602368579937942830), (Int.ofNat 683902676598881218008), (Int.negOfNat 3100584338328299102), (Int.negOfNat 2480058120928543660), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(2953470901748531490140415586550747/2814749767106560000000000000000000), (-1316096900076848425761951104127471/28147497671065600000000000000000000), (-160448257827456507938574718842333/28147497671065600000000000000000000), (17100335372791348229793478354537/28147497671065600000000000000000000), (-411103851171971529847121429553/5629499534213120000000000000000000), (-767632277299346917791404318837/28147497671065600000000000000000000), (136802068165398400820080969901/28147497671065600000000000000000000), (1239969905230957662951929419/2814749767106560000000000000000000), (-2619097198144637433406390167/28147497671065600000000000000000000), (-87055495101868973872852279/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial167.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial167.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial167.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial167 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 26349726018647483347862374206291835), (Int.negOfNat 1850803610201805510550295295872567), (Int.negOfNat 132225144483254641370812364045507), (Int.negOfNat 5988910019464705964038173882606), (Int.negOfNat 998086943639241217691473551418), (Int.ofNat 767056498652064625439291417117), (Int.ofNat 40293786098085917308686109641), (Int.negOfNat 19583281191056778116465770850), (Int.negOfNat 314230179922428851330370707), (Int.ofNat 250418293398550523819535809), (Int.negOfNat 436476774002351059231593), (Int.negOfNat 1912392344992967568970563), (Int.ofNat 20033616902971722005792), (Int.ofNat 9818246185559429886870), (Int.negOfNat 148157016131725621192), (Int.negOfNat 37066256939231323418), (Int.ofNat 627436694511768060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(5269945203729496669572474841258367/5629499534213120000000000000000000), (-1850803610201805510550295295872567/28147497671065600000000000000000000), (-132225144483254641370812364045507/28147497671065600000000000000000000), (-2994455009732352982019086941303/14073748835532800000000000000000000), (-499043471819620608845736775709/14073748835532800000000000000000000), (767056498652064625439291417117/28147497671065600000000000000000000), (40293786098085917308686109641/28147497671065600000000000000000000), (-391665623821135562329315417/562949953421312000000000000000000), (-314230179922428851330370707/28147497671065600000000000000000000), (250418293398550523819535809/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial167.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial167.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial167.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial167 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 22079999065981499901753408149079509), (Int.negOfNat 2422949867844581752324065419636312), (Int.negOfNat 133702843934928210579006797313553), (Int.ofNat 12889645621175442101131865139722), (Int.ofNat 4183776333301022326197301560853), (Int.negOfNat 85400019517475585287874233877), (Int.negOfNat 127381971295810679593223842355), (Int.ofNat 2399637926884163576224159051), (Int.ofNat 2098283626747909938174632514), (Int.negOfNat 51084857341398864610801986), (Int.negOfNat 20073816058506725472728428), (Int.ofNat 563690155151054390421063), (Int.ofNat 124074064896644257235420), (Int.negOfNat 3733489815926284076381), (Int.negOfNat 538422510613288913653), (Int.ofNat 17020125658634019698), (Int.ofNat 2112072647688232010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(22079999065981499901753408149079509/28147497671065600000000000000000000), (-302868733480572719040508177454539/3518437208883200000000000000000000), (-133702843934928210579006797313553/28147497671065600000000000000000000), (6444822810587721050565932569861/14073748835532800000000000000000000), (4183776333301022326197301560853/28147497671065600000000000000000000), (-85400019517475585287874233877/28147497671065600000000000000000000), (-25476394259162135918644768471/5629499534213120000000000000000000), (2399637926884163576224159051/28147497671065600000000000000000000), (1049141813373954969087316257/14073748835532800000000000000000000), (-25542428670699432305400993/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial167.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial167.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial167.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial167 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 16859259521183224972173581139819578), (Int.negOfNat 2697481647729562459045037806110306), (Int.ofNat 11571497892951019749340178118576), (Int.ofNat 27120024861039633575625613451912), (Int.negOfNat 1729259891261040618150815769941), (Int.negOfNat 709717266557101141383285428453), (Int.ofNat 53935510179691797194838642159), (Int.ofNat 14855475318000977597183338216), (Int.negOfNat 946502626520924792762024546), (Int.negOfNat 179953565070678252203297655), (Int.ofNat 10229245636254087515528966), (Int.ofNat 1357822296435226024969141), (Int.negOfNat 72469806120486502804279), (Int.negOfNat 6958517808107006326020), (Int.ofNat 357366315031495589690), (Int.ofNat 25828914855370722214), (Int.negOfNat 1173069275491118585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8429629760591612486086790569909789/14073748835532800000000000000000000), (-1348740823864781229522518903055153/14073748835532800000000000000000000), (723218618309438734333761132411/1759218604441600000000000000000000), (3390003107629954196953201681489/3518437208883200000000000000000000), (-1729259891261040618150815769941/28147497671065600000000000000000000), (-709717266557101141383285428453/28147497671065600000000000000000000), (53935510179691797194838642159/28147497671065600000000000000000000), (1856934414750122199647917277/3518437208883200000000000000000000), (-473251313260462396381012273/14073748835532800000000000000000000), (-35990713014135650440659531/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial167.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial167.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial167.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial167 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 11682195146310428245822178533391153), (Int.negOfNat 2422176453289189802496854417983294), (Int.ofNat 96564291535198067158694383493247), (Int.negOfNat 612978225951614571594114464132), (Int.negOfNat 3032893094269378220792572753553), (Int.ofNat 511978336042926580032937393923), (Int.ofNat 83933541451948172208257081448), (Int.negOfNat 11622935918180939528936973536), (Int.negOfNat 1327768575154252244116613368), (Int.ofNat 145089536673304632635581809), (Int.ofNat 12450331432567188384037739), (Int.negOfNat 1169609091763705579287152), (Int.negOfNat 76295010520495437384689), (Int.ofNat 6519384244187210525907), (Int.ofNat 329291209152259053853), (Int.negOfNat 26535718283739862448), (Int.negOfNat 1288864554558368510), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(11682195146310428245822178533391153/28147497671065600000000000000000000), (-1211088226644594901248427208991647/14073748835532800000000000000000000), (96564291535198067158694383493247/28147497671065600000000000000000000), (-153244556487903642898528616033/7036874417766400000000000000000000), (-3032893094269378220792572753553/28147497671065600000000000000000000), (511978336042926580032937393923/28147497671065600000000000000000000), (10491692681493521526032135181/3518437208883200000000000000000000), (-363216747443154360279280423/879609302220800000000000000000000), (-165971071894281530514576671/3518437208883200000000000000000000), (145089536673304632635581809/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial167.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial167.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial167.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial167 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 7190681084435766294733059540856517), (Int.negOfNat 2089437447735455558449080247597786), (Int.ofNat 71784378615775110551786498725256), (Int.ofNat 1059514375848217865126095167529), (Int.ofNat 3077285941332841738042663706509), (Int.ofNat 300994115277415757769972624093), (Int.negOfNat 108356221578325882646521038540), (Int.negOfNat 7318290041994803910581167400), (Int.ofNat 1684470998877851734511363439), (Int.ofNat 88739561159960716396799826), (Int.negOfNat 16088537576915035721329361), (Int.negOfNat 661338765895386808125465), (Int.ofNat 103928788807472010149616), (Int.ofNat 3342915130131169679555), (Int.negOfNat 480660329114957129007), (Int.negOfNat 12016011468421012010), (Int.ofNat 1444299158760514610), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(7190681084435766294733059540856517/28147497671065600000000000000000000), (-1044718723867727779224540123798893/14073748835532800000000000000000000), (8973047326971888818973312340657/3518437208883200000000000000000000), (1059514375848217865126095167529/28147497671065600000000000000000000), (3077285941332841738042663706509/28147497671065600000000000000000000), (300994115277415757769972624093/28147497671065600000000000000000000), (-5417811078916294132326051927/1407374883553280000000000000000000), (-36591450209974019552905837/140737488355328000000000000000000), (1684470998877851734511363439/28147497671065600000000000000000000), (44369780579980358198399913/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial167.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial167.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial167.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial167 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 3358875940899536205757341725649629), (Int.negOfNat 1689273863591896724152399343714089), (Int.ofNat 148383364244380475577204524241181), (Int.ofNat 19515220871253535235461786238958), (Int.negOfNat 449148617867207284274629576291), (Int.negOfNat 818646104374115866308089169392), (Int.negOfNat 19860495048038784686045685529), (Int.ofNat 16254450861405499098197356140), (Int.ofNat 376785084277729720695312910), (Int.negOfNat 189581630785176385466239243), (Int.negOfNat 3547334397125720266372580), (Int.ofNat 1448848939240914864423324), (Int.ofNat 20997906207794529100581), (Int.negOfNat 7760679283360028181169), (Int.negOfNat 85895643009332072145), (Int.ofNat 30744076876826212548), (Int.ofNat 465656461428505010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(3358875940899536205757341725649629/28147497671065600000000000000000000), (-1689273863591896724152399343714089/28147497671065600000000000000000000), (148383364244380475577204524241181/28147497671065600000000000000000000), (9757610435626767617730893119479/14073748835532800000000000000000000), (-449148617867207284274629576291/28147497671065600000000000000000000), (-51165381523382241644255573087/1759218604441600000000000000000000), (-19860495048038784686045685529/28147497671065600000000000000000000), (812722543070274954909867807/1407374883553280000000000000000000), (37678508427772972069531291/2814749767106560000000000000000000), (-189581630785176385466239243/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial167.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial167.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial167.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial167 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 697408630443652879814690420140158), (Int.negOfNat 938006131566445928520922490544711), (Int.ofNat 195161621138005947996335937455939), (Int.negOfNat 11236193278381697108059331011416), (Int.negOfNat 5605046483817414915757639280307), (Int.ofNat 108816508059237778156632160359), (Int.ofNat 131552858596868210540177664482), (Int.negOfNat 1080053993189494700515199831), (Int.negOfNat 1906630115259904660080499541), (Int.ofNat 10502943386786891378624652), (Int.ofNat 17586146006015162467120487), (Int.negOfNat 85441052785767882981027), (Int.negOfNat 110719782685725903669257), (Int.ofNat 533721241766506210605), (Int.ofNat 502152575289701154310), (Int.negOfNat 3056285744904762694), (Int.negOfNat 1715529042029910635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(348704315221826439907345210070079/14073748835532800000000000000000000), (-938006131566445928520922490544711/28147497671065600000000000000000000), (195161621138005947996335937455939/28147497671065600000000000000000000), (-1404524159797712138507416376427/3518437208883200000000000000000000), (-5605046483817414915757639280307/28147497671065600000000000000000000), (108816508059237778156632160359/28147497671065600000000000000000000), (65776429298434105270088832241/14073748835532800000000000000000000), (-1080053993189494700515199831/28147497671065600000000000000000000), (-1906630115259904660080499541/28147497671065600000000000000000000), (2625735846696722844656163/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial167.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial167.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial167.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial167 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 566229501464294672520180928124273), (Int.negOfNat 439917596744100700628727349840140), (Int.ofNat 29600243536227916970557703931894), (Int.negOfNat 34385933253628972348825919685953), (Int.ofNat 1200207234500128387849284392685), (Int.ofNat 892463027013718466051451348817), (Int.negOfNat 38289624263385835563246723471), (Int.negOfNat 16182301207471689544863457158), (Int.ofNat 569506879954983920194282039), (Int.ofNat 183743314949751706018555415), (Int.negOfNat 5296409015402656514629810), (Int.negOfNat 1381936766000586575630292), (Int.ofNat 33808157123399398813069), (Int.ofNat 7323793172373549997181), (Int.negOfNat 156314945549769008922), (Int.negOfNat 28917934660655750177), (Int.ofNat 447961592791157165), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-566229501464294672520180928124273/28147497671065600000000000000000000), (-21995879837205035031436367492007/1407374883553280000000000000000000), (14800121768113958485278851965947/14073748835532800000000000000000000), (-34385933253628972348825919685953/28147497671065600000000000000000000), (240041446900025677569856878537/5629499534213120000000000000000000), (892463027013718466051451348817/28147497671065600000000000000000000), (-38289624263385835563246723471/28147497671065600000000000000000000), (-8091150603735844772431728579/14073748835532800000000000000000000), (569506879954983920194282039/28147497671065600000000000000000000), (36748662989950341203711083/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial167.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial167.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial167.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial167 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 1559279113117385042062810649382464), (Int.negOfNat 637980394759088965641843913260879), (Int.negOfNat 94806667916274145000938673424733), (Int.negOfNat 2399762522062937388317856590083), (Int.ofNat 4552289400085258882411778520093), (Int.negOfNat 378733425451836936846681303794), (Int.negOfNat 112387769166867502366175920229), (Int.ofNat 8557444754532207806628078292), (Int.ofNat 1617777002806784533539793911), (Int.negOfNat 100870133490948870441521185), (Int.negOfNat 14812627734185651439425840), (Int.ofNat 767209387512600438896708), (Int.ofNat 92916756223126955173531), (Int.negOfNat 4084993528006121493119), (Int.negOfNat 421878889578723811078), (Int.ofNat 16497693834580530223), (Int.ofNat 1347543568789598985), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-24363736142459141282231416396601/439804651110400000000000000000000), (-637980394759088965641843913260879/28147497671065600000000000000000000), (-94806667916274145000938673424733/28147497671065600000000000000000000), (-2399762522062937388317856590083/28147497671065600000000000000000000), (4552289400085258882411778520093/28147497671065600000000000000000000), (-189366712725918468423340651897/14073748835532800000000000000000000), (-112387769166867502366175920229/28147497671065600000000000000000000), (2139361188633051951657019573/7036874417766400000000000000000000), (1617777002806784533539793911/28147497671065600000000000000000000), (-20174026698189774088304237/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial167.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial167.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial167.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial167 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 3178695728648687239897968248746423), (Int.negOfNat 947015324053799605043288028212362), (Int.negOfNat 49180737009711157889375990164337), (Int.ofNat 7849996335496803031888004107952), (Int.negOfNat 2333798336332567965526511430112), (Int.negOfNat 576213503669278001663775261177), (Int.ofNat 86719447208793627310534059218), (Int.ofNat 11502016552618180210331525869), (Int.negOfNat 1347603468773070969254230409), (Int.negOfNat 131679503815277477137481948), (Int.ofNat 12621111697132839048982913), (Int.ofNat 995827637998676071988223), (Int.negOfNat 79536228865843082196343), (Int.negOfNat 5318385870342664049695), (Int.ofNat 359847277987565818190), (Int.ofNat 21616429748048431706), (Int.negOfNat 1177586910390663515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-3178695728648687239897968248746423/28147497671065600000000000000000000), (-473507662026899802521644014106181/14073748835532800000000000000000000), (-49180737009711157889375990164337/28147497671065600000000000000000000), (490624770968550189493000256747/1759218604441600000000000000000000), (-72931198010392748922703482191/879609302220800000000000000000000), (-576213503669278001663775261177/28147497671065600000000000000000000), (43359723604396813655267029609/14073748835532800000000000000000000), (11502016552618180210331525869/28147497671065600000000000000000000), (-1347603468773070969254230409/28147497671065600000000000000000000), (-32919875953819369284370487/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial167.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial167.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial167.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial167 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 5255804462621902951574404540154713), (Int.negOfNat 1150123596312187850161980696792094), (Int.negOfNat 78501298892876702795702658062739), (Int.negOfNat 16449794969199246437843024255188), (Int.negOfNat 1512365953299983641324032051583), (Int.ofNat 683224501678407187431784529438), (Int.ofNat 59904415585245840218052504229), (Int.negOfNat 14062512398908580247509295810), (Int.negOfNat 898663727955245753442551360), (Int.ofNat 166693458858292753006070107), (Int.ofNat 8403018974932516472245980), (Int.negOfNat 1271576284500719756172426), (Int.negOfNat 54028045496922054644681), (Int.ofNat 6746682814258673464131), (Int.ofNat 250136460567375462645), (Int.negOfNat 26633578293974609852), (Int.negOfNat 614745436749534160), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-5255804462621902951574404540154713/28147497671065600000000000000000000), (-575061798156093925080990348396047/14073748835532800000000000000000000), (-78501298892876702795702658062739/28147497671065600000000000000000000), (-4112448742299811609460756063797/7036874417766400000000000000000000), (-1512365953299983641324032051583/28147497671065600000000000000000000), (341612250839203593715892264719/14073748835532800000000000000000000), (59904415585245840218052504229/28147497671065600000000000000000000), (-1406251239890858024750929581/2814749767106560000000000000000000), (-2808324149860142979507973/87960930222080000000000000000000), (166693458858292753006070107/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial167.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial167.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial167.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial167 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 8002094873939119895182288586514444), (Int.negOfNat 1650570855688357948406684730920797), (Int.negOfNat 154695630713137088656581939948639), (Int.negOfNat 152919816542442310189469357176), (Int.ofNat 4697273151580257595763652537897), (Int.ofNat 181359995765868367341049828454), (Int.negOfNat 117760154384156883618686576735), (Int.negOfNat 3648952073444881083989908100), (Int.ofNat 1810659696543278700647468761), (Int.ofNat 44025717893777140131261176), (Int.negOfNat 17137187703078082774393039), (Int.negOfNat 360527296589790505022465), (Int.ofNat 108614135017598746603984), (Int.ofNat 2086264373144122899855), (Int.negOfNat 490902104067949505493), (Int.negOfNat 9248457190378756410), (Int.ofNat 1448816793660059540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-2000523718484779973795572146628611/7036874417766400000000000000000000), (-1650570855688357948406684730920797/28147497671065600000000000000000000), (-154695630713137088656581939948639/28147497671065600000000000000000000), (-19114977067805288773683669647/3518437208883200000000000000000000), (4697273151580257595763652537897/28147497671065600000000000000000000), (90679997882934183670524914227/14073748835532800000000000000000000), (-23552030876831376723737315347/5629499534213120000000000000000000), (-36489520734448810839899081/281474976710656000000000000000000), (1810659696543278700647468761/28147497671065600000000000000000000), (5503214736722142516407647/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial167.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial167.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial167.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial167 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 11849818055201504747280137331231950), (Int.negOfNat 2128745085845891445591213186103186), (Int.negOfNat 55836840927421083838889349226224), (Int.ofNat 27010026136551908423071723016363), (Int.ofNat 397466802118530699718267201452), (Int.negOfNat 776014382882794001218249565232), (Int.ofNat 7117339968963933373477864352), (Int.ofNat 16067312277238092513393943164), (Int.negOfNat 107478401032818322158475432), (Int.negOfNat 194841331565200593802321291), (Int.ofNat 525920691169542890141861), (Int.ofNat 1508789788695858324829098), (Int.ofNat 446458726995671006289), (Int.negOfNat 8076837131597621395393), (Int.negOfNat 20184072612803841353), (Int.ofNat 31827855654227321952), (Int.negOfNat 208462656380329340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-236996361104030094945602746624639/562949953421312000000000000000000), (-1064372542922945722795606593051593/14073748835532800000000000000000000), (-3489802557963817739930584326639/1759218604441600000000000000000000), (27010026136551908423071723016363/28147497671065600000000000000000000), (99366700529632674929566800363/7036874417766400000000000000000000), (-48500898930174625076140597827/1759218604441600000000000000000000), (222416874030122917921183261/879609302220800000000000000000000), (4016828069309523128348485791/7036874417766400000000000000000000), (-13434800129102290269809429/3518437208883200000000000000000000), (-194841331565200593802321291/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial167.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial167.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial167.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial167 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 16130659955504530260754733516221715), (Int.negOfNat 2069309361868432874304981597365874), (Int.ofNat 65143639707246800233945924572710), (Int.ofNat 8115124529849983315564938317554), (Int.negOfNat 3274798181381997024786610174727), (Int.ofNat 264410635305311933831751591340), (Int.ofNat 111478879695249941651882314291), (Int.negOfNat 6071492791149888454882633084), (Int.negOfNat 1835893787725915333436196904), (Int.ofNat 64485917748595489074613245), (Int.ofNat 17918703931601803077932934), (Int.negOfNat 421567375717407796340359), (Int.negOfNat 115772366514391780914821), (Int.ofNat 1862926402461026459680), (Int.ofNat 532421977391705999810), (Int.negOfNat 5476519984506801386), (Int.negOfNat 1720046676929455565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-3226131991100906052150946703244343/5629499534213120000000000000000000), (-1034654680934216437152490798682937/14073748835532800000000000000000000), (6514363970724680023394592457271/2814749767106560000000000000000000), (4057562264924991657782469158777/14073748835532800000000000000000000), (-3274798181381997024786610174727/28147497671065600000000000000000000), (13220531765265596691587579567/1407374883553280000000000000000000), (111478879695249941651882314291/28147497671065600000000000000000000), (-1517873197787472113720658271/7036874417766400000000000000000000), (-229486723465739416679524613/3518437208883200000000000000000000), (12897183549719097814922649/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial167.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial167.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial167.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial167 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 19981781194713453339534103036701272), (Int.negOfNat 1777957155492278326306385576134459), (Int.ofNat 76261413515493795273858959018788), (Int.ofNat 4231809989865179232113857866343), (Int.ofNat 2771375634783856624259115631573), (Int.ofNat 521094393674649595525572817703), (Int.negOfNat 87891360350535240079111793945), (Int.negOfNat 13699764201331829561397701399), (Int.ofNat 1245159085049854729460280286), (Int.ofNat 177340797792221795212584114), (Int.negOfNat 10564296049535987426782172), (Int.negOfNat 1425922052111039277676437), (Int.ofNat 59588164723194219540980), (Int.ofNat 7824255016753153294919), (Int.negOfNat 239198892553248241847), (Int.negOfNat 31353259138101346702), (Int.ofNat 1031670749510192840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-2497722649339181667441762879587659/3518437208883200000000000000000000), (-1777957155492278326306385576134459/28147497671065600000000000000000000), (19065353378873448818464739754697/7036874417766400000000000000000000), (4231809989865179232113857866343/28147497671065600000000000000000000), (2771375634783856624259115631573/28147497671065600000000000000000000), (521094393674649595525572817703/28147497671065600000000000000000000), (-17578272070107048015822358789/5629499534213120000000000000000000), (-13699764201331829561397701399/28147497671065600000000000000000000), (622579542524927364730140143/14073748835532800000000000000000000), (88670398896110897606292057/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial167.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial167.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial167.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial167 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 23144760833448899407445505615931939), (Int.negOfNat 1313155513415790515405477832388812), (Int.ofNat 182444492198476352485008408855403), (Int.ofNat 28483087704463863252683255234977), (Int.ofNat 790395806815899370263689889077), (Int.negOfNat 888097151423533357733012917097), (Int.negOfNat 72647033731226592844817018841), (Int.ofNat 16308430709522006685721931450), (Int.ofNat 1379529249891282530880575657), (Int.negOfNat 176973814926053408752723341), (Int.negOfNat 14548570274006129946984807), (Int.ofNat 1233209969055614490479437), (Int.ofNat 98903045938612882551808), (Int.negOfNat 5945390039233890165830), (Int.negOfNat 468214967581627400808), (Int.ofNat 21242334299895197182), (Int.ofNat 1716873862488897090), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-23144760833448899407445505615931939/28147497671065600000000000000000000), (-328288878353947628851369458097203/7036874417766400000000000000000000), (182444492198476352485008408855403/28147497671065600000000000000000000), (28483087704463863252683255234977/28147497671065600000000000000000000), (790395806815899370263689889077/28147497671065600000000000000000000), (-888097151423533357733012917097/28147497671065600000000000000000000), (-72647033731226592844817018841/28147497671065600000000000000000000), (326168614190440133714438629/562949953421312000000000000000000), (1379529249891282530880575657/28147497671065600000000000000000000), (-176973814926053408752723341/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial167.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial167.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial167.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial167 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 24831513370545055435459313436413986), (Int.negOfNat 293031293324244703155044558480116), (Int.ofNat 296318052358456162081053735635712), (Int.negOfNat 1850010760825268094145786985785), (Int.negOfNat 7185019511120953065435114240714), (Int.negOfNat 201895286513577905545841957996), (Int.ofNat 164848293990155141907237265899), (Int.ofNat 7131885277814902717674983890), (Int.negOfNat 2326724057319540244479822133), (Int.negOfNat 111932077446800282822145379), (Int.ofNat 20259108626907411021526273), (Int.ofNat 1015466954647340832096563), (Int.negOfNat 117469520340048965951612), (Int.negOfNat 5983993310308235330130), (Int.ofNat 485811079465790791992), (Int.ofNat 24855308804196978298), (Int.negOfNat 1761296067109699190), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-12415756685272527717729656718206993/14073748835532800000000000000000000), (-73257823331061175788761139620029/7036874417766400000000000000000000), (1157492392025219383129116154827/109951162777600000000000000000000), (-370002152165053618829157397157/5629499534213120000000000000000000), (-3592509755560476532717557120357/14073748835532800000000000000000000), (-50473821628394476386460489499/7036874417766400000000000000000000), (164848293990155141907237265899/28147497671065600000000000000000000), (713188527781490271767498389/2814749767106560000000000000000000), (-2326724057319540244479822133/28147497671065600000000000000000000), (-111932077446800282822145379/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial167.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial167.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial167.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial167 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 24357692270125566554080146920958789), (Int.ofNat 656286060207942258059137032115154), (Int.ofNat 136550126666075442881272858769208), (Int.negOfNat 41468141366783429021188166336210), (Int.negOfNat 74732753311845342685462954984), (Int.ofNat 1287409836487727094458426416386), (Int.ofNat 4129170361607774721259854545), (Int.negOfNat 24793289815591279675267208691), (Int.negOfNat 423031581185080654529833754), (Int.ofNat 277986009993502255723053606), (Int.ofNat 7155674616321342890822908), (Int.negOfNat 1966530312024454560825063), (Int.negOfNat 59644926117692081764940), (Int.ofNat 9590430471837596657041), (Int.ofNat 313855567034788773953), (Int.negOfNat 35161875620200917778), (Int.negOfNat 1348888389248585440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-24357692270125566554080146920958789/28147497671065600000000000000000000), (328143030103971129029568516057577/14073748835532800000000000000000000), (17068765833259430360159107346151/3518437208883200000000000000000000), (-4146814136678342902118816633621/2814749767106560000000000000000000), (-9341594163980667835682869373/3518437208883200000000000000000000), (643704918243863547229213208193/14073748835532800000000000000000000), (825834072321554944251970909/5629499534213120000000000000000000), (-24793289815591279675267208691/28147497671065600000000000000000000), (-211515790592540327264916877/14073748835532800000000000000000000), (138993004996751127861526803/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial167.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial167.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial167.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial167 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 22793535486554565162687295261926804), (Int.ofNat 795376469411904214250311632967255), (Int.negOfNat 26182081563062238917803585935496), (Int.negOfNat 3033704601040170187790974242031), (Int.ofNat 6761315505748715069428794239214), (Int.negOfNat 377897444899701323610357936747), (Int.negOfNat 209855106534557511905806231449), (Int.ofNat 4572015003497809720230552244), (Int.ofNat 3224768986786323450883545386), (Int.ofNat 1178084126303912210792725), (Int.negOfNat 28538779106834306637559396), (Int.negOfNat 324119242330908646622891), (Int.ofNat 165788107919837483184599), (Int.ofNat 2812111460583193836280), (Int.negOfNat 687246022864729826990), (Int.negOfNat 13617966720336377094), (Int.ofNat 2306928648089049715), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-5698383871638641290671823815481701/7036874417766400000000000000000000), (159075293882380842850062326593451/5629499534213120000000000000000000), (-3272760195382779864725448241937/3518437208883200000000000000000000), (-3033704601040170187790974242031/28147497671065600000000000000000000), (3380657752874357534714397119607/14073748835532800000000000000000000), (-377897444899701323610357936747/28147497671065600000000000000000000), (-209855106534557511905806231449/28147497671065600000000000000000000), (1143003750874452430057638061/7036874417766400000000000000000000), (1612384493393161725441772693/14073748835532800000000000000000000), (47123365052156488431709/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial167.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial167.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial167.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial167 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 21247740742759247342682252504778224), (Int.ofNat 805289322215852206409779554791453), (Int.ofNat 45820346668072026673896855575496), (Int.ofNat 10276475782654967928848333691444), (Int.negOfNat 5088250552146838339546458273432), (Int.negOfNat 1287752126672781461068646906603), (Int.ofNat 125312878153367403376758509037), (Int.ofNat 31428297669213594220591985176), (Int.negOfNat 1026082960790554254500221642), (Int.negOfNat 362105738630796467214737679), (Int.ofNat 3355438955428434152629531), (Int.ofNat 2545034045819754179876652), (Int.ofNat 3949264524742781687709), (Int.negOfNat 12321042001131139596567), (Int.negOfNat 88952809127649550653), (Int.ofNat 44677468245306760528), (Int.ofNat 525680296118721940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-1327983796422452958917640781548639/1759218604441600000000000000000000), (805289322215852206409779554791453/28147497671065600000000000000000000), (5727543333509003334237106946937/3518437208883200000000000000000000), (2569118945663741982212083422861/7036874417766400000000000000000000), (-636031319018354792443307284179/3518437208883200000000000000000000), (-1287752126672781461068646906603/28147497671065600000000000000000000), (125312878153367403376758509037/28147497671065600000000000000000000), (3928537208651699277573998147/3518437208883200000000000000000000), (-513041480395277127250110821/14073748835532800000000000000000000), (-362105738630796467214737679/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial167.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial167.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial167.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial167 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 19482685647898810310017493401588472), (Int.ofNat 882344468805593603116591314550296), (Int.negOfNat 69862772136825227045367593802929), (Int.negOfNat 47919232024934391105325508722966), (Int.negOfNat 4107675577952160249779096385720), (Int.ofNat 1764986263258199326008506589278), (Int.ofNat 253526014560986631210297593330), (Int.negOfNat 21692101079766483062743286060), (Int.negOfNat 4037343577756931075684965529), (Int.ofNat 139289803192613649131083104), (Int.ofNat 34950180194900384345937291), (Int.negOfNat 532104708330623361827285), (Int.negOfNat 199015668151648882203436), (Int.ofNat 1168152954935395231185), (Int.ofNat 816055584088446217807), (Int.negOfNat 194936666613333110), (Int.negOfNat 2578158531358445740), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-2435335705987351288752186675198559/3518437208883200000000000000000000), (110293058600699200389573914318787/3518437208883200000000000000000000), (-69862772136825227045367593802929/28147497671065600000000000000000000), (-23959616012467195552662754361483/14073748835532800000000000000000000), (-102691889448804006244477409643/703687441776640000000000000000000), (882493131629099663004253294639/14073748835532800000000000000000000), (25352601456098663121029759333/2814749767106560000000000000000000), (-1084605053988324153137164303/1407374883553280000000000000000000), (-4037343577756931075684965529/28147497671065600000000000000000000), (4352806349769176535346347/879609302220800000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial167.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial167.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial167.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial167 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 18377524164627129140184243361712827), (Int.ofNat 72929710490246366876672227478105), (Int.negOfNat 274712720871345068855117599529310), (Int.ofNat 12242181043420019449242613724845), (Int.ofNat 19143029824529938735650932870505), (Int.ofNat 1704366677262991546162358096682), (Int.negOfNat 310084434042117790263701502531), (Int.negOfNat 40061964127132046569957847530), (Int.ofNat 2678561748065915199334134850), (Int.ofNat 432792427951465797297647363), (Int.negOfNat 14864465328752745134413940), (Int.negOfNat 2916826249622404743541574), (Int.ofNat 58076879376566740477899), (Int.ofNat 13778988488445773204829), (Int.negOfNat 168779640315211207555), (Int.negOfNat 48885826838393110628), (Int.ofNat 297527797011141560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-18377524164627129140184243361712827/28147497671065600000000000000000000), (14585942098049273375334445495621/5629499534213120000000000000000000), (-27471272087134506885511759952931/2814749767106560000000000000000000), (2448436208684003889848522744969/5629499534213120000000000000000000), (3828605964905987747130186574101/5629499534213120000000000000000000), (852183338631495773081179048341/14073748835532800000000000000000000), (-310084434042117790263701502531/28147497671065600000000000000000000), (-4006196412713204656995784753/2814749767106560000000000000000000), (53571234961318303986682697/562949953421312000000000000000000), (432792427951465797297647363/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial167.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial167.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial167.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial167 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 18895836850019849294634955824814250), (Int.negOfNat 203939513443307041904560641799199), (Int.ofNat 299727447461991335374321876368740), (Int.ofNat 168298390558044647128327310094540), (Int.ofNat 10798403175792828410883990417009), (Int.negOfNat 3505347089150996577944551987959), (Int.negOfNat 366970821152614374491246964022), (Int.ofNat 38281942219002650575853505291), (Int.ofNat 4900747941926913757224478631), (Int.negOfNat 271410431913951206174668082), (Int.negOfNat 39048192145269409851751667), (Int.ofNat 1373008391249976985245777), (Int.ofNat 212790301728084716230577), (Int.negOfNat 5243372751182771179345), (Int.negOfNat 851555019477363821610), (Int.ofNat 15267233879939107814), (Int.ofNat 2849388414627841765), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-75583347400079397178539823299257/112589990684262400000000000000000), (-203939513443307041904560641799199/28147497671065600000000000000000000), (14986372373099566768716093818437/1407374883553280000000000000000000), (8414919527902232356416365504727/1407374883553280000000000000000000), (10798403175792828410883990417009/28147497671065600000000000000000000), (-3505347089150996577944551987959/28147497671065600000000000000000000), (-183485410576307187245623482011/14073748835532800000000000000000000), (38281942219002650575853505291/28147497671065600000000000000000000), (4900747941926913757224478631/28147497671065600000000000000000000), (-135705215956975603087334041/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial167.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial167.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial167.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial167 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 16715322391328772193936072846520037), (Int.ofNat 3030577442915419837303299092727860), (Int.ofNat 1233037722286808068698615754123268), (Int.ofNat 83997380939477518946145412312310), (Int.negOfNat 31602439517594222623244981931598), (Int.negOfNat 3300188023427039410487760866532), (Int.ofNat 435406413867354543338345436856), (Int.ofNat 51857083079401850360117022298), (Int.negOfNat 3874437973150593691009322299), (Int.negOfNat 481862228792501665745875035), (Int.ofNat 24389409083939103721271330), (Int.ofNat 3019563111435086594421042), (Int.negOfNat 114344283904490847542049), (Int.negOfNat 13710524243072188601841), (Int.ofNat 413801476765096065122), (Int.ofNat 47059684622222648257), (Int.negOfNat 1211145851230803735), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-16715322391328772193936072846520037/28147497671065600000000000000000000), (151528872145770991865164954636393/1407374883553280000000000000000000), (308259430571702017174653938530817/7036874417766400000000000000000000), (8399738093947751894614541231231/2814749767106560000000000000000000), (-15801219758797111311622490965799/14073748835532800000000000000000000), (-825047005856759852621940216633/7036874417766400000000000000000000), (54425801733419317917293179607/3518437208883200000000000000000000), (25928541539700925180058511149/14073748835532800000000000000000000), (-3874437973150593691009322299/28147497671065600000000000000000000), (-96372445758500333149175007/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial167.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial167.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial167.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial167.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial167 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial167 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial167 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 24170554793387639702484429356640668), (Int.negOfNat 4160207245157301371067558868091334), (Int.ofNat 1451931451457456285690011823005379), (Int.negOfNat 74522726271095047253023815304535), (Int.negOfNat 32764214534660322392566158113361), (Int.ofNat 3273184392654957125465159588891), (Int.ofNat 437993911804734337965100701531), (Int.negOfNat 51816911818048351262303271048), (Int.negOfNat 3877605099131611695128109299), (Int.ofNat 481825349525877815975147785), (Int.ofNat 24391849428431450850298080), (Int.negOfNat 3019539060837183004883042), (Int.negOfNat 114344283904490847542049), (Int.ofNat 13710524243072188601841), (Int.ofNat 413801476765096065122), (Int.negOfNat 47059684622222648257), (Int.negOfNat 1211145851230803735), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-6042638698346909925621107339160167/7036874417766400000000000000000000), (-2080103622578650685533779434045667/14073748835532800000000000000000000), (1451931451457456285690011823005379/28147497671065600000000000000000000), (-14904545254219009450604763060907/5629499534213120000000000000000000), (-32764214534660322392566158113361/28147497671065600000000000000000000), (3273184392654957125465159588891/28147497671065600000000000000000000), (437993911804734337965100701531/28147497671065600000000000000000000), (-6477113977256043907787908881/3518437208883200000000000000000000), (-3877605099131611695128109299/28147497671065600000000000000000000), (96365069905175563195029557/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial167.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial167.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial167.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 27678239304324687232263133655916875), (Int.ofNat 24754873851834374111861490284669), (Int.ofNat 546068391632922954628199068869042), (Int.negOfNat 168767421090613126038523373442907), (Int.ofNat 9529427436317858213428818363735), (Int.ofNat 3511294842354823036230261655453), (Int.negOfNat 364191957654879204008214849522), (Int.negOfNat 38295323033115620329382675291), (Int.ofNat 4897376390206180816127946131), (Int.ofNat 271425090809248251442968582), (Int.negOfNat 39045603383299967866998667), (Int.negOfNat 1373017410224190831322527), (Int.ofNat 212790301728084716230577), (Int.ofNat 5243372751182771179345), (Int.negOfNat 851555019477363821610), (Int.negOfNat 15267233879939107814), (Int.ofNat 2849388414627841765), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-44285182886919499571621013849467/45035996273704960000000000000000), (24754873851834374111861490284669/28147497671065600000000000000000000), (273034195816461477314099534434521/14073748835532800000000000000000000), (-168767421090613126038523373442907/28147497671065600000000000000000000), (1905885487263571642685763672747/5629499534213120000000000000000000), (3511294842354823036230261655453/28147497671065600000000000000000000), (-182095978827439602004107424761/14073748835532800000000000000000000), (-38295323033115620329382675291/28147497671065600000000000000000000), (4897376390206180816127946131/28147497671065600000000000000000000), (135712545404624125721484291/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial167.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial167.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial167.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 26556622367888542924040792911163671), (Int.ofNat 688013798404228007669546956520696), (Int.negOfNat 60513566876601845583875197733872), (Int.negOfNat 22193906281339173233369678821535), (Int.ofNat 18092833971839137598349034328936), (Int.negOfNat 1667657003987203341126712264137), (Int.negOfNat 307852190722173409373646665281), (Int.ofNat 39999149090785320940019147530), (Int.ofNat 2675896596517385971734034600), (Int.negOfNat 432730467966546401439736113), (Int.negOfNat 14862433000591446060753940), (Int.ofNat 2916787167400811410542324), (Int.ofNat 58076879376566740477899), (Int.negOfNat 13778988488445773204829), (Int.negOfNat 168779640315211207555), (Int.ofNat 48885826838393110628), (Int.ofNat 297527797011141560), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-26556622367888542924040792911163671/28147497671065600000000000000000000), (86001724800528500958693369565087/3518437208883200000000000000000000), (-3782097929787615348992199858367/1759218604441600000000000000000000), (-4438781256267834646673935764307/5629499534213120000000000000000000), (2261604246479892199793629291117/3518437208883200000000000000000000), (-1667657003987203341126712264137/28147497671065600000000000000000000), (-307852190722173409373646665281/28147497671065600000000000000000000), (3999914909078532094001914753/2814749767106560000000000000000000), (13379482982586929858670173/140737488355328000000000000000000), (-432730467966546401439736113/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial167.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial167.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial167.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 25378208268706694656840746192985308), (Int.ofNat 585703332937883310316003989382618), (Int.ofNat 62847162290466830462765017148042), (Int.ofNat 31351895954534634459485950185532), (Int.negOfNat 4677137969232697469151102094494), (Int.negOfNat 1707820111706816873175573353672), (Int.ofNat 254628163560467164108220610755), (Int.ofNat 21597280257412721833661052060), (Int.negOfNat 4038588112803342492372124029), (Int.negOfNat 139197635447791742626243104), (Int.ofNat 34951100182908642403464791), (Int.ofNat 532047588160602336674535), (Int.negOfNat 199015668151648882203436), (Int.negOfNat 1168152954935395231185), (Int.ofNat 816055584088446217807), (Int.ofNat 194936666613333110), (Int.negOfNat 2578158531358445740), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-6344552067176673664210186548246327/7036874417766400000000000000000000), (292851666468941655158001994691309/14073748835532800000000000000000000), (31423581145233415231382508574021/14073748835532800000000000000000000), (7837973988633658614871487546383/7036874417766400000000000000000000), (-2338568984616348734575551047247/14073748835532800000000000000000000), (-213477513963352109146946669209/3518437208883200000000000000000000), (50925632712093432821644122151/5629499534213120000000000000000000), (1079864012870636091683052603/1407374883553280000000000000000000), (-4038588112803342492372124029/28147497671065600000000000000000000), (-4349926107743491957070097/879609302220800000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial167.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial167.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial167.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 23816090662464816152596689116052822), (Int.ofNat 981308754865877845515008490801720), (Int.ofNat 70231458995988432846675845274640), (Int.negOfNat 28991343846645821869136697535824), (Int.negOfNat 5047484741328112389377048758132), (Int.ofNat 1349813019451906819447327678918), (Int.ofNat 125012285334451580545366113862), (Int.negOfNat 31529194892961816554918617926), (Int.negOfNat 1025583071139787516754510392), (Int.ofNat 362202856313730751469355679), (Int.ofNat 3355000348386761804286781), (Int.negOfNat 2545097178639251102413902), (Int.ofNat 3949264524742781687709), (Int.ofNat 12321042001131139596567), (Int.negOfNat 88952809127649550653), (Int.negOfNat 44677468245306760528), (Int.ofNat 525680296118721940), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-11908045331232408076298344558026411/14073748835532800000000000000000000), (24532718871646946137875212270043/703687441776640000000000000000000), (877893237449855410583448065933/351843720888320000000000000000000), (-1811958990415363866821043595989/1759218604441600000000000000000000), (-1261871185332028097344262189533/7036874417766400000000000000000000), (674906509725953409723663839459/14073748835532800000000000000000000), (62506142667225790272683056931/14073748835532800000000000000000000), (-15764597446480908277459308963/14073748835532800000000000000000000), (-128197883892473439594313799/3518437208883200000000000000000000), (362202856313730751469355679/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial167.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial167.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial167.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 21838157521416550400207332555576786), (Int.ofNat 870454834527078310607804614876223), (Int.negOfNat 108255535373823835349074943533720), (Int.negOfNat 12975789929815839232431956853837), (Int.ofNat 7377346477340929521542516087312), (Int.ofNat 428290288311980885401318201891), (Int.negOfNat 211449366870087458792098593199), (Int.negOfNat 4651664161904940611570294494), (Int.ofNat 3226860163086821132497735386), (Int.negOfNat 1102510611893262095212725), (Int.negOfNat 28540447036962177598005646), (Int.ofNat 324071141135101467546891), (Int.ofNat 165788107919837483184599), (Int.negOfNat 2812111460583193836280), (Int.negOfNat 687246022864729826990), (Int.ofNat 13617966720336377094), (Int.ofNat 2306928648089049715), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-10919078760708275200103666277788393/14073748835532800000000000000000000), (870454834527078310607804614876223/28147497671065600000000000000000000), (-2706388384345595883726873588343/703687441776640000000000000000000), (-12975789929815839232431956853837/28147497671065600000000000000000000), (461084154833808095096407255457/1759218604441600000000000000000000), (428290288311980885401318201891/28147497671065600000000000000000000), (-211449366870087458792098593199/28147497671065600000000000000000000), (-2325832080952470305785147247/14073748835532800000000000000000000), (1613430081543410566248867693/14073748835532800000000000000000000), (-44100424475730483808509/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial167.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial167.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial167.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 20515664057584116243768658820405558), (Int.ofNat 512542438314014508348622211453784), (Int.negOfNat 23196195098968858983203180174882), (Int.ofNat 32107049330652525141458049232270), (Int.ofNat 929891808189067616712821868972), (Int.negOfNat 1261764193401184782402901216022), (Int.ofNat 1698572400471419594537090045), (Int.ofNat 24756155519992177635607211191), (Int.negOfNat 419935037922424552556910004), (Int.negOfNat 277952450448484916374483356), (Int.ofNat 7153238965820359644046908), (Int.ofNat 1966512274076026868671563), (Int.negOfNat 59644926117692081764940), (Int.negOfNat 9590430471837596657041), (Int.ofNat 313855567034788773953), (Int.ofNat 35161875620200917778), (Int.negOfNat 1348888389248585440), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-10257832028792058121884329410202779/14073748835532800000000000000000000), (64067804789251813543577776431723/3518437208883200000000000000000000), (-11598097549484429491601590087441/14073748835532800000000000000000000), (3210704933065252514145804923227/2814749767106560000000000000000000), (232472952047266904178205467243/7036874417766400000000000000000000), (-630882096700592391201450608011/14073748835532800000000000000000000), (339714480094283918907418009/5629499534213120000000000000000000), (24756155519992177635607211191/28147497671065600000000000000000000), (-104983759480606138139227501/7036874417766400000000000000000000), (-69488112612121229093620839/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial167.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial167.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial167.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 19348967034839618250185574262716670), (Int.ofNat 744260962303225876663294591969621), (Int.ofNat 105965196637418781455605691697933), (Int.ofNat 1147741348032647654601839522513), (Int.negOfNat 6076601995820163849023031900835), (Int.ofNat 196689265914061694346178110387), (Int.ofNat 162258771621419304649870866149), (Int.negOfNat 7117055330982711940578403140), (Int.negOfNat 2323478434151442566202206633), (Int.ofNat 111914758109867915776173629), (Int.ofNat 20256577301478058222651773), (Int.negOfNat 1015451923023651088635313), (Int.negOfNat 117469520340048965951612), (Int.ofNat 5983993310308235330130), (Int.ofNat 485811079465790791992), (Int.negOfNat 24855308804196978298), (Int.negOfNat 1761296067109699190), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-1934896703483961825018557426271667/2814749767106560000000000000000000), (744260962303225876663294591969621/28147497671065600000000000000000000), (105965196637418781455605691697933/28147497671065600000000000000000000), (1147741348032647654601839522513/28147497671065600000000000000000000), (-1215320399164032769804606380167/5629499534213120000000000000000000), (196689265914061694346178110387/28147497671065600000000000000000000), (162258771621419304649870866149/28147497671065600000000000000000000), (-355852766549135597028920157/1407374883553280000000000000000000), (-2323478434151442566202206633/28147497671065600000000000000000000), (111914758109867915776173629/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial167.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial167.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial167.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 17509379662137389751966361340386635), (Int.ofNat 1029112131729560446970875819016817), (Int.ofNat 13457746664538717959988517081357), (Int.negOfNat 20926591840097260662645381958744), (Int.ofNat 1699066048523606975845705718068), (Int.ofNat 854461759388526303774030135483), (Int.negOfNat 74685323013428615351136331591), (Int.negOfNat 16246500331439821995477217200), (Int.ofNat 1382033260380545922195988907), (Int.ofNat 176910739379787301982937341), (Int.negOfNat 14550505819674124098740307), (Int.negOfNat 1233167880509283208787937), (Int.ofNat 98903045938612882551808), (Int.ofNat 5945390039233890165830), (Int.negOfNat 468214967581627400808), (Int.negOfNat 21242334299895197182), (Int.ofNat 1716873862488897090), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-3501875932427477950393272268077327/5629499534213120000000000000000000), (1029112131729560446970875819016817/28147497671065600000000000000000000), (13457746664538717959988517081357/28147497671065600000000000000000000), (-2615823980012157582830672744843/3518437208883200000000000000000000), (424766512130901743961426429517/7036874417766400000000000000000000), (854461759388526303774030135483/28147497671065600000000000000000000), (-74685323013428615351136331591/28147497671065600000000000000000000), (-40616250828599554988693043/70368744177664000000000000000000), (1382033260380545922195988907/28147497671065600000000000000000000), (176910739379787301982937341/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial167.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial167.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial167.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 15516641327261474264598195987376709), (Int.ofNat 934670161035462959135697619566612), (Int.negOfNat 28712499154381836424082422896547), (Int.ofNat 8961307053899275636395313179678), (Int.ofNat 3241261115859325936468536160747), (Int.negOfNat 573006766895641765480071869673), (Int.negOfNat 88830402128349275715122091695), (Int.ofNat 13791058448248340678485345399), (Int.ofNat 1246240877694189057243421286), (Int.negOfNat 177431972927271476373713864), (Int.negOfNat 10565102324667448240057672), (Int.ofNat 1425982178605798251521437), (Int.ofNat 59588164723194219540980), (Int.negOfNat 7824255016753153294919), (Int.negOfNat 239198892553248241847), (Int.ofNat 31353259138101346702), (Int.ofNat 1031670749510192840), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-15516641327261474264598195987376709/28147497671065600000000000000000000), (233667540258865739783924404891653/7036874417766400000000000000000000), (-28712499154381836424082422896547/28147497671065600000000000000000000), (4480653526949637818197656589839/14073748835532800000000000000000000), (3241261115859325936468536160747/28147497671065600000000000000000000), (-573006766895641765480071869673/28147497671065600000000000000000000), (-17766080425669855143024418339/5629499534213120000000000000000000), (13791058448248340678485345399/28147497671065600000000000000000000), (623120438847094528621710643/14073748835532800000000000000000000), (-22178996615908934546714233/3518437208883200000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial167.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial167.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial167.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 13660636002999942092066406741809378), (Int.ofNat 975188964816693404504986238285506), (Int.ofNat 46290181502018536385147427754724), (Int.ofNat 6662898051439939213726257088888), (Int.negOfNat 3353980895574516309476573687709), (Int.negOfNat 319626704026671357711863742647), (Int.ofNat 111876021223248290909855747291), (Int.ofNat 6166508842069707357654698834), (Int.negOfNat 1836518766653783130196704654), (Int.negOfNat 64579885230245298921194495), (Int.ofNat 17919237369738532011594934), (Int.ofNat 421627502212166770185359), (Int.negOfNat 115772366514391780914821), (Int.negOfNat 1862926402461026459680), (Int.ofNat 532421977391705999810), (Int.ofNat 5476519984506801386), (Int.negOfNat 1720046676929455565), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-6830318001499971046033203370904689/14073748835532800000000000000000000), (487594482408346702252493119142753/14073748835532800000000000000000000), (11572545375504634096286856938681/7036874417766400000000000000000000), (832862256429992401715782136111/3518437208883200000000000000000000), (-3353980895574516309476573687709/28147497671065600000000000000000000), (-319626704026671357711863742647/28147497671065600000000000000000000), (111876021223248290909855747291/28147497671065600000000000000000000), (3083254421034853678827349417/14073748835532800000000000000000000), (-918259383326891565098352327/14073748835532800000000000000000000), (-12915977046049059784238899/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial167.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial167.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial167.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 11528221014919939524124959376867553), (Int.ofNat 1129713959895913157225664364392044), (Int.ofNat 7817785352328618916749895309003), (Int.negOfNat 14958970779661190452618031895568), (Int.negOfNat 184512765446668906855634699697), (Int.ofNat 733081996686228530742422698627), (Int.ofNat 8714230893221077123396000602), (Int.negOfNat 15995004811635353021637279914), (Int.negOfNat 109622155940220597791618932), (Int.ofNat 194770534199472242903462541), (Int.ofNat 527650646551975403319361), (Int.negOfNat 1508744693824789094445348), (Int.ofNat 446458726995671006289), (Int.ofNat 8076837131597621395393), (Int.negOfNat 20184072612803841353), (Int.negOfNat 31827855654227321952), (Int.negOfNat 208462656380329340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-11528221014919939524124959376867553/28147497671065600000000000000000000), (282428489973978289306416091098011/7036874417766400000000000000000000), (7817785352328618916749895309003/28147497671065600000000000000000000), (-934935673728824403288626993473/1759218604441600000000000000000000), (-184512765446668906855634699697/28147497671065600000000000000000000), (733081996686228530742422698627/28147497671065600000000000000000000), (4357115446610538561698000301/14073748835532800000000000000000000), (-7997502405817676510818639957/14073748835532800000000000000000000), (-27405538985055149447904733/7036874417766400000000000000000000), (194770534199472242903462541/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial167.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial167.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial167.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 9338107773842020151386470683236467), (Int.ofNat 1029049609882346464225902787854136), (Int.negOfNat 35709075126859078334739708885206), (Int.ofNat 6122644005447593590282922644721), (Int.ofNat 3799367788226086199530142970791), (Int.negOfNat 200143838648886614596788108493), (Int.negOfNat 115432226247097768642234435910), (Int.ofNat 3678634951638827406770311350), (Int.ofNat 1807603902573280476675867261), (Int.negOfNat 44053875393386209142306176), (Int.negOfNat 17134752632678790091369539), (Int.ofNat 360545334538218197175965), (Int.ofNat 108614135017598746603984), (Int.negOfNat 2086264373144122899855), (Int.negOfNat 490902104067949505493), (Int.ofNat 9248457190378756410), (Int.ofNat 1448816793660059540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-9338107773842020151386470683236467/28147497671065600000000000000000000), (128631201235293308028237848481767/3518437208883200000000000000000000), (-17854537563429539167369854442603/14073748835532800000000000000000000), (6122644005447593590282922644721/28147497671065600000000000000000000), (3799367788226086199530142970791/28147497671065600000000000000000000), (-200143838648886614596788108493/28147497671065600000000000000000000), (-11543222624709776864223443591/2814749767106560000000000000000000), (73572699032776548135406227/562949953421312000000000000000000), (1807603902573280476675867261/28147497671065600000000000000000000), (-344170901510829758924267/219902325555200000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial167.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial167.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial167.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 7325971414432580929457380457467979), (Int.ofNat 1046406662819188370821082993035289), (Int.ofNat 53824238053302340094900526775569), (Int.ofNat 14868424097244551764426452964192), (Int.negOfNat 2453625559805969546573452453459), (Int.negOfNat 672985577211348887296140935658), (Int.ofNat 62295100312248642848856721979), (Int.ofNat 14041646038868191350301887810), (Int.negOfNat 901775075385219560144617110), (Int.negOfNat 166671355353294948679049607), (Int.ofNat 8405486851172304187857480), (Int.ofNat 1271561252877030012711176), (Int.negOfNat 54028045496922054644681), (Int.negOfNat 6746682814258673464131), (Int.ofNat 250136460567375462645), (Int.ofNat 26633578293974609852), (Int.negOfNat 614745436749534160), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-7325971414432580929457380457467979/28147497671065600000000000000000000), (1046406662819188370821082993035289/28147497671065600000000000000000000), (53824238053302340094900526775569/28147497671065600000000000000000000), (464638253038892242638326655131/879609302220800000000000000000000), (-2453625559805969546573452453459/28147497671065600000000000000000000), (-336492788605674443648070467829/14073748835532800000000000000000000), (62295100312248642848856721979/28147497671065600000000000000000000), (1404164603886819135030188781/2814749767106560000000000000000000), (-90177507538521956014461711/2814749767106560000000000000000000), (-166671355353294948679049607/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial167.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial167.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial167.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 4954228324521346574491759899942308), (Int.ofNat 1324769435133143270018344793261311), (Int.ofNat 52439754534509769427955662195011), (Int.negOfNat 16186482198619485696102365208384), (Int.negOfNat 3038433353403945403849899097493), (Int.ofNat 612057910453309408653376791541), (Int.ofNat 88492395421280342699274009968), (Int.negOfNat 11567219321674487718322266119), (Int.negOfNat 1349901630497794620614332659), (Int.ofNat 131745580147917462135956198), (Int.ofNat 12622931314794165216874413), (Int.negOfNat 995872732869745302371973), (Int.negOfNat 79536228865843082196343), (Int.ofNat 5318385870342664049695), (Int.ofNat 359847277987565818190), (Int.negOfNat 21616429748048431706), (Int.negOfNat 1177586910390663515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1238557081130336643622939974985577/7036874417766400000000000000000000), (1324769435133143270018344793261311/28147497671065600000000000000000000), (52439754534509769427955662195011/28147497671065600000000000000000000), (-252913784353429464001599456381/439804651110400000000000000000000), (-3038433353403945403849899097493/28147497671065600000000000000000000), (612057910453309408653376791541/28147497671065600000000000000000000), (5530774713830021418704625623/1759218604441600000000000000000000), (-11567219321674487718322266119/28147497671065600000000000000000000), (-1349901630497794620614332659/28147497671065600000000000000000000), (65872790073958731067978099/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial167.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial167.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial167.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2249535976809984231381115883486477), (Int.ofNat 1302806876609051027964431440850990), (Int.negOfNat 56870882227907734280124606064994), (Int.negOfNat 9896606068102882675861715872647), (Int.ofNat 4291933594101556882831648078415), (Int.ofNat 429493137022057947079717522233), (Int.negOfNat 111735218516905843020522876479), (Int.negOfNat 8648403633816439568364976792), (Int.ofNat 1616932550715792288130907661), (Int.ofNat 100961722761874147914395435), (Int.negOfNat 14811960066362204426719590), (Int.negOfNat 767269514007359412741708), (Int.ofNat 92916756223126955173531), (Int.ofNat 4084993528006121493119), (Int.negOfNat 421878889578723811078), (Int.negOfNat 16497693834580530223), (Int.ofNat 1347543568789598985), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-2249535976809984231381115883486477/28147497671065600000000000000000000), (130280687660905102796443144085099/2814749767106560000000000000000000), (-28435441113953867140062303032497/14073748835532800000000000000000000), (-9896606068102882675861715872647/28147497671065600000000000000000000), (858386718820311376566329615683/5629499534213120000000000000000000), (429493137022057947079717522233/28147497671065600000000000000000000), (-111735218516905843020522876479/28147497671065600000000000000000000), (-1081050454227054946045622099/3518437208883200000000000000000000), (1616932550715792288130907661/28147497671065600000000000000000000), (20192344552374829582879087/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial167.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial167.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial167.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 124027362229958661538990239915364), (Int.ofNat 1104744078594796047609319291461329), (Int.negOfNat 8335542151770624780538310545867), (Int.ofNat 22089564663452223101786268866433), (Int.ofNat 1460563040485886698333883523357), (Int.negOfNat 841703315443484964006477724606), (Int.negOfNat 38942174913347494908899767221), (Int.ofNat 16091342328187457783126558658), (Int.ofNat 570351332045976165603168289), (Int.negOfNat 183651725678826428545681165), (Int.negOfNat 5297076683226103527336060), (Int.ofNat 1381876639505827601785292), (Int.ofNat 33808157123399398813069), (Int.negOfNat 7323793172373549997181), (Int.negOfNat 156314945549769008922), (Int.ofNat 28917934660655750177), (Int.ofNat 447961592791157165), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(31006840557489665384747559978841/7036874417766400000000000000000000), (1104744078594796047609319291461329/28147497671065600000000000000000000), (-8335542151770624780538310545867/28147497671065600000000000000000000), (22089564663452223101786268866433/28147497671065600000000000000000000), (1460563040485886698333883523357/28147497671065600000000000000000000), (-420851657721742482003238862303/14073748835532800000000000000000000), (-38942174913347494908899767221/28147497671065600000000000000000000), (8045671164093728891563279329/14073748835532800000000000000000000), (570351332045976165603168289/28147497671065600000000000000000000), (-36730345135765285709136233/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial167.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial167.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial167.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 2472941226320656452405855509785923), (Int.ofNat 1315760242647639692243138752571462), (Int.ofNat 93541129594000505228809870693787), (Int.ofNat 2899707415239123981165847020598), (Int.negOfNat 4900411466744721148551677177988), (Int.negOfNat 72972101274130925816945734373), (Int.ofNat 129779910384381495151437713732), (Int.ofNat 1014851224133187192524459581), (Int.negOfNat 1904331953535181008720397291), (Int.negOfNat 10436867054146906380150402), (Int.ofNat 17584326388353836299228987), (Int.ofNat 85395957914698652597277), (Int.negOfNat 110719782685725903669257), (Int.negOfNat 533721241766506210605), (Int.ofNat 502152575289701154310), (Int.ofNat 3056285744904762694), (Int.negOfNat 1715529042029910635), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(2472941226320656452405855509785923/28147497671065600000000000000000000), (657880121323819846121569376285731/14073748835532800000000000000000000), (93541129594000505228809870693787/28147497671065600000000000000000000), (1449853707619561990582923510299/14073748835532800000000000000000000), (-1225102866686180287137919294497/7036874417766400000000000000000000), (-72972101274130925816945734373/28147497671065600000000000000000000), (32444977596095373787859428433/7036874417766400000000000000000000), (1014851224133187192524459581/28147497671065600000000000000000000), (-1904331953535181008720397291/28147497671065600000000000000000000), (-5218433527073453190075201/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial167.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial167.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial167.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 5429042892718948001999945220404213), (Int.ofNat 1585556930101340013665611001054594), (Int.ofNat 16057827298269878848739870194489), (Int.negOfNat 21096591743222351324175671769862), (Int.ofNat 492110988641740234047240846633), (Int.ofNat 828885028840984311251754075962), (Int.negOfNat 22251179775041587316849903279), (Int.negOfNat 16275317221445887995404764140), (Int.ofNat 379896431707703527397378660), (Int.ofNat 189603734290174189793259743), (Int.negOfNat 3549802273365507981984080), (Int.negOfNat 1448863970864604607884574), (Int.ofNat 20997906207794529100581), (Int.ofNat 7760679283360028181169), (Int.negOfNat 85895643009332072145), (Int.negOfNat 30744076876826212548), (Int.ofNat 465656461428505010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(5429042892718948001999945220404213/28147497671065600000000000000000000), (792778465050670006832805500527297/14073748835532800000000000000000000), (16057827298269878848739870194489/28147497671065600000000000000000000), (-10548295871611175662087835884931/14073748835532800000000000000000000), (492110988641740234047240846633/28147497671065600000000000000000000), (414442514420492155625877037981/14073748835532800000000000000000000), (-22251179775041587316849903279/28147497671065600000000000000000000), (-813765861072294399770238207/1407374883553280000000000000000000), (18994821585385176369868933/1407374883553280000000000000000000), (189603734290174189793259743/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial167.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial167.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial167.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 8526693984352364159095679950812844), (Int.ofNat 1467916201931980119154095923173897), (Int.negOfNat 47202176970526193966326905814311), (Int.ofNat 4910209813050639081336182079326), (Int.ofNat 3975191304688547948694795696053), (Int.negOfNat 319777958160627316759827907254), (Int.negOfNat 110684149715565817545152776715), (Int.ofNat 7347972920188750233361570650), (Int.ofNat 1687526792847849958482964939), (Int.negOfNat 88767718659569785407844826), (Int.negOfNat 16090972647314328404352861), (Int.ofNat 661356803843814500278965), (Int.ofNat 103928788807472010149616), (Int.negOfNat 3342915130131169679555), (Int.negOfNat 480660329114957129007), (Int.ofNat 12016011468421012010), (Int.ofNat 1444299158760514610), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(2131673496088091039773919987703211/7036874417766400000000000000000000), (1467916201931980119154095923173897/28147497671065600000000000000000000), (-47202176970526193966326905814311/28147497671065600000000000000000000), (2455104906525319540668091039663/14073748835532800000000000000000000), (3975191304688547948694795696053/28147497671065600000000000000000000), (-159888979080313658379913953627/14073748835532800000000000000000000), (-22136829943113163509030555343/5629499534213120000000000000000000), (146959458403775004667231413/562949953421312000000000000000000), (1687526792847849958482964939/28147497671065600000000000000000000), (-44383859329784892703922413/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial167.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial167.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial167.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 11360598106047474274692493123305050), (Int.ofNat 1423145327341533673201841051649236), (Int.ofNat 32909665255369420693370086035974), (Int.ofNat 12664033582821355133805109568237), (Int.negOfNat 2450913526711629683319393024852), (Int.negOfNat 554910722239483015238965170668), (Int.ofNat 82336650527691028458338945198), (Int.ofNat 11695243383783679020693636786), (Int.negOfNat 1325624820246849968483469868), (Int.negOfNat 145160334039032983534440559), (Int.ofNat 12448601477184755870860239), (Int.ofNat 1169654186634774809670902), (Int.negOfNat 76295010520495437384689), (Int.negOfNat 6519384244187210525907), (Int.ofNat 329291209152259053853), (Int.ofNat 26535718283739862448), (Int.negOfNat 1288864554558368510), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(227211962120949485493849862466101/562949953421312000000000000000000), (355786331835383418300460262912309/7036874417766400000000000000000000), (16454832627684710346685043017987/14073748835532800000000000000000000), (12664033582821355133805109568237/28147497671065600000000000000000000), (-612728381677907420829848256213/7036874417766400000000000000000000), (-138727680559870753809741292667/7036874417766400000000000000000000), (41168325263845514229169472599/14073748835532800000000000000000000), (5847621691891839510346818393/14073748835532800000000000000000000), (-331406205061712492120867467/7036874417766400000000000000000000), (-145160334039032983534440559/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial167.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial167.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial167.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 14389235568701368625835744556859915), (Int.ofNat 1603361250679407009337989183768724), (Int.ofNat 30424956097874907275194798772090), (Int.negOfNat 12342002279803561052454786118254), (Int.negOfNat 1650077177065058402516642038573), (Int.ofNat 654501197836123823336507738460), (Int.ofNat 53538368651693447936865209159), (Int.negOfNat 14760459267081158694411272466), (Int.negOfNat 945877647593056996001516796), (Int.ofNat 179859597589028442356716405), (Int.ofNat 10228712198117358581866966), (Int.negOfNat 1357762169940467051124141), (Int.negOfNat 72469806120486502804279), (Int.ofNat 6958517808107006326020), (Int.ofNat 357366315031495589690), (Int.negOfNat 25828914855370722214), (Int.negOfNat 1173069275491118585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(2877847113740273725167148911371983/5629499534213120000000000000000000), (400840312669851752334497295942181/7036874417766400000000000000000000), (3042495609787490727519479877209/2814749767106560000000000000000000), (-6171001139901780526227393059127/14073748835532800000000000000000000), (-1650077177065058402516642038573/28147497671065600000000000000000000), (32725059891806191166825386923/1407374883553280000000000000000000), (53538368651693447936865209159/28147497671065600000000000000000000), (-7380229633540579347205636233/14073748835532800000000000000000000), (-236469411898264249000379199/7036874417766400000000000000000000), (35971919517805688471343281/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial167.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial167.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial167.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 17614859198553727988420881407514422), (Int.ofNat 1579662873387542593706558361206859), (Int.negOfNat 28728931265621871623429208316888), (Int.ofNat 303471422570671525417688262007), (Int.ofNat 3713890852227133965667684556677), (Int.ofNat 33487646297175693757364387197), (Int.negOfNat 126442929517996643957213544605), (Int.negOfNat 2308343679967652459136515051), (Int.ofNat 2097201834103575610391491514), (Int.ofNat 50993682206349183449672236), (Int.negOfNat 20073009783375264659452928), (Int.negOfNat 563630028656295416576063), (Int.ofNat 124074064896644257235420), (Int.ofNat 3733489815926284076381), (Int.negOfNat 538422510613288913653), (Int.negOfNat 17020125658634019698), (Int.ofNat 2112072647688232010), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(8807429599276863994210440703757211/14073748835532800000000000000000000), (1579662873387542593706558361206859/28147497671065600000000000000000000), (-3591116408202733952928651039611/3518437208883200000000000000000000), (303471422570671525417688262007/28147497671065600000000000000000000), (3713890852227133965667684556677/28147497671065600000000000000000000), (33487646297175693757364387197/28147497671065600000000000000000000), (-25288585903599328791442708921/5629499534213120000000000000000000), (-2308343679967652459136515051/28147497671065600000000000000000000), (1048600917051787805195745757/14073748835532800000000000000000000), (12748420551587295862418059/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial167.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial167.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial167.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 20714344847357370142093143461459989), (Int.ofNat 1566760228513014985740233876432012), (Int.ofNat 36761601050134558367538852809797), (Int.ofNat 13545405883851068966332058249773), (Int.negOfNat 1906757185345719829459961126777), (Int.negOfNat 800691890687445811054570799203), (Int.ofNat 42332075380287939815005422391), (Int.ofNat 19645211569138962806710485100), (Int.negOfNat 316734190411692242645783957), (Int.negOfNat 250481368944816630589321809), (Int.negOfNat 434541228334356907476093), (Int.ofNat 1912434433539298850662063), (Int.ofNat 20033616902971722005792), (Int.negOfNat 9818246185559429886870), (Int.negOfNat 148157016131725621192), (Int.ofNat 37066256939231323418), (Int.ofNat 627436694511768060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(20714344847357370142093143461459989/28147497671065600000000000000000000), (391690057128253746435058469108003/7036874417766400000000000000000000), (36761601050134558367538852809797/28147497671065600000000000000000000), (13545405883851068966332058249773/28147497671065600000000000000000000), (-1906757185345719829459961126777/28147497671065600000000000000000000), (-800691890687445811054570799203/28147497671065600000000000000000000), (42332075380287939815005422391/28147497671065600000000000000000000), (196452115691389628067104851/281474976710656000000000000000000), (-316734190411692242645783957/28147497671065600000000000000000000), (-250481368944816630589321809/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial167.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial167.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial167.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 24052162681794150578724323284843436), (Int.ofNat 1767326569051343527873686307668766), (Int.ofNat 29904597893208607520546978003388), (Int.negOfNat 17802604785554653341506190952515), (Int.negOfNat 3163936771155967619896202043036), (Int.ofNat 762426256700012587606681297596), (Int.ofNat 139391590534134238077447369651), (Int.negOfNat 12384869105477385852422713440), (Int.negOfNat 2622342821312735111684005667), (Int.ofNat 87038175764936606826880529), (Int.ofNat 25676767044664884565628827), (Int.negOfNat 296609635970888358604063), (Int.negOfNat 158489247640251824738788), (Int.ofNat 203602368579937942830), (Int.ofNat 683902676598881218008), (Int.ofNat 3100584338328299102), (Int.negOfNat 2480058120928543660), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(6013040670448537644681080821210859/7036874417766400000000000000000000), (883663284525671763936843153834383/14073748835532800000000000000000000), (7476149473302151880136744500847/7036874417766400000000000000000000), (-3560520957110930668301238190503/5629499534213120000000000000000000), (-790984192788991904974050510759/7036874417766400000000000000000000), (190606564175003146901670324399/7036874417766400000000000000000000), (139391590534134238077447369651/28147497671065600000000000000000000), (-77405431909233661577641959/175921860444160000000000000000000), (-2622342821312735111684005667/28147497671065600000000000000000000), (87038175764936606826880529/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial167.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial167.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial167.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 27544522116594518713552609226686839), (Int.ofNat 1651916165841877899494102490974596), (Int.negOfNat 70741211278035020397699417464558), (Int.negOfNat 1116662659365479692629424175090), (Int.ofNat 7083223092216644289689857506334), (Int.ofNat 578434264383800805286985049414), (Int.negOfNat 196132229179426693517298813595), (Int.negOfNat 22426833102604185648642256359), (Int.ofNat 2054612084921354796736764554), (Int.ofNat 300327556408239071223587044), (Int.negOfNat 12084243595651533667974008), (Int.negOfNat 2278047016989655131085437), (Int.ofNat 45609515305204530475340), (Int.ofNat 11567107320791147429659), (Int.negOfNat 114391474269806391453), (Int.negOfNat 43564207273135691822), (Int.ofNat 102188623087738290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(27544522116594518713552609226686839/28147497671065600000000000000000000), (412979041460469474873525622743649/7036874417766400000000000000000000), (-35370605639017510198849708732279/14073748835532800000000000000000000), (-111666265936547969262942417509/2814749767106560000000000000000000), (3541611546108322144844928753167/14073748835532800000000000000000000), (289217132191900402643492524707/14073748835532800000000000000000000), (-39226445835885338703459762719/5629499534213120000000000000000000), (-22426833102604185648642256359/28147497671065600000000000000000000), (1027306042460677398368382277/14073748835532800000000000000000000), (75081889102059767805896761/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial167.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial167.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial167.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 30673537657513920664296802003919604), (Int.ofNat 1583494699115579445487016740352545), (Int.ofNat 81555606294658788139884746197046), (Int.ofNat 39769257565660900277671913158131), (Int.negOfNat 1916652571826682065576951025114), (Int.negOfNat 2289695400885288211123831200353), (Int.negOfNat 147409158100395961000561422101), (Int.ofNat 32373590736249486386074461306), (Int.ofNat 3060550927043590639528929414), (Int.negOfNat 250032036875972344476079875), (Int.negOfNat 29271236815194033064676204), (Int.ofNat 1271802572493033878730891), (Int.ofNat 176291983969081965882301), (Int.negOfNat 4655151312798729085980), (Int.negOfNat 750920934299743593510), (Int.ofNat 12665229977060096694), (Int.ofNat 2483230935369102135), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(7668384414378480166074200500979901/7036874417766400000000000000000000), (316698939823115889097403348070509/5629499534213120000000000000000000), (40777803147329394069942373098523/14073748835532800000000000000000000), (39769257565660900277671913158131/28147497671065600000000000000000000), (-958326285913341032788475512557/14073748835532800000000000000000000), (-2289695400885288211123831200353/28147497671065600000000000000000000), (-147409158100395961000561422101/28147497671065600000000000000000000), (16186795368124743193037230653/14073748835532800000000000000000000), (1530275463521795319764464707/14073748835532800000000000000000000), (-2000256295007778755808639/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial167.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial167.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial167.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 34376305268754757701075376379265424), (Int.ofNat 2131066901273434011601546737733847), (Int.ofNat 81414588959504726817019145309504), (Int.negOfNat 68845613836619811806933519945094), (Int.negOfNat 22493627075895656441281571492418), (Int.negOfNat 654970503022063406884257509697), (Int.ofNat 409910141486906462726971272013), (Int.ofNat 27614200203579358605670616874), (Int.negOfNat 3951741383761522337148243158), (Int.negOfNat 339349804775965233727827971), (Int.ofNat 24925527830638215636082069), (Int.ofNat 2439197623568222803497848), (Int.negOfNat 112862175842602976498109), (Int.negOfNat 12000343061996262826133), (Int.ofNat 387781628650032053153), (Int.ofNat 44038803789261667072), (Int.negOfNat 925396716217601790), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(2148519079297172356317211023704089/1759218604441600000000000000000000), (2131066901273434011601546737733847/28147497671065600000000000000000000), (1272102952492261356515924145461/439804651110400000000000000000000), (-34422806918309905903466759972547/14073748835532800000000000000000000), (-11246813537947828220640785746209/14073748835532800000000000000000000), (-654970503022063406884257509697/28147497671065600000000000000000000), (409910141486906462726971272013/28147497671065600000000000000000000), (13807100101789679302835308437/14073748835532800000000000000000000), (-1975870691880761168574121579/14073748835532800000000000000000000), (-339349804775965233727827971/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial167.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial167.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial167.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 38061088867250067434607446475610272), (Int.ofNat 944781383773065755144636954831954), (Int.negOfNat 815267387421633992244338503081271), (Int.negOfNat 202379716222232429355392397460584), (Int.negOfNat 2091111362311921903452437741380), (Int.ofNat 4387280092469575159648425516822), (Int.ofNat 236769823540351023935768301220), (Int.negOfNat 51617193653097397970376589490), (Int.negOfNat 3636248001099343718437492271), (Int.ofNat 396433338495740984743029546), (Int.ofNat 30925319888552350954303309), (Int.negOfNat 2162769517027617024345715), (Int.negOfNat 175666874298186894132964), (Int.ofNat 8838923334534747160515), (Int.ofNat 723737944275920875693), (Int.negOfNat 27390207151945654490), (Int.negOfNat 2212001052099706110), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1189409027101564607331482702362821/879609302220800000000000000000000), (472390691886532877572318477415977/14073748835532800000000000000000000), (-815267387421633992244338503081271/28147497671065600000000000000000000), (-25297464527779053669424049682573/3518437208883200000000000000000000), (-104555568115596095172621887069/1407374883553280000000000000000000), (2193640046234787579824212758411/14073748835532800000000000000000000), (11838491177017551196788415061/1407374883553280000000000000000000), (-5161719365309739797037658949/2814749767106560000000000000000000), (-3636248001099343718437492271/28147497671065600000000000000000000), (198216669247870492371514773/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial167.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial167.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial167.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 35185324500646709540250399173554227), (Int.negOfNat 4441122544291369069654351282723455), (Int.negOfNat 1711016200887103352297785730111690), (Int.negOfNat 38657854328889420400070323560395), (Int.ofNat 39366790187284606497721416567495), (Int.ofNat 2234018077233550997777589891618), (Int.negOfNat 562771759212313150335552894519), (Int.negOfNat 37663242245209589855542969520), (Int.ofNat 5293544352417242681953120950), (Int.ofNat 365671782498826053651098287), (Int.negOfNat 34850534000426866304713160), (Int.negOfNat 2368996113178695012179426), (Int.ofNat 168724342997041375636001), (Int.ofNat 11035513924033101171871), (Int.negOfNat 623249563744858525945), (Int.negOfNat 38844526429008954972), (Int.ofNat 1748604809347465290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(35185324500646709540250399173554227/28147497671065600000000000000000000), (-888224508858273813930870256544691/5629499534213120000000000000000000), (-171101620088710335229778573011169/2814749767106560000000000000000000), (-7731570865777884080014064712079/5629499534213120000000000000000000), (7873358037456921299544283313499/5629499534213120000000000000000000), (1117009038616775498888794945809/14073748835532800000000000000000000), (-562771759212313150335552894519/28147497671065600000000000000000000), (-470790528065119873194287119/351843720888320000000000000000000), (105870887048344853639062419/562949953421312000000000000000000), (365671782498826053651098287/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial167.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial167.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial167.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 19811773310568275602267711244054700), (Int.negOfNat 10429485545519240073742731633482101), (Int.negOfNat 969098074827510196436914611432040), (Int.ofNat 265340515194798874619952129400960), (Int.ofNat 24254347149772960751885926064941), (Int.negOfNat 4905333416018988922724847789291), (Int.negOfNat 391729574713518721524468492028), (Int.ofNat 58888150722652427201329600259), (Int.ofNat 4121537448906456549825194669), (Int.negOfNat 478500496928155005786658068), (Int.negOfNat 29755099661265172215849433), (Int.ofNat 2776693220993463361336723), (Int.ofNat 155033500806910646321823), (Int.negOfNat 12015098490932870944355), (Int.negOfNat 608454574641646551890), (Int.ofNat 39758179709615329786), (Int.ofNat 1940771168830310085), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(198117733105682756022677112440547/281474976710656000000000000000000), (-10429485545519240073742731633482101/28147497671065600000000000000000000), (-24227451870687754910922865285801/703687441776640000000000000000000), (414594554991873241593675202189/43980465111040000000000000000000), (24254347149772960751885926064941/28147497671065600000000000000000000), (-4905333416018988922724847789291/28147497671065600000000000000000000), (-97932393678379680381117123007/7036874417766400000000000000000000), (58888150722652427201329600259/28147497671065600000000000000000000), (4121537448906456549825194669/28147497671065600000000000000000000), (-119625124232038751446664517/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial167.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial167.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial167.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 2586514215776606757586020123753613), (Int.negOfNat 10783909382614359253089297762535460), (Int.ofNat 763105061542134649404705162028382), (Int.ofNat 237949787272678478245491269356290), (Int.negOfNat 29395143914015499522051505849402), (Int.negOfNat 3924263386688452913717233834268), (Int.ofNat 520014850013826483413957514694), (Int.ofNat 44442046242486255401241338252), (Int.negOfNat 5528218053366700705725624001), (Int.negOfNat 351430557321566393900607615), (Int.ofNat 39541969775095650370347270), (Int.ofNat 2017202779322647413044458), (Int.negOfNat 203261054696493397631351), (Int.negOfNat 8703907908042219895859), (Int.ofNat 787217637255375940878), (Int.ofNat 28708641969614875343), (Int.negOfNat 2481402941387530115), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2586514215776606757586020123753613/28147497671065600000000000000000000), (-539195469130717962654464888126773/1407374883553280000000000000000000), (381552530771067324702352581014191/14073748835532800000000000000000000), (23794978727267847824549126935629/2814749767106560000000000000000000), (-14697571957007749761025752924701/14073748835532800000000000000000000), (-981065846672113228429308458567/7036874417766400000000000000000000), (260007425006913241706978757347/14073748835532800000000000000000000), (11110511560621563850310334563/7036874417766400000000000000000000), (-5528218053366700705725624001/28147497671065600000000000000000000), (-70286111464313278780121523/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial167.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial167.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial167.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial167.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial167.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial167.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial167.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial167.reflect := by
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

end Bin167
end
end ErdosOverlap.OuterNumerics
