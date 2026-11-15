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

/-! # Exact integer weighted outer models for source bin 132

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin132

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 3940880559689248000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 3234115394611007000)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2372976690829085000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1624213799593611500)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1144541587077571000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 657151374137190100)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 337464193359572900)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 101880753926121060)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial132.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial132.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9557899539000637000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1383403012773232000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1678672938113520400)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 304061329031016500)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 116694761812255850)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 33839225494511176)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 97938786686060380)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 63587902918567490)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 1640521987627299)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial132.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial132.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9557899539000637000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1383403012773232000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1678672938113520400)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 304061329031016500)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 116694761812255850)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 33839225494511176)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 97938786686060380)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 63587902918567490)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 1640521987627299)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial132.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial132.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial132.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 11962825551514617062364318625770755), (Int.ofNat 4251845770429488283910122412235081), (Int.ofNat 1019438196831221597722434864087938), (Int.negOfNat 120540140371037267484349478934537), (Int.negOfNat 25413179326881574128943546511851), (Int.ofNat 2218633325443748549052866820965), (Int.ofNat 354183426389722848151890456869), (Int.negOfNat 25925817068792239155254158591), (Int.negOfNat 3177445974493471457626678864), (Int.ofNat 205079707120662138131458206), (Int.ofNat 19856989555415140811566105), (Int.negOfNat 1161896085923325426603910), (Int.negOfNat 91335794285345499700121), (Int.ofNat 4924421943630834556017), (Int.ofNat 322899603933158133259), (Int.negOfNat 15956599861326615825), (Int.negOfNat 920298997834509484), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-2392565110302923412472863725154151/2251799813685248000000000000000000), (4251845770429488283910122412235081/11258999068426240000000000000000000), (509719098415610798861217432043969/5629499534213120000000000000000000), (-120540140371037267484349478934537/11258999068426240000000000000000000), (-25413179326881574128943546511851/11258999068426240000000000000000000), (443726665088749709810573364193/2251799813685248000000000000000000), (354183426389722848151890456869/11258999068426240000000000000000000), (-25925817068792239155254158591/11258999068426240000000000000000000), (-198590373405841966101667429/703687441776640000000000000000000), (102539853560331069065729103/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial132.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial132.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial132.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial132 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.negOfNat 662658514839778543009248455173243), (Int.ofNat 6301079682028651935524120258254742), (Int.negOfNat 73204633674304613087949780182983), (Int.negOfNat 197293540189248301949917442943389), (Int.ofNat 8241380414893465700977330746063), (Int.ofNat 3399419757059081560924243132392), (Int.negOfNat 181415684161167565931291535807), (Int.negOfNat 35968892416968249267766352613), (Int.ofNat 2080243517755470658039369043), (Int.ofNat 256641707853199335805928819), (Int.negOfNat 15280736935466502352024238), (Int.negOfNat 1318303816517717801605837), (Int.ofNat 79054159351555812402307), (Int.ofNat 5110622287802489022075), (Int.negOfNat 305509986934544165998), (Int.negOfNat 15099936063421152281), (Int.ofNat 980479479973343634), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-662658514839778543009248455173243/11258999068426240000000000000000000), (3150539841014325967762060129127371/5629499534213120000000000000000000), (-73204633674304613087949780182983/11258999068426240000000000000000000), (-197293540189248301949917442943389/11258999068426240000000000000000000), (8241380414893465700977330746063/11258999068426240000000000000000000), (424927469632385195115530391549/1407374883553280000000000000000000), (-181415684161167565931291535807/11258999068426240000000000000000000), (-35968892416968249267766352613/11258999068426240000000000000000000), (2080243517755470658039369043/11258999068426240000000000000000000), (256641707853199335805928819/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial132.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial132.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial132.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial132 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 10293408845619652392517842458636954), (Int.ofNat 4128101105546534195186599779224777), (Int.negOfNat 850226746195602680246223838548800), (Int.negOfNat 39727541110571511610298390926273), (Int.ofNat 24394481158726266052907073448666), (Int.negOfNat 502473283730585750027462580618), (Int.negOfNat 344831080921281422833437417650), (Int.ofNat 15052568960416080344501585415), (Int.ofNat 2977699456929592839315278614), (Int.negOfNat 164382349463664289693080071), (Int.negOfNat 17557472686516131764208886), (Int.ofNat 1094753869702015543356145), (Int.ofNat 75661676444318797023140), (Int.negOfNat 5091953331506678982758), (Int.negOfNat 249219899540477541743), (Int.ofNat 17823992560087247599), (Int.ofNat 616297258043773603), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(5146704422809826196258921229318477/5629499534213120000000000000000000), (4128101105546534195186599779224777/11258999068426240000000000000000000), (-531391716372251675153889899093/7036874417766400000000000000000), (-39727541110571511610298390926273/11258999068426240000000000000000000), (12197240579363133026453536724333/5629499534213120000000000000000000), (-251236641865292875013731290309/5629499534213120000000000000000000), (-6896621618425628456668748353/225179981368524800000000000000000), (3010513792083216068900317083/2251799813685248000000000000000000), (1488849728464796419657639307/5629499534213120000000000000000000), (-164382349463664289693080071/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial132.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial132.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial132.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial132 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 15185636491378395433232460271939169), (Int.ofNat 934019573855679788329754521149628), (Int.negOfNat 611555087778837144523439511176232), (Int.ofNat 92821600527556077253573564329488), (Int.ofNat 5384627623676822266666529413221), (Int.negOfNat 2476834124553722255233583319366), (Int.ofNat 49347309575115467602045518625), (Int.ofNat 29230421261091159225735330940), (Int.negOfNat 1338830028979091727618781856), (Int.negOfNat 209468843416615739976615776), (Int.ofNat 12757808664295816760262831), (Int.ofNat 1031152520043033492859507), (Int.negOfNat 74603489879885886514668), (Int.negOfNat 3738003848357118550404), (Int.ofNat 307606152216259021952), (Int.ofNat 9932567410243448386), (Int.negOfNat 985401045936225531), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(15185636491378395433232460271939169/11258999068426240000000000000000000), (233504893463919947082438630287407/2814749767106560000000000000000000), (-76444385972354643065429938897029/1407374883553280000000000000000000), (5801350032972254828348347770593/703687441776640000000000000000000), (5384627623676822266666529413221/11258999068426240000000000000000000), (-1238417062276861127616791659683/5629499534213120000000000000000000), (394778476600923740816364149/90071992547409920000000000000000), (1461521063054557961286766547/562949953421312000000000000000000), (-41838438405596616488086933/351843720888320000000000000000000), (-6545901356769241874269243/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial132.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial132.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial132.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial132 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 15363388020311331291453358752198789), (Int.negOfNat 403388943166060539416652221553838), (Int.negOfNat 95248880105853079409650911493987), (Int.ofNat 57794836387603040024174384574022), (Int.negOfNat 10377888914073299290946717899250), (Int.negOfNat 326483660628835391260391995539), (Int.ofNat 220994473937069334025446310222), (Int.negOfNat 6817084640781046311133864208), (Int.negOfNat 2132100887930720684679727568), (Int.ofNat 120058720741541343794850144), (Int.ofNat 12607697081094672673744545), (Int.negOfNat 943570662850283722519351), (Int.negOfNat 51350766534140702238371), (Int.ofNat 4755926662202349268717), (Int.ofNat 153033684014711902446), (Int.negOfNat 17761552098937282347), (Int.negOfNat 310654996265410423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(15363388020311331291453358752198789/11258999068426240000000000000000000), (-201694471583030269708326110776919/5629499534213120000000000000000000), (-95248880105853079409650911493987/11258999068426240000000000000000000), (28897418193801520012087192287011/5629499534213120000000000000000000), (-41511555656293197163786871597/45035996273704960000000000000000), (-326483660628835391260391995539/11258999068426240000000000000000000), (110497236968534667012723155111/5629499534213120000000000000000000), (-426067790048815394445866513/703687441776640000000000000000000), (-133256305495670042792482973/703687441776640000000000000000000), (3751835023173166993589067/351843720888320000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial132.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial132.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial132.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial132 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 14474277125025374031000215295287443), (Int.negOfNat 411534408531612372117081282843506), (Int.ofNat 21638210792928252027769165620240), (Int.negOfNat 9771874574438024199047849476605), (Int.negOfNat 4070784922781850103564797667321), (Int.ofNat 1109904475754794474441986113857), (Int.negOfNat 6068437355106814977702641131), (Int.negOfNat 17262144143664662502546557408), (Int.ofNat 856724569899333236244400593), (Int.ofNat 132750024212707944421508446), (Int.negOfNat 10085179662248264535967107), (Int.negOfNat 632798893887146226383271), (Int.ofNat 64672248855017157528532), (Int.ofNat 2046105100667842726784), (Int.negOfNat 279865703678135775385), (Int.negOfNat 4528626809460956391), (Int.ofNat 990322611899107428), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(14474277125025374031000215295287443/11258999068426240000000000000000000), (-205767204265806186058540641421753/5629499534213120000000000000000000), (270477634911603150347114570253/140737488355328000000000000000000), (-1954374914887604839809569895321/2251799813685248000000000000000000), (-4070784922781850103564797667321/11258999068426240000000000000000000), (1109904475754794474441986113857/11258999068426240000000000000000000), (-6068437355106814977702641131/11258999068426240000000000000000000), (-539442004489520703204579919/351843720888320000000000000000000), (856724569899333236244400593/11258999068426240000000000000000000), (66375012106353972210754223/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial132.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial132.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial132.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial132 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 13627648547842981536369775384209988), (Int.negOfNat 491489356660084655502042045049949), (Int.negOfNat 56938549822357135611917687427142), (Int.negOfNat 6504778148194603244492350350000), (Int.ofNat 3171909705136346465495763237614), (Int.ofNat 145399474625632553391726219918), (Int.negOfNat 101764633104306078654005757233), (Int.ofNat 4276904167717285768795137702), (Int.ofNat 1137392675632106079695376427), (Int.negOfNat 89055641669013792213901932), (Int.negOfNat 6728421147095087859149624), (Int.ofNat 763254207922738014895316), (Int.ofNat 24027572446126538486007), (Int.negOfNat 4036964533738957944235), (Int.negOfNat 50115859879383644159), (Int.ofNat 15658215515289641297), (Int.ofNat 5012734487047243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3406912136960745384092443846052497/2814749767106560000000000000000000), (-491489356660084655502042045049949/11258999068426240000000000000000000), (-28469274911178567805958843713571/5629499534213120000000000000000000), (-130095562963892064889847007/225179981368524800000000000000), (1585954852568173232747881618807/5629499534213120000000000000000000), (72699737312816276695863109959/5629499534213120000000000000000000), (-101764633104306078654005757233/11258999068426240000000000000000000), (2138452083858642884397568851/5629499534213120000000000000000000), (1137392675632106079695376427/11258999068426240000000000000000000), (-22263910417253448053475483/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial132.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial132.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial132.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial132 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 12414555570009532496440673548792974), (Int.negOfNat 700856554644663920290858040927533), (Int.negOfNat 28186066245953164742578029909943), (Int.ofNat 12289053285233884586952703372137), (Int.ofNat 575733151130178218191450637504), (Int.negOfNat 417091464573617658251337933914), (Int.ofNat 14863880387060048531325502107), (Int.ofNat 7389265873588203950420042235), (Int.negOfNat 642977339926808717729095635), (Int.negOfNat 58245189344965598522162179), (Int.ofNat 7719211442792984321112063), (Int.ofNat 234698503422716040141375), (Int.negOfNat 51234315954109336547542), (Int.negOfNat 392726408205889114019), (Int.ofNat 225753201589448154746), (Int.negOfNat 953991081654545324), (Int.negOfNat 893363423935868265), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(6207277785004766248220336774396487/5629499534213120000000000000000000), (-700856554644663920290858040927533/11258999068426240000000000000000000), (-28186066245953164742578029909943/11258999068426240000000000000000000), (12289053285233884586952703372137/11258999068426240000000000000000000), (8995830486409034659241416211/175921860444160000000000000000000), (-208545732286808829125668966957/5629499534213120000000000000000000), (14863880387060048531325502107/11258999068426240000000000000000000), (1477853174717640790084008447/2251799813685248000000000000000000), (-128595467985361743545819127/2251799813685248000000000000000000), (-58245189344965598522162179/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial132.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial132.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial132.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial132 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 10995986291914709622113390083564819), (Int.negOfNat 675663474702598512112861392570711), (Int.ofNat 33202932187792841136896023879968), (Int.ofNat 5384887193424149276850996278871), (Int.negOfNat 1482084742043726714238616431441), (Int.ofNat 40585026744486256747419557633), (Int.ofNat 33616263625506650555556843967), (Int.negOfNat 3883373903823190036017246751), (Int.negOfNat 373409626232491447982275235), (Int.ofNat 66388253106048600447017991), (Int.ofNat 1672162625354671048633751), (Int.negOfNat 565234997661245877803263), (Int.ofNat 62262784471479384906), (Int.ofNat 3023683137888937881659), (Int.negOfNat 38217055588405084062), (Int.negOfNat 11702318695843114796), (Int.ofNat 202029817340449475), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(10995986291914709622113390083564819/11258999068426240000000000000000000), (-675663474702598512112861392570711/11258999068426240000000000000000000), (1037591630868526285528000746249/351843720888320000000000000000000), (5384887193424149276850996278871/11258999068426240000000000000000000), (-1482084742043726714238616431441/11258999068426240000000000000000000), (40585026744486256747419557633/11258999068426240000000000000000000), (33616263625506650555556843967/11258999068426240000000000000000000), (-3883373903823190036017246751/11258999068426240000000000000000000), (-74681925246498289596455047/2251799813685248000000000000000000), (66388253106048600447017991/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial132.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial132.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial132.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial132 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9799728879465581153671281422039680), (Int.negOfNat 517925500852596977493019529797263), (Int.ofNat 38287876867033761704159644796227), (Int.negOfNat 1954070359538105553576498380642), (Int.negOfNat 297499959572733802053748733644), (Int.ofNat 82030901822395330599649644812), (Int.negOfNat 20085779690167561096886420221), (Int.negOfNat 1377026769870259259765105210), (Int.ofNat 485920141640748494679657915), (Int.ofNat 4611216612203539473575248), (Int.negOfNat 5345635642483988320470096), (Int.ofNat 73143162361189398382188), (Int.ofNat 35029276118676076245983), (Int.negOfNat 901337553023270445197), (Int.negOfNat 154870432829520911295), (Int.ofNat 5240288277458631103), (Int.ofNat 692882960058880743), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(15312076374164970552611377221937/17592186044416000000000000000000), (-517925500852596977493019529797263/11258999068426240000000000000000000), (38287876867033761704159644796227/11258999068426240000000000000000000), (-977035179769052776788249190321/5629499534213120000000000000000000), (-74374989893183450513437183411/2814749767106560000000000000000000), (20507725455598832649912411203/2814749767106560000000000000000000), (-20085779690167561096886420221/11258999068426240000000000000000000), (-137702676987025925976510521/1125899906842624000000000000000000), (97184028328149698935931583/2251799813685248000000000000000000), (288201038262721217098453/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial132.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial132.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial132.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial132 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8897921628642672592172048353419043), (Int.negOfNat 395171284703440720707324303515212), (Int.ofNat 21074644860692362265667617090411), (Int.negOfNat 4217576866581832130905954416736), (Int.negOfNat 569870771604176656622672262387), (Int.negOfNat 85510261176493536116692042913), (Int.ofNat 3048359030451084754301458833), (Int.ofNat 3047551835505689423939702436), (Int.negOfNat 80705553764473339421699063), (Int.negOfNat 42590226953484007833287706), (Int.ofNat 1652395667722371621401077), (Int.ofNat 343503936252575204856903), (Int.negOfNat 16502114208521631026548), (Int.negOfNat 1803046087120882760688), (Int.ofNat 99507279302035764311), (Int.ofNat 6497604477481098791), (Int.negOfNat 308832137229452432), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(8897921628642672592172048353419043/11258999068426240000000000000000000), (-98792821175860180176831075878803/2814749767106560000000000000000000), (21074644860692362265667617090411/11258999068426240000000000000000000), (-131799277080682254090811075523/351843720888320000000000000000000), (-569870771604176656622672262387/11258999068426240000000000000000000), (-85510261176493536116692042913/11258999068426240000000000000000000), (3048359030451084754301458833/11258999068426240000000000000000000), (761887958876422355984925609/2814749767106560000000000000000000), (-80705553764473339421699063/11258999068426240000000000000000000), (-21295113476742003916643853/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial132.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial132.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial132.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial132 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8146827792813432687412592713720216), (Int.negOfNat 384778654904391443103202516169650), (Int.negOfNat 22282508137235017896250758341153), (Int.negOfNat 10338589395204558127268071536048), (Int.negOfNat 616788842040131156686672690097), (Int.ofNat 106378263026179635898004529162), (Int.ofNat 17401906036701513734058385974), (Int.negOfNat 1541423158683597463563614020), (Int.negOfNat 278511142430891874585149768), (Int.ofNat 24135033539993404171664492), (Int.ofNat 2710711205968807172329649), (Int.negOfNat 247340056796236741980681), (Int.negOfNat 16893444393443428403803), (Int.ofNat 1635310396258476404427), (Int.ofNat 71667226986641976590), (Int.negOfNat 7507677059869002053), (Int.negOfNat 387240698280517563), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(1018353474101679085926574089215027/1407374883553280000000000000000000), (-7695573098087828862064050323393/225179981368524800000000000000000), (-22282508137235017896250758341153/11258999068426240000000000000000000), (-646161837200284882954254471003/703687441776640000000000000000000), (-616788842040131156686672690097/11258999068426240000000000000000000), (53189131513089817949002264581/5629499534213120000000000000000000), (8700953018350756867029192987/5629499534213120000000000000000000), (-77071157934179873178180701/562949953421312000000000000000000), (-34813892803861484323143721/1407374883553280000000000000000000), (6033758384998351042916123/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial132.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial132.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial132.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial132 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 7199826910705768845952346140574753), (Int.negOfNat 606766950839036550206971940985358), (Int.negOfNat 87830570055504049082838743255571), (Int.negOfNat 9436199018363322850911694227290), (Int.ofNat 869384471656840790103924583905), (Int.ofNat 123027087351654594015261341614), (Int.negOfNat 14305496360315463305602307544), (Int.negOfNat 1455599634438474329394304592), (Int.ofNat 258278071564188278533580224), (Int.ofNat 14991642470286696260882060), (Int.negOfNat 3057657284424241644795225), (Int.negOfNat 105780476370995401791755), (Int.ofNat 23364877312166704036100), (Int.ofNat 499029994295311045500), (Int.negOfNat 121393436296333512824), (Int.negOfNat 1305946669947000546), (Int.ofNat 313753703192334329), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(7199826910705768845952346140574753/11258999068426240000000000000000000), (-303383475419518275103485970492679/5629499534213120000000000000000000), (-87830570055504049082838743255571/11258999068426240000000000000000000), (-943619901836332285091169422729/1125899906842624000000000000000000), (173876894331368158020784916781/2251799813685248000000000000000000), (61513543675827297007630670807/5629499534213120000000000000000000), (-1788187045039432913200288443/1407374883553280000000000000000000), (-90974977152404645587144037/703687441776640000000000000000000), (4035594868190441852087191/175921860444160000000000000000000), (749582123514334813044103/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial132.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial132.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial132.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial132 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 5576296831457024474817864711478418), (Int.negOfNat 1036777155850584021514409602442712), (Int.negOfNat 117656526650639878220846761908816), (Int.negOfNat 169373900822406872561192079098), (Int.ofNat 1140928882092461149576846676988), (Int.negOfNat 50355723611213931535652341777), (Int.negOfNat 6123254073015239817527605526), (Int.ofNat 1934940590062790168869800317), (Int.ofNat 20361658790345259880671558), (Int.negOfNat 30294683077565680926004229), (Int.ofNat 41830169938156029947538), (Int.ofNat 281491259993591447633303), (Int.negOfNat 1373507298759153370340), (Int.negOfNat 1735181861038489608498), (Int.ofNat 10592801710927495913), (Int.ofNat 7740731807732206401), (Int.ofNat 81598436502154383), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(2788148415728512237408932355739209/5629499534213120000000000000000000), (-129597144481323002689301200305339/1407374883553280000000000000000000), (-7353532915664992388802922619301/703687441776640000000000000000000), (-84686950411203436280596039549/5629499534213120000000000000000000), (285232220523115287394211669247/2814749767106560000000000000000000), (-50355723611213931535652341777/11258999068426240000000000000000000), (-3061627036507619908763802763/5629499534213120000000000000000000), (1934940590062790168869800317/11258999068426240000000000000000000), (10180829395172629940335779/5629499534213120000000000000000000), (-30294683077565680926004229/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial132.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial132.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial132.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial132 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 3047250986668333308635248315607724), (Int.negOfNat 1477308981040745173754242475946733), (Int.negOfNat 95583296137551024063892906761805), (Int.ofNat 6933190318576582549599823500318), (Int.ofNat 724092059959059691433952518329), (Int.negOfNat 5268169450893708234323454988), (Int.ofNat 6755437779340845153815141205), (Int.negOfNat 783881907596683845100308079), (Int.negOfNat 220200883959487762629650709), (Int.ofNat 13140765372770389297296945), (Int.ofNat 2728532326182624808807210), (Int.negOfNat 119537207841534652786587), (Int.negOfNat 20677802763343534641477), (Int.ofNat 723103575800555994277), (Int.ofNat 106753688899375365346), (Int.negOfNat 3714760069487401559), (Int.negOfNat 318675269155216226), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(761812746667083327158812078901931/2814749767106560000000000000000000), (-1477308981040745173754242475946733/11258999068426240000000000000000000), (-19116659227510204812778581352361/2251799813685248000000000000000000), (3466595159288291274799911750159/5629499534213120000000000000000000), (724092059959059691433952518329/11258999068426240000000000000000000), (-1317042362723427058580863747/2814749767106560000000000000000000), (1351087555868169030763028241/2251799813685248000000000000000000), (-783881907596683845100308079/11258999068426240000000000000000000), (-220200883959487762629650709/11258999068426240000000000000000000), (2628153074554077859459389/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial132.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial132.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial132.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial132 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 222532906033344099534563049596262), (Int.negOfNat 1752931568535862280035918349987730), (Int.negOfNat 36240088134540218586604386195282), (Int.ofNat 12867957026028603074771992211757), (Int.ofNat 692973339294796428512347899634), (Int.negOfNat 45499798820144494883650402722), (Int.negOfNat 13642748453995227909410517991), (Int.negOfNat 831409263892271464187180533), (Int.ofNat 232547692868691256040920096), (Int.ofNat 18649706713470816617017782), (Int.negOfNat 2461771412238313801289607), (Int.negOfNat 191174038728739497132402), (Int.ofNat 17079288522471800505847), (Int.ofNat 1235537307823020679383), (Int.negOfNat 83434443559811383109), (Int.negOfNat 5828389558461165375), (Int.ofNat 225684347263836096), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-111266453016672049767281524798131/5629499534213120000000000000000000), (-175293156853586228003591834998773/1125899906842624000000000000000000), (-18120044067270109293302193097641/5629499534213120000000000000000000), (12867957026028603074771992211757/11258999068426240000000000000000000), (346486669647398214256173949817/5629499534213120000000000000000000), (-22749899410072247441825201361/5629499534213120000000000000000000), (-13642748453995227909410517991/11258999068426240000000000000000000), (-831409263892271464187180533/11258999068426240000000000000000000), (7267115402146601751278753/351843720888320000000000000000000), (9324853356735408308508891/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial132.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial132.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial132.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial132 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 3761694468825131097069798377698530), (Int.negOfNat 1727666337999088759578025617431212), (Int.ofNat 50596300232653692038558675946353), (Int.ofNat 14416635663016396293063003072735), (Int.negOfNat 516378618301593661004119378751), (Int.negOfNat 160737548404145222318320942073), (Int.ofNat 3403323759915433293388120431), (Int.ofNat 2726950047054164045509356907), (Int.ofNat 39464504951631450619993104), (Int.negOfNat 35050839968042323531257418), (Int.negOfNat 1014077237502059643227553), (Int.ofNat 292413166044157777491518), (Int.ofNat 9818272738630325203993), (Int.negOfNat 1668361136498807505337), (Int.negOfNat 57953008217669008051), (Int.ofNat 7192558567214442705), (Int.ofNat 118194805278228704), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-376169446882513109706979837769853/1125899906842624000000000000000000), (-431916584499772189894506404357803/2814749767106560000000000000000000), (50596300232653692038558675946353/11258999068426240000000000000000000), (2883327132603279258612600614547/2251799813685248000000000000000000), (-516378618301593661004119378751/11258999068426240000000000000000000), (-160737548404145222318320942073/11258999068426240000000000000000000), (3403323759915433293388120431/11258999068426240000000000000000000), (2726950047054164045509356907/11258999068426240000000000000000000), (2466531559476965663749569/703687441776640000000000000000000), (-17525419984021161765628709/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial132.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial132.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial132.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial132 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 6912155912533612806708585167966035), (Int.negOfNat 1379831613183424349014400327465695), (Int.ofNat 114399471735809254251293261517995), (Int.ofNat 5807378916819019612835669703507), (Int.negOfNat 1253816284750930643477660851730), (Int.ofNat 57061482051167265872474765358), (Int.ofNat 23551001618457250205061087155), (Int.negOfNat 1065995149422470203470246599), (Int.negOfNat 383882430549751506331978971), (Int.ofNat 5899759749070624591671345), (Int.ofNat 3993018971454399803004990), (Int.ofNat 3910229605137117211533), (Int.negOfNat 27382434764867025169923), (Int.negOfNat 249586379267644928443), (Int.ofNat 131669948120722706614), (Int.ofNat 2266268982520659801), (Int.negOfNat 432726899091332814), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1382431182506722561341717033593207/2251799813685248000000000000000000), (-275966322636684869802880065493139/2251799813685248000000000000000000), (22879894347161850850258652303599/2251799813685248000000000000000000), (5807378916819019612835669703507/11258999068426240000000000000000000), (-125381628475093064347766085173/1125899906842624000000000000000000), (28530741025583632936237382679/5629499534213120000000000000000000), (4710200323691450041012217431/2251799813685248000000000000000000), (-1065995149422470203470246599/11258999068426240000000000000000000), (-383882430549751506331978971/11258999068426240000000000000000000), (1179951949814124918334269/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial132.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial132.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial132.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial132 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 9184717765415712630196024959813493), (Int.negOfNat 884417840536192699851275598568265), (Int.ofNat 128036502202953574601480257924719), (Int.ofNat 632750338729741239237306029130), (Int.ofNat 75625811072891169198077502771), (Int.ofNat 119637716071182055200526381504), (Int.negOfNat 18501076823173022653434509354), (Int.negOfNat 3168043613613422358633296043), (Int.ofNat 244263297229317394829838042), (Int.ofNat 43878714312354021411021451), (Int.negOfNat 1684559538901544867600538), (Int.negOfNat 374769152523099634650657), (Int.ofNat 6985514945803991763180), (Int.ofNat 2161256479798640476582), (Int.negOfNat 17609708643232591353), (Int.negOfNat 9059951265975074479), (Int.ofNat 185806934512507177), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-9184717765415712630196024959813493/11258999068426240000000000000000000), (-176883568107238539970255119713653/2251799813685248000000000000000000), (128036502202953574601480257924719/11258999068426240000000000000000000), (63275033872974123923730602913/1125899906842624000000000000000000), (75625811072891169198077502771/11258999068426240000000000000000000), (1869339313612219612508224711/175921860444160000000000000000000), (-9250538411586511326717254677/5629499534213120000000000000000000), (-3168043613613422358633296043/11258999068426240000000000000000000), (122131648614658697414919021/5629499534213120000000000000000000), (43878714312354021411021451/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial132.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial132.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial132.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial132 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 10432814043034259835952925757085625), (Int.negOfNat 357320616226954380888580936721531), (Int.ofNat 137260614059921697145565417945721), (Int.ofNat 1922286363965363238699888365226), (Int.negOfNat 311455994994131027685055562375), (Int.negOfNat 193890641936702902415614465656), (Int.negOfNat 16357688757693939023414971737), (Int.ofNat 3855618062664360361243195488), (Int.ofNat 370269382024542551667393416), (Int.negOfNat 39001596576846765023365860), (Int.negOfNat 4196892436904993781486935), (Int.ofNat 245477898555329456053245), (Int.ofNat 30010825737212624873860), (Int.negOfNat 1047681679064466465300), (Int.negOfNat 147432933996379392216), (Int.ofNat 2901099670657044094), (Int.ofNat 437648465054214711), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-16692502468854815737524681211337/18014398509481984000000000000000), (-357320616226954380888580936721531/11258999068426240000000000000000000), (137260614059921697145565417945721/11258999068426240000000000000000000), (961143181982681619349944182613/5629499534213120000000000000000000), (-2491647959953048221480444499/90071992547409920000000000000000), (-24236330242087862801951808207/1407374883553280000000000000000000), (-16357688757693939023414971737/11258999068426240000000000000000000), (120488064458261261288849859/351843720888320000000000000000000), (46283672753067818958424177/1407374883553280000000000000000000), (-1950079828842338251168293/562949953421312000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial132.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial132.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial132.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial132 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 10594704560443523092427280700826372), (Int.ofNat 188169312837550975691366428195008), (Int.ofNat 124917444417113461597799266595847), (Int.negOfNat 8380344824003291900460803072682), (Int.negOfNat 1937560068048409608660337890350), (Int.negOfNat 3083018587629438876950276920), (Int.ofNat 43852840265017148221501459286), (Int.ofNat 2019520930241311711893265660), (Int.negOfNat 592824834129798988786262152), (Int.negOfNat 35854782251350952309732548), (Int.ofNat 4906030750758120643085911), (Int.ofNat 340875717324827885115599), (Int.negOfNat 26965346771323065537877), (Int.negOfNat 2088146279867043757733), (Int.ofNat 104301199217432550890), (Int.ofNat 8997510804825109227), (Int.negOfNat 491449196290870357), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-2648676140110880773106820175206593/2814749767106560000000000000000000), (2940145513086733995177600440547/175921860444160000000000000000000), (124917444417113461597799266595847/11258999068426240000000000000000000), (-4190172412001645950230401536341/5629499534213120000000000000000000), (-38751201360968192173206757807/225179981368524800000000000000000), (-77075464690735971923756923/281474976710656000000000000000000), (21926420132508574110750729643/5629499534213120000000000000000000), (100976046512065585594663283/562949953421312000000000000000000), (-74103104266224873598282769/1407374883553280000000000000000000), (-8963695562837738077433137/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial132.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial132.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial132.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial132 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 9813937977405105280476390428298069), (Int.ofNat 533689416255594026373444579677540), (Int.ofNat 38605537726952416143094872501788), (Int.negOfNat 17025657942232652689241877112824), (Int.ofNat 495999563702795229342258631382), (Int.ofNat 401273262917267500888011366798), (Int.ofNat 1206213594593235995454346807), (Int.negOfNat 6973370012403545446289232844), (Int.negOfNat 178518174251926145521205217), (Int.ofNat 74899872860131342957848214), (Int.ofNat 2833588568429095803629243), (Int.negOfNat 517672088498664202370217), (Int.negOfNat 23732148119294657530652), (Int.ofNat 2456478855361427422112), (Int.ofNat 128510425899931601889), (Int.negOfNat 8305040271439536089), (Int.negOfNat 442570031017096608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-9813937977405105280476390428298069/11258999068426240000000000000000000), (26684470812779701318672228983877/562949953421312000000000000000000), (9651384431738104035773718125447/2814749767106560000000000000000000), (-2128207242779081586155234639103/1407374883553280000000000000000000), (247999781851397614671129315691/5629499534213120000000000000000000), (200636631458633750444005683399/5629499534213120000000000000000000), (1206213594593235995454346807/11258999068426240000000000000000000), (-1743342503100886361572308211/2814749767106560000000000000000000), (-178518174251926145521205217/11258999068426240000000000000000000), (37449936430065671478924107/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial132.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial132.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial132.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial132 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 8708386499587540789000808445056562), (Int.ofNat 528883045737449086478725175947949), (Int.negOfNat 23897045282966596166810868695230), (Int.negOfNat 616285366911516682188865416082), (Int.ofNat 2744830668325690264997644130842), (Int.negOfNat 92944809627910102448230882671), (Int.negOfNat 65005247932590206636134899099), (Int.ofNat 651060893891734498213431630), (Int.ofNat 925921619172585440815575925), (Int.ofNat 8943442591355037242873808), (Int.negOfNat 8149994922280097138455184), (Int.negOfNat 179948585760721941845012), (Int.ofNat 47269020592760885439817), (Int.ofNat 1416228016378646957323), (Int.negOfNat 193416845856840934825), (Int.negOfNat 6894174221177468177), (Int.ofNat 797091458069233537), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-4354193249793770394500404222528281/5629499534213120000000000000000000), (528883045737449086478725175947949/11258999068426240000000000000000000), (-2389704528296659616681086869523/1125899906842624000000000000000000), (-308142683455758341094432708041/5629499534213120000000000000000000), (1372415334162845132498822065421/5629499534213120000000000000000000), (-92944809627910102448230882671/11258999068426240000000000000000000), (-65005247932590206636134899099/11258999068426240000000000000000000), (65106089389173449821343163/1125899906842624000000000000000000), (37036864766903417632623037/450359962737049600000000000000000), (558965161959689827679613/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial132.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial132.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial132.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial132 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 7714039712739633561885597562852901), (Int.ofNat 495035312672802384953713563656406), (Int.ofNat 17286699234747056246664308043734), (Int.ofNat 9168454136779130133700381225604), (Int.negOfNat 940383774488937602746955148431), (Int.negOfNat 451472677731614496525284671518), (Int.ofNat 26724160101339914362138147453), (Int.ofNat 9240736170009450793174455329), (Int.negOfNat 225547370937494156473138845), (Int.negOfNat 107857293417790140614349649), (Int.ofNat 198370059148335762638929), (Int.ofNat 778053021218227981397017), (Int.ofNat 8624386685865710195854), (Int.negOfNat 3797640135516116037381), (Int.negOfNat 71702769931154705138), (Int.ofNat 13787658162555037804), (Int.ofNat 345610843053857445), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-7714039712739633561885597562852901/11258999068426240000000000000000000), (247517656336401192476856781828203/5629499534213120000000000000000000), (8643349617373528123332154021867/5629499534213120000000000000000000), (2292113534194782533425095306401/2814749767106560000000000000000000), (-940383774488937602746955148431/11258999068426240000000000000000000), (-225736338865807248262642335759/5629499534213120000000000000000000), (26724160101339914362138147453/11258999068426240000000000000000000), (9240736170009450793174455329/11258999068426240000000000000000000), (-45109474187498831294627769/2251799813685248000000000000000000), (-107857293417790140614349649/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial132.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial132.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial132.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial132 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 6608185925955603868394300469368630), (Int.ofNat 616794673599394657001023465858413), (Int.ofNat 25356941598360418947986440705029), (Int.negOfNat 7911123506782195633399358698810), (Int.negOfNat 1916549445686554560142038918462), (Int.ofNat 351151206953381725778171307445), (Int.ofNat 70179003182237014585662481213), (Int.negOfNat 5807712365649149177419218485), (Int.negOfNat 1194480947461729362688323085), (Int.ofNat 38958183192506714567859581), (Int.ofNat 11115791806798239323611857), (Int.negOfNat 100738286562655890367345), (Int.negOfNat 65657553514183140361618), (Int.negOfNat 218193144826273153859), (Int.ofNat 270575059257810042454), (Int.ofNat 2938277401730941676), (Int.negOfNat 1004134009896730255), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-660818592595560386839430046936863/1125899906842624000000000000000000), (616794673599394657001023465858413/11258999068426240000000000000000000), (25356941598360418947986440705029/11258999068426240000000000000000000), (-791112350678219563339935869881/1125899906842624000000000000000000), (-958274722843277280071019459231/5629499534213120000000000000000000), (70230241390676345155634261489/2251799813685248000000000000000000), (70179003182237014585662481213/11258999068426240000000000000000000), (-1161542473129829835483843697/2251799813685248000000000000000000), (-238896189492345872537664617/2251799813685248000000000000000000), (38958183192506714567859581/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial132.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial132.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial132.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial132 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 5352412614408954500789701168514896), (Int.ofNat 599844781180896316174497666082437), (Int.negOfNat 28914855153944512776645051969686), (Int.negOfNat 2992992152522590300934321628814), (Int.ofNat 3135825171966187215861819378426), (Int.ofNat 329074294006009393514193086373), (Int.negOfNat 86592753873162753890417972247), (Int.negOfNat 10739160663433042590185083258), (Int.ofNat 897367700069395375683824533), (Int.ofNat 138119273516005812892280028), (Int.negOfNat 4746284072761104809227696), (Int.negOfNat 1009915510843504232112884), (Int.ofNat 13512591322568012205593), (Int.ofNat 4924274337694433241485), (Int.negOfNat 10896128503504337721), (Int.negOfNat 18073955358359123583), (Int.negOfNat 145130379176869923), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-334525788400559656299356323032181/703687441776640000000000000000000), (599844781180896316174497666082437/11258999068426240000000000000000000), (-14457427576972256388322525984843/5629499534213120000000000000000000), (-1496496076261295150467160814407/5629499534213120000000000000000000), (1567912585983093607930909689213/5629499534213120000000000000000000), (329074294006009393514193086373/11258999068426240000000000000000000), (-86592753873162753890417972247/11258999068426240000000000000000000), (-5369580331716521295092541629/5629499534213120000000000000000000), (897367700069395375683824533/11258999068426240000000000000000000), (34529818379001453223070007/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial132.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial132.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial132.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial132 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4238245768927552654194080847922185), (Int.ofNat 554706894294938195694181618062916), (Int.ofNat 28877063095521981713728101908931), (Int.ofNat 17625783448708766706763979456703), (Int.negOfNat 317008249016303775412962022749), (Int.negOfNat 996867649527007643766782049013), (Int.negOfNat 72670547977539613781604283309), (Int.ofNat 14468831011980964158693266112), (Int.ofNat 1489576734640009082821999487), (Int.negOfNat 105041958097868719447301034), (Int.negOfNat 13918151475229495192913813), (Int.ofNat 462126677787519396487609), (Int.ofNat 80827763017520437619068), (Int.negOfNat 1317099709286330105616), (Int.negOfNat 329982270503219714815), (Int.ofNat 2266436816631074329), (Int.ofNat 1110936329785733212), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-847649153785510530838816169584437/2251799813685248000000000000000000), (138676723573734548923545404515729/2814749767106560000000000000000000), (28877063095521981713728101908931/11258999068426240000000000000000000), (17625783448708766706763979456703/11258999068426240000000000000000000), (-317008249016303775412962022749/11258999068426240000000000000000000), (-996867649527007643766782049013/11258999068426240000000000000000000), (-72670547977539613781604283309/11258999068426240000000000000000000), (226075484562202564979582283/175921860444160000000000000000000), (1489576734640009082821999487/11258999068426240000000000000000000), (-52520979048934359723650517/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial132.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial132.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial132.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial132 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 2911773702399826261707663930807504), (Int.ofNat 785579297165682186734201828292876), (Int.ofNat 41599374653507588230197394057923), (Int.negOfNat 26390895732885217235706137825208), (Int.negOfNat 9507951820983918480027198624135), (Int.negOfNat 289100601934875974612924250251), (Int.ofNat 190455467393622252446722396617), (Int.ofNat 14023076390166082764156489272), (Int.negOfNat 1768824770795116460296637312), (Int.negOfNat 173529633897513490337495296), (Int.ofNat 10000992515381467746607495), (Int.ofNat 1211847512644516289720929), (Int.negOfNat 38604055156439397298349), (Int.negOfNat 5722948923904876919643), (Int.ofNat 107766154940325102074), (Int.ofNat 20341344140769494533), (Int.negOfNat 160511882601493257), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-181985856399989141356728995675469/703687441776640000000000000000000), (196394824291420546683550457073219/2814749767106560000000000000000000), (41599374653507588230197394057923/11258999068426240000000000000000000), (-3298861966610652154463267228151/1407374883553280000000000000000000), (-1901590364196783696005439724827/2251799813685248000000000000000000), (-289100601934875974612924250251/11258999068426240000000000000000000), (190455467393622252446722396617/11258999068426240000000000000000000), (1752884548770760345519561159/1407374883553280000000000000000000), (-13818943521836847346067479/87960930222080000000000000000000), (-677850132412162071630841/43980465111040000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial132.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial132.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial132.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial132 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 1533268266086476452263198317132145), (Int.ofNat 348605858500627081047526340505925), (Int.negOfNat 316755560498026488821121072835449), (Int.negOfNat 79596471532031107830766625692336), (Int.ofNat 452854032284756315650936082307), (Int.ofNat 2142882925097719238707891633564), (Int.ofNat 120168071558265841478059238516), (Int.negOfNat 24796079423288819745126441780), (Int.negOfNat 1998269691334448963802133584), (Int.ofNat 172317368122884306784042704), (Int.ofNat 16776117376758719168784929), (Int.negOfNat 821666746933362887671493), (Int.negOfNat 91709051902478445061692), (Int.ofNat 2892307932931827089996), (Int.ofNat 361363152449083143088), (Int.negOfNat 7458094624165172574), (Int.negOfNat 1115857895748615109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-306653653217295290452639663426429/2251799813685248000000000000000000), (13944234340025083241901053620237/450359962737049600000000000000000), (-316755560498026488821121072835449/11258999068426240000000000000000000), (-4974779470751944239422914105771/703687441776640000000000000000000), (452854032284756315650936082307/11258999068426240000000000000000000), (535720731274429809676972908391/2814749767106560000000000000000000), (30042017889566460369514809629/2814749767106560000000000000000000), (-1239803971164440987256322089/562949953421312000000000000000000), (-124891855708403060237633349/703687441776640000000000000000000), (10769835507680269174002669/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial132.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial132.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial132.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial132 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 2659923967728732655503606969875057), (Int.negOfNat 1677263084011640170031951551765160), (Int.negOfNat 602480235325139253497405652890638), (Int.ofNat 12641984568806202530196432345516), (Int.ofNat 20786129037947945448737786890205), (Int.ofNat 1057176689046772072399377473464), (Int.negOfNat 295304358185524621143832501370), (Int.negOfNat 22054711013793163436904563745), (Int.ofNat 2491043166843418551066517586), (Int.ofNat 217959587137271252673041009), (Int.negOfNat 14350214160897434175794714), (Int.negOfNat 1368645344636698192369815), (Int.ofNat 60849348682079678003420), (Int.ofNat 6097586784688593669522), (Int.negOfNat 198844124079570030817), (Int.negOfNat 20574398888632698881), (Int.ofNat 466154144379856437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-2659923967728732655503606969875057/11258999068426240000000000000000000), (-41931577100291004250798788794129/281474976710656000000000000000000), (-301240117662569626748702826445319/5629499534213120000000000000000000), (3160496142201550632549108086379/2814749767106560000000000000000000), (4157225807589589089747557378041/2251799813685248000000000000000000), (132147086130846509049922184183/1407374883553280000000000000000000), (-29530435818552462114383250137/1125899906842624000000000000000000), (-4410942202758632687380912749/2251799813685248000000000000000000), (1245521583421709275533258793/5629499534213120000000000000000000), (217959587137271252673041009/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial132.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial132.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial132.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial132 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 7977817863727207419097174528687494), (Int.negOfNat 3249362983303346830190696526472826), (Int.negOfNat 23611460120339223077641368663323), (Int.ofNat 166984674373280220999692598242256), (Int.ofNat 10892104864007452812235880445210), (Int.negOfNat 2931949175562599281330717026639), (Int.negOfNat 242317701830470970177321570353), (Int.ofNat 30280167035079617119522302667), (Int.ofNat 2704901893070724927653569437), (Int.negOfNat 211551073351751050162180181), (Int.negOfNat 19218582793427061909493562), (Int.ofNat 1075906140423583832786283), (Int.ofNat 96195707557681834121493), (Int.negOfNat 4172193520082129059845), (Int.negOfNat 360525582548044869962), (Int.ofNat 12478801363599574679), (Int.ofNat 1120779461711497006), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-3988908931863603709548587264343747/5629499534213120000000000000000000), (-1624681491651673415095348263236413/5629499534213120000000000000000000), (-23611460120339223077641368663323/11258999068426240000000000000000000), (10436542148330013812480787390141/703687441776640000000000000000000), (1089210486400745281223588044521/1125899906842624000000000000000000), (-2931949175562599281330717026639/11258999068426240000000000000000000), (-242317701830470970177321570353/11258999068426240000000000000000000), (30280167035079617119522302667/11258999068426240000000000000000000), (2704901893070724927653569437/11258999068426240000000000000000000), (-211551073351751050162180181/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial132.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial132.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial132.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial132 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 13165726424373029732906453467992324), (Int.negOfNat 1256762563580045906309833633717351), (Int.ofNat 971030162438025833343870972470247), (Int.ofNat 118499115437373119965077458617537), (Int.negOfNat 22514001148962059020438780527676), (Int.negOfNat 2626028743179771905119314762176), (Int.ofNat 298258878053846644985183353192), (Int.ofNat 32174201970448571692109017649), (Int.negOfNat 2607845090163118418204172136), (Int.negOfNat 255342401591493024704266394), (Int.ofNat 16195567140029114447988655), (Int.ofNat 1426177680062671321211010), (Int.negOfNat 74989745895121354446119), (Int.negOfNat 5920808281918411096903), (Int.ofNat 268990612048364641901), (Int.ofNat 18662056639361657855), (Int.negOfNat 773436928145846916), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3291431606093257433226613366998081/2814749767106560000000000000000000), (-1256762563580045906309833633717351/11258999068426240000000000000000000), (971030162438025833343870972470247/11258999068426240000000000000000000), (118499115437373119965077458617537/11258999068426240000000000000000000), (-5628500287240514755109695131919/2814749767106560000000000000000000), (-41031699112183936017489293159/175921860444160000000000000000000), (37282359756730830623147919149/1407374883553280000000000000000000), (32174201970448571692109017649/11258999068426240000000000000000000), (-325980636270389802275521517/1407374883553280000000000000000000), (-127671200795746512352133197/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial132.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial132.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial132.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial132.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial132 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial132 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial132 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 15876960196426713616342939666165925), (Int.ofNat 357680361294302737500556466732759), (Int.ofNat 1051313894011230544602696069803262), (Int.negOfNat 106776696151663330382448125082903), (Int.negOfNat 23171951905750819348041155138429), (Int.ofNat 2556370479636504519492299044275), (Int.ofNat 301151950186388395455721350491), (Int.negOfNat 31940880529442324338475171649), (Int.negOfNat 2615328078354571521753317136), (Int.ofNat 254865368125430394362116394), (Int.ofNat 16207892296477730560116655), (Int.negOfNat 1425532230402765810091010), (Int.negOfNat 75003983755266328956119), (Int.ofNat 5918435305227582011903), (Int.ofNat 268990612048364641901), (Int.negOfNat 18662056639361657855), (Int.negOfNat 773436928145846916), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-635078407857068544653717586646637/450359962737049600000000000000000), (357680361294302737500556466732759/11258999068426240000000000000000000), (525656947005615272301348034901631/5629499534213120000000000000000000), (-106776696151663330382448125082903/11258999068426240000000000000000000), (-23171951905750819348041155138429/11258999068426240000000000000000000), (102254819185460180779691961771/450359962737049600000000000000000), (301151950186388395455721350491/11258999068426240000000000000000000), (-31940880529442324338475171649/11258999068426240000000000000000000), (-163458004897160720109582321/703687441776640000000000000000000), (127432684062715197181058197/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial132.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial132.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial132.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 12084845160560487069146599593156957), (Int.ofNat 2786108959626862787287270251296778), (Int.ofNat 106478988673978924923194281753943), (Int.negOfNat 162734399357840955914985551001051), (Int.ofNat 9766372379397877155348192713577), (Int.ofNat 2912409563168856778362400029808), (Int.negOfNat 237266789820963889811203105353), (Int.negOfNat 30220442677269532816628374667), (Int.ofNat 2691769307957788264498011437), (Int.ofNat 211431791638147843402147181), (Int.negOfNat 19196927134871880912826562), (Int.negOfNat 1075744778008607455006283), (Int.ofNat 96171977790773543271493), (Int.ofNat 4172193520082129059845), (Int.negOfNat 360525582548044869962), (Int.negOfNat 12478801363599574679), (Int.ofNat 1120779461711497006), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-12084845160560487069146599593156957/11258999068426240000000000000000000), (1393054479813431393643635125648389/5629499534213120000000000000000000), (106478988673978924923194281753943/11258999068426240000000000000000000), (-162734399357840955914985551001051/11258999068426240000000000000000000), (9766372379397877155348192713577/11258999068426240000000000000000000), (182025597698053548647650001863/703687441776640000000000000000000), (-237266789820963889811203105353/11258999068426240000000000000000000), (-30220442677269532816628374667/11258999068426240000000000000000000), (2691769307957788264498011437/11258999068426240000000000000000000), (211431791638147843402147181/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial132.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial132.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial132.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7157404801490889444542739023314274), (Int.ofNat 1748770468294720589667674110700023), (Int.negOfNat 474240362345404294032657064047040), (Int.negOfNat 17361400609129486787764246518647), (Int.ofNat 19769883212143452018862302972294), (Int.negOfNat 1017035522159131166261493230182), (Int.negOfNat 290894643773384438979564618270), (Int.ofNat 21908145733466743403998442745), (Int.ofNat 2479677142981034870337493586), (Int.negOfNat 217653953762615482485573009), (Int.negOfNat 14331509722514597669626714), (Int.ofNat 1368230073715803102494815), (Int.ofNat 60827991891862216238420), (Int.negOfNat 6097586784688593669522), (Int.negOfNat 198844124079570030817), (Int.ofNat 20574398888632698881), (Int.ofNat 466154144379856437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-3578702400745444722271369511657137/5629499534213120000000000000000000), (1748770468294720589667674110700023/11258999068426240000000000000000000), (-1482001132329388418852053325147/35184372088832000000000000000000), (-17361400609129486787764246518647/11258999068426240000000000000000000), (9884941606071726009431151486147/5629499534213120000000000000000000), (-508517761079565583130746615091/5629499534213120000000000000000000), (-29089464377338443897956461827/1125899906842624000000000000000000), (4381629146693348680799688549/2251799813685248000000000000000000), (1239838571490517435168746793/5629499534213120000000000000000000), (-217653953762615482485573009/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial132.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial132.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial132.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 5427244857189519266798855750377369), (Int.ofNat 150689612030182364285176562080572), (Int.negOfNat 237069707767554206402022554714408), (Int.ofNat 68957755992202544362230171955632), (Int.ofNat 50298163642311544293160802859), (Int.negOfNat 2066475928770734774655892862634), (Int.ofNat 121513822035702074505206807815), (Int.ofNat 24526948329938577360194914780), (Int.negOfNat 2001463429818366360105370584), (Int.negOfNat 171760607234349768984219704), (Int.ofNat 16781267372283539941432929), (Int.ofNat 820912140345679238641493), (Int.negOfNat 91713797855860103231692), (Int.negOfNat 2892307932931827089996), (Int.ofNat 361363152449083143088), (Int.ofNat 7458094624165172574), (Int.negOfNat 1115857895748615109), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-5427244857189519266798855750377369/11258999068426240000000000000000000), (37672403007545591071294140520143/2814749767106560000000000000000000), (-29633713470944275800252819339301/1407374883553280000000000000000000), (4309859749512659022639385747227/703687441776640000000000000000000), (50298163642311544293160802859/11258999068426240000000000000000000), (-1033237964385367387327946431317/5629499534213120000000000000000000), (24302764407140414901041361563/2251799813685248000000000000000000), (1226347416496928868009745739/562949953421312000000000000000000), (-250182928727295795013171323/1407374883553280000000000000000000), (-21470075904293721123027463/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial132.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial132.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial132.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 5577470385428651739891095669318909), (Int.negOfNat 101838386768403563249321582630082), (Int.ofNat 54043157194654045292017561740747), (Int.ofNat 15649936506576938450486713417138), (Int.negOfNat 9142344670253027664893466970950), (Int.ofNat 358760087633688746565859507539), (Int.ofNat 188055787633292963218347421378), (Int.negOfNat 14262242468360160500956428272), (Int.negOfNat 1762082088153550362818750312), (Int.ofNat 174021499687947088727678296), (Int.ofNat 9989680408770960265369495), (Int.negOfNat 1212511946117948433520929), (Int.negOfNat 38589817296294422788349), (Int.ofNat 5725321900595706004643), (Int.ofNat 107766154940325102074), (Int.negOfNat 20341344140769494533), (Int.negOfNat 160511882601493257), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-5577470385428651739891095669318909/11258999068426240000000000000000000), (-50919193384201781624660791315041/5629499534213120000000000000000000), (54043157194654045292017561740747/11258999068426240000000000000000000), (7824968253288469225243356708569/5629499534213120000000000000000000), (-182846893405060553297869339419/225179981368524800000000000000000), (358760087633688746565859507539/11258999068426240000000000000000000), (94027893816646481609173710689/5629499534213120000000000000000000), (-891390154272510031309776767/703687441776640000000000000000000), (-220260261019193795352343789/1407374883553280000000000000000000), (21752687460993386090959787/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial132.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial132.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial132.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 5564716584543143666671340280743763), (Int.ofNat 66629911012418313511036254446346), (Int.negOfNat 9500020685314395083457600655840), (Int.negOfNat 23158860899655615446933651072435), (Int.ofNat 543603168269180412658051670241), (Int.ofNat 1021543940776064000048875456143), (Int.negOfNat 77379802432885666316267957309), (Int.negOfNat 14543271560815018001937350112), (Int.ofNat 1502383155385853653417336487), (Int.ofNat 105190102205195346121112034), (Int.negOfNat 13939483052259729962262813), (Int.negOfNat 462326007829549039627609), (Int.ofNat 80853865761119557554068), (Int.ofNat 1317099709286330105616), (Int.negOfNat 329982270503219714815), (Int.negOfNat 2266436816631074329), (Int.ofNat 1110936329785733212), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-5564716584543143666671340280743763/11258999068426240000000000000000000), (33314955506209156755518127223173/5629499534213120000000000000000000), (-59375129283214969271610004099/70368744177664000000000000000000), (-4631772179931123089386730214487/2251799813685248000000000000000000), (543603168269180412658051670241/11258999068426240000000000000000000), (1021543940776064000048875456143/11258999068426240000000000000000000), (-77379802432885666316267957309/11258999068426240000000000000000000), (-454477236275469312560542191/351843720888320000000000000000000), (1502383155385853653417336487/11258999068426240000000000000000000), (52595051102597673060556017/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial132.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial132.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial132.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 5619730938678102525046339659480028), (Int.negOfNat 169823753740310631637601745926611), (Int.negOfNat 79018489388578512201741043276618), (Int.ofNat 4560102487200841304390868247280), (Int.ofNat 3954449384481339477866733850826), (Int.negOfNat 361301546224445058650246249118), (Int.negOfNat 90883469073140846012517027247), (Int.ofNat 10870049544109158798152008258), (Int.ofNat 908933308830394310810623533), (Int.negOfNat 138398199485312159131683028), (Int.negOfNat 4765510777224799102500696), (Int.ofNat 1010295187114036885712884), (Int.ofNat 13533948112785473970593), (Int.negOfNat 4924274337694433241485), (Int.negOfNat 10896128503504337721), (Int.ofNat 18073955358359123583), (Int.negOfNat 145130379176869923), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-1404932734669525631261584914870007/2814749767106560000000000000000000), (-169823753740310631637601745926611/11258999068426240000000000000000000), (-39509244694289256100870521638309/5629499534213120000000000000000000), (57001281090010516304885853091/140737488355328000000000000000000), (1977224692240669738933366925413/5629499534213120000000000000000000), (-180650773112222529325123124559/5629499534213120000000000000000000), (-90883469073140846012517027247/11258999068426240000000000000000000), (5435024772054579399076004129/5629499534213120000000000000000000), (908933308830394310810623533/11258999068426240000000000000000000), (-34599549871328039782920757/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial132.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial132.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial132.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 6191528187110130939838087553975414), (Int.negOfNat 345519136666890215439316059985587), (Int.ofNat 802186874218587990558076312423), (Int.ofNat 14143869930980617399427604651823), (Int.negOfNat 1629402662281183303596253128384), (Int.negOfNat 419395024507427907606620939806), (Int.ofNat 68770859577382610682477478213), (Int.ofNat 6067541402865423018511092485), (Int.negOfNat 1190740300827280249924994085), (Int.negOfNat 39504826483755233202368581), (Int.ofNat 11109593591681793753591857), (Int.ofNat 101483401243576223057345), (Int.negOfNat 65650434584110653106618), (Int.ofNat 218193144826273153859), (Int.ofNat 270575059257810042454), (Int.negOfNat 2938277401730941676), (Int.negOfNat 1004134009896730255), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-3095764093555065469919043776987707/5629499534213120000000000000000000), (-345519136666890215439316059985587/11258999068426240000000000000000000), (802186874218587990558076312423/11258999068426240000000000000000000), (14143869930980617399427604651823/11258999068426240000000000000000000), (-25459416598143489118691455131/175921860444160000000000000000000), (-209697512253713953803310469903/5629499534213120000000000000000000), (68770859577382610682477478213/11258999068426240000000000000000000), (1213508280573084603702218497/2251799813685248000000000000000000), (-238148060165456049984998817/2251799813685248000000000000000000), (-39504826483755233202368581/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial132.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial132.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial132.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 6800833591309966175715161926092379), (Int.negOfNat 243608058311472408441778917469969), (Int.ofNat 31401225310431205439130287673232), (Int.negOfNat 3444383582574639487987454766191), (Int.negOfNat 1345477450404982173623850257319), (Int.ofNat 388703040086949652330208422047), (Int.ofNat 28995659508303747923917302513), (Int.negOfNat 9001697470142390793168219329), (Int.negOfNat 231754329848021912348737845), (Int.ofNat 107354366541839523517847649), (Int.ofNat 208721830788329278011929), (Int.negOfNat 777367230954578375832017), (Int.ofNat 8612521802411564770854), (Int.ofNat 3797640135516116037381), (Int.negOfNat 71702769931154705138), (Int.negOfNat 13787658162555037804), (Int.ofNat 345610843053857445), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-6800833591309966175715161926092379/11258999068426240000000000000000000), (-243608058311472408441778917469969/11258999068426240000000000000000000), (1962576581901950339945642979577/703687441776640000000000000000000), (-3444383582574639487987454766191/11258999068426240000000000000000000), (-1345477450404982173623850257319/11258999068426240000000000000000000), (388703040086949652330208422047/11258999068426240000000000000000000), (28995659508303747923917302513/11258999068426240000000000000000000), (-9001697470142390793168219329/11258999068426240000000000000000000), (-46350865969604382469747569/2251799813685248000000000000000000), (107354366541839523517847649/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial132.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial132.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial132.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 7198391189536103761605331450749680), (Int.negOfNat 169757646131249733555875709927497), (Int.ofNat 10510576002687826288946396831253), (Int.ofNat 1072482363329090980248549011842), (Int.ofNat 1906448125016060637969064206764), (Int.ofNat 73820107860305932272901003588), (Int.negOfNat 60376284653263542669877868099), (Int.negOfNat 570568369797000007797453630), (Int.ofNat 913311066566485760945220925), (Int.negOfNat 9116122221717611410529808), (Int.negOfNat 8128978951149742637411184), (Int.ofNat 180183510453114021260012), (Int.ofNat 47245290825852594589817), (Int.negOfNat 1416228016378646957323), (Int.negOfNat 193416845856840934825), (Int.ofNat 6894174221177468177), (Int.ofNat 797091458069233537), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-89979889869201297020066643134371/140737488355328000000000000000000), (-169757646131249733555875709927497/11258999068426240000000000000000000), (10510576002687826288946396831253/11258999068426240000000000000000000), (536241181664545490124274505921/5629499534213120000000000000000000), (476612031254015159492266051691/2814749767106560000000000000000000), (18455026965076483068225250897/2814749767106560000000000000000000), (-60376284653263542669877868099/11258999068426240000000000000000000), (-57056836979700000779745363/1125899906842624000000000000000000), (36532442662659430437808837/450359962737049600000000000000000), (-569757638857350713158113/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial132.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial132.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial132.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 7458134656294074776068116818426603), (Int.negOfNat 58905764878313653328850485107508), (Int.ofNat 55241079251336531629334247770229), (Int.ofNat 10772320042929380651020348887736), (Int.negOfNat 247885031758695293968593535013), (Int.negOfNat 363912710789218835735800414607), (Int.ofNat 5506305758127041756084932807), (Int.ofNat 6848028740863380663737898844), (Int.negOfNat 190336713747303340416265217), (Int.negOfNat 74643510303742860424914214), (Int.ofNat 2853320801411486847369243), (Int.ofNat 517325633901803155960217), (Int.negOfNat 23753504909512119295652), (Int.negOfNat 2456478855361427422112), (Int.ofNat 128510425899931601889), (Int.ofNat 8305040271439536089), (Int.negOfNat 442570031017096608), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-7458134656294074776068116818426603/11258999068426240000000000000000000), (-14726441219578413332212621276877/2814749767106560000000000000000000), (55241079251336531629334247770229/11258999068426240000000000000000000), (1346540005366172581377543610967/1407374883553280000000000000000000), (-247885031758695293968593535013/11258999068426240000000000000000000), (-363912710789218835735800414607/11258999068426240000000000000000000), (5506305758127041756084932807/11258999068426240000000000000000000), (1712007185215845165934474711/2814749767106560000000000000000000), (-190336713747303340416265217/11258999068426240000000000000000000), (-37321755151871430212457107/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial132.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial132.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial132.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 7283268802200237554753836633339216), (Int.ofNat 258059036833049882842744980874850), (Int.ofNat 90096583800396021051220090367113), (Int.negOfNat 1731338710607922111373531171952), (Int.negOfNat 2096884422397490821228613263183), (Int.ofNat 76884857507360824339188141438), (Int.ofNat 45306691083805156921317925346), (Int.negOfNat 2280453287248703717306533660), (Int.negOfNat 597094873335434294776057152), (Int.ofNat 36395041966878765584637548), (Int.ofNat 4913262142533224067045911), (Int.negOfNat 341606594145603243295599), (Int.negOfNat 26974838678086381877877), (Int.ofNat 2088146279867043757733), (Int.ofNat 104301199217432550890), (Int.negOfNat 8997510804825109227), (Int.negOfNat 491449196290870357), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-455204300137514847172114789583701/703687441776640000000000000000000), (5161180736660997656854899617497/225179981368524800000000000000000), (90096583800396021051220090367113/11258999068426240000000000000000000), (-108208669412995131960845698247/703687441776640000000000000000000), (-2096884422397490821228613263183/11258999068426240000000000000000000), (38442428753680412169594070719/5629499534213120000000000000000000), (22653345541902578460658962673/5629499534213120000000000000000000), (-114022664362435185865326683/562949953421312000000000000000000), (-9329607395866160855875893/175921860444160000000000000000000), (9098760491719691396159387/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial132.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial132.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial132.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 6449227190552230675617193745194233), (Int.ofNat 543890231273976760539152152165718), (Int.ofNat 44018492285414574616584114576091), (Int.negOfNat 10274665295465541383185562462750), (Int.ofNat 278869318579833996481068748935), (Int.ofNat 262432578974169233325043207786), (Int.negOfNat 18658957016567204189438786096), (Int.negOfNat 4104133127410192311352104488), (Int.ofNat 376022450788588677013493416), (Int.ofNat 39519034433824345813928860), (Int.negOfNat 4206294806659780274454935), (Int.negOfNat 246180299655814865213245), (Int.ofNat 30020317643975941213860), (Int.ofNat 1047681679064466465300), (Int.negOfNat 147432933996379392216), (Int.negOfNat 2901099670657044094), (Int.ofNat 437648465054214711), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-6449227190552230675617193745194233/11258999068426240000000000000000000), (271945115636988380269576076082859/5629499534213120000000000000000000), (44018492285414574616584114576091/11258999068426240000000000000000000), (-41098661181862165532742249851/45035996273704960000000000000000), (55773863715966799296213749787/2251799813685248000000000000000000), (131216289487084616662521603893/5629499534213120000000000000000000), (-1166184813535450261839924131/703687441776640000000000000000000), (-513016640926274038919013061/1407374883553280000000000000000000), (47002806348573584626686677/1407374883553280000000000000000000), (1975951721691217290696443/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial132.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial132.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial132.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 5256318018784639184249223830495298), (Int.ofNat 621618035628475152748171113384312), (Int.ofNat 3624529434407711395346277044696), (Int.negOfNat 2015302057446609094665021642422), (Int.ofNat 1152085502974388121765373125332), (Int.negOfNat 96061019648997053067016537823), (Int.negOfNat 23330697240347587670003777354), (Int.ofNat 3073693052452973835320559043), (Int.ofNat 256820373496780578483923042), (Int.negOfNat 43678222756590113215984451), (Int.negOfNat 1705266006780394230267538), (Int.ofNat 374496260203654289875657), (Int.ofNat 7009244712712282613180), (Int.negOfNat 2161256479798640476582), (Int.negOfNat 17609708643232591353), (Int.ofNat 9059951265975074479), (Int.ofNat 185806934512507177), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-2628159009392319592124611915247649/5629499534213120000000000000000000), (77702254453559394093521389173039/1407374883553280000000000000000000), (453066179300963924418284630587/1407374883553280000000000000000000), (-1007651028723304547332510821211/5629499534213120000000000000000000), (288021375743597030441343281333/2814749767106560000000000000000000), (-96061019648997053067016537823/11258999068426240000000000000000000), (-11665348620173793835001888677/5629499534213120000000000000000000), (3073693052452973835320559043/11258999068426240000000000000000000), (128410186748390289241961521/5629499534213120000000000000000000), (-43678222756590113215984451/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial132.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial132.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial132.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 4000404148167455505251089478005004), (Int.ofNat 638169798126224550822614440730013), (Int.ofNat 8214026015751901498315330582525), (Int.ofNat 1562492389333602782768533834362), (Int.negOfNat 243199512653646014144885165209), (Int.negOfNat 93508543707603004907641880212), (Int.ofNat 18869404414886542515619819155), (Int.ofNat 1180719102345090354002723599), (Int.negOfNat 371612492946642876318078971), (Int.negOfNat 6130681252097134777123345), (Int.ofNat 3972746716068197085211990), (Int.negOfNat 3601742635329336161533), (Int.negOfNat 27358704997958734319923), (Int.ofNat 249586379267644928443), (Int.ofNat 131669948120722706614), (Int.negOfNat 2266268982520659801), (Int.negOfNat 432726899091332814), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1000101037041863876312772369501251/2814749767106560000000000000000000), (638169798126224550822614440730013/11258999068426240000000000000000000), (328561040630076059932613223301/450359962737049600000000000000000), (781246194666801391384266917181/5629499534213120000000000000000000), (-243199512653646014144885165209/11258999068426240000000000000000000), (-23377135926900751226910470053/2814749767106560000000000000000000), (3773880882977308503123963831/2251799813685248000000000000000000), (1180719102345090354002723599/11258999068426240000000000000000000), (-371612492946642876318078971/11258999068426240000000000000000000), (-1226136250419426955424669/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial132.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial132.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial132.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2684327519337586513221280360069698), (Int.ofNat 678289629805914222621453954483810), (Int.ofNat 8943331477683440075422640608122), (Int.negOfNat 1084072243726954764244492446637), (Int.negOfNat 106450864424860094928462202514), (Int.ofNat 82627465445483775688986624562), (Int.ofNat 1484680977717149377142103431), (Int.negOfNat 2466436635685489698763096907), (Int.ofNat 44505691996654571716179104), (Int.ofNat 34518762718492155359076418), (Int.negOfNat 1022409521494607451903553), (Int.negOfNat 291694154106836564736518), (Int.ofNat 9827764645393641543993), (Int.ofNat 1668361136498807505337), (Int.negOfNat 57953008217669008051), (Int.negOfNat 7192558567214442705), (Int.ofNat 118194805278228704), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1342163759668793256610640180034849/5629499534213120000000000000000000), (67828962980591422262145395448381/1125899906842624000000000000000000), (4471665738841720037711320304061/5629499534213120000000000000000000), (-1084072243726954764244492446637/11258999068426240000000000000000000), (-53225432212430047464231101257/5629499534213120000000000000000000), (41313732722741887844493312281/5629499534213120000000000000000000), (1484680977717149377142103431/11258999068426240000000000000000000), (-2466436635685489698763096907/11258999068426240000000000000000000), (1390802874895455366130597/351843720888320000000000000000000), (17259381359246077679538209/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial132.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial132.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial132.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 1299899855517251994148157005726870), (Int.ofNat 703554860343041733633568184536532), (Int.ofNat 5412880620595703988694468217087), (Int.ofNat 464606393246639823568317104785), (Int.ofNat 283045585416111144377095893191), (Int.negOfNat 32610284138197179410449913647), (Int.negOfNat 11724105671796943993164500991), (Int.ofNat 1091922675260945810933440533), (Int.ofNat 227506505823668134944734096), (Int.negOfNat 19181783963020984789198782), (Int.negOfNat 2453439128245765992613607), (Int.ofNat 191893050666060709887402), (Int.ofNat 17069796615708484165847), (Int.negOfNat 1235537307823020679383), (Int.negOfNat 83434443559811383109), (Int.ofNat 5828389558461165375), (Int.ofNat 225684347263836096), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-129989985551725199414815700572687/1125899906842624000000000000000000), (175888715085760433408392046134133/2814749767106560000000000000000000), (5412880620595703988694468217087/11258999068426240000000000000000000), (92921278649327964713663420957/2251799813685248000000000000000000), (283045585416111144377095893191/11258999068426240000000000000000000), (-32610284138197179410449913647/11258999068426240000000000000000000), (-11724105671796943993164500991/11258999068426240000000000000000000), (1091922675260945810933440533/11258999068426240000000000000000000), (14219156613979258434045881/703687441776640000000000000000000), (-9590891981510492394599391/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial132.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial132.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial132.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 135499222306984617235599223412915), (Int.ofNat 735647165984272800636397166176935), (Int.ofNat 10602149582537301664702211043565), (Int.ofNat 436680987554535086283820032453), (Int.negOfNat 286524712136387491111616274870), (Int.negOfNat 31178892205286655872623426478), (Int.ofNat 11437034982911552843256409205), (Int.ofNat 898605860519303995632785079), (Int.negOfNat 232470821562596392643550709), (Int.negOfNat 13371686875796899482748945), (Int.ofNat 2748804581568827526600210), (Int.ofNat 119845694811342433836587), (Int.negOfNat 20701532530251825491477), (Int.negOfNat 723103575800555994277), (Int.ofNat 106753688899375365346), (Int.ofNat 3714760069487401559), (Int.negOfNat 318675269155216226), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(27099844461396923447119844682583/2251799813685248000000000000000000), (147129433196854560127279433235387/2251799813685248000000000000000000), (2120429916507460332940442208713/2251799813685248000000000000000000), (436680987554535086283820032453/11258999068426240000000000000000000), (-28652471213638749111161627487/1125899906842624000000000000000000), (-15589446102643327936311713239/5629499534213120000000000000000000), (2287406996582310568651281841/2251799813685248000000000000000000), (898605860519303995632785079/11258999068426240000000000000000000), (-232470821562596392643550709/11258999068426240000000000000000000), (-2674337375159379896549789/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial132.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial132.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial132.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1647897084832213450282636490101013), (Int.ofNat 773977350943539375092219624824065), (Int.ofNat 6755446117857664454201607291201), (Int.negOfNat 1213177817895812689876282194890), (Int.ofNat 64469190193726477388530547589), (Int.ofNat 73932420033147863101463170096), (Int.negOfNat 1293633655840674800958337526), (Int.negOfNat 2029291151223238692182537317), (Int.ofNat 7804582522882076226586558), (Int.ofNat 30495174633329589121041229), (Int.ofNat 62536637817005392614538), (Int.negOfNat 281764152313036792408303), (Int.negOfNat 1397237065667444220340), (Int.ofNat 1735181861038489608498), (Int.ofNat 10592801710927495913), (Int.negOfNat 7740731807732206401), (Int.ofNat 81598436502154383), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(1647897084832213450282636490101013/11258999068426240000000000000000000), (154795470188707875018443924964813/2251799813685248000000000000000000), (6755446117857664454201607291201/11258999068426240000000000000000000), (-121317781789581268987628219489/1125899906842624000000000000000000), (64469190193726477388530547589/11258999068426240000000000000000000), (4620776252071741443841448131/703687441776640000000000000000000), (-646816827920337400479168763/5629499534213120000000000000000000), (-2029291151223238692182537317/11258999068426240000000000000000000), (3902291261441038113293279/5629499534213120000000000000000000), (30495174633329589121041229/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial132.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial132.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial132.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3216240058231126854107461623614825), (Int.ofNat 793336565886543220329712709923291), (Int.ofNat 5411551718964273678499379129839), (Int.ofNat 1083820086866756595421693459894), (Int.ofNat 279059158081426197561717929095), (Int.negOfNat 54485150314511316485041855224), (Int.negOfNat 12004228101445479183553747783), (Int.ofNat 1207084569692642379285395592), (Int.ofNat 252525002800142153187480224), (Int.negOfNat 14474204613309115470319060), (Int.negOfNat 3048254914669455151827225), (Int.ofNat 105078075270509992631755), (Int.ofNat 23355385405403387696100), (Int.negOfNat 499029994295311045500), (Int.negOfNat 121393436296333512824), (Int.ofNat 1305946669947000546), (Int.ofNat 313753703192334329), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(128649602329245074164298464944593/450359962737049600000000000000000), (793336565886543220329712709923291/11258999068426240000000000000000000), (5411551718964273678499379129839/11258999068426240000000000000000000), (541910043433378297710846729947/5629499534213120000000000000000000), (55811831616285239512343585819/2251799813685248000000000000000000), (-6810643789313914560630231903/1407374883553280000000000000000000), (-12004228101445479183553747783/11258999068426240000000000000000000), (150885571211580297410674449/1407374883553280000000000000000000), (7891406337504442287108757/351843720888320000000000000000000), (-723710230665455773515953/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial132.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial132.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial132.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4835392034578348824252014051299612), (Int.ofNat 831007004575301432794131879533152), (Int.ofNat 12538352479427095127063355370673), (Int.ofNat 226905860580504479249116090162), (Int.negOfNat 457464487694501149782328884170), (Int.negOfNat 32576424106200460912042903880), (Int.ofNat 15948055217913505034241919914), (Int.ofNat 1280490801676205458150346020), (Int.negOfNat 274241103225256568595354768), (Int.negOfNat 23594773824465590896759492), (Int.ofNat 2703479814193703748369649), (Int.ofNat 246609179975461383800681), (Int.negOfNat 16883952486680112063803), (Int.negOfNat 1635310396258476404427), (Int.ofNat 71667226986641976590), (Int.ofNat 7507677059869002053), (Int.negOfNat 387240698280517563), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1208848008644587206063003512824903/2814749767106560000000000000000000), (25968968892978169774816621235411/351843720888320000000000000000000), (12538352479427095127063355370673/11258999068426240000000000000000000), (113452930290252239624558045081/5629499534213120000000000000000000), (-45746448769450114978232888417/1125899906842624000000000000000000), (-814410602655011522801072597/281474976710656000000000000000000), (7974027608956752517120959957/5629499534213120000000000000000000), (64024540083810272907517301/562949953421312000000000000000000), (-17140068951578535537209673/703687441776640000000000000000000), (-5898693456116397724189873/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial132.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial132.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial132.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6542118307540103330722195315561789), (Int.ofNat 869954936080569953969253714658580), (Int.ofNat 4439103336131477246827172407572), (Int.negOfNat 2035761032742844303185424260296), (Int.ofNat 174013823861604107715337202978), (Int.ofNat 122870813305064413265459626202), (Int.negOfNat 1251733133082721006329127167), (Int.negOfNat 3172893107045854206491036436), (Int.negOfNat 68887014269096144526639063), (Int.ofNat 42846589509872490366221706), (Int.ofNat 1632663434739980577661077), (Int.negOfNat 343850390849436251266903), (Int.negOfNat 16480757418304169261548), (Int.ofNat 1803046087120882760688), (Int.ofNat 99507279302035764311), (Int.negOfNat 6497604477481098791), (Int.negOfNat 308832137229452432), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6542118307540103330722195315561789/11258999068426240000000000000000000), (43497746804028497698462685732929/562949953421312000000000000000000), (1109775834032869311706793101893/2814749767106560000000000000000000), (-254470129092855537898178032537/1407374883553280000000000000000000), (87006911930802053857668601489/5629499534213120000000000000000000), (61435406652532206632729813101/5629499534213120000000000000000000), (-1251733133082721006329127167/11258999068426240000000000000000000), (-793223276761463551622759109/2814749767106560000000000000000000), (-68887014269096144526639063/11258999068426240000000000000000000), (21423294754936245183110853/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial132.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial132.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial132.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 8289733569421445425505173232270122), (Int.ofNat 877050900457777278665074054888331), (Int.ofNat 3880255581151090609321619649070), (Int.ofNat 2410267355961938755345602627242), (Int.ofNat 540882583739884108014604532838), (Int.negOfNat 101155603590318249793667561609), (Int.negOfNat 24714742969494225063143451221), (Int.ofNat 1457519293964993750181083210), (Int.ofNat 498530694246848174550012915), (Int.negOfNat 4783896242566113641231248), (Int.negOfNat 5366651613614342821514096), (Int.negOfNat 72908237668797318967188), (Int.ofNat 35053005885584367095983), (Int.ofNat 901337553023270445197), (Int.negOfNat 154870432829520911295), (Int.negOfNat 5240288277458631103), (Int.ofNat 692882960058880743), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(4144866784710722712752586616135061/5629499534213120000000000000000000), (877050900457777278665074054888331/11258999068426240000000000000000000), (388025558115109060932161964907/1125899906842624000000000000000000), (1205133677980969377672801313621/5629499534213120000000000000000000), (270441291869942054007302266419/5629499534213120000000000000000000), (-101155603590318249793667561609/11258999068426240000000000000000000), (-24714742969494225063143451221/11258999068426240000000000000000000), (145751929396499375018108321/1125899906842624000000000000000000), (99706138849369634910002583/2251799813685248000000000000000000), (-298993515160382102576953/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial132.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial132.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial132.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 10082780170489513010179278345964821), (Int.ofNat 927090729062211149886695089298354), (Int.ofNat 19088406112007202343620830529106), (Int.ofNat 339183360807362738634122879756), (Int.negOfNat 1076991066127767130812149329929), (Int.negOfNat 103354664389477435365680317442), (Int.ofNat 31344764218542816993777688907), (Int.ofNat 4122412603690250036023482751), (Int.negOfNat 367202667321963692106676235), (Int.negOfNat 66891179981999217543519991), (Int.ofNat 1661810853714677533260751), (Int.ofNat 565920787924895483368263), (Int.ofNat 74127667925624809906), (Int.negOfNat 3023683137888937881659), (Int.negOfNat 38217055588405084062), (Int.ofNat 11702318695843114796), (Int.ofNat 202029817340449475), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(10082780170489513010179278345964821/11258999068426240000000000000000000), (463545364531105574943347544649177/5629499534213120000000000000000000), (9544203056003601171810415264553/5629499534213120000000000000000000), (84795840201840684658530719939/2814749767106560000000000000000000), (-1076991066127767130812149329929/11258999068426240000000000000000000), (-51677332194738717682840158721/5629499534213120000000000000000000), (31344764218542816993777688907/11258999068426240000000000000000000), (4122412603690250036023482751/11258999068426240000000000000000000), (-73440533464392738421335247/2251799813685248000000000000000000), (-66891179981999217543519991/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial132.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial132.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial132.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 11997897831164879561357608480273070), (Int.ofNat 972132091575318067299421752007627), (Int.negOfNat 3631311521780747821394375976709), (Int.negOfNat 6056306861022519468987753986990), (Int.ofNat 288586367722999690799978481382), (Int.ofNat 348847647019626669417215196155), (Int.ofNat 16272023991914452434510505107), (Int.negOfNat 7129436836371930109328168235), (Int.negOfNat 646717986561257830492424635), (Int.ofNat 57698546053717079887653179), (Int.ofNat 7725409657909429891132063), (Int.negOfNat 233953388741795707451375), (Int.negOfNat 51241434884181823802542), (Int.ofNat 392726408205889114019), (Int.ofNat 225753201589448154746), (Int.ofNat 953991081654545324), (Int.negOfNat 893363423935868265), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(1199789783116487956135760848027307/1125899906842624000000000000000000), (972132091575318067299421752007627/11258999068426240000000000000000000), (-3631311521780747821394375976709/11258999068426240000000000000000000), (-605630686102251946898775398699/1125899906842624000000000000000000), (144293183861499845399989240691/5629499534213120000000000000000000), (69769529403925333883443039231/2251799813685248000000000000000000), (16272023991914452434510505107/11258999068426240000000000000000000), (-1425887367274386021865633647/2251799813685248000000000000000000), (-129343597312251566098484927/2251799813685248000000000000000000), (57698546053717079887653179/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial132.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial132.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial132.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 13894966872109449892181930717970736), (Int.ofNat 921510384099067046298157834110923), (Int.negOfNat 6834915587634937600502825658714), (Int.ofNat 8071888482869810816883014153174), (Int.ofNat 2353285492620503266052284762174), (Int.negOfNat 177626726843674205653605849973), (Int.negOfNat 97473917904327986531906702233), (Int.negOfNat 4146015287041169560828212702), (Int.ofNat 1125827066871107144568577427), (Int.ofNat 88776715699707445974498932), (Int.negOfNat 6709194442631393565876624), (Int.negOfNat 762874531652205361295316), (Int.ofNat 24006215655909076721007), (Int.ofNat 4036964533738957944235), (Int.negOfNat 50115859879383644159), (Int.negOfNat 15658215515289641297), (Int.ofNat 5012734487047243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(868435429506840618261370669873171/703687441776640000000000000000000), (921510384099067046298157834110923/11258999068426240000000000000000000), (-3417457793817468800251412829357/5629499534213120000000000000000000), (4035944241434905408441507076587/5629499534213120000000000000000000), (1176642746310251633026142381087/5629499534213120000000000000000000), (-177626726843674205653605849973/11258999068426240000000000000000000), (-97473917904327986531906702233/11258999068426240000000000000000000), (-2073007643520584780414106351/5629499534213120000000000000000000), (1125827066871107144568577427/11258999068426240000000000000000000), (22194178924926861493624733/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial132.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial132.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial132.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 15800747940635398314134826114008945), (Int.ofNat 1032871213837680317507433697131844), (Int.ofNat 60015294573849341435961708080069), (Int.ofNat 4238797123490707499203049958737), (Int.negOfNat 4931396340068730138834618720171), (Int.negOfNat 1085228184505669416392357720947), (Int.negOfNat 1359182899760762443038967131), (Int.ofNat 17187703594830608659302473408), (Int.ofNat 843918149153488665649063593), (Int.negOfNat 132601880105381317747697446), (Int.negOfNat 10063848085218029766618107), (Int.ofNat 632599563845116583243271), (Int.ofNat 64646146111418037593532), (Int.negOfNat 2046105100667842726784), (Int.negOfNat 279865703678135775385), (Int.ofNat 4528626809460956391), (Int.ofNat 990322611899107428), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(3160149588127079662826965222801789/2251799813685248000000000000000000), (258217803459420079376858424282961/2814749767106560000000000000000000), (60015294573849341435961708080069/11258999068426240000000000000000000), (4238797123490707499203049958737/11258999068426240000000000000000000), (-4931396340068730138834618720171/11258999068426240000000000000000000), (-1085228184505669416392357720947/11258999068426240000000000000000000), (-1359182899760762443038967131/11258999068426240000000000000000000), (268557868669228260301601147/175921860444160000000000000000000), (843918149153488665649063593/11258999068426240000000000000000000), (-66300940052690658873848723/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial132.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial132.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial132.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 18029084703332404099936565382949424), (Int.ofNat 1087129853562456904637933854585684), (Int.negOfNat 107692662646871093895509426599403), (Int.negOfNat 68535795613903864733705211348232), (Int.negOfNat 10743496064803304953104298282705), (Int.ofNat 396143146327514425319539608651), (Int.ofNat 223394153697395342209846030863), (Int.ofNat 6577918562586968574333925208), (Int.negOfNat 2138843570572286782157614568), (Int.negOfNat 119566854951107745404667144), (Int.ofNat 12619009187705180154982545), (Int.ofNat 942906229376851578719351), (Int.negOfNat 51365004394285676748371), (Int.negOfNat 4753553685511520183717), (Int.ofNat 153033684014711902446), (Int.ofNat 17761552098937282347), (Int.negOfNat 310654996265410423), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(1126817793958275256246035336434339/703687441776640000000000000000000), (271782463390614226159483463646421/2814749767106560000000000000000000), (-107692662646871093895509426599403/11258999068426240000000000000000000), (-8566974451737983091713151418529/1407374883553280000000000000000000), (-2148699212960660990620859656541/2251799813685248000000000000000000), (396143146327514425319539608651/11258999068426240000000000000000000), (223394153697395342209846030863/11258999068426240000000000000000000), (822239820323371071791740651/1407374883553280000000000000000000), (-267355446321535847769701821/1407374883553280000000000000000000), (-14945856868888468175583393/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial132.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial132.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial132.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 19079613082472426027404870153546825), (Int.negOfNat 434724103325234048044035047873245), (Int.negOfNat 691240940509163933854790820823151), (Int.negOfNat 103460316067388129598115224115264), (Int.ofNat 5787183492317743459690126641453), (Int.ofNat 2553241120880638017518047104516), (Int.ofNat 48001559097682515618873203924), (Int.negOfNat 29499552354441401610666857940), (Int.negOfNat 1335636290495174331315544856), (Int.ofNat 210025604305150277776438776), (Int.ofNat 12752658668770995987614831), (Int.negOfNat 1031907126630717141889507), (Int.negOfNat 74598743926504228344668), (Int.ofNat 3738003848357118550404), (Int.ofNat 307606152216259021952), (Int.negOfNat 9932567410243448386), (Int.negOfNat 985401045936225531), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(763184523298897041096194806141873/450359962737049600000000000000000), (-86944820665046809608807009574649/2251799813685248000000000000000000), (-691240940509163933854790820823151/11258999068426240000000000000000000), (-1616567438552939524970550376801/175921860444160000000000000000000), (5787183492317743459690126641453/11258999068426240000000000000000000), (638310280220159504379511776129/2814749767106560000000000000000000), (12000389774420628904718300981/2814749767106560000000000000000000), (-1474977617722070080533342897/562949953421312000000000000000000), (-166954536311896791414443107/1407374883553280000000000000000000), (26253200538143784722054847/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial132.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial132.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial132.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14790889679372570041404134871936537), (Int.negOfNat 4056593721263331554691293056898040), (Int.negOfNat 978466619175250965313848146108962), (Int.ofNat 35008125070232195376137412170604), (Int.ofNat 25410726984529820798847864056315), (Int.ofNat 542614450618487569864971603056), (Int.negOfNat 349240795333421604997705300750), (Int.negOfNat 15199134240742500377407706415), (Int.ofNat 2989065480791976520044302614), (Int.ofNat 164687982838320059880548071), (Int.negOfNat 17576177124898968270376886), (Int.negOfNat 1095169140622910633231145), (Int.ofNat 75683033234536258788140), (Int.ofNat 5091953331506678982758), (Int.negOfNat 249219899540477541743), (Int.negOfNat 17823992560087247599), (Int.ofNat 616297258043773603), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(14790889679372570041404134871936537/11258999068426240000000000000000000), (-101414843031583288867282326422451/281474976710656000000000000000000), (-489233309587625482656924073054481/5629499534213120000000000000000000), (8752031267558048844034353042651/2814749767106560000000000000000000), (5082145396905964159769572811263/2251799813685248000000000000000000), (33913403163655473116560725191/703687441776640000000000000000000), (-1396963181333686419990821203/45035996273704960000000000000000), (-3039826848148500075481541283/2251799813685248000000000000000000), (1494532740395988260022151307/5629499534213120000000000000000000), (164687982838320059880548071/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial132.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial132.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial132.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 3444368781984732366380228982711254), (Int.negOfNat 6764333705704846836704785697930014), (Int.negOfNat 203295082468606404255442670123677), (Int.ofNat 201543815204673221055283318109344), (Int.ofNat 9367112899503965841338964002310), (Int.negOfNat 3418959369452758643169000398041), (Int.negOfNat 186466596170674646297410000807), (Int.ofNat 36028616774778333570660280613), (Int.ofNat 2093376102868407321194927043), (Int.negOfNat 256760989566802542565961819), (Int.negOfNat 15302392594021683348691238), (Int.ofNat 1318465178932694179385837), (Int.ofNat 79077889118464103252307), (Int.negOfNat 5110622287802489022075), (Int.negOfNat 305509986934544165998), (Int.ofNat 15099936063421152281), (Int.ofNat 980479479973343634), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1722184390992366183190114491355627/5629499534213120000000000000000000), (-3382166852852423418352392848965007/5629499534213120000000000000000000), (-203295082468606404255442670123677/11258999068426240000000000000000000), (6298244225146038157977603690917/351843720888320000000000000000000), (936711289950396584133896400231/1125899906842624000000000000000000), (-3418959369452758643169000398041/11258999068426240000000000000000000), (-186466596170674646297410000807/11258999068426240000000000000000000), (36028616774778333570660280613/11258999068426240000000000000000000), (2093376102868407321194927043/11258999068426240000000000000000000), (-256760989566802542565961819/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial132.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial132.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial132.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 9251591779469251349609546733526196), (Int.negOfNat 5150927972715104837699670496052889), (Int.ofNat 939154465257952805281021711983873), (Int.ofNat 132262559656741412414627385502463), (Int.negOfNat 24755228570092468288897999498884), (Int.negOfNat 2288291588987077689762159942664), (Int.ofNat 351290354257184378725327714168), (Int.ofNat 26159138509798486508888004591), (Int.negOfNat 3169962986302018354077533864), (Int.negOfNat 205556740586724768473608206), (Int.ofNat 19844664398966524699438105), (Int.ofNat 1162541535583230937723910), (Int.negOfNat 91321556425200525190121), (Int.negOfNat 4926794920321663641017), (Int.ofNat 322899603933158133259), (Int.ofNat 15956599861326615825), (Int.negOfNat 920298997834509484), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2312897944867312837402386683381549/2814749767106560000000000000000000), (-5150927972715104837699670496052889/11258999068426240000000000000000000), (939154465257952805281021711983873/11258999068426240000000000000000000), (132262559656741412414627385502463/11258999068426240000000000000000000), (-6188807142523117072224499874721/2814749767106560000000000000000000), (-286036448623384711220269992833/1407374883553280000000000000000000), (43911294282148047340665964271/1407374883553280000000000000000000), (26159138509798486508888004591/11258999068426240000000000000000000), (-396245373287752294259691733/1407374883553280000000000000000000), (-102778370293362384236804103/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial132.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial132.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial132.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial132.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial132.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial132.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial132.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial132.reflect := by
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

end Bin132
end
end ErdosOverlap.OuterNumerics
