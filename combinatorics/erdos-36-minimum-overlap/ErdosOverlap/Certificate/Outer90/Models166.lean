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

/-! # Exact integer weighted outer models for source bin 166

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin166

def weightDenominator : ℤ := (Int.ofNat 100000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4265504228564768000)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 17616130022395360000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 12155227073988518000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 4870505646499513600)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 8658773042769886000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 7028810713965743000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 4952672758106770000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 3524883993098084000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 1913576931422615000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 1101600816057216600)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial166.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial166.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 90235946753208130000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 34885980174775294000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 11459961697255325000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 9333698985520635000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 4707916517819761000)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 1752762457646325000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 10326173523018847)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 363764648548340900)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 342043396310693240)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial166.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial166.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 90235946753208130000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 34885980174775294000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 11459961697255325000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 9333698985520635000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 4707916517819761000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1752762457646325000)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 10326173523018847)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 363764648548340900)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 342043396310693240)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial166.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial166.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial166.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 40349521643969720751659651340635389), (Int.ofNat 38772359645541712844965864999712268), (Int.ofNat 3930225342019844671704596934841702), (Int.negOfNat 919037522808640447486308467474260), (Int.negOfNat 122010012287801344068659012886053), (Int.ofNat 15730470621597722038851061697013), (Int.ofNat 2083673486176011293684297255533), (Int.negOfNat 179881515717231327652679264844), (Int.negOfNat 22024370049680361379257222557), (Int.ofNat 1428039505703621700298796070), (Int.ofNat 157246540200154531960089675), (Int.negOfNat 8217222928956324152621396), (Int.negOfNat 807276072960220652390182), (Int.ofNat 35517804351964845983618), (Int.ofNat 3123224929222937545821), (Int.negOfNat 117318908348680116906), (Int.negOfNat 9837606038121198340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-40349521643969720751659651340635389/112589990684262400000000000000000000), (9693089911385428211241466249928067/28147497671065600000000000000000000), (1965112671009922335852298467420851/56294995342131200000000000000000000), (-45951876140432022374315423373713/5629499534213120000000000000000000), (-122010012287801344068659012886053/112589990684262400000000000000000000), (15730470621597722038851061697013/112589990684262400000000000000000000), (2083673486176011293684297255533/112589990684262400000000000000000000), (-44970378929307831913169816211/28147497671065600000000000000000000), (-22024370049680361379257222557/112589990684262400000000000000000000), (142803950570362170029879607/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial166.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial166.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial166.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial166 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 44220578105166245712323637426708020), (Int.ofNat 41119838553853224574188891396013707), (Int.negOfNat 2905956205618367497783864712823079), (Int.negOfNat 1063045471680100293967442458754036), (Int.ofNat 92718644029008448681779441057200), (Int.ofNat 19594205162907344771029106549794), (Int.negOfNat 1572801457689091607283901134696), (Int.negOfNat 234495902543470343695645156643), (Int.ofNat 16682549721706332297571008218), (Int.ofNat 1901137158069740842461158726), (Int.negOfNat 120671153103474700045600301), (Int.negOfNat 11010625710233722414228136), (Int.ofNat 629266444198701416834106), (Int.ofNat 47561997850811577208190), (Int.negOfNat 2470737635046857518740), (Int.negOfNat 157126459004929706607), (Int.ofNat 7892844410032017340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(2211028905258312285616181871335401/5629499534213120000000000000000000), (41119838553853224574188891396013707/112589990684262400000000000000000000), (-2905956205618367497783864712823079/112589990684262400000000000000000000), (-265761367920025073491860614688509/28147497671065600000000000000000000), (231796610072521121704448602643/281474976710656000000000000000000), (9797102581453672385514553274897/56294995342131200000000000000000000), (-196600182211136450910487641837/14073748835532800000000000000000000), (-234495902543470343695645156643/112589990684262400000000000000000000), (8341274860853166148785504109/56294995342131200000000000000000000), (950568579034870421230579363/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial166.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial166.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial166.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial166 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 108317005637794277970231220530714192), (Int.ofNat 20887708019923461413011328203146483), (Int.negOfNat 5989494296991010005041254821151496), (Int.ofNat 117385708030321640602872409372895), (Int.ofNat 152990931959946973671001577534033), (Int.negOfNat 8892723193386979282962122535836), (Int.negOfNat 2232542372509465155348255405648), (Int.ofNat 152086486840856046694977690020), (Int.ofNat 21015313019575351976934755220), (Int.negOfNat 1478682192043446221320152439), (Int.negOfNat 138034722720054193911475880), (Int.ofNat 9580435885575991418929667), (Int.ofNat 666548054434241954444237), (Int.negOfNat 44625183680800123698407), (Int.negOfNat 2456152941777778311140), (Int.ofNat 157057714813781318099), (Int.ofNat 6874846986260241780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(6769812852362142373139451283169637/7036874417766400000000000000000000), (20887708019923461413011328203146483/112589990684262400000000000000000000), (-748686787123876250630156852643937/14073748835532800000000000000000000), (23477141606064328120574481874579/22517998136852480000000000000000000), (152990931959946973671001577534033/112589990684262400000000000000000000), (-2223180798346744820740530633959/28147497671065600000000000000000000), (-139533898281841572209265962853/7036874417766400000000000000000000), (7604324342042802334748884501/5629499534213120000000000000000000), (1050765650978767598846737761/5629499534213120000000000000000000), (-1478682192043446221320152439/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial166.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial166.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial166.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial166 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 129117905719404626828455831333819926), (Int.ofNat 2179665643449034270709836601163909), (Int.negOfNat 2728861140335055939694310843194274), (Int.ofNat 741620894610284389805380892467981), (Int.negOfNat 11113942528332973833240427997332), (Int.negOfNat 17253086266207574817559232919211), (Int.ofNat 962721779325238624737312094415), (Int.ofNat 204674761053444369288083060875), (Int.negOfNat 14685802180306984843025129897), (Int.negOfNat 1568932245436667776932573257), (Int.ofNat 124736959418229477059719698), (Int.ofNat 8528966478894687221956040), (Int.negOfNat 708105529339961433700108), (Int.negOfNat 34726552709673081043665), (Int.ofNat 2916073310782201577691), (Int.ofNat 107166742973206256360), (Int.negOfNat 8918974598964097060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(64558952859702313414227915666909963/56294995342131200000000000000000000), (2179665643449034270709836601163909/112589990684262400000000000000000000), (-1364430570167527969847155421597137/56294995342131200000000000000000000), (741620894610284389805380892467981/112589990684262400000000000000000000), (-2778485632083243458310106999333/28147497671065600000000000000000000), (-17253086266207574817559232919211/112589990684262400000000000000000000), (192544355865047724947462418883/22517998136852480000000000000000000), (1637398088427554954304664487/900719925474099200000000000000000), (-14685802180306984843025129897/112589990684262400000000000000000000), (-1568932245436667776932573257/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial166.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial166.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial166.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial166 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 127848229529390685326623637825852404), (Int.negOfNat 1313621622738661447003322372621245), (Int.ofNat 410555679712595488292197803777375), (Int.ofNat 198676345953136661866028727395068), (Int.negOfNat 89409087419837263872371174298796), (Int.ofNat 2928127587958727935445474976334), (Int.ofNat 1627187263810214496507781011531), (Int.negOfNat 111798590448752907120230716923), (Int.negOfNat 15635323520617365950692176396), (Int.ofNat 1366213198303533583038555052), (Int.ofNat 98149269864813730626397198), (Int.negOfNat 9806868117318162918056261), (Int.negOfNat 441933030858068034312588), (Int.ofNat 48212011907986736879716), (Int.ofNat 1509222792488756463951), (Int.negOfNat 176827091509125365579), (Int.negOfNat 3570044538088591980), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(31962057382347671331655909456463101/28147497671065600000000000000000000), (-262724324547732289400664474524249/22517998136852480000000000000000000), (3284445437700763906337582430219/900719925474099200000000000000000), (49669086488284165466507181848767/28147497671065600000000000000000000), (-22352271854959315968092793574699/28147497671065600000000000000000000), (1464063793979363967722737488167/56294995342131200000000000000000000), (1627187263810214496507781011531/112589990684262400000000000000000000), (-111798590448752907120230716923/112589990684262400000000000000000000), (-3908830880154341487673044099/28147497671065600000000000000000000), (341553299575883395759638763/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial166.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial166.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial166.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial166 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 127202380102117555080853792366879942), (Int.ofNat 335731921769678842603708939121959), (Int.negOfNat 14448075620592506403632454762635), (Int.negOfNat 221343778375497443832237076283056), (Int.negOfNat 4935601648467599837137900371994), (Int.ofNat 9286529691370710710288964659703), (Int.negOfNat 601109589000033806704282220787), (Int.negOfNat 128330124813848634849790182297), (Int.ofNat 12302798189310050428709075063), (Int.ofNat 983334679994426581238829090), (Int.negOfNat 117409224593550859368476983), (Int.negOfNat 4960557098474578677859532), (Int.ofNat 706414522966270391783847), (Int.ofNat 17965179445139222501360), (Int.negOfNat 3006929624239513445065), (Int.negOfNat 48162957383154508113), (Int.ofNat 9945104787896176780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(63601190051058777540426896183439971/56294995342131200000000000000000000), (335731921769678842603708939121959/112589990684262400000000000000000000), (-2889615124118501280726490952527/22517998136852480000000000000000000), (-13833986148468590239514817267691/7036874417766400000000000000000000), (-2467800824233799918568950185997/56294995342131200000000000000000000), (9286529691370710710288964659703/112589990684262400000000000000000000), (-601109589000033806704282220787/112589990684262400000000000000000000), (-128330124813848634849790182297/112589990684262400000000000000000000), (12302798189310050428709075063/112589990684262400000000000000000000), (98333467999442658123882909/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial166.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial166.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial166.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial166 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 126212129058142103296888934447248511), (Int.negOfNat 1951882912166215002244681433981603), (Int.negOfNat 923411909062442060539602998608221), (Int.negOfNat 32007180763687011953459831401375), (Int.ofNat 31980059478409773241805263542906), (Int.negOfNat 2231532714531747641399074462356), (Int.negOfNat 783484512010778265223275559895), (Int.ofNat 89742542753281489588719719938), (Int.ofNat 8069846743234466734736683823), (Int.negOfNat 1201467260962493104289427153), (Int.negOfNat 46871282410448607685466976), (Int.ofNat 9104668463390188175903549), (Int.ofNat 173351313375075664174535), (Int.negOfNat 46194260590238838618088), (Int.negOfNat 417437313950996513416), (Int.ofNat 173880365090703694579), (Int.ofNat 265242089916942180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(126212129058142103296888934447248511/112589990684262400000000000000000000), (-1951882912166215002244681433981603/112589990684262400000000000000000000), (-923411909062442060539602998608221/112589990684262400000000000000000000), (-256057446109496095627678651211/900719925474099200000000000000000), (15990029739204886620902631771453/56294995342131200000000000000000000), (-557883178632936910349768615589/28147497671065600000000000000000000), (-156696902402155653044655111979/22517998136852480000000000000000000), (44871271376640744794359859969/56294995342131200000000000000000000), (8069846743234466734736683823/112589990684262400000000000000000000), (-1201467260962493104289427153/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial166.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial166.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial166.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial166 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 118761695802967712023545431537758790), (Int.negOfNat 5289642087855554833903794535169317), (Int.negOfNat 645539916724100205365277341849496), (Int.ofNat 67143004979762696117748315692069), (Int.negOfNat 8262783994360189134083031634685), (Int.negOfNat 3008160916633141182223223467884), (Int.ofNat 546676312647496330471682634717), (Int.ofNat 48336014641961214942440235220), (Int.negOfNat 10448792032441202324463824534), (Int.negOfNat 333516873559351453059680833), (Int.ofNat 102324050713458113990645714), (Int.ofNat 1076348232707707112403106), (Int.negOfNat 631148619245744817393266), (Int.negOfNat 241309728400206652115), (Int.ofNat 2721551437508329038476), (Int.negOfNat 14596975229865889334), (Int.negOfNat 9869634160771039900), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(11876169580296771202354543153775879/11258999068426240000000000000000000), (-5289642087855554833903794535169317/112589990684262400000000000000000000), (-80692489590512525670659667731187/14073748835532800000000000000000000), (67143004979762696117748315692069/112589990684262400000000000000000000), (-1652556798872037826816606326937/22517998136852480000000000000000000), (-752040229158285295555805866971/28147497671065600000000000000000000), (546676312647496330471682634717/112589990684262400000000000000000000), (2416800732098060747122011761/5629499534213120000000000000000000), (-5224396016220601162231912267/56294995342131200000000000000000000), (-333516873559351453059680833/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial166.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial166.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial166.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial166 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 105947363390173346077934163867262710), (Int.negOfNat 7455478451153114965044394676765999), (Int.negOfNat 537051162598946788966299976254144), (Int.negOfNat 23718578340456194694670789619802), (Int.negOfNat 3713788669446907327587175698546), (Int.ofNat 3054334923844195016289491737944), (Int.ofNat 153331641454416330122497853317), (Int.negOfNat 77851642676224361729382149420), (Int.negOfNat 1135570925806342531526901334), (Int.ofNat 994694497005235328652876633), (Int.negOfNat 2885077848666692694718286), (Int.negOfNat 7590894756007893696425106), (Int.ofNat 87257577479307510343134), (Int.ofNat 38944608193225799296915), (Int.negOfNat 624403238006068377524), (Int.negOfNat 146935158773921687866), (Int.ofNat 2622046334818877500), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(10594736339017334607793416386726271/11258999068426240000000000000000000), (-7455478451153114965044394676765999/112589990684262400000000000000000000), (-8391424415608543577598437128971/1759218604441600000000000000000000), (-11859289170228097347335394809901/56294995342131200000000000000000000), (-1856894334723453663793587849273/56294995342131200000000000000000000), (381791865480524377036186467243/14073748835532800000000000000000000), (153331641454416330122497853317/112589990684262400000000000000000000), (-3892582133811218086469107471/5629499534213120000000000000000000), (-567785462903171265763450667/56294995342131200000000000000000000), (994694497005235328652876633/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial166.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial166.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial166.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial166 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 88736820263124494934484407385784983), (Int.negOfNat 9767205556447438374425588134636109), (Int.negOfNat 537350093309109462238139350223026), (Int.ofNat 52648751339274660762325714269524), (Int.ofNat 16634654499912384118321646210791), (Int.negOfNat 375738127176266798230822868344), (Int.negOfNat 504360485020657519322134300895), (Int.ofNat 10366109269201292414852927862), (Int.ofNat 8299430380122387353644722623), (Int.negOfNat 213900508789730471898857047), (Int.negOfNat 79354410244676021528649376), (Int.ofNat 2329041239020631020113651), (Int.ofNat 490172544463576751994135), (Int.negOfNat 15328719273470943605512), (Int.negOfNat 2125575530939975484616), (Int.ofNat 69610392391170779421), (Int.ofNat 8350519321277993180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(88736820263124494934484407385784983/112589990684262400000000000000000000), (-9767205556447438374425588134636109/112589990684262400000000000000000000), (-268675046654554731119069675111513/56294995342131200000000000000000000), (13162187834818665190581428567381/28147497671065600000000000000000000), (16634654499912384118321646210791/112589990684262400000000000000000000), (-46967265897033349778852858543/14073748835532800000000000000000000), (-100872097004131503864426860179/22517998136852480000000000000000000), (5183054634600646207426463931/56294995342131200000000000000000000), (8299430380122387353644722623/112589990684262400000000000000000000), (-213900508789730471898857047/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial166.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial166.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial166.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial166 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 67699317928645902478410586379602151), (Int.negOfNat 10867127479838923859844206623280002), (Int.ofNat 46702887718705243592143999228307), (Int.ofNat 108455244843318715950385296106234), (Int.negOfNat 6962515170173478125137701703087), (Int.negOfNat 2798712978541542067747047213856), (Int.ofNat 218570585443656703535893165413), (Int.ofNat 58424501050770051753805994897), (Int.negOfNat 3842864655585140483003783737), (Int.negOfNat 707381092590870659099025290), (Int.ofNat 41512087218520257743599817), (Int.ofNat 5334873291633041211231532), (Int.negOfNat 293810699199527316334153), (Int.negOfNat 27320204080989028809760), (Int.ofNat 1447547549937213678935), (Int.ofNat 101298048323481990113), (Int.negOfNat 4749777339808173820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(67699317928645902478410586379602151/112589990684262400000000000000000000), (-5433563739919461929922103311640001/56294995342131200000000000000000000), (46702887718705243592143999228307/112589990684262400000000000000000000), (54227622421659357975192648053117/56294995342131200000000000000000000), (-6962515170173478125137701703087/112589990684262400000000000000000000), (-87459780579423189617095225433/3518437208883200000000000000000000), (218570585443656703535893165413/112589990684262400000000000000000000), (58424501050770051753805994897/112589990684262400000000000000000000), (-3842864655585140483003783737/112589990684262400000000000000000000), (-70738109259087065909902529/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial166.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial166.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial166.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial166 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 46838730355233413936307713217521351), (Int.negOfNat 9762711539182862380264617617788973), (Int.ofNat 388613976209474048139235454505689), (Int.negOfNat 1370562330912818055478483230954), (Int.negOfNat 11894964461895798805780731591221), (Int.ofNat 2039555805456571974846552784326), (Int.ofNat 327049484597858093043723587131), (Int.negOfNat 46584997779899454574433707677), (Int.negOfNat 5172551167234880460001730396), (Int.ofNat 582908451520898593515301148), (Int.ofNat 48494831961959475316422798), (Int.negOfNat 4703450660127608586015339), (Int.negOfNat 296973678407537112575388), (Int.ofNat 26225851799222569474284), (Int.ofNat 1280332746500226336751), (Int.negOfNat 106761458440661774421), (Int.negOfNat 5045716873106343380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(46838730355233413936307713217521351/112589990684262400000000000000000000), (-9762711539182862380264617617788973/112589990684262400000000000000000000), (388613976209474048139235454505689/112589990684262400000000000000000000), (-685281165456409027739241615477/56294995342131200000000000000000000), (-11894964461895798805780731591221/112589990684262400000000000000000000), (1019777902728285987423276392163/56294995342131200000000000000000000), (327049484597858093043723587131/112589990684262400000000000000000000), (-46584997779899454574433707677/112589990684262400000000000000000000), (-1293137791808720115000432599/28147497671065600000000000000000000), (145727112880224648378825287/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial166.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial166.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial166.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial166 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 28745726642633676758037044559993189), (Int.negOfNat 8404017498411981964761276335817317), (Int.ofNat 299090218937687090578677686326702), (Int.ofNat 5677957879467405888877243132708), (Int.ofNat 12062852805425424043927721070508), (Int.ofNat 1140336274822810349373659794011), (Int.negOfNat 430457343027463539616824572145), (Int.negOfNat 27961289763100217000377648675), (Int.ofNat 6718059755479419098157673703), (Int.ofNat 339644246571738978050207457), (Int.negOfNat 64289450840961841538007502), (Int.negOfNat 2530304638239055657001240), (Int.ofNat 415734458377179878458292), (Int.ofNat 12769204603841587486065), (Int.negOfNat 1923896144164309534709), (Int.negOfNat 45735349043583211960), (Int.ofNat 5775907528740253540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(28745726642633676758037044559993189/112589990684262400000000000000000000), (-8404017498411981964761276335817317/112589990684262400000000000000000000), (149545109468843545289338843163351/56294995342131200000000000000000000), (1419489469866851472219310783177/28147497671065600000000000000000000), (3015713201356356010981930267627/28147497671065600000000000000000000), (1140336274822810349373659794011/112589990684262400000000000000000000), (-86091468605492707923364914429/22517998136852480000000000000000000), (-1118451590524008680015105947/4503599627370496000000000000000000), (6718059755479419098157673703/112589990684262400000000000000000000), (339644246571738978050207457/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial166.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial166.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial166.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial166 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 13379668756619404552452600148658278), (Int.negOfNat 6750142566262265330979609300964163), (Int.ofNat 604614952860318511907207513092842), (Int.ofNat 76082132585214317257541849204401), (Int.negOfNat 2212343861707090742951514017922), (Int.negOfNat 3228438494432509281884390571624), (Int.negOfNat 68827592169492544636233593848), (Int.ofNat 64414354165918323618231665380), (Int.ofNat 1352128985932966187381490020), (Int.negOfNat 753261507741987676019486961), (Int.negOfNat 12776785264365982369573880), (Int.ofNat 5765755112845776362068733), (Int.ofNat 75258901263578742949437), (Int.negOfNat 30915024435024506522793), (Int.negOfNat 304650208652601521540), (Int.ofNat 122564594961629823901), (Int.ofNat 1740914424934693580), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(6689834378309702276226300074329139/56294995342131200000000000000000000), (-6750142566262265330979609300964163/112589990684262400000000000000000000), (302307476430159255953603756546421/56294995342131200000000000000000000), (76082132585214317257541849204401/112589990684262400000000000000000000), (-1106171930853545371475757008961/56294995342131200000000000000000000), (-403554811804063660235548821453/14073748835532800000000000000000000), (-8603449021186568079529199231/14073748835532800000000000000000000), (3220717708295916180911583269/5629499534213120000000000000000000), (67606449296648309369074501/5629499534213120000000000000000000), (-753261507741987676019486961/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial166.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial166.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial166.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial166 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2771592287982631943589934628012941), (Int.negOfNat 3732475721803785555795494069565772), (Int.ofNat 775471539990818509674465335339893), (Int.negOfNat 47274336382341334090344956395732), (Int.negOfNat 22043058603573346947630582664834), (Int.ofNat 508569510900522210853160366653), (Int.ofNat 518267358680148798882177103504), (Int.negOfNat 5666561285787925132295013957), (Int.negOfNat 7532404214381250727481147382), (Int.ofNat 57079094861848423497700674), (Int.ofNat 69613744046498710044430499), (Int.negOfNat 453159921956550628161464), (Int.negOfNat 438880409973122302859494), (Int.ofNat 2714783788449307152610), (Int.ofNat 1992409943180143730860), (Int.negOfNat 14465016530414997793), (Int.negOfNat 6802037717672333260), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(2771592287982631943589934628012941/112589990684262400000000000000000000), (-933118930450946388948873517391443/28147497671065600000000000000000000), (775471539990818509674465335339893/112589990684262400000000000000000000), (-11818584095585333522586239098933/28147497671065600000000000000000000), (-11021529301786673473815291332417/56294995342131200000000000000000000), (508569510900522210853160366653/112589990684262400000000000000000000), (32391709917509299930136068969/7036874417766400000000000000000000), (-5666561285787925132295013957/112589990684262400000000000000000000), (-3766202107190625363740573691/56294995342131200000000000000000000), (28539547430924211748850337/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial166.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial166.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial166.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial166 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 2275469067037033850380844007401166), (Int.negOfNat 1772845972049948988601062243449155), (Int.ofNat 111579547417453727571505829888598), (Int.negOfNat 135714812468102691528273486320826), (Int.ofNat 5209700296413772118005571406315), (Int.ofNat 3498659819368595443160802616494), (Int.negOfNat 163041394729252661900800340267), (Int.negOfNat 63535112109381732551394126156), (Int.ofNat 2415605806673060679142207843), (Int.ofNat 722947071456269215897328530), (Int.negOfNat 22418243670601270901932325), (Int.negOfNat 5446634158027499276540204), (Int.ofNat 142830218427994962764618), (Int.ofNat 28904256131234477911982), (Int.negOfNat 659168573227694707779), (Int.negOfNat 114273128610066363094), (Int.ofNat 1905931419547649460), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1137734533518516925190422003700583/56294995342131200000000000000000000), (-354569194409989797720212448689831/22517998136852480000000000000000000), (55789773708726863785752914944299/56294995342131200000000000000000000), (-67857406234051345764136743160413/56294995342131200000000000000000000), (1041940059282754423601114281263/22517998136852480000000000000000000), (1749329909684297721580401308247/56294995342131200000000000000000000), (-163041394729252661900800340267/112589990684262400000000000000000000), (-15883778027345433137848531539/28147497671065600000000000000000000), (2415605806673060679142207843/112589990684262400000000000000000000), (72294707145626921589732853/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial166.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial166.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial166.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial166 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 6282860905444606958388998912132788), (Int.negOfNat 2564301949956310128425035766692128), (Int.negOfNat 372346862822149686476642330781366), (Int.negOfNat 8092321942204554275459813629701), (Int.ofNat 17740725828284736271875479335961), (Int.negOfNat 1573956201418483351384140230013), (Int.negOfNat 437990106563504215257227302133), (Int.ofNat 35275947837841684797366648244), (Int.ofNat 6316448322040029599327822157), (Int.negOfNat 414998532871025636213186270), (Int.negOfNat 57948917173811080464918875), (Int.ofNat 3154230849702186367063396), (Int.ofNat 364154821768618846596982), (Int.negOfNat 16788406906232480701218), (Int.negOfNat 1655957830688620707821), (Int.ofNat 67724915296703345706), (Int.ofNat 5282922878179286540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-1570715226361151739597249728033197/28147497671065600000000000000000000), (-80134435936134691513282367709129/3518437208883200000000000000000000), (-186173431411074843238321165390683/56294995342131200000000000000000000), (-8092321942204554275459813629701/112589990684262400000000000000000000), (17740725828284736271875479335961/112589990684262400000000000000000000), (-1573956201418483351384140230013/112589990684262400000000000000000000), (-437990106563504215257227302133/112589990684262400000000000000000000), (8818986959460421199341662061/28147497671065600000000000000000000), (6316448322040029599327822157/112589990684262400000000000000000000), (-41499853287102563621318627/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial166.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial166.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial166.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial166 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 12754268881769287179684327288077086), (Int.negOfNat 3772042408262927907839582879621789), (Int.negOfNat 193602666906215335153516236549549), (Int.ofNat 28917546411219976814306252186644), (Int.negOfNat 9606903350594129103730459329774), (Int.negOfNat 2217626162665618803963374625694), (Int.ofNat 353144005871796260505331396096), (Int.ofNat 44397917493507219859823419243), (Int.negOfNat 5476239031000960739570464618), (Int.negOfNat 509361760522549583785498526), (Int.ofNat 51267070220538329068135101), (Int.ofNat 3861463326115805542094136), (Int.negOfNat 323091873325174466933306), (Int.negOfNat 20671599076927052478590), (Int.ofNat 1461999129310039296740), (Int.ofNat 84251528445859117807), (Int.negOfNat 4793219844283469140), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-6377134440884643589842163644038543/56294995342131200000000000000000000), (-3772042408262927907839582879621789/112589990684262400000000000000000000), (-193602666906215335153516236549549/112589990684262400000000000000000000), (7229386602804994203576563046661/28147497671065600000000000000000000), (-4803451675297064551865229664887/56294995342131200000000000000000000), (-1108813081332809401981687312847/56294995342131200000000000000000000), (689734386468352071299475383/219902325555200000000000000000000), (44397917493507219859823419243/112589990684262400000000000000000000), (-2738119515500480369785232309/56294995342131200000000000000000000), (-254680880261274791892749263/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial166.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial166.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial166.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial166 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 21039418106650561279908062985976246), (Int.negOfNat 4603063714008989140506800731601063), (Int.negOfNat 324968956069807991661561081576173), (Int.negOfNat 66919259002256986907255321381591), (Int.negOfNat 5544926024850283093632975093681), (Int.ofNat 2759029467202746642085692114336), (Int.ofNat 226071920721092451518184052248), (Int.negOfNat 56679438419918261486252813420), (Int.negOfNat 3400072254958290393746556820), (Int.ofNat 671824240855585214960144639), (Int.ofNat 31912203887912179287691080), (Int.negOfNat 5126881978735980858931667), (Int.negOfNat 206100255539172876875037), (Int.ofNat 27213965033165119968007), (Int.ofNat 957947348235492033140), (Int.negOfNat 107463721761804546899), (Int.negOfNat 2320163826318329980), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-10519709053325280639954031492988123/56294995342131200000000000000000000), (-4603063714008989140506800731601063/112589990684262400000000000000000000), (-324968956069807991661561081576173/112589990684262400000000000000000000), (-66919259002256986907255321381591/112589990684262400000000000000000000), (-5544926024850283093632975093681/112589990684262400000000000000000000), (86219670850085832565177878573/3518437208883200000000000000000000), (28258990090136556439773006531/14073748835532800000000000000000000), (-2833971920995913074312640671/5629499534213120000000000000000000), (-170003612747914519687327841/5629499534213120000000000000000000), (671824240855585214960144639/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial166.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial166.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial166.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial166 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 32074496544971719086844034166595563), (Int.negOfNat 6646504184042214639174065002966514), (Int.negOfNat 625454925847839517134246713690903), (Int.ofNat 1291206507394648651362242325383), (Int.ofNat 18837013915351021956701750988919), (Int.ofNat 636445599617662888347725885958), (Int.negOfNat 471114094633094719910867493215), (Int.negOfNat 12771437035194411931836403475), (Int.ofNat 7248767304300934468584332297), (Int.ofNat 155634337252859171830391057), (Int.negOfNat 68675918624163213176104498), (Int.negOfNat 1295772564465063923062040), (Int.ofNat 435634660159281943453308), (Int.ofNat 7614980449615142046065), (Int.negOfNat 1970272403057957245691), (Int.negOfNat 34291812414135667560), (Int.ofNat 5819350033215548860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-32074496544971719086844034166595563/112589990684262400000000000000000000), (-3323252092021107319587032501483257/56294995342131200000000000000000000), (-625454925847839517134246713690903/112589990684262400000000000000000000), (1291206507394648651362242325383/112589990684262400000000000000000000), (18837013915351021956701750988919/112589990684262400000000000000000000), (318222799808831444173862942979/56294995342131200000000000000000000), (-94222818926618943982173498643/22517998136852480000000000000000000), (-510857481407776477273456139/4503599627370496000000000000000000), (7248767304300934468584332297/112589990684262400000000000000000000), (155634337252859171830391057/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial166.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial166.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial166.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial166 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 47567158323416684836350665612712110), (Int.negOfNat 8567878842115920989477160365312437), (Int.negOfNat 223444266319067401049276665464908), (Int.ofNat 107681567444461082659952094301471), (Int.ofNat 1182949737848534473241280539584), (Int.negOfNat 3076023633738448115150896095594), (Int.ofNat 42515903118691343000439223869), (Int.ofNat 63845982656637883352303692323), (Int.negOfNat 641748454802650903747512004), (Int.negOfNat 776033867842197679560879252), (Int.ofNat 3983342633330301208565602), (Int.ofNat 6019092461637484072138261), (Int.negOfNat 9365405855538906404612), (Int.negOfNat 32257815696974765257316), (Int.negOfNat 33110956434861095951), (Int.ofNat 127233098457148594379), (Int.negOfNat 984638621853319820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-4756715832341668483635066561271211/11258999068426240000000000000000000), (-8567878842115920989477160365312437/112589990684262400000000000000000000), (-55861066579766850262319166366227/28147497671065600000000000000000000), (107681567444461082659952094301471/112589990684262400000000000000000000), (18483589653883351144395008431/1759218604441600000000000000000000), (-1538011816869224057575448047797/56294995342131200000000000000000000), (42515903118691343000439223869/112589990684262400000000000000000000), (63845982656637883352303692323/112589990684262400000000000000000000), (-160437113700662725936878001/28147497671065600000000000000000000), (-194008466960549419890219813/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial166.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial166.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial166.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial166 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 64804398300134111301340169989727680), (Int.negOfNat 8343297402546908773966135616896463), (Int.ofNat 253546077657325438037162539356470), (Int.ofNat 31643682733077080088502510877378), (Int.negOfNat 12702079357614648977745117985639), (Int.ofNat 1144110350681611821348203754910), (Int.ofNat 438014291449930136474618474187), (Int.negOfNat 26156500388787164633879535103), (Int.negOfNat 7256000048146189318032523463), (Int.ofNat 279081067737191194922877110), (Int.ofNat 71050053583762673046673783), (Int.negOfNat 1837739481899855299862468), (Int.negOfNat 459978828295696995385047), (Int.ofNat 8208608222740843544240), (Int.ofNat 2118277723156586523065), (Int.negOfNat 24711973175916080687), (Int.negOfNat 6845480222147628580), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-202513744687919097816688031217899/351843720888320000000000000000000), (-8343297402546908773966135616896463/112589990684262400000000000000000000), (25354607765732543803716253935647/11258999068426240000000000000000000), (15821841366538540044251255438689/56294995342131200000000000000000000), (-12702079357614648977745117985639/112589990684262400000000000000000000), (114411035068161182134820375491/11258999068426240000000000000000000), (438014291449930136474618474187/112589990684262400000000000000000000), (-26156500388787164633879535103/112589990684262400000000000000000000), (-7256000048146189318032523463/112589990684262400000000000000000000), (27908106773719119492287711/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial166.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial166.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial166.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial166 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 80367243627121849196066350066196739), (Int.negOfNat 7198400679271649272372716778988538), (Int.ofNat 306654333580670698642960813380776), (Int.ofNat 20689484488935370561526445529126), (Int.ofNat 11518639492368773475350664425926), (Int.ofNat 1991780969615623387486693035216), (Int.negOfNat 365645170465555055925152775505), (Int.negOfNat 53471463526637763320891535338), (Int.ofNat 5187793015522837477831714577), (Int.ofNat 697280385149577996589107353), (Int.negOfNat 44078486333602450807515824), (Int.negOfNat 5628539766073877299931549), (Int.ofNat 249122980708910372736665), (Int.ofNat 30958791727333729883688), (Int.negOfNat 1002747973920910264584), (Int.negOfNat 124286372038726923379), (Int.ofNat 4289441070024969620), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-80367243627121849196066350066196739/112589990684262400000000000000000000), (-3599200339635824636186358389494269/56294995342131200000000000000000000), (38331791697583837330370101672597/14073748835532800000000000000000000), (10344742244467685280763222764563/56294995342131200000000000000000000), (5759319746184386737675332212963/56294995342131200000000000000000000), (124486310600976461717918314701/7036874417766400000000000000000000), (-73129034093111011185030555101/22517998136852480000000000000000000), (-26735731763318881660445767669/56294995342131200000000000000000000), (5187793015522837477831714577/112589990684262400000000000000000000), (697280385149577996589107353/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial166.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial166.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial166.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial166 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 93152492517948228444477819910760723), (Int.negOfNat 5283092297809691306406148472136954), (Int.ofNat 754758021643708437111230545056801), (Int.ofNat 116229071653733328768970527412504), (Int.ofNat 2358888205070599404957746951724), (Int.negOfNat 3645503794925778282470389404469), (Int.negOfNat 275476886067411759364861630717), (Int.ofNat 67002541270471356067673174180), (Int.ofNat 5343066425473972888308120934), (Int.negOfNat 727170843037383792592189367), (Int.negOfNat 56853588037905965548732514), (Int.ofNat 5069239326557271879414894), (Int.ofNat 388384602733167935670466), (Int.negOfNat 24459635888127774285485), (Int.negOfNat 1844027340400944476476), (Int.ofNat 87471905788936478134), (Int.ofNat 6770009595022491700), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-93152492517948228444477819910760723/112589990684262400000000000000000000), (-2641546148904845653203074236068477/56294995342131200000000000000000000), (754758021643708437111230545056801/112589990684262400000000000000000000), (14528633956716666096121315926563/14073748835532800000000000000000000), (589722051267649851239436737931/28147497671065600000000000000000000), (-3645503794925778282470389404469/112589990684262400000000000000000000), (-275476886067411759364861630717/112589990684262400000000000000000000), (3350127063523567803383658709/5629499534213120000000000000000000), (2671533212736986444154060467/56294995342131200000000000000000000), (-727170843037383792592189367/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial166.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial166.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial166.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial166 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 99856831518705503771718646962125977), (Int.negOfNat 1104771693270127729720759856598732), (Int.ofNat 1201750226516264868208528229411039), (Int.negOfNat 12233100457126095141472947261825), (Int.negOfNat 29323104599980367088682471529193), (Int.negOfNat 674138261110272768350887813197), (Int.ofNat 672681613987822989477498058083), (Int.ofNat 26485613572358429947448766820), (Int.negOfNat 9485472560860732052659005066), (Int.negOfNat 428179409270731276179884833), (Int.ofNat 82560392012722459910253086), (Int.ofNat 3934945877736792513329106), (Int.negOfNat 478782744123204444956334), (Int.negOfNat 23342424647574144754515), (Int.ofNat 1981039698635736855524), (Int.ofNat 97341165721944916666), (Int.negOfNat 7176729494760789300), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-99856831518705503771718646962125977/112589990684262400000000000000000000), (-276192923317531932430189964149683/28147497671065600000000000000000000), (1201750226516264868208528229411039/112589990684262400000000000000000000), (-489324018285043805658917890473/4503599627370496000000000000000000), (-29323104599980367088682471529193/112589990684262400000000000000000000), (-674138261110272768350887813197/112589990684262400000000000000000000), (672681613987822989477498058083/112589990684262400000000000000000000), (1324280678617921497372438341/5629499534213120000000000000000000), (-4742736280430366026329502533/56294995342131200000000000000000000), (-428179409270731276179884833/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial166.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial166.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial166.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial166 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 97804096144190852494608131276624208), (Int.ofNat 2693936645849817560184166445331968), (Int.ofNat 531963582039820859810235157588831), (Int.negOfNat 169247121769697367655622869630720), (Int.ofNat 571095316851439185318914784277), (Int.ofNat 5238290532946171362031383196057), (Int.negOfNat 2774834548417544402398177705), (Int.negOfNat 100612340340756977479790979262), (Int.negOfNat 1452907500009212028819279023), (Int.ofNat 1126781255608774827988133247), (Int.ofNat 26720306818076920373100176), (Int.negOfNat 7968734745271193833633651), (Int.negOfNat 228051979884436127993335), (Int.ofNat 38865970073354810575112), (Int.ofNat 1212546805912693822616), (Int.negOfNat 142485322950241368221), (Int.negOfNat 5250894755529444980), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-6112756009011928280913008204789013/7036874417766400000000000000000000), (5261595011425424922234700088539/219902325555200000000000000000000), (531963582039820859810235157588831/112589990684262400000000000000000000), (-132224313882576068480955366899/87960930222080000000000000000000), (571095316851439185318914784277/112589990684262400000000000000000000), (5238290532946171362031383196057/112589990684262400000000000000000000), (-554966909683508880479635541/22517998136852480000000000000000000), (-50306170170378488739895489631/56294995342131200000000000000000000), (-1452907500009212028819279023/112589990684262400000000000000000000), (1126781255608774827988133247/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial166.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial166.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial166.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial166 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 91478423236754632376862668994162613), (Int.ofNat 3183708651087322636265494982976845), (Int.negOfNat 116363935686597163536148239696642), (Int.negOfNat 8419511892524462957632221106412), (Int.ofNat 27540655405129591685616605361233), (Int.negOfNat 1655436020329618377193573370044), (Int.negOfNat 849309596650989022156563360813), (Int.ofNat 20746026233498674142922003703), (Int.ofNat 13022359925440358842054034137), (Int.negOfNat 19894533810610941043562510), (Int.negOfNat 115168585802836047461614617), (Int.negOfNat 1132938789043705262837532), (Int.ofNat 668951248206674011063353), (Int.ofNat 10471811625353174799360), (Int.negOfNat 2773245515558912716935), (Int.negOfNat 51704055271505218913), (Int.ofNat 9304460499750085620), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-91478423236754632376862668994162613/112589990684262400000000000000000000), (636741730217464527253098996595369/22517998136852480000000000000000000), (-58181967843298581768074119848321/56294995342131200000000000000000000), (-2104877973131115739408055276603/28147497671065600000000000000000000), (27540655405129591685616605361233/112589990684262400000000000000000000), (-413859005082404594298393342511/28147497671065600000000000000000000), (-849309596650989022156563360813/112589990684262400000000000000000000), (20746026233498674142922003703/112589990684262400000000000000000000), (13022359925440358842054034137/112589990684262400000000000000000000), (-1989453381061094104356251/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial166.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial166.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial166.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial166 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 85304635496962679789947918476138838), (Int.ofNat 3225014940585817693071584560833491), (Int.ofNat 193698438394302802210871191815597), (Int.ofNat 42905093254844700162775015154693), (Int.negOfNat 21168607143299156959994373304414), (Int.negOfNat 5204452872067240523709952412886), (Int.ofNat 522219549176900226023580440709), (Int.ofNat 126546725783690396234710511077), (Int.negOfNat 4378813996585952553967951204), (Int.negOfNat 1456604967382542294679227348), (Int.ofNat 15656716136718625409468402), (Int.ofNat 10234639353163546918245339), (Int.ofNat 3268935336082765308588), (Int.negOfNat 49544628816704025171884), (Int.negOfNat 304366423460370784751), (Int.ofNat 179636388999732363221), (Int.ofNat 1946092307357795180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-42652317748481339894973959238069419/56294995342131200000000000000000000), (3225014940585817693071584560833491/112589990684262400000000000000000000), (193698438394302802210871191815597/112589990684262400000000000000000000), (42905093254844700162775015154693/112589990684262400000000000000000000), (-10584303571649578479997186652207/56294995342131200000000000000000000), (-2602226436033620261854976206443/56294995342131200000000000000000000), (522219549176900226023580440709/112589990684262400000000000000000000), (126546725783690396234710511077/112589990684262400000000000000000000), (-1094703499146488138491987801/28147497671065600000000000000000000), (-364151241845635573669806837/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial166.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial166.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial166.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial166 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 78194021446993870047562362287093199), (Int.ofNat 3570230215053705091099732118929012), (Int.negOfNat 276999661204504449592758543097038), (Int.negOfNat 195219361973960161881661748204097), (Int.negOfNat 16598977468310192575159356500795), (Int.ofNat 7207003677541287490489893514736), (Int.ofNat 1018059037239783447378492833545), (Int.negOfNat 89394398906163133226980667925), (Int.negOfNat 16196732217187188164945840103), (Int.ofNat 583991108681956296044406343), (Int.ofNat 140160568053247817810516302), (Int.negOfNat 2308599370754642140806760), (Int.negOfNat 797969639255759045555492), (Int.ofNat 5533510584646295636335), (Int.ofNat 3271687867274399482709), (Int.negOfNat 3858644008393559240), (Int.negOfNat 10330590688682165340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-78194021446993870047562362287093199/112589990684262400000000000000000000), (892557553763426272774933029732253/28147497671065600000000000000000000), (-138499830602252224796379271548519/56294995342131200000000000000000000), (-195219361973960161881661748204097/112589990684262400000000000000000000), (-3319795493662038515031871300159/22517998136852480000000000000000000), (450437729846330468155618344671/7036874417766400000000000000000000), (203611807447956689475698566709/22517998136852480000000000000000000), (-3575775956246525329079226717/4503599627370496000000000000000000), (-16196732217187188164945840103/112589990684262400000000000000000000), (583991108681956296044406343/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial166.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial166.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial166.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial166 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 73708272517995197208433719309911924), (Int.ofNat 305843618146074482107120811605030), (Int.negOfNat 1110705590254039037686886390190580), (Int.ofNat 49182010168391406291265504614490), (Int.ofNat 77428894052699780275723089118070), (Int.ofNat 6821941035177182562262533069884), (Int.negOfNat 1261800240144282192878857536752), (Int.negOfNat 160329228617502054459225480780), (Int.ofNat 10996076633344431659830995580), (Int.ofNat 1731561834787863981955813161), (Int.negOfNat 61762881585491770307517320), (Int.negOfNat 11666743312635615005190733), (Int.ofNat 245266363565980556289363), (Int.ofNat 55099616156570673088393), (Int.negOfNat 728465121028571440460), (Int.negOfNat 195439525520700412701), (Int.ofNat 1358710140813854620), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-18427068129498799302108429827477981/28147497671065600000000000000000000), (30584361814607448210712081160503/11258999068426240000000000000000000), (-55535279512701951884344319509529/5629499534213120000000000000000000), (4918201016839140629126550461449/11258999068426240000000000000000000), (7742889405269978027572308911807/11258999068426240000000000000000000), (1705485258794295640565633267471/28147497671065600000000000000000000), (-78862515009017637054928596047/7036874417766400000000000000000000), (-8016461430875102722961274039/5629499534213120000000000000000000), (549803831667221582991549779/5629499534213120000000000000000000), (1731561834787863981955813161/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial166.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial166.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial166.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial166 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 75786448645637196653213605542623975), (Int.negOfNat 822597176728758329143057774763563), (Int.ofNat 1204530817573715530859539833209535), (Int.ofNat 677433631762688495099968287894840), (Int.ofNat 43072453785768090830185532746608), (Int.negOfNat 14171564770388428001111227452313), (Int.negOfNat 1465669794977278430967793786904), (Int.ofNat 155706604726109836758067586557), (Int.ofNat 19570041952597268176636009782), (Int.negOfNat 1111756709075002730175022474), (Int.negOfNat 155865548985539857676977299), (Int.ofNat 5666956798550251051371464), (Int.ofNat 848997803414605341870694), (Int.negOfNat 21808196213157215247010), (Int.negOfNat 3396128214472222268860), (Int.ofNat 64059009582391768993), (Int.ofNat 11356720877614245060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-3031457945825487866128544221704959/4503599627370496000000000000000000), (-822597176728758329143057774763563/112589990684262400000000000000000000), (240906163514743106171907966641907/22517998136852480000000000000000000), (16935840794067212377499207197371/2814749767106560000000000000000000), (2692028361610505676886595796663/7036874417766400000000000000000000), (-14171564770388428001111227452313/112589990684262400000000000000000000), (-183208724372159803870974223363/14073748835532800000000000000000000), (155706604726109836758067586557/112589990684262400000000000000000000), (9785020976298634088318004891/56294995342131200000000000000000000), (-555878354537501365087511237/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial166.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial166.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial166.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial166 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 67027957951378251622029438103138364), (Int.ofNat 12174434344405933667411070237026095), (Int.ofNat 4950383660314385483125459198485066), (Int.ofNat 334864071147195668828854140758665), (Int.negOfNat 127308771967406082988175012960576), (Int.negOfNat 13167818236061764165592869479394), (Int.ofNat 1762092364093072476716447755627), (Int.ofNat 206819627357185805230668019556), (Int.negOfNat 15758298146359598790782897443), (Int.negOfNat 1920389514539901147538158730), (Int.ofNat 99663916191018749466789525), (Int.ofNat 12024646643877749109362204), (Int.negOfNat 469146684616084513067418), (Int.negOfNat 54558990200361726589582), (Int.ofNat 1703411706884410029779), (Int.ofNat 187148059169136951894), (Int.negOfNat 5005555985296197660), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-16756989487844562905507359525784591/28147497671065600000000000000000000), (2434886868881186733482214047405219/22517998136852480000000000000000000), (2475191830157192741562729599242533/56294995342131200000000000000000000), (66972814229439133765770828151733/22517998136852480000000000000000000), (-1989199561990720046690234577509/1759218604441600000000000000000000), (-6583909118030882082796434739697/56294995342131200000000000000000000), (1762092364093072476716447755627/112589990684262400000000000000000000), (51704906839296451307667004889/28147497671065600000000000000000000), (-15758298146359598790782897443/112589990684262400000000000000000000), (-192038951453990114753815873/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial166.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial166.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial166.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial166.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial166 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial166 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial166 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 97126389792732996850388190323333811), (Int.negOfNat 16730080664459636659289297455113468), (Int.ofNat 5834670361422667321799346089940698), (Int.negOfNat 296621236859274220793322783882140), (Int.negOfNat 132003993429991119310567635733547), (Int.ofNat 13058745933543516568381219562587), (Int.ofNat 1772551851783342307071962856867), (Int.negOfNat 206657293300807268661311989556), (Int.negOfNat 15771102133951754848181953443), (Int.ofNat 1920240444136637904531960730), (Int.ofNat 99673782535139296618903525), (Int.negOfNat 12024549402061157201218204), (Int.negOfNat 469146684616084513067418), (Int.ofNat 54558990200361726589582), (Int.ofNat 1703411706884410029779), (Int.negOfNat 187148059169136951894), (Int.negOfNat 5005555985296197660), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-97126389792732996850388190323333811/112589990684262400000000000000000000), (-4182520166114909164822324363778367/28147497671065600000000000000000000), (2917335180711333660899673044970349/56294995342131200000000000000000000), (-14831061842963711039666139194107/5629499534213120000000000000000000), (-132003993429991119310567635733547/112589990684262400000000000000000000), (13058745933543516568381219562587/112589990684262400000000000000000000), (1772551851783342307071962856867/112589990684262400000000000000000000), (-51664323325201817165327997389/28147497671065600000000000000000000), (-15771102133951754848181953443/112589990684262400000000000000000000), (192024044413663790453196073/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial166.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial166.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial166.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 111231010663337349264092128494823220), (Int.ofNat 106106345590364282566857396937893), (Int.ofNat 2199459275001997395855867739856679), (Int.negOfNat 679374627302512675583411677642764), (Int.ofNat 37944726560132520971198458667600), (Int.ofNat 14195687514139708690131326380206), (Int.negOfNat 1454437612813027247789388110904), (Int.negOfNat 155760765819694781318079786557), (Int.ofNat 19556412047969279183834589782), (Int.ofNat 1111816005842627747790306474), (Int.negOfNat 155855082807810913855473299), (Int.negOfNat 5666993264231473016925464), (Int.ofNat 848997803414605341870694), (Int.ofNat 21808196213157215247010), (Int.negOfNat 3396128214472222268860), (Int.negOfNat 64059009582391768993), (Int.ofNat 11356720877614245060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-5561550533166867463204606424741161/5629499534213120000000000000000000), (106106345590364282566857396937893/112589990684262400000000000000000000), (2199459275001997395855867739856679/112589990684262400000000000000000000), (-169843656825628168895852919410691/28147497671065600000000000000000000), (94861816400331302427996146669/281474976710656000000000000000000), (7097843757069854345065663190103/56294995342131200000000000000000000), (-181804701601628405973673513863/14073748835532800000000000000000000), (-155760765819694781318079786557/112589990684262400000000000000000000), (9778206023984639591917294891/56294995342131200000000000000000000), (555908002921313873895153237/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial166.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial166.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial166.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 106702193561634152160688890514808192), (Int.ofNat 2774048529628059887306334323685517), (Int.negOfNat 245923444999054120117205770078104), (Int.negOfNat 89437042384746195676315998575295), (Int.ofNat 73186271972061833782608932247967), (Int.negOfNat 6673485617430930005568761408564), (Int.negOfNat 1252778754606358315684008266752), (Int.ofNat 160075229640045414099548960780), (Int.ofNat 10985303212785386443108293580), (Int.negOfNat 1731311305850012651817063161), (Int.negOfNat 61754665358192691536677320), (Int.ofNat 11666585294683653154456733), (Int.ofNat 245266363565980556289363), (Int.negOfNat 55099616156570673088393), (Int.negOfNat 728465121028571440460), (Int.ofNat 195439525520700412701), (Int.ofNat 1358710140813854620), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-833610887200266813755381957146939/879609302220800000000000000000000), (2774048529628059887306334323685517/112589990684262400000000000000000000), (-30740430624881765014650721259763/14073748835532800000000000000000000), (-17887408476949239135263199715059/22517998136852480000000000000000000), (73186271972061833782608932247967/112589990684262400000000000000000000), (-1668371404357732501392190352141/28147497671065600000000000000000000), (-1223416752545271792660164323/109951162777600000000000000000000), (8003761482002270704977448039/5629499534213120000000000000000000), (549265160639269322155414679/5629499534213120000000000000000000), (-1731311305850012651817063161/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial166.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial166.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial166.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 101953659010173431066403952591797926), (Int.ofNat 2363450573034617976426197609894091), (Int.ofNat 258282201711034956766307754678274), (Int.ofNat 128244927819463748398719722889219), (Int.negOfNat 18897829014911054333443121297468), (Int.negOfNat 6975886735987550873435287606389), (Int.ofNat 1022511237562359144007128216785), (Int.ofNat 89011032205374786920881035925), (Int.negOfNat 16201761734978598605612828103), (Int.negOfNat 583618461140584872680526343), (Int.ofNat 140164286846529520829696302), (Int.ofNat 2308368421440236358964760), (Int.negOfNat 797969639255759045555492), (Int.negOfNat 5533510584646295636335), (Int.ofNat 3271687867274399482709), (Int.ofNat 3858644008393559240), (Int.negOfNat 10330590688682165340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-50976829505086715533201976295898963/56294995342131200000000000000000000), (2363450573034617976426197609894091/112589990684262400000000000000000000), (129141100855517478383153877339137/56294995342131200000000000000000000), (128244927819463748398719722889219/112589990684262400000000000000000000), (-4724457253727763583360780324367/28147497671065600000000000000000000), (-6975886735987550873435287606389/112589990684262400000000000000000000), (204502247512471828801425643357/22517998136852480000000000000000000), (3560441288214991476835241437/4503599627370496000000000000000000), (-16201761734978598605612828103/112589990684262400000000000000000000), (-583618461140584872680526343/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial166.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial166.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial166.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 95620730611716356842054772987027604), (Int.ofNat 3991704994010179810698786845510445), (Int.ofNat 291254260563320025894086696319825), (Int.negOfNat 118534958042756807939778472140268), (Int.negOfNat 21000590720057272912176064089604), (Int.ofNat 5455314260194403301924829963266), (Int.ofNat 521000624564941018218873196069), (Int.negOfNat 126954623977543981122457873077), (Int.negOfNat 4376790703474018911562721204), (Int.ofNat 1456997611476664045614171348), (Int.ofNat 15654942000784062793346402), (Int.negOfNat 10234894612932100677123339), (Int.ofNat 3268935336082765308588), (Int.ofNat 49544628816704025171884), (Int.negOfNat 304366423460370784751), (Int.negOfNat 179636388999732363221), (Int.ofNat 1946092307357795180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-23905182652929089210513693246756901/28147497671065600000000000000000000), (798340998802035962139757369102089/22517998136852480000000000000000000), (11650170422532801035763467852793/4503599627370496000000000000000000), (-29633739510689201984944618035067/28147497671065600000000000000000000), (-5250147680014318228044016022401/28147497671065600000000000000000000), (2727657130097201650962414981633/56294995342131200000000000000000000), (521000624564941018218873196069/112589990684262400000000000000000000), (-126954623977543981122457873077/112589990684262400000000000000000000), (-1094197675868504727890680301/28147497671065600000000000000000000), (364249402869166011403542837/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial166.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial166.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial166.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 87565307790214706338844239616231542), (Int.ofNat 3540707824086314084662269411863641), (Int.negOfNat 449047238770774639263216266018565), (Int.negOfNat 56249517828213728442852566224544), (Int.ofNat 30033753872796521305528661161994), (Int.ofNat 1859083400876975609315368788297), (Int.negOfNat 855758163144055260109491674813), (Int.negOfNat 21067983933323357074019601703), (Int.ofNat 13030816576763277494000794137), (Int.ofNat 20200056260152302666922510), (Int.negOfNat 115175330193222694206764617), (Int.ofNat 1132744305410521446549532), (Int.ofNat 668951248206674011063353), (Int.negOfNat 10471811625353174799360), (Int.negOfNat 2773245515558912716935), (Int.ofNat 51704055271505218913), (Int.ofNat 9304460499750085620), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-43782653895107353169422119808115771/56294995342131200000000000000000000), (3540707824086314084662269411863641/112589990684262400000000000000000000), (-89809447754154927852643253203713/22517998136852480000000000000000000), (-1757797432131679013839142694517/3518437208883200000000000000000000), (15016876936398260652764330580997/56294995342131200000000000000000000), (1859083400876975609315368788297/112589990684262400000000000000000000), (-855758163144055260109491674813/112589990684262400000000000000000000), (-21067983933323357074019601703/112589990684262400000000000000000000), (13030816576763277494000794137/112589990684262400000000000000000000), (2020005626015230266692251/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial166.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial166.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial166.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 82244278510536675319726370226050911), (Int.ofNat 2018416166887359101701349458742803), (Int.negOfNat 114355277862629836812425040678579), (Int.ofNat 131473393659001066979331767646175), (Int.ofNat 4634210544884241371834679381094), (Int.negOfNat 5134725526650483563887488434044), (Int.negOfNat 12603610789211154859221653705), (Int.ofNat 100462298679192303058277399262), (Int.negOfNat 1440386699606410825873309023), (Int.negOfNat 1126645613747103601809111247), (Int.ofNat 26710458617304635323852176), (Int.ofNat 7968661813908749902525651), (Int.negOfNat 228051979884436127993335), (Int.negOfNat 38865970073354810575112), (Int.ofNat 1212546805912693822616), (Int.ofNat 142485322950241368221), (Int.negOfNat 5250894755529444980), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-82244278510536675319726370226050911/112589990684262400000000000000000000), (2018416166887359101701349458742803/112589990684262400000000000000000000), (-114355277862629836812425040678579/112589990684262400000000000000000000), (5258935746360042679173270705847/4503599627370496000000000000000000), (2317105272442120685917339690547/56294995342131200000000000000000000), (-1283681381662620890971872108511/28147497671065600000000000000000000), (-2520722157842230971844330741/22517998136852480000000000000000000), (50231149339596151529138699631/56294995342131200000000000000000000), (-1440386699606410825873309023/112589990684262400000000000000000000), (-1126645613747103601809111247/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial166.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial166.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial166.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 77692094582697376122947173624264790), (Int.ofNat 2914927955745916130300039910365717), (Int.ofNat 432152176495886779514428862980696), (Int.ofNat 9473279188767192250579942833531), (Int.negOfNat 24841642541298248286382521943315), (Int.ofNat 652955895279092431395081135884), (Int.ofNat 662211734743767839468480320083), (Int.negOfNat 26425546590236749942484380820), (Int.negOfNat 9472349872613194382620161066), (Int.ofNat 428109333950793508278290833), (Int.ofNat 82550157311526161578097086), (Int.negOfNat 3934885101601422570739106), (Int.negOfNat 478782744123204444956334), (Int.ofNat 23342424647574144754515), (Int.ofNat 1981039698635736855524), (Int.negOfNat 97341165721944916666), (Int.negOfNat 7176729494760789300), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-7769209458269737612294717362426479/11258999068426240000000000000000000), (2914927955745916130300039910365717/112589990684262400000000000000000000), (54019022061985847439303607872587/14073748835532800000000000000000000), (9473279188767192250579942833531/112589990684262400000000000000000000), (-4968328508259649657276504388663/22517998136852480000000000000000000), (163238973819773107848770283971/28147497671065600000000000000000000), (662211734743767839468480320083/112589990684262400000000000000000000), (-1321277329511837497124219041/5629499534213120000000000000000000), (-4736174936306597191310080533/56294995342131200000000000000000000), (428109333950793508278290833/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial166.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial166.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial166.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 70397547340522260594545124952763910), (Int.ofNat 4121480619194404759906565967154399), (Int.ofNat 72012214815003676477641290942144), (Int.negOfNat 85603049816753795422873892809398), (Int.ofNat 6031432523653325077059061536146), (Int.ofNat 3509385568246857840923146096056), (Int.negOfNat 283716563108764048579753852117), (Int.negOfNat 66752045171148230184423600180), (Int.ofNat 5353189746737648131444206934), (Int.ofNat 726915769219612846490781367), (Int.negOfNat 56861413537299259804656514), (Int.negOfNat 5069069153378236040162894), (Int.ofNat 388384602733167935670466), (Int.ofNat 24459635888127774285485), (Int.negOfNat 1844027340400944476476), (Int.negOfNat 87471905788936478134), (Int.ofNat 6770009595022491700), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-7039754734052226059454512495276391/11258999068426240000000000000000000), (4121480619194404759906565967154399/112589990684262400000000000000000000), (1125190856484432444963145170971/1759218604441600000000000000000000), (-42801524908376897711436946404699/56294995342131200000000000000000000), (3015716261826662538529530768073/56294995342131200000000000000000000), (438673196030857230115393262007/14073748835532800000000000000000000), (-283716563108764048579753852117/112589990684262400000000000000000000), (-3337602258557411509221180009/5629499534213120000000000000000000), (2676594873368824065722103467/56294995342131200000000000000000000), (726915769219612846490781367/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial166.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial166.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial166.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 62367584756219996116055600308887783), (Int.ofNat 3778489940183816065059289908442909), (Int.negOfNat 116876045446096711573111227283374), (Int.ofNat 32710749265607789116475681173676), (Int.ofNat 13415971811402098562792273952809), (Int.negOfNat 2201770435850435253348186394056), (Int.negOfNat 369439111547499457377953057505), (Int.ofNat 53840662960886008239327567338), (Int.ofNat 5192165259138257197077322577), (Int.negOfNat 697649061879095429995645353), (Int.negOfNat 44081745695097696612679824), (Int.ofNat 5628782870615357070291549), (Int.ofNat 249122980708910372736665), (Int.negOfNat 30958791727333729883688), (Int.negOfNat 1002747973920910264584), (Int.ofNat 124286372038726923379), (Int.ofNat 4289441070024969620), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-62367584756219996116055600308887783/112589990684262400000000000000000000), (3778489940183816065059289908442909/112589990684262400000000000000000000), (-58438022723048355786555613641687/56294995342131200000000000000000000), (8177687316401947279118920293419/28147497671065600000000000000000000), (13415971811402098562792273952809/112589990684262400000000000000000000), (-275221304481304406668523299257/14073748835532800000000000000000000), (-73887822309499891475590611501/22517998136852480000000000000000000), (26920331480443004119663783669/56294995342131200000000000000000000), (5192165259138257197077322577/112589990684262400000000000000000000), (-697649061879095429995645353/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial166.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial166.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial166.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 54888037526315572880555715285570951), (Int.ofNat 3913424007708325116196555830466002), (Int.ofNat 178497581029014771199634084990893), (Int.ofNat 28141165107648354521917047065766), (Int.negOfNat 13025525607923504071141074925713), (Int.negOfNat 1367418024041374432762331897344), (Int.ofNat 439623697309838437964884698187), (Int.ofNat 26540716511443806542638241103), (Int.negOfNat 7258529172515688995254005463), (Int.negOfNat 279461019912510415778547110), (Int.ofNat 71052211226060654888529783), (Int.ofNat 1837982586441335070222468), (Int.negOfNat 459978828295696995385047), (Int.negOfNat 8208608222740843544240), (Int.ofNat 2118277723156586523065), (Int.ofNat 24711973175916080687), (Int.negOfNat 6845480222147628580), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-54888037526315572880555715285570951/112589990684262400000000000000000000), (1956712003854162558098277915233001/56294995342131200000000000000000000), (178497581029014771199634084990893/112589990684262400000000000000000000), (14070582553824177260958523532883/56294995342131200000000000000000000), (-13025525607923504071141074925713/112589990684262400000000000000000000), (-2670738328205809438988929487/219902325555200000000000000000000), (439623697309838437964884698187/112589990684262400000000000000000000), (26540716511443806542638241103/112589990684262400000000000000000000), (-7258529172515688995254005463/112589990684262400000000000000000000), (-27946101991251041577854711/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial166.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial166.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial166.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 46344629186254545899804471053671751), (Int.ofNat 4527492424298322945205868300764173), (Int.ofNat 35227199587856660800901601165111), (Int.negOfNat 58950461965655101001334274052646), (Int.negOfNat 1173753731380015576844405327179), (Int.ofNat 2902428482203643282299953683274), (Int.ofNat 48976536934981330753837234469), (Int.negOfNat 63553619703863897488553286323), (Int.negOfNat 650418548778179809540740004), (Int.ofNat 775747614880696448499509252), (Int.ofNat 3990338056003730480585602), (Int.negOfNat 6018910133231374244368261), (Int.negOfNat 9365405855538906404612), (Int.ofNat 32257815696974765257316), (Int.negOfNat 33110956434861095951), (Int.negOfNat 127233098457148594379), (Int.negOfNat 984638621853319820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-46344629186254545899804471053671751/112589990684262400000000000000000000), (4527492424298322945205868300764173/112589990684262400000000000000000000), (35227199587856660800901601165111/112589990684262400000000000000000000), (-29475230982827550500667137026323/56294995342131200000000000000000000), (-1173753731380015576844405327179/112589990684262400000000000000000000), (1451214241101821641149976841637/56294995342131200000000000000000000), (48976536934981330753837234469/112589990684262400000000000000000000), (-63553619703863897488553286323/112589990684262400000000000000000000), (-162604637194544952385185001/28147497671065600000000000000000000), (193936903720174112124877313/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial166.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial166.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial166.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 37551019291923822300429020169288389), (Int.ofNat 4137636692740673923928279036708117), (Int.negOfNat 143115073025109620181953822338702), (Int.ofNat 22822928582224177253137033542092), (Int.ofNat 15203094924467646096994873855492), (Int.negOfNat 712354663927287813479513017611), (Int.negOfNat 461697875669935996810152651055), (Int.ofNat 12891421003602235780663409475), (Int.ofNat 7236409731743899848475200297), (Int.negOfNat 155748170049747731930391057), (Int.negOfNat 68666072184030345009196498), (Int.ofNat 1295845495827507854170040), (Int.ofNat 435634660159281943453308), (Int.negOfNat 7614980449615142046065), (Int.negOfNat 1970272403057957245691), (Int.ofNat 34291812414135667560), (Int.ofNat 5819350033215548860), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-37551019291923822300429020169288389/112589990684262400000000000000000000), (4137636692740673923928279036708117/112589990684262400000000000000000000), (-71557536512554810090976911169351/56294995342131200000000000000000000), (5705732145556044313284258385523/28147497671065600000000000000000000), (3800773731116911524248718463873/28147497671065600000000000000000000), (-712354663927287813479513017611/112589990684262400000000000000000000), (-92339575133987199362030530211/22517998136852480000000000000000000), (515656840144089431226536379/4503599627370496000000000000000000), (7236409731743899848475200297/112589990684262400000000000000000000), (-155748170049747731930391057/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial166.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial166.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial166.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 29471360353761173662689655317952278), (Int.ofNat 4192415923745639565739917272244563), (Int.ofNat 211086893923588757664965856407958), (Int.ofNat 60476862589771084825484492551199), (Int.negOfNat 9353531766409044399528441758478), (Int.negOfNat 2717549940908232791875225608776), (Int.ofNat 235741204173121059259774454248), (Int.ofNat 56595006335900566377116069420), (Int.negOfNat 3412654039158361461964342820), (Int.negOfNat 671734841399634418140300639), (Int.ofNat 31922182802121684153463080), (Int.ofNat 5126821202600610916341667), (Int.negOfNat 206100255539172876875037), (Int.negOfNat 27213965033165119968007), (Int.ofNat 957947348235492033140), (Int.ofNat 107463721761804546899), (Int.negOfNat 2320163826318329980), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-14735680176880586831344827658976139/56294995342131200000000000000000000), (4192415923745639565739917272244563/112589990684262400000000000000000000), (105543446961794378832482928203979/56294995342131200000000000000000000), (60476862589771084825484492551199/112589990684262400000000000000000000), (-4676765883204522199764220879239/56294995342131200000000000000000000), (-339693742613529098984403201097/14073748835532800000000000000000000), (29467650521640132407471806781/14073748835532800000000000000000000), (2829750316795028318855803471/5629499534213120000000000000000000), (-170632701957918073098217141/5629499534213120000000000000000000), (-671734841399634418140300639/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial166.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial166.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial166.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 19973827965995540420836218219591741), (Int.ofNat 5311558288845051271402170519981772), (Int.ofNat 217952497077224430815980578718107), (Int.negOfNat 62691719872322361826253340291068), (Int.negOfNat 12457797815574472429366454318366), (Int.ofNat 2362666678892545611729014705347), (Int.ofNat 360314544715885697642043702096), (Int.negOfNat 44661637217395659879516921243), (Int.negOfNat 5485532269548464036758662618), (Int.ofNat 509628963665549797733392526), (Int.ofNat 51274427833181623646027101), (Int.negOfNat 3861645654521915369864136), (Int.negOfNat 323091873325174466933306), (Int.ofNat 20671599076927052478590), (Int.ofNat 1461999129310039296740), (Int.negOfNat 84251528445859117807), (Int.negOfNat 4793219844283469140), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-19973827965995540420836218219591741/112589990684262400000000000000000000), (1327889572211262817850542629995443/28147497671065600000000000000000000), (217952497077224430815980578718107/112589990684262400000000000000000000), (-15672929968080590456563335072767/28147497671065600000000000000000000), (-6228898907787236214683227159183/56294995342131200000000000000000000), (2362666678892545611729014705347/112589990684262400000000000000000000), (22519659044742856102627731381/7036874417766400000000000000000000), (-44661637217395659879516921243/112589990684262400000000000000000000), (-2742766134774232018379331309/56294995342131200000000000000000000), (254814481832774898866696263/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial166.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial166.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial166.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 9087911051913945923168590677664834), (Int.ofNat 5266372755387752339655804844073555), (Int.negOfNat 218726598329834490336950179025398), (Int.negOfNat 41702895069032110566488252342374), (Int.ofNat 16687387438785181574243381331685), (Int.ofNat 1779319918734063938720930523106), (Int.negOfNat 435350961763901130594062092133), (Int.negOfNat 35643818984695311352721916244), (Int.ofNat 6313033575371069771312352157), (Int.ofNat 415368896908720404577800270), (Int.negOfNat 57946217479979477839088875), (Int.negOfNat 3154473954243666137423396), (Int.ofNat 364154821768618846596982), (Int.ofNat 16788406906232480701218), (Int.negOfNat 1655957830688620707821), (Int.negOfNat 67724915296703345706), (Int.ofNat 5282922878179286540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-4543955525956972961584295338832417/56294995342131200000000000000000000), (1053274551077550467931160968814711/22517998136852480000000000000000000), (-109363299164917245168475089512699/56294995342131200000000000000000000), (-20851447534516055283244126171187/56294995342131200000000000000000000), (3337477487757036314848676266337/22517998136852480000000000000000000), (889659959367031969360465261553/56294995342131200000000000000000000), (-435350961763901130594062092133/112589990684262400000000000000000000), (-8910954746173827838180479061/28147497671065600000000000000000000), (6313033575371069771312352157/112589990684262400000000000000000000), (41536889690872040457780027/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial166.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial166.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial166.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 529581079439045066945125007187988), (Int.ofNat 4474916777484321209538323793126928), (Int.negOfNat 42040717073391177361455245356634), (Int.ofNat 85919595456822555053759197493701), (Int.ofNat 6263038685921690615290993875239), (Int.negOfNat 3293296102052950760972490990387), (Int.negOfNat 165680539528855746563965550267), (Int.ofNat 63167240962528105996038858156), (Int.ofNat 2419020553342020507157677843), (Int.negOfNat 722576707418574447532714530), (Int.negOfNat 22420943364432873527762325), (Int.ofNat 5446391053486019506180204), (Int.ofNat 142830218427994962764618), (Int.negOfNat 28904256131234477911982), (Int.negOfNat 659168573227694707779), (Int.ofNat 114273128610066363094), (Int.ofNat 1905931419547649460), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(132395269859761266736281251796997/28147497671065600000000000000000000), (279682298592770075596145237070433/7036874417766400000000000000000000), (-21020358536695588680727622678317/56294995342131200000000000000000000), (85919595456822555053759197493701/112589990684262400000000000000000000), (6263038685921690615290993875239/112589990684262400000000000000000000), (-3293296102052950760972490990387/112589990684262400000000000000000000), (-165680539528855746563965550267/112589990684262400000000000000000000), (15791810240632026499009714539/28147497671065600000000000000000000), (2419020553342020507157677843/112589990684262400000000000000000000), (-72257670741857444753271453/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial166.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial166.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial166.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 9991151372226376174600898075253086), (Int.ofNat 5271991602393305218317502907815789), (Int.ofNat 363916376008242901834336806472349), (Int.ofNat 13500162921160550593467571256956), (Int.negOfNat 19192164138587656331565590444626), (Int.negOfNat 363528994669341696528084917506), (Int.ofNat 511096819836059361745464797504), (Int.ofNat 5402841561899485112601511957), (Int.negOfNat 7523110975833747430292949382), (Int.negOfNat 56811891718848209549806674), (Int.ofNat 69606386433855415466538499), (Int.ofNat 452977593550440800391464), (Int.negOfNat 438880409973122302859494), (Int.negOfNat 2714783788449307152610), (Int.ofNat 1992409943180143730860), (Int.ofNat 14465016530414997793), (Int.negOfNat 6802037717672333260), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(4995575686113188087300449037626543/56294995342131200000000000000000000), (5271991602393305218317502907815789/112589990684262400000000000000000000), (363916376008242901834336806472349/112589990684262400000000000000000000), (3375040730290137648366892814239/28147497671065600000000000000000000), (-9596082069293828165782795222313/56294995342131200000000000000000000), (-181764497334670848264042458753/56294995342131200000000000000000000), (7985887809938427527272887461/1759218604441600000000000000000000), (5402841561899485112601511957/112589990684262400000000000000000000), (-3761555487916873715146474691/56294995342131200000000000000000000), (-28405945859424104774903337/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial166.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial166.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial166.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 21811611003765076489289829636859446), (Int.ofNat 6339494776008705476977213536034663), (Int.ofNat 68559102867203952814956799478973), (Int.negOfNat 82524528997756099443995970458809), (Int.ofNat 1596261879863362987193958262881), (Int.ofNat 3269918020726252160293285100064), (Int.negOfNat 78496875621521152377823995848), (Int.negOfNat 64498786249936018727368409380), (Int.ofNat 1364710770133037255599276020), (Int.ofNat 753350907197938472839330961), (Int.negOfNat 12786764178575487235345880), (Int.negOfNat 5765815888981146304658733), (Int.ofNat 75258901263578742949437), (Int.ofNat 30915024435024506522793), (Int.negOfNat 304650208652601521540), (Int.negOfNat 122564594961629823901), (Int.ofNat 1740914424934693580), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(10905805501882538244644914818429723/56294995342131200000000000000000000), (6339494776008705476977213536034663/112589990684262400000000000000000000), (68559102867203952814956799478973/112589990684262400000000000000000000), (-82524528997756099443995970458809/112589990684262400000000000000000000), (1596261879863362987193958262881/112589990684262400000000000000000000), (102184938147695380009165159377/3518437208883200000000000000000000), (-9812109452690144047227999481/14073748835532800000000000000000000), (-3224939312496800936368420469/5629499534213120000000000000000000), (68235538506651862779963801/5629499534213120000000000000000000), (753350907197938472839330961/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial166.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial166.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial166.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 34222249389640764839451594677049963), (Int.ofNat 5895150007120635862129467051235314), (Int.negOfNat 183249633885131155594533619923097), (Int.ofNat 18436177210124528472011180173017), (Int.ofNat 15696771796314715231785238421881), (Int.negOfNat 1216245339133183456149589645158), (Int.negOfNat 439873561991306349510160800785), (Int.ofNat 28081273731508040849204654675), (Int.ofNat 6730417328036453718266805703), (Int.negOfNat 339758079368627538150207457), (Int.negOfNat 64299297281094709704915502), (Int.ofNat 2530377569601499588109240), (Int.ofNat 415734458377179878458292), (Int.negOfNat 12769204603841587486065), (Int.negOfNat 1923896144164309534709), (Int.ofNat 45735349043583211960), (Int.ofNat 5775907528740253540), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(34222249389640764839451594677049963/112589990684262400000000000000000000), (2947575003560317931064733525617657/56294995342131200000000000000000000), (-183249633885131155594533619923097/112589990684262400000000000000000000), (18436177210124528472011180173017/112589990684262400000000000000000000), (15696771796314715231785238421881/112589990684262400000000000000000000), (-608122669566591728074794822579/56294995342131200000000000000000000), (-87974712398261269902032160157/22517998136852480000000000000000000), (1123250949260321633968186187/4503599627370496000000000000000000), (6730417328036453718266805703/112589990684262400000000000000000000), (-339758079368627538150207457/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial166.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial166.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial166.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 45616201218146018542660184079571710), (Int.ofNat 5722325121374598016929026692022437), (Int.ofNat 129942510302226994571687323866908), (Int.ofNat 50101667809633183207939561098529), (Int.negOfNat 9538260992696839400171285506384), (Int.negOfNat 2213150956991289922688544606006), (Int.ofNat 320588850781568105290325576531), (Int.ofNat 46877360732673440438184113677), (Int.negOfNat 5163881073259351554208502396), (Int.negOfNat 583194704482399824576671148), (Int.ofNat 48487836539286046044402798), (Int.ofNat 4703632988533718413785339), (Int.negOfNat 296973678407537112575388), (Int.negOfNat 26225851799222569474284), (Int.ofNat 1280332746500226336751), (Int.ofNat 106761458440661774421), (Int.negOfNat 5045716873106343380), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(4561620121814601854266018407957171/11258999068426240000000000000000000), (5722325121374598016929026692022437/112589990684262400000000000000000000), (32485627575556748642921830966727/28147497671065600000000000000000000), (50101667809633183207939561098529/112589990684262400000000000000000000), (-596141312043552462510705344149/7036874417766400000000000000000000), (-1106575478495644961344272303003/56294995342131200000000000000000000), (320588850781568105290325576531/112589990684262400000000000000000000), (46877360732673440438184113677/112589990684262400000000000000000000), (-1290970268314837888552125599/28147497671065600000000000000000000), (-145798676120599956144167787/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial166.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial166.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial166.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 57782957154918643507932223987150880), (Int.ofNat 6437254085006682530597876226862463), (Int.ofNat 121751384345789319114571268224730), (Int.negOfNat 48670397002807724741358569330978), (Int.negOfNat 6639068919850501831661683707561), (Int.ofNat 2575405305183232377116729215090), (Int.ofNat 216961179583748402045626941413), (Int.negOfNat 58040284928113409845047288897), (Int.negOfNat 3840335531215640805782301737), (Int.ofNat 707001140415551438243355290), (Int.ofNat 41509929576222275901743817), (Int.negOfNat 5334630187091561440871532), (Int.negOfNat 293810699199527316334153), (Int.ofNat 27320204080989028809760), (Int.ofNat 1447547549937213678935), (Int.negOfNat 101298048323481990113), (Int.negOfNat 4749777339808173820), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(361143482218241521924576399919693/703687441776640000000000000000000), (6437254085006682530597876226862463/112589990684262400000000000000000000), (12175138434578931911457126822473/11258999068426240000000000000000000), (-24335198501403862370679284665489/56294995342131200000000000000000000), (-6639068919850501831661683707561/112589990684262400000000000000000000), (257540530518323237711672921509/11258999068426240000000000000000000), (216961179583748402045626941413/112589990684262400000000000000000000), (-58040284928113409845047288897/112589990684262400000000000000000000), (-3840335531215640805782301737/112589990684262400000000000000000000), (70700114041555143824335529/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial166.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial166.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial166.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 70737161392319808545035820661333139), (Int.ofNat 6347294817358696611156343224638138), (Int.negOfNat 113819714284620017396011496277976), (Int.ofNat 751482415196296635123909808874), (Int.ofNat 14737322180885023487932514055274), (Int.ofNat 165748660944189485483050182384), (Int.negOfNat 500566543938713117869334018895), (Int.negOfNat 9996909834953047496416895862), (Int.ofNat 8295058136506967634399114623), (Int.ofNat 213531832060213038492319047), (Int.negOfNat 79351150883180775723485376), (Int.negOfNat 2328798134479151249753651), (Int.ofNat 490172544463576751994135), (Int.ofNat 15328719273470943605512), (Int.negOfNat 2125575530939975484616), (Int.negOfNat 69610392391170779421), (Int.ofNat 8350519321277993180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(70737161392319808545035820661333139/112589990684262400000000000000000000), (3173647408679348305578171612319069/56294995342131200000000000000000000), (-14227464285577502174501437034747/14073748835532800000000000000000000), (375741207598148317561954904437/56294995342131200000000000000000000), (7368661090442511743966257027637/56294995342131200000000000000000000), (10359291309011842842690636399/7036874417766400000000000000000000), (-100113308787742623573866803779/22517998136852480000000000000000000), (-4998454917476523748208447931/56294995342131200000000000000000000), (8295058136506967634399114623/112589990684262400000000000000000000), (213531832060213038492319047/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial166.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial166.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial166.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 83192418212833275422985760675302723), (Int.ofNat 6293866772527572180533310496477754), (Int.ofNat 145694644227561619481358052251599), (Int.ofNat 54344600177513046206164576776296), (Int.negOfNat 7386332988024941278693770574124), (Int.negOfNat 3190453150524547726273499152331), (Int.ofNat 161571318495768619337390074717), (Int.ofNat 78102138775547487612631723420), (Int.negOfNat 1145694247070017774662987334), (Int.negOfNat 994949570823006274754284633), (Int.negOfNat 2877252349273398438794286), (Int.ofNat 7591064929186929535677106), (Int.ofNat 87257577479307510343134), (Int.negOfNat 38944608193225799296915), (Int.negOfNat 624403238006068377524), (Int.ofNat 146935158773921687866), (Int.ofNat 2622046334818877500), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(83192418212833275422985760675302723/112589990684262400000000000000000000), (3146933386263786090266655248238877/56294995342131200000000000000000000), (145694644227561619481358052251599/112589990684262400000000000000000000), (6793075022189130775770572097037/14073748835532800000000000000000000), (-1846583247006235319673442643531/28147497671065600000000000000000000), (-3190453150524547726273499152331/112589990684262400000000000000000000), (161571318495768619337390074717/112589990684262400000000000000000000), (3905106938777374380631586171/5629499534213120000000000000000000), (-572847123535008887331493667/56294995342131200000000000000000000), (-994949570823006274754284633/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial166.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial166.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial166.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 96596958867016933240844631818701177), (Int.ofNat 7099798350313351936532381152183132), (Int.ofNat 124058133294776527049196655489761), (Int.negOfNat 69902826248005110652564209405375), (Int.negOfNat 12744246053023172632880840000007), (Int.ofNat 2986978550802711164721942729997), (Int.ofNat 557146191891551480480700372717), (Int.negOfNat 48275947659839534937475849220), (Int.negOfNat 10461914720688739994502668534), (Int.ofNat 333446798239413685158086833), (Int.ofNat 102334285414654412322801714), (Int.negOfNat 1076287456572337169813106), (Int.negOfNat 631148619245744817393266), (Int.ofNat 241309728400206652115), (Int.ofNat 2721551437508329038476), (Int.ofNat 14596975229865889334), (Int.negOfNat 9869634160771039900), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(96596958867016933240844631818701177/112589990684262400000000000000000000), (1774949587578337984133095288045783/28147497671065600000000000000000000), (124058133294776527049196655489761/112589990684262400000000000000000000), (-559222609984040885220513675243/900719925474099200000000000000000), (-12744246053023172632880840000007/112589990684262400000000000000000000), (2986978550802711164721942729997/112589990684262400000000000000000000), (557146191891551480480700372717/112589990684262400000000000000000000), (-2413797382991976746873792461/5629499534213120000000000000000000), (-5230957360344369997251334267/56294995342131200000000000000000000), (333446798239413685158086833/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial166.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial166.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial166.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 110652311424504417059456424427276208), (Int.ofNat 6664235724881458440013469268466832), (Int.negOfNat 277093049160345120908834740817231), (Int.negOfNat 5766547346889349775730507560080), (Int.ofNat 27916944250376363546457079865323), (Int.ofNat 2335097720825362183064440680343), (Int.negOfNat 773655735769984654766452083895), (Int.negOfNat 89892584414846164010233299938), (Int.ofNat 8057325942831665531790713823), (Int.ofNat 1201602902824164330468449153), (Int.negOfNat 46861434209676322636218976), (Int.negOfNat 9104741394752632107011549), (Int.ofNat 173351313375075664174535), (Int.ofNat 46194260590238838618088), (Int.negOfNat 417437313950996513416), (Int.negOfNat 173880365090703694579), (Int.ofNat 265242089916942180), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(6915769464031526066216026526704763/7036874417766400000000000000000000), (416514732805091152500841829279177/7036874417766400000000000000000000), (-277093049160345120908834740817231/112589990684262400000000000000000000), (-72081841836116872196631344501/1407374883553280000000000000000000), (27916944250376363546457079865323/112589990684262400000000000000000000), (2335097720825362183064440680343/112589990684262400000000000000000000), (-154731147153996930953290416779/22517998136852480000000000000000000), (-44946292207423082005116649969/56294995342131200000000000000000000), (8057325942831665531790713823/112589990684262400000000000000000000), (1201602902824164330468449153/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial166.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial166.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial166.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 123289264655550076051196129693757013), (Int.ofNat 6388684553382535741349588603614755), (Int.ofNat 318235227464368237785221119404242), (Int.ofNat 156674748654910223826824847952412), (Int.negOfNat 7428700116155883540134365431633), (Int.negOfNat 9082882310824060355117219885556), (Int.negOfNat 594661022506967568751353906787), (Int.ofNat 128008167114023951918692584297), (Int.ofNat 12294341537987131776762315063), (Int.negOfNat 983029157544885219615469090), (Int.negOfNat 117402480203164212623326983), (Int.ofNat 4960362614841394861571532), (Int.ofNat 706414522966270391783847), (Int.negOfNat 17965179445139222501360), (Int.negOfNat 3006929624239513445065), (Int.ofNat 48162957383154508113), (Int.ofNat 9945104787896176780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(123289264655550076051196129693757013/112589990684262400000000000000000000), (1277736910676507148269917720722951/22517998136852480000000000000000000), (159117613732184118892610559702121/56294995342131200000000000000000000), (39168687163727555956706211988103/28147497671065600000000000000000000), (-7428700116155883540134365431633/112589990684262400000000000000000000), (-2270720577706015088779304971389/28147497671065600000000000000000000), (-594661022506967568751353906787/112589990684262400000000000000000000), (128008167114023951918692584297/112589990684262400000000000000000000), (12294341537987131776762315063/112589990684262400000000000000000000), (-98302915754488521961546909/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial166.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial166.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial166.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 138164324644078450993952038587679638), (Int.ofNat 8530341557318172277633535515036109), (Int.ofNat 312999857545267827871714791547603), (Int.negOfNat 274306210741000701068183113833893), (Int.negOfNat 89577103843088310598515564536386), (Int.negOfNat 2677266199833660860112936880714), (Int.ofNat 1628406188421489617519866869691), (Int.ofNat 111390692254899322232483354923), (Int.negOfNat 15637346813729299593097406396), (Int.negOfNat 1365820554209411832103611052), (Int.ofNat 98151044000748293242519198), (Int.ofNat 9806612857549609159178261), (Int.negOfNat 441933030858068034312588), (Int.negOfNat 48212011907986736879716), (Int.ofNat 1509222792488756463951), (Int.ofNat 176827091509125365579), (Int.negOfNat 3570044538088591980), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(69082162322039225496976019293839819/56294995342131200000000000000000000), (8530341557318172277633535515036109/112589990684262400000000000000000000), (312999857545267827871714791547603/112589990684262400000000000000000000), (-274306210741000701068183113833893/112589990684262400000000000000000000), (-44788551921544155299257782268193/56294995342131200000000000000000000), (-1338633099916830430056468440357/56294995342131200000000000000000000), (1628406188421489617519866869691/112589990684262400000000000000000000), (111390692254899322232483354923/112589990684262400000000000000000000), (-3909336703432324898274351599/28147497671065600000000000000000000), (-341455138552352958025902763/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial166.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial166.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial166.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 152877543282491692736125395114992799), (Int.ofNat 3754015144629106602274286711090588), (Int.negOfNat 3264143003249081139627507213570162), (Int.negOfNat 808595328764866632502708321210303), (Int.negOfNat 8815090981758546224383110329205), (Int.ofNat 17484203207762018311563889471664), (Int.ofNat 958269579003347014901298097655), (Int.negOfNat 205058127754232715594182692875), (Int.negOfNat 14680772662515574402358141897), (Int.ofNat 1569304892978039200296453257), (Int.ofNat 124733240624947774040539698), (Int.negOfNat 8529197428209093003798040), (Int.negOfNat 708105529339961433700108), (Int.ofNat 34726552709673081043665), (Int.ofNat 2916073310782201577691), (Int.negOfNat 107166742973206256360), (Int.negOfNat 8918974598964097060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(152877543282491692736125395114992799/112589990684262400000000000000000000), (938503786157276650568571677772647/28147497671065600000000000000000000), (-1632071501624540569813753606785081/56294995342131200000000000000000000), (-808595328764866632502708321210303/112589990684262400000000000000000000), (-1763018196351709244876622065841/22517998136852480000000000000000000), (1092762700485126144472743091979/7036874417766400000000000000000000), (191653915800669402980259619531/22517998136852480000000000000000000), (-1640465022033861724753461543/900719925474099200000000000000000), (-14680772662515574402358141897/112589990684262400000000000000000000), (1569304892978039200296453257/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial166.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial166.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial166.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 141310926681324920382089743663307124), (Int.negOfNat 17807815872155269790524401680969830), (Int.negOfNat 6854276442245354615029694401173020), (Int.negOfNat 157640740246805941451244158946090), (Int.ofNat 157233554040603123362492835628730), (Int.ofNat 9041178611136055071835330333716), (Int.negOfNat 2241563858047389032543104675648), (Int.negOfNat 152340485818312687054654210020), (Int.ofNat 21026086440134397193657457220), (Int.ofNat 1478932720981297551458902439), (Int.negOfNat 138042938947353272682315880), (Int.negOfNat 9580593903527953269663667), (Int.ofNat 666548054434241954444237), (Int.ofNat 44625183680800123698407), (Int.negOfNat 2456152941777778311140), (Int.negOfNat 157057714813781318099), (Int.ofNat 6874846986260241780), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(35327731670331230095522435915826781/28147497671065600000000000000000000), (-1780781587215526979052440168096983/11258999068426240000000000000000000), (-342713822112267730751484720058651/5629499534213120000000000000000000), (-15764074024680594145124415894609/11258999068426240000000000000000000), (15723355404060312336249283562873/11258999068426240000000000000000000), (2260294652784013767958832583429/28147497671065600000000000000000000), (-35024435281990453633486010557/1759218604441600000000000000000000), (-7617024290915634352732710501/5629499534213120000000000000000000), (1051304322006719859682872861/5629499534213120000000000000000000), (1478932720981297551458902439/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial166.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial166.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial166.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 79665140122748174372158646885011575), (Int.negOfNat 41836329384995746476328627124338037), (Int.negOfNat 3900884663046042799216865328392335), (Int.ofNat 1061104476140318348344977534227960), (Int.ofNat 97846371254677445225486884746992), (Int.negOfNat 19570082419157455045751679652487), (Int.negOfNat 1584033639853342790462306810696), (Int.ofNat 234441741449885399135632956643), (Int.ofNat 16696179626334321290372428218), (Int.negOfNat 1901077861302115824845874726), (Int.negOfNat 120681619281203643867104301), (Int.ofNat 11010589244552500448674136), (Int.ofNat 629266444198701416834106), (Int.negOfNat 47561997850811577208190), (Int.negOfNat 2470737635046857518740), (Int.ofNat 157126459004929706607), (Int.ofNat 7892844410032017340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3186605604909926974886345875400463/4503599627370496000000000000000000), (-41836329384995746476328627124338037/112589990684262400000000000000000000), (-780176932609208559843373065678467/22517998136852480000000000000000000), (26527611903507958708624438355699/2814749767106560000000000000000000), (6115398203417340326592930296687/7036874417766400000000000000000000), (-19570082419157455045751679652487/112589990684262400000000000000000000), (-198004204981667848807788351337/14073748835532800000000000000000000), (234441741449885399135632956643/112589990684262400000000000000000000), (8348089813167160645186214109/56294995342131200000000000000000000), (-950538930651057912422937363/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial166.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial166.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial166.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 10251089802739584749306898163313636), (Int.negOfNat 43328005965597231500844242089774095), (Int.ofNat 3045938640912376099881377512785334), (Int.ofNat 957280357096618727694697172604135), (Int.negOfNat 117314790825233142427304630217824), (Int.negOfNat 15839542924118088129102480326206), (Int.ofNat 2073213998486425550121403540773), (Int.ofNat 180043849773609864222035294844), (Int.negOfNat 22011566062088205321858166557), (Int.negOfNat 1428188576106884943304994070), (Int.ofNat 157236673856033984807975675), (Int.ofNat 8217320170772916060765396), (Int.negOfNat 807276072960220652390182), (Int.negOfNat 35517804351964845983618), (Int.ofNat 3123224929222937545821), (Int.ofNat 117318908348680116906), (Int.negOfNat 9837606038121198340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2562772450684896187326724540828409/28147497671065600000000000000000000), (-8665601193119446300168848417954819/22517998136852480000000000000000000), (1522969320456188049940688756392667/56294995342131200000000000000000000), (191456071419323745538939434520827/22517998136852480000000000000000000), (-3666087213288535700853269694307/3518437208883200000000000000000000), (-7919771462059044064551240163103/56294995342131200000000000000000000), (2073213998486425550121403540773/112589990684262400000000000000000000), (45010962443402466055508823711/28147497671065600000000000000000000), (-22011566062088205321858166557/112589990684262400000000000000000000), (-142818857610688494330499407/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial166.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial166.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial166.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial166.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial166.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial166.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial166.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial166.reflect := by
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

end Bin166
end
end ErdosOverlap.OuterNumerics
