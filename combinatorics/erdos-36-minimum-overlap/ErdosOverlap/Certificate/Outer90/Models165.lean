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

/-! # Exact integer weighted outer models for source bin 165

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin165

def weightDenominator : ℤ := (Int.ofNat 100000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 4109749107978806500)⟩, ⟨(731972361809/125000000000), (Int.negOfNat 17560297831101626000)⟩, ⟨(8483417085427/1000000000000), (Int.negOfNat 12272632226979277000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 4781734460409924000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 8617547821107781000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 7000307876985010000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 4943879189613701000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 3540945954838158000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 1937237713234260200)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 1121172874756669500)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial165.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial165.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 90561199785920010000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 35109135786685364000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 11536843230846884000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 9464234772136869000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 4823323908952229600)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 1815465611718686600)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 31863777464252773)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 349059883511521320)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 316692351773950830)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial165.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial165.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 90561199785920010000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 35109135786685364000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 11536843230846884000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 9464234772136869000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 4823323908952229600)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1815465611718686600)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 31863777464252773)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 349059883511521320)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 316692351773950830)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial165.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial165.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial165.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 39781833272138112510840331371735439), (Int.ofNat 39092442633686961820042450532368218), (Int.ofNat 3895039501034464020160822832031362), (Int.negOfNat 933805719768657033002701433441590), (Int.negOfNat 121196344288427155160860750737103), (Int.ofNat 16092028203875920323196476374583), (Int.ofNat 2073237937980931382130861328703), (Int.negOfNat 185054589520073189524932274834), (Int.negOfNat 21929522916796510047528146437), (Int.ofNat 1475718322027067937978251710), (Int.ofNat 156583020050688873995226085), (Int.negOfNat 8521031365288048046465276), (Int.negOfNat 803688241722876998777812), (Int.ofNat 36928502888969767402668), (Int.ofNat 3108277225497900439511), (Int.negOfNat 122239593814076451076), (Int.negOfNat 9792316081172834000), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-39781833272138112510840331371735439/112589990684262400000000000000000000), (19546221316843480910021225266184109/56294995342131200000000000000000000), (1947519750517232010080411416015681/56294995342131200000000000000000000), (-93380571976865703300270143344159/11258999068426240000000000000000000), (-121196344288427155160860750737103/112589990684262400000000000000000000), (16092028203875920323196476374583/112589990684262400000000000000000000), (2073237937980931382130861328703/112589990684262400000000000000000000), (-92527294760036594762466137417/56294995342131200000000000000000000), (-21929522916796510047528146437/112589990684262400000000000000000000), (147571832202706793797825171/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial165.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial165.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial165.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial165 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 45192849432382303421299767636506890), (Int.ofNat 41172800951306939241037373426573227), (Int.negOfNat 2986905497787969650346906996058949), (Int.negOfNat 1061004570344174981170989293785986), (Int.ofNat 95350955936457726386758666428170), (Int.ofNat 19521074977258498342288355783094), (Int.negOfNat 1619219420086955605435100727386), (Int.negOfNat 233295123976207137503501437993), (Int.ofNat 17195018178115002241336925848), (Int.ofNat 1888760361045870423102805016), (Int.negOfNat 124504615791199693773517161), (Int.negOfNat 10923713599857629475210626), (Int.ofNat 649797274151607601886716), (Int.ofNat 47124497212381454541120), (Int.negOfNat 2552952057975059010000), (Int.negOfNat 155492016605753052817), (Int.ofNat 8169618545923622060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(4519284943238230342129976763650689/11258999068426240000000000000000000), (41172800951306939241037373426573227/112589990684262400000000000000000000), (-2986905497787969650346906996058949/112589990684262400000000000000000000), (-530502285172087490585494646892993/56294995342131200000000000000000000), (9535095593645772638675866642817/11258999068426240000000000000000000), (9760537488629249171144177891547/56294995342131200000000000000000000), (-809609710043477802717550363693/56294995342131200000000000000000000), (-233295123976207137503501437993/112589990684262400000000000000000000), (2149377272264375280167115731/14073748835532800000000000000000000), (236095045130733802887850627/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial165.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial165.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial165.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial165 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 109124812763336991030495456934943192), (Int.ofNat 20711851406518162165752028880447133), (Int.negOfNat 6010385611922460854726899995226836), (Int.ofNat 131604181577741530632240213317845), (Int.ofNat 152921656770391291203749675251313), (Int.negOfNat 9243852375304331739300225468596), (Int.negOfNat 2223604720971145681119912505408), (Int.ofNat 156923528754952113717337622950), (Int.ofNat 20860601345122512809623042740), (Int.negOfNat 1521886960671419150765580729), (Int.negOfNat 136582756765255762283952840), (Int.ofNat 9849758939834468755142557), (Int.ofNat 657604147443188195756497), (Int.negOfNat 45856732018492822268747), (Int.negOfNat 2416768835836488908990), (Int.ofNat 161327681687221021529), (Int.ofNat 6745489808676776330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(13640601595417123878811932116867899/14073748835532800000000000000000000), (20711851406518162165752028880447133/112589990684262400000000000000000000), (-1502596402980615213681724998806709/28147497671065600000000000000000000), (26320836315548306126448042663569/22517998136852480000000000000000000), (152921656770391291203749675251313/112589990684262400000000000000000000), (-2310963093826082934825056367149/28147497671065600000000000000000000), (-34743823765174151267498632897/1759218604441600000000000000000000), (3138470575099042274346752459/2251799813685248000000000000000000), (1043030067256125640481152137/5629499534213120000000000000000000), (-1521886960671419150765580729/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial165.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial165.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial165.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial165 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 129592969026407029992701149871073636), (Int.ofNat 2064193555416002692856304980991929), (Int.negOfNat 2689251827824416686615595877594014), (Int.ofNat 744901601787032076383678140501701), (Int.negOfNat 13121999893270338093198710287802), (Int.negOfNat 17228652154012632195661925056691), (Int.ofNat 1001117459611720614796462997465), (Int.ofNat 203292290125018197357270741995), (Int.negOfNat 15112357696774543921351450677), (Int.negOfNat 1550035292765244290790888697), (Int.ofNat 127886419621107683985543028), (Int.ofNat 8381990557474257851916650), (Int.negOfNat 724704468126284500648688), (Int.negOfNat 33956280178455415573125), (Int.ofNat 2981554741284400204871), (Int.ofNat 104215621921993093040), (Int.negOfNat 9119695601245474550), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(32398242256601757498175287467768409/28147497671065600000000000000000000), (2064193555416002692856304980991929/112589990684262400000000000000000000), (-1344625913912208343307797938797007/56294995342131200000000000000000000), (744901601787032076383678140501701/112589990684262400000000000000000000), (-6560999946635169046599355143901/56294995342131200000000000000000000), (-17228652154012632195661925056691/112589990684262400000000000000000000), (200223491922344122959292599493/22517998136852480000000000000000000), (40658458025003639471454148399/22517998136852480000000000000000000), (-15112357696774543921351450677/112589990684262400000000000000000000), (-1550035292765244290790888697/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial165.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial165.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial165.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial165 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 128247868249147752368200703495831514), (Int.negOfNat 1287217602469839318824547051075325), (Int.ofNat 431250385665779102520856854768905), (Int.ofNat 191616852200406733110578184600288), (Int.negOfNat 89623347736104395549026337920456), (Int.ofNat 3163860729593878710608815447904), (Int.ofNat 1618791180343765492033700919711), (Int.negOfNat 115350485211928388875682797023), (Int.negOfNat 15438953144757790822178883276), (Int.ofNat 1398385149910498883289624212), (Int.ofNat 96134664932415710135302008), (Int.negOfNat 10005116781745366391952751), (Int.negOfNat 429081404010812751491058), (Int.ofNat 49102250280724497189866), (Int.ofNat 1451908079641958784171), (Int.negOfNat 179860602398411654189), (Int.negOfNat 3381971184406767830), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(64123934124573876184100351747915757/56294995342131200000000000000000000), (-51488704098793572752981882043013/4503599627370496000000000000000000), (86250077133155820504171370953781/22517998136852480000000000000000000), (5988026631262710409705568268759/3518437208883200000000000000000000), (-11202918467013049443628292240057/14073748835532800000000000000000000), (98870647799808709706525482747/3518437208883200000000000000000000), (1618791180343765492033700919711/112589990684262400000000000000000000), (-115350485211928388875682797023/112589990684262400000000000000000000), (-3859738286189447705544720819/28147497671065600000000000000000000), (349596287477624720822406053/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial165.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial165.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial165.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial165 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 127684317372596959530893056147179812), (Int.ofNat 369262880763670319567325269523339), (Int.negOfNat 26323521448435846816474594466435), (Int.negOfNat 223533268820048348478204029879586), (Int.negOfNat 3974735595209711736272270355764), (Int.ofNat 9255405510849283387114443141413), (Int.negOfNat 624413801212364598210059449097), (Int.negOfNat 126693605052175994214957433457), (Int.ofNat 12579564108039689443390954673), (Int.ofNat 960068083798981060781202530), (Int.negOfNat 119455260862302886045316433), (Int.negOfNat 4775308144158245290623482), (Int.ofNat 716958473493128359931067), (Int.ofNat 16982554814908854971260), (Int.negOfNat 3047397011928442346035), (Int.negOfNat 44363034453240777663), (Int.ofNat 10069772656567327040), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(31921079343149239882723264036794953/28147497671065600000000000000000000), (369262880763670319567325269523339/112589990684262400000000000000000000), (-5264704289687169363294918893287/22517998136852480000000000000000000), (-111766634410024174239102014939793/56294995342131200000000000000000000), (-993683898802427934068067588941/28147497671065600000000000000000000), (9255405510849283387114443141413/112589990684262400000000000000000000), (-624413801212364598210059449097/112589990684262400000000000000000000), (-126693605052175994214957433457/112589990684262400000000000000000000), (12579564108039689443390954673/112589990684262400000000000000000000), (96006808379898106078120253/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial165.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial165.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial165.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial165 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 126709263686198421909834479663016531), (Int.negOfNat 1967389474294620581701519649012613), (Int.negOfNat 931975774038413142310783651960181), (Int.negOfNat 30218774546885674599860293604535), (Int.ofNat 31887095853672442276740567406906), (Int.negOfNat 2338059767940892705092872153656), (Int.negOfNat 772263777822177201962626941325), (Int.ofNat 91619098709124234672435170858), (Int.ofNat 7842689892017125349948896813), (Int.negOfNat 1218860237331621574677465693), (Int.negOfNat 44558688086890745067205936), (Int.ofNat 9208577499287675269975549), (Int.ofNat 158524845839305599870265), (Int.negOfNat 46636866055571453036158), (Int.negOfNat 350984002680661559526), (Int.ofNat 175336680910920995189), (Int.ofNat 18452560136759330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(126709263686198421909834479663016531/112589990684262400000000000000000000), (-1967389474294620581701519649012613/112589990684262400000000000000000000), (-931975774038413142310783651960181/112589990684262400000000000000000000), (-6043754909377134919972058720907/22517998136852480000000000000000000), (15943547926836221138370283703453/56294995342131200000000000000000000), (-292257470992611588136609019207/14073748835532800000000000000000000), (-30890551112887088078505077653/4503599627370496000000000000000000), (45809549354562117336217585429/56294995342131200000000000000000000), (7842689892017125349948896813/112589990684262400000000000000000000), (-1218860237331621574677465693/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial165.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial165.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial165.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial165 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 119203866599355607749899695234576690), (Int.negOfNat 5326705208712612990204527854122167), (Int.negOfNat 650631305747303168809413556879126), (Int.ofNat 66310401275295788698571587248239), (Int.negOfNat 8513382530447334896080488796865), (Int.negOfNat 2939096138192413101282354505244), (Int.ofNat 555424636967880398288817435807), (Int.ofNat 46448075431987331898302271910), (Int.negOfNat 10558038758000185895804344384), (Int.negOfNat 308570467396919232846646183), (Int.ofNat 103081922862129099384314124), (Int.ofNat 879638426757422182902336), (Int.negOfNat 634573633973310863730306), (Int.ofNat 803069441665839521655), (Int.ofNat 2732479676215228989336), (Int.negOfNat 18637308757288695314), (Int.negOfNat 9898676837132510030), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(11920386659935560774989969523457669/11258999068426240000000000000000000), (-5326705208712612990204527854122167/112589990684262400000000000000000000), (-325315652873651584404706778439563/56294995342131200000000000000000000), (66310401275295788698571587248239/112589990684262400000000000000000000), (-1702676506089466979216097759373/22517998136852480000000000000000000), (-734774034548103275320588626311/28147497671065600000000000000000000), (555424636967880398288817435807/112589990684262400000000000000000000), (4644807543198733189830227191/11258999068426240000000000000000000), (-164969355593752904621942881/1759218604441600000000000000000000), (-308570467396919232846646183/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial165.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial165.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial165.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial165 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 106286885465161551462263716883285900), (Int.negOfNat 7524611217783305385450723923077889), (Int.negOfNat 546874143508680059162108673717324), (Int.negOfNat 23509298844183472544427629241792), (Int.negOfNat 3297410221422527444934812823356), (Int.ofNat 3071433123730953960732534914854), (Int.ofNat 139840535091227574079926085927), (Int.negOfNat 78180145167690037581243771390), (Int.negOfNat 904280554625870748557127904), (Int.ofNat 996890657587825292532833623), (Int.negOfNat 5164932003824774662422636), (Int.negOfNat 7594466534239398988944536), (Int.ofNat 101802472065957012344934), (Int.ofNat 38906886511751356962865), (Int.negOfNat 689798366888840046464), (Int.negOfNat 146628379859623805446), (Int.ofNat 2857277892924481330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(1062868854651615514622637168832859/1125899906842624000000000000000000), (-7524611217783305385450723923077889/112589990684262400000000000000000000), (-136718535877170014790527168429331/28147497671065600000000000000000000), (-367332794440366758506681706903/1759218604441600000000000000000000), (-824352555355631861233703205839/28147497671065600000000000000000000), (1535716561865476980366267457427/56294995342131200000000000000000000), (139840535091227574079926085927/112589990684262400000000000000000000), (-7818014516769003758124377139/11258999068426240000000000000000000), (-28258767332058460892410247/3518437208883200000000000000000000), (996890657587825292532833623/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial165.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial165.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial165.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial165 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 88906820886727042722529152589821823), (Int.negOfNat 9860933851617107377940001711824919), (Int.negOfNat 537615896624663644093097659343496), (Int.ofNat 54923137636617273192424626975204), (Int.ofNat 16559440719810462486696901461051), (Int.negOfNat 457174243063603984074802680584), (Int.negOfNat 501979246325645039127233949405), (Int.ofNat 12184508318925838812112319022), (Int.ofNat 8257190846291330002837590493), (Int.negOfNat 236704800445872474908722547), (Int.negOfNat 78872364222725378556691696), (Int.ofNat 2506819476437410650415051), (Int.ofNat 486597427545684859904705), (Int.negOfNat 16272262651640811643162), (Int.negOfNat 2107370552765763179526), (Int.ofNat 73250655099121347571), (Int.ofNat 8289715791167072690), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(88906820886727042722529152589821823/112589990684262400000000000000000000), (-9860933851617107377940001711824919/112589990684262400000000000000000000), (-67201987078082955511637207417937/14073748835532800000000000000000000), (13730784409154318298106156743801/28147497671065600000000000000000000), (16559440719810462486696901461051/112589990684262400000000000000000000), (-57146780382950498009350335073/14073748835532800000000000000000000), (-100395849265129007825446789881/22517998136852480000000000000000000), (6092254159462919406056159511/56294995342131200000000000000000000), (8257190846291330002837590493/112589990684262400000000000000000000), (-236704800445872474908722547/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial165.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial165.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial165.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial165 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 67695547963816225325470985229055021), (Int.negOfNat 10942367701301754921463011698860642), (Int.ofNat 53386245018572927169547004066737), (Int.ofNat 108085743282272134360996988214394), (Int.negOfNat 7326101511735768623184530599917), (Int.negOfNat 2755226030349380749962068456006), (Int.ofNat 230205883783979897575212730383), (Int.ofNat 57503843724906107201449857737), (Int.negOfNat 4035170819805409448633434207), (Int.negOfNat 696347434942970494232114170), (Int.ofNat 43385571120233171094838127), (Int.ofNat 5248220997924634331996282), (Int.negOfNat 305760930853895195429973), (Int.negOfNat 26845349726900390120380), (Int.ofNat 1501335347234408576965), (Int.ofNat 99398926682863368423), (Int.negOfNat 4928527823003003320), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(67695547963816225325470985229055021/112589990684262400000000000000000000), (-5471183850650877460731505849430321/56294995342131200000000000000000000), (53386245018572927169547004066737/112589990684262400000000000000000000), (54042871641136067180498494107197/56294995342131200000000000000000000), (-7326101511735768623184530599917/112589990684262400000000000000000000), (-1377613015174690374981034228003/56294995342131200000000000000000000), (230205883783979897575212730383/112589990684262400000000000000000000), (57503843724906107201449857737/112589990684262400000000000000000000), (-4035170819805409448633434207/112589990684262400000000000000000000), (-69634743494297049423211417/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial165.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial165.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial165.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial165 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 46704416495611285180805487008914571), (Int.negOfNat 9822149781017701414263661843775933), (Int.ofNat 389731656846412267837962449045159), (Int.negOfNat 1824547427602426881227088036494), (Int.negOfNat 11534015097944920867062585751811), (Int.ofNat 2092960312317595319672990729506), (Int.ofNat 316118555318656148107735824891), (Int.negOfNat 47883810160549529931588029257), (Int.negOfNat 5010223129689066464751276756), (Int.ofNat 599368180299798027064078828), (Int.ofNat 46998967031627206384437568), (Int.negOfNat 4832677922852289298052049), (Int.negOfNat 287584300875446870388898), (Int.ofNat 26916705029931190949254), (Int.ofNat 1237873123243428717371), (Int.negOfNat 109443811764007089571), (Int.negOfNat 4926197166897064190), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(46704416495611285180805487008914571/112589990684262400000000000000000000), (-9822149781017701414263661843775933/112589990684262400000000000000000000), (389731656846412267837962449045159/112589990684262400000000000000000000), (-912273713801213440613544018247/56294995342131200000000000000000000), (-11534015097944920867062585751811/112589990684262400000000000000000000), (1046480156158797659836495364753/56294995342131200000000000000000000), (316118555318656148107735824891/112589990684262400000000000000000000), (-47883810160549529931588029257/112589990684262400000000000000000000), (-1252555782422266616187819189/28147497671065600000000000000000000), (149842045074949506766019707/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial165.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial165.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial165.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial165 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 28500041677980295987341910593238219), (Int.negOfNat 8451095410261822037728454706430037), (Int.ofNat 307269503296909767196979435833992), (Int.ofNat 8123632652151869776412365875808), (Int.ofNat 12162326934950689156570117971898), (Int.ofNat 1044620644291076450441393414811), (Int.negOfNat 436597766228124312432822591785), (Int.negOfNat 26119277171458878151229480875), (Int.ofNat 6829822021320138848715558803), (Int.ofNat 318853878903490298766470937), (Int.negOfNat 65418331192698979774768332), (Int.negOfNat 2376307664111760188608850), (Int.ofNat 423092209436015347674552), (Int.ofNat 11965892780855078104045), (Int.negOfNat 1957626820010588589129), (Int.negOfNat 42649535176922055800), (Int.ofNat 5878604878324855810), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(28500041677980295987341910593238219/112589990684262400000000000000000000), (-8451095410261822037728454706430037/112589990684262400000000000000000000), (38408687912113720899622429479249/14073748835532800000000000000000000), (253863520379745930512886433619/3518437208883200000000000000000000), (6081163467475344578285058985949/56294995342131200000000000000000000), (1044620644291076450441393414811/112589990684262400000000000000000000), (-87319553245624862486564518357/22517998136852480000000000000000000), (-208954217371671025209835847/900719925474099200000000000000000), (6829822021320138848715558803/112589990684262400000000000000000000), (318853878903490298766470937/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial165.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial165.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial165.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial165 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 13090499129303502776021956238870198), (Int.negOfNat 6739920428009385062654742327896323), (Int.ofNat 622058712472123978331938491942222), (Int.ofNat 75622283315233281838336742196561), (Int.negOfNat 2889395129912945823620080738762), (Int.negOfNat 3239046906239217148672172957614), (Int.negOfNat 51908520362259800067058481688), (Int.ofNat 64869175394039874465713280930), (Int.ofNat 1111270127184672842680189820), (Int.negOfNat 760048253324126945722566911), (Int.negOfNat 10620840534588592668977200), (Int.ofNat 5823354615618423263415643), (Int.ofNat 62071168967115268909537), (Int.negOfNat 31237404677232880095173), (Int.negOfNat 246091639556166647190), (Int.ofNat 123846895637307343231), (Int.ofNat 1562678542627055690), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(6545249564651751388010978119435099/56294995342131200000000000000000000), (-6739920428009385062654742327896323/112589990684262400000000000000000000), (311029356236061989165969245971111/56294995342131200000000000000000000), (75622283315233281838336742196561/112589990684262400000000000000000000), (-1444697564956472911810040369381/56294995342131200000000000000000000), (-1619523453119608574336086478807/56294995342131200000000000000000000), (-6488565045282475008382310211/14073748835532800000000000000000000), (6486917539403987446571328093/11258999068426240000000000000000000), (55563506359233642134009491/5629499534213120000000000000000000), (-760048253324126945722566911/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial165.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial165.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial165.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial165 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2558869065000792873686960738009541), (Int.negOfNat 3677309751429396893582018549686022), (Int.ofNat 776987163486305211776861346770983), (Int.negOfNat 51047272067230754246212356801032), (Int.negOfNat 21951144121374312050514316835004), (Int.ofNat 635315625343155781221986985813), (Int.ofNat 517308435013977636361224782294), (Int.negOfNat 8011978817324579601696541727), (Int.negOfNat 7537426467006343628679594432), (Int.ofNat 83042925222268652423518944), (Int.ofNat 69773326744403617513750999), (Int.negOfNat 642613567123476584164974), (Int.negOfNat 440324708543821073426924), (Int.ofNat 3690616219682105793160), (Int.ofNat 2000140798915290276200), (Int.negOfNat 18191357614984934423), (Int.negOfNat 6828681933646708300), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(2558869065000792873686960738009541/112589990684262400000000000000000000), (-1838654875714698446791009274843011/56294995342131200000000000000000000), (776987163486305211776861346770983/112589990684262400000000000000000000), (-6380909008403844280776544600129/14073748835532800000000000000000000), (-5487786030343578012628579208751/28147497671065600000000000000000000), (635315625343155781221986985813/112589990684262400000000000000000000), (258654217506988818180612391147/56294995342131200000000000000000000), (-8011978817324579601696541727/112589990684262400000000000000000000), (-117772288546974119198118663/1759218604441600000000000000000000), (2595091413195895388234967/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial165.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial165.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial165.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial165 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 2396804632669164649863773035474286), (Int.negOfNat 1744993266347740591870217418249955), (Int.ofNat 101104134063406383272824870857958), (Int.negOfNat 135024297030485342733202141660996), (Int.ofNat 5948198873421642966734304394335), (Int.ofNat 3462833626160157603647710933054), (Int.negOfNat 182090246930897643979910595417), (Int.negOfNat 63001319064655058103450444846), (Int.ofNat 2683793528622811173026410083), (Int.ofNat 718373830491277884563251130), (Int.negOfNat 24796794896500647793131755), (Int.negOfNat 5420601425530128586413524), (Int.ofNat 157276537522194890150348), (Int.ofNat 28798111218176835735852), (Int.negOfNat 722791817737946610089), (Int.negOfNat 113958231682294754684), (Int.ofNat 2117532433416903640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1198402316334582324931886517737143/56294995342131200000000000000000000), (-348998653269548118374043483649991/22517998136852480000000000000000000), (50552067031703191636412435428979/56294995342131200000000000000000000), (-33756074257621335683300535415249/28147497671065600000000000000000000), (1189639774684328593346860878867/22517998136852480000000000000000000), (1731416813080078801823855466527/56294995342131200000000000000000000), (-182090246930897643979910595417/112589990684262400000000000000000000), (-31500659532327529051725222423/56294995342131200000000000000000000), (2683793528622811173026410083/112589990684262400000000000000000000), (71837383049127788456325113/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial165.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial165.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial165.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial165 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 6375285862049264987999448121930348), (Int.negOfNat 2552464548949755583483507965820848), (Int.negOfNat 367600541338744297066070261551116), (Int.negOfNat 5253635877734468860054103501911), (Int.ofNat 17380285219273561720931832111011), (Int.negOfNat 1699645317970771797264874168563), (Int.negOfNat 429424542844162939057282142383), (Int.ofNat 37624483650708043674569453954), (Int.ofNat 6207288134645784352358172717), (Int.negOfNat 440884140691841355731153270), (Int.negOfNat 57070725744265486753827845), (Int.ofNat 3342591924608213519193476), (Int.ofNat 359278207713591659442052), (Int.negOfNat 17756741458679895444348), (Int.negOfNat 1636082131754673575911), (Int.ofNat 71417903262948806916), (Int.ofNat 5219720887681270960), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-1593821465512316246999862030482587/28147497671065600000000000000000000), (-159529034309359723967719247863803/7036874417766400000000000000000000), (-91900135334686074266517565387779/28147497671065600000000000000000000), (-5253635877734468860054103501911/112589990684262400000000000000000000), (17380285219273561720931832111011/112589990684262400000000000000000000), (-1699645317970771797264874168563/112589990684262400000000000000000000), (-429424542844162939057282142383/112589990684262400000000000000000000), (18812241825354021837284726977/56294995342131200000000000000000000), (6207288134645784352358172717/112589990684262400000000000000000000), (-44088414069184135573115327/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial165.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial165.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial165.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial165 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 12790304495597680859009850625888976), (Int.negOfNat 3726212955788602362928850976148979), (Int.negOfNat 187195930408968228114734953889099), (Int.ofNat 26216670873218377667514502990634), (Int.negOfNat 10260524654654499384131490676374), (Int.negOfNat 2132471998607953323487495805234), (Int.ofNat 370226325394866271247805132506), (Int.ofNat 42894268630303440669183754073), (Int.negOfNat 5716604975400227223709977368), (Int.negOfNat 493602530221593174642939456), (Int.ofNat 53403090136651341873220601), (Int.ofNat 3752953766145071329872026), (Int.negOfNat 336097897065794050628476), (Int.negOfNat 20142807005368270513040), (Int.ofNat 1519458837001007114800), (Int.ofNat 82330493509888044177), (Int.negOfNat 4993262886478144300), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-799394030974855053688115664118061/7036874417766400000000000000000000), (-3726212955788602362928850976148979/112589990684262400000000000000000000), (-187195930408968228114734953889099/112589990684262400000000000000000000), (13108335436609188833757251495317/56294995342131200000000000000000000), (-5130262327327249692065745338187/56294995342131200000000000000000000), (-1066235999303976661743747902617/56294995342131200000000000000000000), (185113162697433135623902566253/56294995342131200000000000000000000), (42894268630303440669183754073/112589990684262400000000000000000000), (-714575621925028402963747171/14073748835532800000000000000000000), (-7712539534712393353795929/1759218604441600000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial165.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial165.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial165.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial165 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 20986658628038104803654650978062216), (Int.negOfNat 4575715596692146293556706972905513), (Int.negOfNat 340890087352054975724791696765943), (Int.negOfNat 69870870668426058565335482090631), (Int.negOfNat 4926034505213221854417992502271), (Int.ofNat 2859875228136027446910734987596), (Int.ofNat 210730048792985718463529902488), (Int.negOfNat 58532437657237594627329618870), (Int.negOfNat 3187841431678823182260925620), (Int.ofNat 692417521407027582087464489), (Int.ofNat 30092283960819007911393800), (Int.negOfNat 5278124325123083187072357), (Int.negOfNat 195480097443454455609937), (Int.ofNat 27997497425069239412027), (Int.ofNat 912900396373410404190), (Int.negOfNat 110505991136093377369), (Int.negOfNat 2172894615185213290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-2623332328504763100456831372257777/14073748835532800000000000000000000), (-4575715596692146293556706972905513/112589990684262400000000000000000000), (-340890087352054975724791696765943/112589990684262400000000000000000000), (-69870870668426058565335482090631/112589990684262400000000000000000000), (-4926034505213221854417992502271/112589990684262400000000000000000000), (714968807034006861727683746899/28147497671065600000000000000000000), (26341256099123214807941237811/14073748835532800000000000000000000), (-5853243765723759462732961887/11258999068426240000000000000000000), (-159392071583941159113046281/5629499534213120000000000000000000), (692417521407027582087464489/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial165.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial165.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial165.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial165 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 32042365234623176753367263841937013), (Int.negOfNat 6693909478803702439028609667670084), (Int.negOfNat 640641123627947703787023962082153), (Int.ofNat 4290250372731593790091055694643), (Int.ofNat 19316472729310616420643541247869), (Int.ofNat 516265589550275778409622467058), (Int.negOfNat 482381077874308898556489203685), (Int.negOfNat 10477497530708069689389927675), (Int.ofNat 7410280337887098089614559997), (Int.ofNat 130622941793384443616299337), (Int.negOfNat 70144672093957003984676268), (Int.negOfNat 1118874373581401150421850), (Int.ofNat 444740692876088680358848), (Int.ofNat 6735166633721518348245), (Int.negOfNat 2011019001809150094871), (Int.negOfNat 31054098826128084400), (Int.ofNat 5943339941799996790), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-32042365234623176753367263841937013/112589990684262400000000000000000000), (-1673477369700925609757152416917521/28147497671065600000000000000000000), (-640641123627947703787023962082153/112589990684262400000000000000000000), (4290250372731593790091055694643/112589990684262400000000000000000000), (19316472729310616420643541247869/112589990684262400000000000000000000), (258132794775137889204811233529/56294995342131200000000000000000000), (-96476215574861779711297840737/22517998136852480000000000000000000), (-419099901228322787575597107/4503599627370496000000000000000000), (7410280337887098089614559997/112589990684262400000000000000000000), (130622941793384443616299337/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial165.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial165.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial165.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial165 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 47663164495435614131395305591491470), (Int.negOfNat 8635345287478284455185540662270377), (Int.negOfNat 219743435852144988805728268150818), (Int.ofNat 109331596655365946741888737933691), (Int.ofNat 495473249248428072333766003364), (Int.negOfNat 3122792734114977227517686439874), (Int.ofNat 62649220020442397456897220809), (Int.ofNat 64768709778661326322955941543), (Int.negOfNat 930259978105705135916535444), (Int.negOfNat 786975493166706444665498572), (Int.ofNat 6501076833534310758719832), (Int.ofNat 6103153626714191178915951), (Int.negOfNat 24250333896359889404702), (Int.negOfNat 32708195874982585829946), (Int.ofNat 30563982421396978629), (Int.ofNat 129038911847284010029), (Int.negOfNat 1190624009084795210), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-4766316449543561413139530559149147/11258999068426240000000000000000000), (-8635345287478284455185540662270377/112589990684262400000000000000000000), (-109871717926072494402864134075409/56294995342131200000000000000000000), (109331596655365946741888737933691/112589990684262400000000000000000000), (123868312312107018083441500841/28147497671065600000000000000000000), (-1561396367057488613758843219937/56294995342131200000000000000000000), (62649220020442397456897220809/112589990684262400000000000000000000), (64768709778661326322955941543/112589990684262400000000000000000000), (-232564994526426283979133861/28147497671065600000000000000000000), (-196743873291676611166374643/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial165.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial165.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial165.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial165 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 65018500175314390565076093196511730), (Int.negOfNat 8397929162384097354731099348596403), (Int.ofNat 251821075038572276066171700003170), (Int.ofNat 29125823498204738010182106829898), (Int.negOfNat 12722727133621097049715806028299), (Int.ofNat 1286338635146245732708533956690), (Int.ofNat 440174648707637861478212008417), (Int.negOfNat 28961761254565186622475425463), (Int.negOfNat 7300762187709929283381797593), (Int.ofNat 309965304463681052806693430), (Int.ofNat 71534870958869166866157473), (Int.negOfNat 2058014440152727274300718), (Int.negOfNat 463334455341621925658427), (Int.ofNat 9312595484162044598420), (Int.ofNat 2134566962087288710035), (Int.negOfNat 28798488642624230977), (Int.negOfNat 6893416997121849280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-6501850017531439056507609319651173/11258999068426240000000000000000000), (-8397929162384097354731099348596403/112589990684262400000000000000000000), (25182107503857227606617170000317/11258999068426240000000000000000000), (14562911749102369005091053414949/56294995342131200000000000000000000), (-12722727133621097049715806028299/112589990684262400000000000000000000), (128633863514624573270853395669/11258999068426240000000000000000000), (440174648707637861478212008417/112589990684262400000000000000000000), (-28961761254565186622475425463/112589990684262400000000000000000000), (-7300762187709929283381797593/112589990684262400000000000000000000), (30996530446368105280669343/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial165.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial165.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial165.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial165 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 80713647381790182036877246729071259), (Int.negOfNat 7280245895659575099297871990824908), (Int.ofNat 299399677118782552024874298089476), (Int.ofNat 22554197451068585095015806304366), (Int.ofNat 12336010033054869303426154286006), (Int.ofNat 1963924659139458602668323462526), (Int.negOfNat 388599323244053231137389316795), (Int.negOfNat 53206739087623265776752299778), (Int.ofNat 5514042780999785490935955707), (Int.ofNat 695840543176293034339012853), (Int.negOfNat 46933672593086851431390704), (Int.negOfNat 5625873819992047934823949), (Int.ofNat 266101543301571983961895), (Int.ofNat 30978317000939987105038), (Int.negOfNat 1075792440330767164474), (Int.negOfNat 124514990359793351029), (Int.ofNat 4554142633354803710), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-80713647381790182036877246729071259/112589990684262400000000000000000000), (-1820061473914893774824467997706227/28147497671065600000000000000000000), (74849919279695638006218574522369/28147497671065600000000000000000000), (11277098725534292547507903152183/56294995342131200000000000000000000), (6168005016527434651713077143003/56294995342131200000000000000000000), (981962329569729301334161731263/56294995342131200000000000000000000), (-77719864648810646227477863359/22517998136852480000000000000000000), (-26603369543811632888376149889/56294995342131200000000000000000000), (5514042780999785490935955707/112589990684262400000000000000000000), (695840543176293034339012853/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial165.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial165.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial165.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial165 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 93665856348869602369622564232317593), (Int.negOfNat 5351624248973007955506400756268134), (Int.ofNat 771295241046855279847674470282121), (Int.ofNat 120529098179054383413572305172104), (Int.ofNat 1917987567498611350459430770594), (Int.negOfNat 3804606982082773679299818896069), (Int.negOfNat 267752872184821222766834508227), (Int.ofNat 69954453018484076898216533810), (Int.ofNat 5254837195090413905554321704), (Int.negOfNat 759421660752652080985044977), (Int.negOfNat 56193239036968380421429964), (Int.ofNat 5300275285452306934125464), (Int.ofNat 385008881053448043704466), (Int.negOfNat 25624092809089262960935), (Int.negOfNat 1831547455335472190536), (Int.ofNat 91798831853153703954), (Int.ofNat 6722321177687032270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-93665856348869602369622564232317593/112589990684262400000000000000000000), (-2675812124486503977753200378134067/56294995342131200000000000000000000), (771295241046855279847674470282121/112589990684262400000000000000000000), (15066137272381797926696538146513/14073748835532800000000000000000000), (958993783749305675229715385297/56294995342131200000000000000000000), (-3804606982082773679299818896069/112589990684262400000000000000000000), (-267752872184821222766834508227/112589990684262400000000000000000000), (6995445301848407689821653381/11258999068426240000000000000000000), (656854649386301738194290213/14073748835532800000000000000000000), (-759421660752652080985044977/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial165.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial165.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial165.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial165 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 100418021665502986576835217440064457), (Int.negOfNat 1079744868508612722832043331773282), (Int.ofNat 1224322171555263495197467228504729), (Int.negOfNat 15247783177052299693167560961105), (Int.negOfNat 30276108638108461814321267728733), (Int.negOfNat 585681102982673062795669949727), (Int.ofNat 695377279084689734669740563393), (Int.ofNat 25034281387573274709520332710), (Int.negOfNat 9799373245319468293678350816), (Int.negOfNat 413593808680634571896438583), (Int.ofNat 85318033167319127904763276), (Int.ofNat 3838865804512793393957336), (Int.negOfNat 495308002928580562282294), (Int.negOfNat 22897591986847915508545), (Int.ofNat 2052612293110382267664), (Int.ofNat 95806689308496161286), (Int.negOfNat 7429873086416044370), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-100418021665502986576835217440064457/112589990684262400000000000000000000), (-539872434254306361416021665886641/56294995342131200000000000000000000), (1224322171555263495197467228504729/112589990684262400000000000000000000), (-3049556635410459938633512192221/22517998136852480000000000000000000), (-30276108638108461814321267728733/112589990684262400000000000000000000), (-585681102982673062795669949727/112589990684262400000000000000000000), (695377279084689734669740563393/112589990684262400000000000000000000), (2503428138757327470952033271/11258999068426240000000000000000000), (-306230413916233384177448463/3518437208883200000000000000000000), (-413593808680634571896438583/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial165.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial165.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial165.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial165 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 98260283333203046353003931945557588), (Int.ofNat 2753087705512703104827279309079178), (Int.ofNat 524656312852729065445920753196571), (Int.negOfNat 173976470633549209390748565970320), (Int.ofNat 1196410577808861281588048960197), (Int.ofNat 5383895516009161530468998830367), (Int.negOfNat 18738183117377317681690071875), (Int.negOfNat 103188039809224585691017572342), (Int.negOfNat 1235487071983141067389331613), (Int.ofNat 1155174805298302412936910907), (Int.ofNat 24914059243347205023827536), (Int.negOfNat 8175080396084048264341451), (Int.negOfNat 217932936490412256613665), (Int.ofNat 39916235856702712213642), (Int.ofNat 1171523264883618863526), (Int.negOfNat 146412178194986356211), (Int.negOfNat 5113360131721594930), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-24565070833300761588250982986389397/28147497671065600000000000000000000), (1376543852756351552413639654539589/56294995342131200000000000000000000), (524656312852729065445920753196571/112589990684262400000000000000000000), (-2174705882919365117384357074629/1407374883553280000000000000000000), (1196410577808861281588048960197/112589990684262400000000000000000000), (5383895516009161530468998830367/112589990684262400000000000000000000), (-5996218597560741658140823/36028797018963968000000000000000), (-51594019904612292845508786171/56294995342131200000000000000000000), (-1235487071983141067389331613/112589990684262400000000000000000000), (1155174805298302412936910907/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial165.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial165.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial165.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial165 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 91869991140113542631728108119431643), (Int.ofNat 3184594842352912380444581456052605), (Int.negOfNat 130458737350002963948287433091092), (Int.negOfNat 5811455518677997501803464233062), (Int.ofNat 28269640249905746173738174517963), (Int.negOfNat 1782451944887554923328526819094), (Int.negOfNat 866232040643360705218254009103), (Int.ofNat 23262451072209136733604077743), (Int.ofNat 13266169483895710441737720527), (Int.negOfNat 46842487529027161491438070), (Int.negOfNat 117387384894152671249932967), (Int.negOfNat 949334562448531306522482), (Int.ofNat 682518586976865461964533), (Int.ofNat 9595855495503638164460), (Int.negOfNat 2832475927736099156965), (Int.negOfNat 48577236131735724263), (Int.ofNat 9501123016494566360), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-91869991140113542631728108119431643/112589990684262400000000000000000000), (636918968470582476088916291210521/22517998136852480000000000000000000), (-32614684337500740987071858272773/28147497671065600000000000000000000), (-2905727759338998750901732116531/56294995342131200000000000000000000), (28269640249905746173738174517963/112589990684262400000000000000000000), (-891225972443777461664263409547/56294995342131200000000000000000000), (-866232040643360705218254009103/112589990684262400000000000000000000), (23262451072209136733604077743/112589990684262400000000000000000000), (13266169483895710441737720527/112589990684262400000000000000000000), (-4684248752902716149143807/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial165.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial165.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial165.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial165 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 85723060690155842789648158596098378), (Int.ofNat 3212041653440573260632967784525951), (Int.ofNat 200509086408187793655605729199127), (Int.ofNat 45232941529004177928440632975073), (Int.negOfNat 21876834172495072793208168252364), (Int.negOfNat 5279685379893962925177869381116), (Int.ofNat 545557557229730604509003868819), (Int.ofNat 128150632357733760142081834177), (Int.negOfNat 4714040795366701990032515924), (Int.negOfNat 1476261359539284742636035388), (Int.ofNat 18477489346283732737328392), (Int.ofNat 10384588094592935611341249), (Int.negOfNat 12677664260977688246542), (Int.negOfNat 50324641645076494674934), (Int.negOfNat 239068353862482616171), (Int.ofNat 182605334859872098211), (Int.ofNat 1749841507451586430), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-42861530345077921394824079298049189/56294995342131200000000000000000000), (3212041653440573260632967784525951/112589990684262400000000000000000000), (200509086408187793655605729199127/112589990684262400000000000000000000), (45232941529004177928440632975073/112589990684262400000000000000000000), (-5469208543123768198302042063091/28147497671065600000000000000000000), (-1319921344973490731294467345279/28147497671065600000000000000000000), (545557557229730604509003868819/112589990684262400000000000000000000), (128150632357733760142081834177/112589990684262400000000000000000000), (-1178510198841675497508128981/28147497671065600000000000000000000), (-369065339884821185659008847/28147497671065600000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial165.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial165.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial165.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial165 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 78604660733508672471620252405144829), (Int.ofNat 3588578426873507286091860693097982), (Int.negOfNat 273214786779638005607945878168568), (Int.negOfNat 197593070952476527261556109815237), (Int.negOfNat 16622851451003060927149310705925), (Int.ofNat 7382127475013265986647688695316), (Int.ofNat 1023733553313862744280152768905), (Int.negOfNat 92942506793897578788734918205), (Int.negOfNat 16324270353969669735281490523), (Int.ofNat 621548915512141280939550903), (Int.ofNat 141497736020238960880608372), (Int.negOfNat 2562698007029787813825350), (Int.negOfNat 806585331844379730283912), (Int.ofNat 6745394890419228996675), (Int.ofNat 3310163777912001911129), (Int.negOfNat 8172155374205588360), (Int.negOfNat 10451200071816418850), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-78604660733508672471620252405144829/112589990684262400000000000000000000), (1794289213436753643045930346548991/56294995342131200000000000000000000), (-34151848347454750700993234771071/14073748835532800000000000000000000), (-197593070952476527261556109815237/112589990684262400000000000000000000), (-664914058040122437085972428237/4503599627370496000000000000000000), (1845531868753316496661922173829/28147497671065600000000000000000000), (204746710662772548856030553781/22517998136852480000000000000000000), (-18588501358779515757746983641/22517998136852480000000000000000000), (-16324270353969669735281490523/112589990684262400000000000000000000), (621548915512141280939550903/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial165.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial165.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial165.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial165 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 74080947162164152724997636545230594), (Int.ofNat 323552485382910729915842997035850), (Int.negOfNat 1108796097604203443145924450566240), (Int.ofNat 52525816211629968008380758860490), (Int.ofNat 78518466094622264694813961875180), (Int.ofNat 6788518339088053373094817503604), (Int.negOfNat 1294333895905124783117522697792), (Int.negOfNat 160643552442805274900038031250), (Int.ofNat 11435108187272335068382647460), (Int.ofNat 1739635842522226973340574871), (Int.negOfNat 65349824579925986562738560), (Int.negOfNat 11739388979681538483113443), (Int.ofNat 265300263146155044735103), (Int.ofNat 55498977407668202876053), (Int.negOfNat 810418819458875928010), (Int.negOfNat 197008418733172351871), (Int.ofNat 1613677116818422070), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-37040473581082076362498818272615297/56294995342131200000000000000000000), (6471049707658214598316859940717/2251799813685248000000000000000000), (-6929975610026271519662027816039/703687441776640000000000000000000), (5252581621162996800838075886049/11258999068426240000000000000000000), (3925923304731113234740698093759/5629499534213120000000000000000000), (1697129584772013343273704375901/28147497671065600000000000000000000), (-20223967123517574736211292153/1759218604441600000000000000000000), (-5140593678169768796801217/3602879701896396800000000000000), (571755409363616753419132373/5629499534213120000000000000000000), (1739635842522226973340574871/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial165.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial165.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial165.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial165 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 76074963109293768753032445094070275), (Int.negOfNat 730869964326520373209936798732703), (Int.ofNat 1242741725503149973889549701071065), (Int.ofNat 683549997261444856187178785618800), (Int.ofNat 42263360068387371613347790425448), (Int.negOfNat 14437828141116303450776001627883), (Int.negOfNat 1459925176725035922317727572814), (Int.ofNat 160267019097786556471419363207), (Int.ofNat 19571832831955501273807585352), (Int.negOfNat 1156931179545481016856793584), (Int.negOfNat 156173180713546314992447239), (Int.ofNat 5964189199471665345490374), (Int.ofNat 851557038467685395691884), (Int.negOfNat 23209736372439836922680), (Int.negOfNat 3408373375868630637000), (Int.ofNat 69013048166112578583), (Int.ofNat 11401277127138271340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-3042998524371750750121297803762811/4503599627370496000000000000000000), (-730869964326520373209936798732703/112589990684262400000000000000000000), (248548345100629994777909940214213/22517998136852480000000000000000000), (1708874993153612140467946964047/281474976710656000000000000000000), (5282920008548421451668473803181/14073748835532800000000000000000000), (-14437828141116303450776001627883/112589990684262400000000000000000000), (-729962588362517961158863786407/56294995342131200000000000000000000), (160267019097786556471419363207/112589990684262400000000000000000000), (2446479103994437659225948169/14073748835532800000000000000000000), (-72308198721592563553549599/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial165.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial165.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial165.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial165 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 66951780351440143559034830549455004), (Int.ofNat 12448255051151359997800744316958045), (Int.ofNat 4988816569419011897643969049472096), (Int.ofNat 327098182149338090755693387173935), (Int.negOfNat 129330810884799301840707699061056), (Int.negOfNat 13066232610788352227547881930174), (Int.ofNat 1804733522146460530049772849667), (Int.ofNat 206091322608540585846018659366), (Int.negOfNat 16268431032228305623611117763), (Int.negOfNat 1917075003632549709268359890), (Int.ofNat 103632415506482614990584315), (Int.ofNat 12013879515201229267887724), (Int.negOfNat 490845362621574593665788), (Int.negOfNat 54530424132455518295132), (Int.ofNat 1791200105714386022489), (Int.ofNat 187119754778159763324), (Int.negOfNat 5293888092862381400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-16737945087860035889758707637363751/28147497671065600000000000000000000), (2489651010230271999560148863391609/22517998136852480000000000000000000), (155900517794344121801374032796003/3518437208883200000000000000000000), (65419636429867618151138677434787/22517998136852480000000000000000000), (-2020793920074989091261057797829/1759218604441600000000000000000000), (-6533116305394176113773940965087/56294995342131200000000000000000000), (1804733522146460530049772849667/112589990684262400000000000000000000), (103045661304270292923009329683/56294995342131200000000000000000000), (-16268431032228305623611117763/112589990684262400000000000000000000), (-191707500363254970926835989/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial165.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial165.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial165.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial165.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial165 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial165 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial165 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 97220022246607641098357842247159561), (Int.negOfNat 17016274662894502702762036025723018), (Int.ofNat 5879620091071102005370319202039238), (Int.negOfNat 288662490447158856456809897399210), (Int.negOfNat 134065733631148250951297894781497), (Int.ofNat 12956402355539958435987231317217), (Int.ofNat 1815287730627214035403973942497), (Int.negOfNat 205927656243415283277287582366), (Int.negOfNat 16281354920704566810295111763), (Int.ofNat 1916924602986925517558352890), (Int.ofNat 103642375791947865959771315), (Int.negOfNat 12013781334143413433671724), (Int.negOfNat 490845362621574593665788), (Int.ofNat 54530424132455518295132), (Int.ofNat 1791200105714386022489), (Int.negOfNat 187119754778159763324), (Int.negOfNat 5293888092862381400), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-97220022246607641098357842247159561/112589990684262400000000000000000000), (-8508137331447251351381018012861509/56294995342131200000000000000000000), (2939810045535551002685159601019619/56294995342131200000000000000000000), (-28866249044715885645680989739921/11258999068426240000000000000000000), (-134065733631148250951297894781497/112589990684262400000000000000000000), (12956402355539958435987231317217/112589990684262400000000000000000000), (1815287730627214035403973942497/112589990684262400000000000000000000), (-102963828121707641638643791183/56294995342131200000000000000000000), (-16281354920704566810295111763/112589990684262400000000000000000000), (191692460298692551755835289/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial165.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial165.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial165.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 111687124896335645576410823750402490), (Int.ofNat 29074993258537900981991089038773), (Int.ofNat 2244354089344684251120746460234749), (Int.negOfNat 685630382886346440309463911697614), (Int.ofNat 37094269966237710146268646093030), (Int.ofNat 14462385876455000053028837873706), (Int.negOfNat 1448593618743402312791146318814), (Int.negOfNat 160321864373067588754860317207), (Int.ofNat 19558076728340582949840479352), (Int.ofNat 1156991123850371077184753584), (Int.negOfNat 156162615478737356650917239), (Int.negOfNat 5964226017368346283321374), (Int.ofNat 851557038467685395691884), (Int.ofNat 23209736372439836922680), (Int.negOfNat 3408373375868630637000), (Int.negOfNat 69013048166112578583), (Int.ofNat 11401277127138271340), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-11168712489633564557641082375040249/11258999068426240000000000000000000), (29074993258537900981991089038773/112589990684262400000000000000000000), (2244354089344684251120746460234749/112589990684262400000000000000000000), (-342815191443173220154731955848807/56294995342131200000000000000000000), (3709426996623771014626864609303/11258999068426240000000000000000000), (7231192938227500026514418936853/56294995342131200000000000000000000), (-724296809371701156395573159407/56294995342131200000000000000000000), (-160321864373067588754860317207/112589990684262400000000000000000000), (2444759591042572868730059919/14073748835532800000000000000000000), (72311945240648192324047099/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial165.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial165.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial165.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 107188097395722975801387922402348192), (Int.ofNat 2794828300781424061767474705353467), (Int.negOfNat 239101127767911043894979885389164), (Int.negOfNat 93218446041103876941293440748245), (Int.ofNat 74244464607514100028715060727287), (Int.negOfNat 6638547341146693484558788129204), (Int.negOfNat 1285235988369250077855896354792), (Int.ofNat 160387035014886565025840769250), (Int.ofNat 11424237115483352376661236460), (Int.negOfNat 1739382863488654037100473871), (Int.negOfNat 65341531479380038122032560), (Int.ofNat 11739229435462587752512443), (Int.ofNat 265300263146155044735103), (Int.negOfNat 55498977407668202876053), (Int.negOfNat 810418819458875928010), (Int.ofNat 197008418733172351871), (Int.ofNat 1613677116818422070), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-3349628043616342993793372575073381/3518437208883200000000000000000000), (2794828300781424061767474705353467/112589990684262400000000000000000000), (-59775281941977760973744971347291/28147497671065600000000000000000000), (-18643689208220775388258688149649/22517998136852480000000000000000000), (74244464607514100028715060727287/112589990684262400000000000000000000), (-1659636835286673371139697032301/28147497671065600000000000000000000), (-160654498546156259731987044349/14073748835532800000000000000000000), (641548140059546260103363077/450359962737049600000000000000000), (571211855774167618833061823/5629499534213120000000000000000000), (-1739382863488654037100473871/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial165.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial165.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial165.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 102384848719367350535990963626395036), (Int.ofNat 2397121682764612107622355147129271), (Int.ofNat 263738941718107302813007836507214), (Int.ofNat 130001283620053274737213030190099), (Int.negOfNat 18934144976184782887560498092998), (Int.negOfNat 7148827677397687705713687492109), (Int.ofNat 1028217859900928630618794378735), (Int.ofNat 92555476658046100489498126205), (Int.negOfNat 16329341934968916832899696523), (Int.negOfNat 621172686939805014588264903), (Int.ofNat 141501488246860926988824372), (Int.ofNat 2562464827017475207562350), (Int.negOfNat 806585331844379730283912), (Int.negOfNat 6745394890419228996675), (Int.ofNat 3310163777912001911129), (Int.ofNat 8172155374205588360), (Int.negOfNat 10451200071816418850), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-25596212179841837633997740906598759/28147497671065600000000000000000000), (2397121682764612107622355147129271/112589990684262400000000000000000000), (131869470859053651406503918253607/56294995342131200000000000000000000), (130001283620053274737213030190099/112589990684262400000000000000000000), (-9467072488092391443780249046499/56294995342131200000000000000000000), (-7148827677397687705713687492109/112589990684262400000000000000000000), (205643571980185726123758875747/22517998136852480000000000000000000), (18511095331609220097899625241/22517998136852480000000000000000000), (-16329341934968916832899696523/112589990684262400000000000000000000), (-621172686939805014588264903/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial165.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial165.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial165.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 95954046590870851865256454672614114), (Int.ofNat 4055757800576456872973538978982925), (Int.ofNat 295913861210429810260338611198095), (Int.negOfNat 121489351311948082100645857633688), (Int.negOfNat 21698562873690594511835742008544), (Int.ofNat 5532795746678892184302405228896), (Int.ofNat 544317224030845807741023207489), (Int.negOfNat 128562331600101544048758365177), (Int.negOfNat 4711992197962075037250826924), (Int.ofNat 1476657731480918352886047388), (Int.ofNat 18475696040440122946919392), (Int.negOfNat 10384845819869702176158249), (Int.negOfNat 12677664260977688246542), (Int.ofNat 50324641645076494674934), (Int.negOfNat 239068353862482616171), (Int.negOfNat 182605334859872098211), (Int.ofNat 1749841507451586430), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-47977023295435425932628227336307057/56294995342131200000000000000000000), (162230312023058274918941559159317/4503599627370496000000000000000000), (59182772242085962052067722239619/22517998136852480000000000000000000), (-15186168913993510262580732204211/14073748835532800000000000000000000), (-678080089802831078494866937767/3518437208883200000000000000000000), (172899867083715380759450163403/3518437208883200000000000000000000), (544317224030845807741023207489/112589990684262400000000000000000000), (-128562331600101544048758365177/112589990684262400000000000000000000), (-1177998049490518759312706731/28147497671065600000000000000000000), (369164432870229588221511847/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial165.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial165.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial165.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 87782989793115911110024850802079012), (Int.ofNat 3575280718202158259944975725607261), (Int.negOfNat 468633952594717840033810256928365), (Int.negOfNat 59317610015237588032788259848414), (Int.ofNat 30793177585419647568137756305564), (Int.ofNat 1987790740753989194163487684387), (Int.negOfNat 872749990113805876628965408103), (Int.negOfNat 23587298786186316638332952743), (Int.ofNat 13274712060684316920614194527), (Int.ofNat 47150858820563272127350070), (Int.negOfNat 117394196009276096830055967), (Int.ofNat 949138200332899638090482), (Int.ofNat 682518586976865461964533), (Int.negOfNat 9595855495503638164460), (Int.negOfNat 2832475927736099156965), (Int.ofNat 48577236131735724263), (Int.ofNat 9501123016494566360), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-21945747448278977777506212700519753/28147497671065600000000000000000000), (3575280718202158259944975725607261/112589990684262400000000000000000000), (-93726790518943568006762051385673/22517998136852480000000000000000000), (-29658805007618794016394129924207/56294995342131200000000000000000000), (7698294396354911892034439076391/28147497671065600000000000000000000), (1987790740753989194163487684387/112589990684262400000000000000000000), (-872749990113805876628965408103/112589990684262400000000000000000000), (-23587298786186316638332952743/112589990684262400000000000000000000), (13274712060684316920614194527/112589990684262400000000000000000000), (4715085882056327212735007/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial165.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial165.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial165.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 82480773203348832220307788025433331), (Int.ofNat 1968330949134502698292277255288813), (Int.negOfNat 129067255750937551524469698717219), (Int.ofNat 136041322777318087486452826793735), (Int.ofNat 5302013398563194245115903459094), (Int.negOfNat 5279670801416092292092882110744), (Int.negOfNat 28665513285874969183999535875), (Int.ofNat 103036820487396259751143072342), (Int.negOfNat 1222843171178953376540998613), (Int.negOfNat 1155037979620897818590303907), (Int.ofNat 24904115016641314340299536), (Int.ofNat 8175006760290686388679451), (Int.negOfNat 217932936490412256613665), (Int.negOfNat 39916235856702712213642), (Int.ofNat 1171523264883618863526), (Int.ofNat 146412178194986356211), (Int.negOfNat 5113360131721594930), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-82480773203348832220307788025433331/112589990684262400000000000000000000), (1968330949134502698292277255288813/112589990684262400000000000000000000), (-129067255750937551524469698717219/112589990684262400000000000000000000), (27208264555463617497290565358747/22517998136852480000000000000000000), (2651006699281597122557951729547/56294995342131200000000000000000000), (-659958850177011536511610263843/14073748835532800000000000000000000), (-229324106286999753471996287/900719925474099200000000000000000), (51518410243698129875571536171/56294995342131200000000000000000000), (-1222843171178953376540998613/112589990684262400000000000000000000), (-1155037979620897818590303907/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial165.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial165.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial165.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 78045676256266470514988734090626490), (Int.ofNat 2868804159112081591875956466203767), (Int.ofNat 447399153847331282949098625065526), (Int.ofNat 12676628579190002068522494031961), (Int.negOfNat 25751663553404933751892445813535), (Int.ofNat 563933619634518599537001497444), (Int.ofNat 684806610937815293587516740393), (Int.negOfNat 24973346787196704793873985710), (Int.negOfNat 9786124009188417819495786816), (Int.ofNat 413522922733711300307459583), (Int.ofNat 85307699610984011353529276), (Int.negOfNat 3838804441351658497572336), (Int.negOfNat 495308002928580562282294), (Int.ofNat 22897591986847915508545), (Int.ofNat 2052612293110382267664), (Int.negOfNat 95806689308496161286), (Int.negOfNat 7429873086416044370), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-7804567625626647051498873409062649/11258999068426240000000000000000000), (2868804159112081591875956466203767/112589990684262400000000000000000000), (223699576923665641474549312532763/56294995342131200000000000000000000), (12676628579190002068522494031961/112589990684262400000000000000000000), (-5150332710680986750378489162707/22517998136852480000000000000000000), (140983404908629649884250374361/28147497671065600000000000000000000), (684806610937815293587516740393/112589990684262400000000000000000000), (-2497334678719670479387398571/11258999068426240000000000000000000), (-152908187643569028429621669/1759218604441600000000000000000000), (413522922733711300307459583/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial165.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial165.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial165.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 70772623842243743998472752950864100), (Int.ofNat 4143191139654296343509215450060889), (Int.ofNat 83319465396969692841659249940724), (Int.negOfNat 89408569597499866122367112241608), (Int.ofNat 5622196500535573641571285842956), (Int.ofNat 3666841333358093700117984754546), (Int.negOfNat 276067884424618432142429467727), (Int.negOfNat 69701272177275347040092140810), (Int.ofNat 5265055754060841283445692704), (Int.ofNat 759163999835893161736888977), (Int.negOfNat 56201139217520517606659964), (Int.negOfNat 5300103468601129224247464), (Int.ofNat 385008881053448043704466), (Int.ofNat 25624092809089262960935), (Int.negOfNat 1831547455335472190536), (Int.negOfNat 91798831853153703954), (Int.ofNat 6722321177687032270), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-707726238422437439984727529508641/1125899906842624000000000000000000), (4143191139654296343509215450060889/112589990684262400000000000000000000), (20829866349242423210414812485181/28147497671065600000000000000000000), (-11176071199687483265295889030201/14073748835532800000000000000000000), (1405549125133893410392821460739/28147497671065600000000000000000000), (1833420666679046850058992377273/56294995342131200000000000000000000), (-276067884424618432142429467727/112589990684262400000000000000000000), (-6970127217727534704009214081/11258999068426240000000000000000000), (164532992314401290107677897/3518437208883200000000000000000000), (759163999835893161736888977/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial165.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial165.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial165.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 62685858402920009217646211533997623), (Int.ofNat 3799396235023613420449605819930119), (Int.negOfNat 125781591646030362476423501058904), (Int.ofNat 31517568590388621104209176849396), (Int.ofNat 14244859667895735995148075654349), (Int.negOfNat 2176203150145230575957237760616), (Int.negOfNat 392422309369853984751667667795), (Int.ofNat 53579712467340131254044563778), (Int.ofNat 5518452710807590306522827707), (Int.negOfNat 696212877608878558445511853), (Int.negOfNat 46936961854286229796238704), (Int.ofNat 5626119272636587520363949), (Int.ofNat 266101543301571983961895), (Int.negOfNat 30978317000939987105038), (Int.negOfNat 1075792440330767164474), (Int.ofNat 124514990359793351029), (Int.ofNat 4554142633354803710), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-62685858402920009217646211533997623/112589990684262400000000000000000000), (3799396235023613420449605819930119/112589990684262400000000000000000000), (-15722698955753795309552937632363/14073748835532800000000000000000000), (7879392147597155276052294212349/28147497671065600000000000000000000), (14244859667895735995148075654349/112589990684262400000000000000000000), (-272025393768153821994654720077/14073748835532800000000000000000000), (-78484461873970796950333533559/22517998136852480000000000000000000), (26789856233670065627022281889/56294995342131200000000000000000000), (5518452710807590306522827707/112589990684262400000000000000000000), (-696212877608878558445511853/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial165.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial165.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial165.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 55197008777089026281757931249393221), (Int.ofNat 3908753250728452769312228785840442), (Int.ofNat 179239791673603127208010228975463), (Int.ofNat 31328647878408064221684860249806), (Int.negOfNat 13058205154515459181593711741683), (Int.negOfNat 1511957523661547954797092738394), (Int.ofNat 441809542400987857881591366417), (Int.ofNat 29349811495698405056387946463), (Int.negOfNat 7303321686055643070619860593), (Int.negOfNat 310348983702508003730440430), (Int.ofNat 71537051701278435871081473), (Int.ofNat 2058259892797266859840718), (Int.negOfNat 463334455341621925658427), (Int.negOfNat 9312595484162044598420), (Int.ofNat 2134566962087288710035), (Int.ofNat 28798488642624230977), (Int.negOfNat 6893416997121849280), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-55197008777089026281757931249393221/112589990684262400000000000000000000), (1954376625364226384656114392920221/56294995342131200000000000000000000), (179239791673603127208010228975463/112589990684262400000000000000000000), (15664323939204032110842430124903/56294995342131200000000000000000000), (-13058205154515459181593711741683/112589990684262400000000000000000000), (-755978761830773977398546369197/56294995342131200000000000000000000), (441809542400987857881591366417/112589990684262400000000000000000000), (29349811495698405056387946463/112589990684262400000000000000000000), (-7303321686055643070619860593/112589990684262400000000000000000000), (-31034898370250800373044043/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial165.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial165.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial165.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 46639148281041654878823100887403171), (Int.ofNat 4552997346260261344884781058417933), (Int.ofNat 44947947162432563340902818080841), (Int.negOfNat 60113419264873401909890107127306), (Int.negOfNat 1893819956107742284689066687189), (Int.ofNat 2947493421206748067654816087694), (Int.ofNat 69183224722282978349827281309), (Int.negOfNat 64473501069286640838543218543), (Int.negOfNat 939020374123277300186727444), (Int.ofNat 786686465170068728612313572), (Int.ofNat 6508142083569917515889832), (Int.negOfNat 6102969537230786489760951), (Int.negOfNat 24250333896359889404702), (Int.ofNat 32708195874982585829946), (Int.ofNat 30563982421396978629), (Int.negOfNat 129038911847284010029), (Int.negOfNat 1190624009084795210), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-46639148281041654878823100887403171/112589990684262400000000000000000000), (4552997346260261344884781058417933/112589990684262400000000000000000000), (44947947162432563340902818080841/112589990684262400000000000000000000), (-30056709632436700954945053563653/56294995342131200000000000000000000), (-1893819956107742284689066687189/112589990684262400000000000000000000), (1473746710603374033827408043847/56294995342131200000000000000000000), (69183224722282978349827281309/112589990684262400000000000000000000), (-64473501069286640838543218543/112589990684262400000000000000000000), (-234755093530819325046681861/28147497671065600000000000000000000), (196671616292517182153078393/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial165.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial165.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial165.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 37773918640831812453727080839449019), (Int.ofNat 4171841054629303574332643152738437), (Int.negOfNat 150258061200059749880586581273792), (Int.ofNat 19995229653523425473320623449192), (Int.ofNat 15638010134989533462497355832302), (Int.negOfNat 592804759171678553884963058411), (Int.negOfNat 472863367543573254115356468015), (Int.ofNat 10598558212144967458806308675), (Int.ofNat 7397797101956394777216331997), (Int.negOfNat 130737835889627950797333337), (Int.negOfNat 70134728063013661219760268), (Int.ofNat 1118948009374763026083850), (Int.ofNat 444740692876088680358848), (Int.negOfNat 6735166633721518348245), (Int.negOfNat 2011019001809150094871), (Int.ofNat 31054098826128084400), (Int.ofNat 5943339941799996790), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-37773918640831812453727080839449019/112589990684262400000000000000000000), (4171841054629303574332643152738437/112589990684262400000000000000000000), (-2347782206250933591884165332403/1759218604441600000000000000000000), (2499403706690428184165077931149/14073748835532800000000000000000000), (7819005067494766731248677916151/56294995342131200000000000000000000), (-592804759171678553884963058411/112589990684262400000000000000000000), (-94572673508714650823071293603/22517998136852480000000000000000000), (423942328485798698352252347/4503599627370496000000000000000000), (7397797101956394777216331997/112589990684262400000000000000000000), (-130737835889627950797333337/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial165.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial165.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial165.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 29667216062607649511700552278281598), (Int.ofNat 4184639885572178109189935771024123), (Int.ofNat 203142439497529301174875903567778), (Int.ofNat 63234878356456383964492276672039), (Int.negOfNat 8779237631578271060534391054238), (Int.negOfNat 2817775102750990747285952258586), (Int.ofNat 220501444593701394385203219488), (Int.ofNat 58447014688912555549024668870), (Int.negOfNat 3200549954503457153664084620), (Int.negOfNat 692327176877860467030244489), (Int.ofNat 30102361293415828713777800), (Int.ofNat 5278062961961948290687357), (Int.negOfNat 195480097443454455609937), (Int.negOfNat 27997497425069239412027), (Int.ofNat 912900396373410404190), (Int.ofNat 110505991136093377369), (Int.negOfNat 2172894615185213290), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-14833608031303824755850276139140799/56294995342131200000000000000000000), (4184639885572178109189935771024123/112589990684262400000000000000000000), (101571219748764650587437951783889/56294995342131200000000000000000000), (63234878356456383964492276672039/112589990684262400000000000000000000), (-4389618815789135530267195527119/56294995342131200000000000000000000), (-1408887551375495373642976129293/56294995342131200000000000000000000), (6890670143553168574537600609/3518437208883200000000000000000000), (5844701468891255554902466887/11258999068426240000000000000000000), (-160027497725172857683204231/5629499534213120000000000000000000), (-692327176877860467030244489/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial165.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial165.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial165.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 20189663991257938616398721885337141), (Int.ofNat 5313526038306431475733282476270422), (Int.ofNat 230177265168205752387695298898817), (Int.negOfNat 60500832821778570970631032726168), (Int.negOfNat 13144098065504844049385178292196), (Int.ofNat 2279221125240661019168265319787), (Int.ofNat 377471863512283045015473415506), (Int.negOfNat 43160780895974879362087073073), (Int.negOfNat 5725991408353257837107434368), (Int.ofNat 493872428127257679741936456), (Int.ofNat 53410520171051720539542601), (Int.negOfNat 3753137855628476019027026), (Int.negOfNat 336097897065794050628476), (Int.ofNat 20142807005368270513040), (Int.ofNat 1519458837001007114800), (Int.negOfNat 82330493509888044177), (Int.negOfNat 4993262886478144300), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-20189663991257938616398721885337141/112589990684262400000000000000000000), (2656763019153215737866641238135211/56294995342131200000000000000000000), (230177265168205752387695298898817/112589990684262400000000000000000000), (-7562604102722321371328879090771/14073748835532800000000000000000000), (-3286024516376211012346294573049/28147497671065600000000000000000000), (2279221125240661019168265319787/112589990684262400000000000000000000), (188735931756141522507736707753/56294995342131200000000000000000000), (-43160780895974879362087073073/112589990684262400000000000000000000), (-44734307877759826852401831/879609302220800000000000000000000), (61734053515907209967742057/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial165.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial165.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial165.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 9245813565106167300149992336737714), (Int.ofNat 5318588843337417054250279992020355), (Int.negOfNat 211853812610805530675287867714358), (Int.negOfNat 45234372191734376194880106729404), (Int.ofNat 16314979417396430745570770554065), (Int.ofNat 1907347275137237216290281135146), (Int.negOfNat 426757905191319037613544971383), (Int.negOfNat 37996190775029775194570765954), (Int.ofNat 6203839208519528343432509717), (Int.ofNat 441258213531427056685522270), (Int.negOfNat 57067999522610078619754845), (Int.negOfNat 3342837377252753104733476), (Int.ofNat 359278207713591659442052), (Int.ofNat 17756741458679895444348), (Int.negOfNat 1636082131754673575911), (Int.negOfNat 71417903262948806916), (Int.ofNat 5219720887681270960), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-4622906782553083650074996168368857/56294995342131200000000000000000000), (1063717768667483410850055998404071/22517998136852480000000000000000000), (-105926906305402765337643933857179/56294995342131200000000000000000000), (-11308593047933594048720026682351/28147497671065600000000000000000000), (3262995883479286149114154110813/22517998136852480000000000000000000), (953673637568618608145140567573/56294995342131200000000000000000000), (-426757905191319037613544971383/112589990684262400000000000000000000), (-18998095387514887597285382977/56294995342131200000000000000000000), (6203839208519528343432509717/112589990684262400000000000000000000), (44125821353142705668552227/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial165.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial165.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial165.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.ofNat 473723070394370575786311519116948), (Int.ofNat 4511117560738320258901953706194648), (Int.negOfNat 54642594663065820142400455694284), (Int.ofNat 84536288960974937763306867191311), (Int.ofNat 7013504675307834215246725111789), (Int.negOfNat 3255131668993691177113757331037), (Int.negOfNat 184756884583741545423647766417), (Int.ofNat 62629611940333326583449132846), (Int.ofNat 2687242454749067181952073083), (Int.negOfNat 717999757651692183608882130), (Int.negOfNat 24799521118156055927204755), (Int.ofNat 5420355972885589000873524), (Int.ofNat 157276537522194890150348), (Int.negOfNat 28798111218176835735852), (Int.negOfNat 722791817737946610089), (Int.ofNat 113958231682294754684), (Int.ofNat 2117532433416903640), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(118430767598592643946577879779237/28147497671065600000000000000000000), (563889695092290032362744213274331/14073748835532800000000000000000000), (-13660648665766455035600113923571/28147497671065600000000000000000000), (84536288960974937763306867191311/112589990684262400000000000000000000), (7013504675307834215246725111789/112589990684262400000000000000000000), (-3255131668993691177113757331037/112589990684262400000000000000000000), (-184756884583741545423647766417/112589990684262400000000000000000000), (31314805970166663291724566423/56294995342131200000000000000000000), (2687242454749067181952073083/112589990684262400000000000000000000), (-71799975765169218360888213/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial165.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial165.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial165.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 9958228560678414607032864258676976), (Int.ofNat 5264622833954624646492943383927379), (Int.ofNat 359613967910007672966877118245899), (Int.ofNat 16763110118595171018805371894566), (Int.negOfNat 19067570710518741979278533796026), (Int.negOfNat 488566498706182762105685560966), (Int.ofNat 510062896896560862593556499294), (Int.ofNat 7745466551653140908793222727), (Int.negOfNat 7528040034053313015282137432), (Int.negOfNat 82773027316604147324521944), (Int.ofNat 69765896710003238847428999), (Int.ofNat 642429477640071895009974), (Int.negOfNat 440324708543821073426924), (Int.negOfNat 3690616219682105793160), (Int.ofNat 2000140798915290276200), (Int.ofNat 18191357614984934423), (Int.negOfNat 6828681933646708300), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(622389285042400912939554016167311/7036874417766400000000000000000000), (5264622833954624646492943383927379/112589990684262400000000000000000000), (359613967910007672966877118245899/112589990684262400000000000000000000), (8381555059297585509402685947283/56294995342131200000000000000000000), (-9533785355259370989639266898013/56294995342131200000000000000000000), (-244283249353091381052842780483/56294995342131200000000000000000000), (255031448448280431296778249647/56294995342131200000000000000000000), (7745466551653140908793222727/112589990684262400000000000000000000), (-941005004256664126910267179/14073748835532800000000000000000000), (-10346628414575518415565243/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial165.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial165.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial165.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 21771056563908051877142616697633216), (Int.ofNat 6348844716899280971058785702664513), (Int.ofNat 78026185622841229028880732445943), (Int.negOfNat 82258275627259765488864183224569), (Int.ofNat 963807996463174620741399688471), (Int.ofNat 3281147031623490993466457503004), (Int.negOfNat 61679916162975475988731798688), (Int.negOfNat 64954598362364913544018230930), (Int.ofNat 1123978650009306814083348820), (Int.ofNat 760138597853294060779786911), (Int.negOfNat 10630917867185413471361200), (Int.negOfNat 5823415978779558159800643), (Int.ofNat 62071168967115268909537), (Int.ofNat 31237404677232880095173), (Int.negOfNat 246091639556166647190), (Int.negOfNat 123846895637307343231), (Int.ofNat 1562678542627055690), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(340172758811063310580353385900519/1759218604441600000000000000000000), (6348844716899280971058785702664513/112589990684262400000000000000000000), (78026185622841229028880732445943/112589990684262400000000000000000000), (-82258275627259765488864183224569/112589990684262400000000000000000000), (963807996463174620741399688471/112589990684262400000000000000000000), (820286757905872748366614375751/28147497671065600000000000000000000), (-1927497380092983624647868709/3518437208883200000000000000000000), (-6495459836236491354401823093/11258999068426240000000000000000000), (56198932500465340704167441/5629499534213120000000000000000000), (760138597853294060779786911/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial165.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial165.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial165.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 34231595084244067303542712708194613), (Int.ofNat 5929026986097737059654046303006484), (Int.negOfNat 183113559131067356695991869709647), (Int.ofNat 16161847374071761250843842357957), (Int.ofNat 15840789529277881704443282468931), (Int.negOfNat 1121159813913113618128828543258), (Int.negOfNat 446115476559493341577503229115), (Int.ofNat 26240337852895775920645861875), (Int.ofNat 6842305257250842161113786803), (Int.negOfNat 318968772999733805947504937), (Int.negOfNat 65428275223642322539684332), (Int.ofNat 2376381299905122064270850), (Int.ofNat 423092209436015347674552), (Int.negOfNat 11965892780855078104045), (Int.negOfNat 1957626820010588589129), (Int.ofNat 42649535176922055800), (Int.ofNat 5878604878324855810), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(34231595084244067303542712708194613/112589990684262400000000000000000000), (1482256746524434264913511575751621/28147497671065600000000000000000000), (-183113559131067356695991869709647/112589990684262400000000000000000000), (16161847374071761250843842357957/112589990684262400000000000000000000), (15840789529277881704443282468931/112589990684262400000000000000000000), (-560579906956556809064414271629/56294995342131200000000000000000000), (-89223095311898668315500645823/22517998136852480000000000000000000), (41984540564633241473033379/180143985094819840000000000000000), (6842305257250842161113786803/112589990684262400000000000000000000), (-318968772999733805947504937/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial165.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial165.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial165.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 45680400281292423898942086651706870), (Int.ofNat 5739801839809083844883145908953577), (Int.ofNat 125040273831493285299322397007818), (Int.ofNat 51042724818008989780399177301709), (Int.negOfNat 9144721892617652825419862907964), (Int.negOfNat 2268259625225695009408910799726), (Int.ofNat 309584550616815567214805764391), (Int.ofNat 48179018869924215416000752257), (Int.negOfNat 5001462733671494300481084756), (Int.negOfNat 599657208296435743117263828), (Int.ofNat 46991901781591599627267568), (Int.ofNat 4832862012335693987207049), (Int.negOfNat 287584300875446870388898), (Int.negOfNat 26916705029931190949254), (Int.ofNat 1237873123243428717371), (Int.ofNat 109443811764007089571), (Int.negOfNat 4926197166897064190), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(4568040028129242389894208665170687/11258999068426240000000000000000000), (5739801839809083844883145908953577/112589990684262400000000000000000000), (62520136915746642649661198503909/56294995342131200000000000000000000), (51042724818008989780399177301709/112589990684262400000000000000000000), (-2286180473154413206354965726991/28147497671065600000000000000000000), (-1134129812612847504704455399863/56294995342131200000000000000000000), (309584550616815567214805764391/112589990684262400000000000000000000), (48179018869924215416000752257/112589990684262400000000000000000000), (-1250365683417873575120271189/28147497671065600000000000000000000), (-149914302074108935779315957/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial165.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial165.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial165.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 57874056565682574517048638909312530), (Int.ofNat 6453191789652469338860141389460803), (Int.ofNat 125967528382311368303927595209030), (Int.negOfNat 47631271905869885771881841499698), (Int.negOfNat 6990623490827248758427014154901), (Int.ofNat 2529607141835282577234223607510), (Int.ofNat 228570990090629901171833372383), (Int.negOfNat 57115793483772888767537336737), (Int.negOfNat 4032611321459695661395371207), (Int.ofNat 695963755704143543308367170), (Int.ofNat 43383390377823902089914127), (Int.negOfNat 5247975545280094746456282), (Int.negOfNat 305760930853895195429973), (Int.ofNat 26845349726900390120380), (Int.ofNat 1501335347234408576965), (Int.negOfNat 99398926682863368423), (Int.negOfNat 4928527823003003320), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(5787405656568257451704863890931253/11258999068426240000000000000000000), (6453191789652469338860141389460803/112589990684262400000000000000000000), (12596752838231136830392759520903/11258999068426240000000000000000000), (-23815635952934942885940920749849/56294995342131200000000000000000000), (-6990623490827248758427014154901/112589990684262400000000000000000000), (252960714183528257723422360751/11258999068426240000000000000000000), (228570990090629901171833372383/112589990684262400000000000000000000), (-57115793483772888767537336737/112589990684262400000000000000000000), (-4032611321459695661395371207/112589990684262400000000000000000000), (69596375570414354330836717/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial165.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial165.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial165.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 70879031907954516130466059196258859), (Int.ofNat 6380084190980277737896956955914508), (Int.negOfNat 112434627862117563559507963015876), (Int.negOfNat 851371595232539617226674285966), (Int.ofNat 14650591084974207932474585159994), (Int.ofNat 244895752060700087178827572074), (Int.negOfNat 498156260199844285512955598405), (Int.negOfNat 11811534939208973334820055022), (Int.ofNat 8252780916483525187250718493), (Int.ofNat 236332466013286950802223547), (Int.negOfNat 78869074961526000191843696), (Int.negOfNat 2506574023792871064875051), (Int.ofNat 486597427545684859904705), (Int.ofNat 16272262651640811643162), (Int.negOfNat 2107370552765763179526), (Int.negOfNat 73250655099121347571), (Int.ofNat 8289715791167072690), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(70879031907954516130466059196258859/112589990684262400000000000000000000), (1595021047745069434474239238978627/28147497671065600000000000000000000), (-28108656965529390889876990753969/28147497671065600000000000000000000), (-425685797616269808613337142983/56294995342131200000000000000000000), (7325295542487103966237292579997/56294995342131200000000000000000000), (122447876030350043589413786037/56294995342131200000000000000000000), (-99631252039968857102591119681/22517998136852480000000000000000000), (-5905767469604486667410027511/56294995342131200000000000000000000), (8252780916483525187250718493/112589990684262400000000000000000000), (236332466013286950802223547/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial165.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial165.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial165.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 83393652958622173551704446695850793), (Int.ofNat 6316178108454383299282375928282934), (Int.ofNat 141101632138994418116434090414679), (Int.ofNat 54629827425808373538598198876896), (Int.negOfNat 7001619154455093008611284156394), (Int.negOfNat 3209198772456901716830011495131), (Int.ofNat 148155547331024783455521045427), (Int.ofNat 78433326008898767439368164390), (Int.negOfNat 914499113596298126448498904), (Int.negOfNat 997148318504584211780989623), (Int.negOfNat 5157031823272637477192636), (Int.ofNat 7594638351090576698822536), (Int.ofNat 101802472065957012344934), (Int.negOfNat 38906886511751356962865), (Int.negOfNat 689798366888840046464), (Int.ofNat 146628379859623805446), (Int.ofNat 2857277892924481330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(83393652958622173551704446695850793/112589990684262400000000000000000000), (3158089054227191649641187964141467/56294995342131200000000000000000000), (141101632138994418116434090414679/112589990684262400000000000000000000), (1707182107056511673081193714903/3518437208883200000000000000000000), (-3500809577227546504305642078197/56294995342131200000000000000000000), (-3209198772456901716830011495131/112589990684262400000000000000000000), (148155547331024783455521045427/112589990684262400000000000000000000), (7843332600889876743936816439/11258999068426240000000000000000000), (-114312389199537265806062363/14073748835532800000000000000000000), (-997148318504584211780989623/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial165.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial165.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial165.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 96831521190177005704562015141976257), (Int.ofNat 7115764499298004444957884341164882), (Int.ofNat 126291711959083115843623429362671), (Int.negOfNat 68881555873042806813109430315095), (Int.negOfNat 13037827615130044596322625572267), (Int.ofNat 2917348654845085220409112742127), (Int.ofNat 565995305114754839371041258807), (Int.negOfNat 46387140831610761982655924910), (Int.negOfNat 10571287994131236369986908384), (Int.ofNat 308499581449995961257667183), (Int.ofNat 103092256418464215935548124), (Int.negOfNat 879577063596287286517336), (Int.negOfNat 634573633973310863730306), (Int.negOfNat 803069441665839521655), (Int.ofNat 2732479676215228989336), (Int.ofNat 18637308757288695314), (Int.negOfNat 9898676837132510030), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(96831521190177005704562015141976257/112589990684262400000000000000000000), (3557882249649002222478942170582441/56294995342131200000000000000000000), (126291711959083115843623429362671/112589990684262400000000000000000000), (-13776311174608561362621886063019/22517998136852480000000000000000000), (-13037827615130044596322625572267/112589990684262400000000000000000000), (2917348654845085220409112742127/112589990684262400000000000000000000), (565995305114754839371041258807/112589990684262400000000000000000000), (-4638714083161076198265592491/11258999068426240000000000000000000), (-330352749816601136562090887/3518437208883200000000000000000000), (308499581449995961257667183/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial165.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial165.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial165.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 110929753556360929390010752546097788), (Int.ofNat 6688808128919665174523508737540822), (Int.negOfNat 278252205435116201052080761423971), (Int.negOfNat 7716373309216903504428793735880), (Int.ofNat 27781493032918103349305624819203), (Int.ofNat 2442284482531598789161193938833), (Int.negOfNat 762336447653679550460317477325), (Int.negOfNat 91770318030952560612309670858), (Int.ofNat 7830045991212937659100563813), (Int.ofNat 1218997063009026169024072693), (Int.negOfNat 44548743860184854383677936), (Int.negOfNat 9208651135081037145637549), (Int.ofNat 158524845839305599870265), (Int.ofNat 46636866055571453036158), (Int.negOfNat 350984002680661559526), (Int.negOfNat 175336680910920995189), (Int.ofNat 18452560136759330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(27732438389090232347502688136524447/28147497671065600000000000000000000), (3344404064459832587261754368770411/56294995342131200000000000000000000), (-278252205435116201052080761423971/112589990684262400000000000000000000), (-192909332730422587610719843397/2814749767106560000000000000000000), (27781493032918103349305624819203/112589990684262400000000000000000000), (2442284482531598789161193938833/112589990684262400000000000000000000), (-30493457906147182018412699093/4503599627370496000000000000000000), (-45885159015476280306154835429/56294995342131200000000000000000000), (7830045991212937659100563813/112589990684262400000000000000000000), (1218997063009026169024072693/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial165.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial165.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial165.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 123597316025571559409540973797284843), (Int.ofNat 6390612679769794339839014787510595), (Int.ofNat 311851693797097294109797560975292), (Int.ofNat 158404203286288710025240722548462), (Int.negOfNat 6498272930746420637937052950563), (Int.negOfNat 9050066714983610963601433824306), (Int.negOfNat 617895851741919426799348050097), (Int.ofNat 126368757338198814310228558457), (Int.ofNat 12571021531251082964514480673), (Int.negOfNat 959759712507444950145290530), (Int.negOfNat 119448449747179460465193433), (Int.ofNat 4775111782042613622191482), (Int.ofNat 716958473493128359931067), (Int.negOfNat 16982554814908854971260), (Int.negOfNat 3047397011928442346035), (Int.ofNat 44363034453240777663), (Int.ofNat 10069772656567327040), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(123597316025571559409540973797284843/112589990684262400000000000000000000), (1278122535953958867967802957502119/22517998136852480000000000000000000), (77962923449274323527449390243823/28147497671065600000000000000000000), (79202101643144355012620361274231/56294995342131200000000000000000000), (-6498272930746420637937052950563/112589990684262400000000000000000000), (-4525033357491805481800716912153/56294995342131200000000000000000000), (-617895851741919426799348050097/112589990684262400000000000000000000), (126368757338198814310228558457/112589990684262400000000000000000000), (12571021531251082964514480673/112589990684262400000000000000000000), (-95975971250744495014529053/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial165.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial165.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial165.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 138478854149796426490681458200578178), (Int.ofNat 8555017056470356578080752495179249), (Int.ofNat 335845610865260441737599667494873), (Int.negOfNat 267873261983308053822269146599673), (Int.negOfNat 89801619034918791730371146075036), (Int.negOfNat 2910750362810914340658398446084), (Int.ofNat 1620031513542016904098133679381), (Int.ofNat 114938785969560604969006266023), (Int.negOfNat 15441001742162417774960572276), (Int.negOfNat 1397988777968865273039612212), (Int.ofNat 96136458238259319925711008), (Int.ofNat 10004859056468599827135751), (Int.negOfNat 429081404010812751491058), (Int.negOfNat 49102250280724497189866), (Int.ofNat 1451908079641958784171), (Int.ofNat 179860602398411654189), (Int.negOfNat 3381971184406767830), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(69239427074898213245340729100289089/56294995342131200000000000000000000), (8555017056470356578080752495179249/112589990684262400000000000000000000), (335845610865260441737599667494873/112589990684262400000000000000000000), (-267873261983308053822269146599673/112589990684262400000000000000000000), (-22450404758729697932592786518759/28147497671065600000000000000000000), (-727687590702728585164599611521/28147497671065600000000000000000000), (1620031513542016904098133679381/112589990684262400000000000000000000), (114938785969560604969006266023/112589990684262400000000000000000000), (-3860250435540604443740143069/28147497671065600000000000000000000), (-349497194492216318259903053/28147497671065600000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial165.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial165.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial165.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 153373157012172819849661531189437029), (Int.ofNat 3921506554211965126068205646417018), (Int.negOfNat 3226205556320652332530700662886232), (Int.negOfNat 812493389119546544882275634100963), (Int.negOfNat 10810706368114629434427855325475), (Int.ofNat 17461951951628972323917877808084), (Int.ofNat 996633153025288113161369289295), (Int.negOfNat 203679320260869675656507533995), (Int.negOfNat 15107286115775296823733244677), (Int.ofNat 1550411521337580557142174697), (Int.ofNat 127882667394485717877327028), (Int.negOfNat 8382223737486570458179650), (Int.negOfNat 724704468126284500648688), (Int.ofNat 33956280178455415573125), (Int.ofNat 2981554741284400204871), (Int.negOfNat 104215621921993093040), (Int.negOfNat 9119695601245474550), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(153373157012172819849661531189437029/112589990684262400000000000000000000), (1960753277105982563034102823208509/56294995342131200000000000000000000), (-403275694540081541566337582860779/14073748835532800000000000000000000), (-812493389119546544882275634100963/112589990684262400000000000000000000), (-432428254724585177377114213019/4503599627370496000000000000000000), (4365487987907243080979469452021/28147497671065600000000000000000000), (199326630605057622632273857859/22517998136852480000000000000000000), (-40735864052173935131301506799/22517998136852480000000000000000000), (-15107286115775296823733244677/112589990684262400000000000000000000), (1550411521337580557142174697/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial165.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial165.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial165.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 142231962996787117797631134216398194), (Int.negOfNat 17593470620359798479001081185711250), (Int.negOfNat 6880080581758130492343353847559760), (Int.negOfNat 172296811407343599312355881609690), (Int.ofNat 157195658257518407323760073114820), (Int.ofNat 9393823373248354636777396731596), (Int.negOfNat 2232702628507020386381538848408), (Int.negOfNat 157180046182870823591534884950), (Int.ofNat 20871472416911495501344453740), (Int.ofNat 1522139939704992087005681729), (Int.negOfNat 136591049865801710724658840), (Int.negOfNat 9849918484053419485743557), (Int.ofNat 657604147443188195756497), (Int.ofNat 45856732018492822268747), (Int.negOfNat 2416768835836488908990), (Int.negOfNat 161327681687221021529), (Int.ofNat 6745489808676776330), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(71115981498393558898815567108199097/56294995342131200000000000000000000), (-14074776496287838783200864948569/90071992547409920000000000000000), (-86001007271976631154291923094497/1407374883553280000000000000000000), (-17229681140734359931235588160969/11258999068426240000000000000000000), (7859782912875920366188003655741/5629499534213120000000000000000000), (2348455843312088659194349182899/28147497671065600000000000000000000), (-279087828563377548297692356051/14073748835532800000000000000000000), (-3143600923657416471830697699/2251799813685248000000000000000000), (1043573620845574775067222687/5629499534213120000000000000000000), (1522139939704992087005681729/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial165.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial165.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial165.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 80805011219305465150893518862376075), (Int.negOfNat 41874595922379116275824410551058497), (Int.negOfNat 3988517861628896127768126693532265), (Int.ofNat 1058924184719318925644668058869200), (Int.ofNat 100520046038640918935653278589352), (Int.negOfNat 19496517241921196972061018987117), (Int.negOfNat 1630550978068589214961681981386), (Int.ofNat 233240278700926105220060483993), (Int.ofNat 17208774281729920565304031848), (Int.negOfNat 1888700416740980362774845016), (Int.negOfNat 124515181026008652115047161), (Int.ofNat 10923676781960948537379626), (Int.ofNat 649797274151607601886716), (Int.negOfNat 47124497212381454541120), (Int.negOfNat 2552952057975059010000), (Int.ofNat 155492016605753052817), (Int.ofNat 8169618545923622060), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3232200448772218606035740754495043/4503599627370496000000000000000000), (-41874595922379116275824410551058497/112589990684262400000000000000000000), (-797703572325779225553625338706453/22517998136852480000000000000000000), (2647310461798297314111670147173/281474976710656000000000000000000), (12565005754830114866956659823669/14073748835532800000000000000000000), (-19496517241921196972061018987117/112589990684262400000000000000000000), (-815275489034294607480840990693/56294995342131200000000000000000000), (233240278700926105220060483993/112589990684262400000000000000000000), (2151096785216240070663003981/14073748835532800000000000000000000), (-236087552092622545346855627/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial165.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial165.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial165.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 9513591377095825142412354125968596), (Int.negOfNat 43660462245431952369692641596155445), (Int.ofNat 3004235979383202072619183387544504), (Int.ofNat 972241411470894534542725524091465), (Int.negOfNat 116461421542095364007022876193944), (Int.negOfNat 16201858459126407466549649480026), (Int.ofNat 2062683729500811261480208137533), (Int.ofNat 185218255885198492093663351834), (Int.negOfNat 21916599028320248860844152437), (Int.negOfNat 1475868722672692129688258710), (Int.ofNat 156573059765223623026039085), (Int.ofNat 8521129546345863880681276), (Int.negOfNat 803688241722876998777812), (Int.negOfNat 36928502888969767402668), (Int.ofNat 3108277225497900439511), (Int.ofNat 122239593814076451076), (Int.negOfNat 9792316081172834000), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2378397844273956285603088531492149/28147497671065600000000000000000000), (-8732092449086390473938528319231089/22517998136852480000000000000000000), (375529497422900259077397923443063/14073748835532800000000000000000000), (194448282294178906908545104818293/22517998136852480000000000000000000), (-14557677692761920500877859524243/14073748835532800000000000000000000), (-8100929229563203733274824740013/56294995342131200000000000000000000), (2062683729500811261480208137533/112589990684262400000000000000000000), (92609127942599246046831675917/56294995342131200000000000000000000), (-21916599028320248860844152437/112589990684262400000000000000000000), (-147586872267269212968825871/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial165.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial165.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial165.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial165.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial165.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial165.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial165.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial165.reflect := by
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

end Bin165
end
end ErdosOverlap.OuterNumerics
