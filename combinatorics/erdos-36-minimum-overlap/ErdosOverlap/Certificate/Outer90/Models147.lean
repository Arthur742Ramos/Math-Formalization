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

/-! # Exact integer weighted outer models for source bin 147

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin147

def weightDenominator : ℤ := (Int.ofNat 100000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 24979072252898904000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 24662215833214057000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 21846779931256560000)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 14927545425243452000)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 9629697501368482000)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 5479812085484251500)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 3252836231479721400)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 4983422359866762000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 1720965740982484000)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial147.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial147.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 97129150216278150000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 22696284117454940000)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 14823927492049943000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 9331861573593751000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 2980665908203060700)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 507677142707209200)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 1166319120709139600)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 1064302978044992300)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 29957446124919643)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial147.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial147.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 97129150216278150000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 22696284117454940000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 14823927492049943000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 9331861573593751000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 2980665908203060700)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 507677142707209200)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 1166319120709139600)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 1064302978044992300)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 29957446124919643)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial147.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial147.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial147.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 87061545500068252995639077046640689), (Int.ofNat 49150753317930742617416679781381031), (Int.ofNat 9376365179600788813150725292646740), (Int.negOfNat 1620990368291027488209498665621237), (Int.negOfNat 274719385710550708580756355288971), (Int.ofNat 32987196636404062731063260301137), (Int.ofNat 4321208764694951229947186071967), (Int.negOfNat 409563060064512406523603729567), (Int.negOfNat 42376733739182957077387819972), (Int.ofNat 3351761895404602344513573616), (Int.ofNat 281985785030609521149360207), (Int.negOfNat 19328729550879468920457302), (Int.negOfNat 1353593756047179252077601), (Int.ofNat 82672091991751557527721), (Int.ofNat 4903556460079931312105), (Int.negOfNat 270536337430250488655), (Int.negOfNat 14472809366074656442), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-87061545500068252995639077046640689/112589990684262400000000000000000000), (49150753317930742617416679781381031/112589990684262400000000000000000000), (468818258980039440657536264632337/5629499534213120000000000000000000), (-1620990368291027488209498665621237/112589990684262400000000000000000000), (-274719385710550708580756355288971/112589990684262400000000000000000000), (32987196636404062731063260301137/112589990684262400000000000000000000), (4321208764694951229947186071967/112589990684262400000000000000000000), (-409563060064512406523603729567/112589990684262400000000000000000000), (-10594183434795739269346954993/28147497671065600000000000000000000), (209485118462787646532098351/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial147.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial147.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial147.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial147 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 32652824348202704999142226890120503), (Int.ofNat 61663999195304001056030312395040262), (Int.negOfNat 3599869541013554453644247566178297), (Int.negOfNat 2091749838496415715806362928924453), (Int.ofNat 168636174877345518859692262030125), (Int.ofNat 39807307630046457494958545387460), (Int.negOfNat 3303673584026245447431768011223), (Int.negOfNat 459870561114930162746865766921), (Int.ofNat 36565928545380299770240376321), (Int.ofNat 3514446721445956282417156071), (Int.negOfNat 264104491589332810725090832), (Int.negOfNat 18966448913934658961950055), (Int.ofNat 1352518988357506203021525), (Int.ofNat 76032079167127511153857), (Int.negOfNat 5191281387838246726768), (Int.negOfNat 233156809292761345183), (Int.ofNat 16085709353198836272), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(32652824348202704999142226890120503/112589990684262400000000000000000000), (30831999597652000528015156197520131/56294995342131200000000000000000000), (-3599869541013554453644247566178297/112589990684262400000000000000000000), (-2091749838496415715806362928924453/112589990684262400000000000000000000), (1349089399018764150877538096241/900719925474099200000000000000000), (1990365381502322874747927269373/5629499534213120000000000000000000), (-3303673584026245447431768011223/112589990684262400000000000000000000), (-459870561114930162746865766921/112589990684262400000000000000000000), (36565928545380299770240376321/112589990684262400000000000000000000), (3514446721445956282417156071/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial147.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial147.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial147.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial147 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 128559917027187730719482651636618952), (Int.ofNat 29948149423949482906502652548971095), (Int.negOfNat 9942184853098537942323223507232232), (Int.ofNat 143248989350825262921817853748351), (Int.ofNat 290691840606926332060417625384540), (Int.negOfNat 17533503207366956397101992605468), (Int.negOfNat 4360326931122187374628696102624), (Int.ofNat 317644402700146545072881752107), (Int.ofNat 39960833884318585634160048048), (Int.negOfNat 3072315080150770389741994373), (Int.negOfNat 247086956029365765488964782), (Int.ofNat 19430042987222581830272463), (Int.ofNat 1101223021357897005724660), (Int.negOfNat 88040765360787810280000), (Int.negOfNat 3709305935448067324745), (Int.ofNat 301363273005331730377), (Int.ofNat 9279954697002284799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(16069989628398466339935331454577369/14073748835532800000000000000000000), (5989629884789896581300530509794219/22517998136852480000000000000000000), (-1242773106637317242790402938404029/14073748835532800000000000000000000), (143248989350825262921817853748351/112589990684262400000000000000000000), (14534592030346316603020881269227/5629499534213120000000000000000000), (-4383375801841739099275498151367/28147497671065600000000000000000000), (-136260216597568355457146753207/3518437208883200000000000000000000), (317644402700146545072881752107/112589990684262400000000000000000000), (2497552117769911602135003003/7036874417766400000000000000000000), (-3072315080150770389741994373/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial147.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial147.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial147.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial147 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 153693510747391680412732526106351119), (Int.negOfNat 864204468504711635013102839602614), (Int.negOfNat 4286575876135430494007471428120384), (Int.ofNat 1299886749345971094339503389674862), (Int.negOfNat 27349526153510412781644290351651), (Int.negOfNat 32804812140947416055556702575800), (Int.ofNat 1998516010091938621466824382013), (Int.ofNat 397138498611391642625265513338), (Int.negOfNat 29516413664593982354650367748), (Int.negOfNat 2940691680793129872515779384), (Int.ofNat 242058847061291922449251169), (Int.ofNat 14849933277335568531140333), (Int.negOfNat 1328453174025867259012252), (Int.negOfNat 54666633679337855842186), (Int.ofNat 5308877541933379980732), (Int.ofNat 147825479672472490138), (Int.negOfNat 15995837014824077343), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(153693510747391680412732526106351119/112589990684262400000000000000000000), (-432102234252355817506551419801307/56294995342131200000000000000000000), (-66977748064616101468866741064381/1759218604441600000000000000000000), (649943374672985547169751694837431/56294995342131200000000000000000000), (-27349526153510412781644290351651/112589990684262400000000000000000000), (-164024060704737080277783512879/562949953421312000000000000000000), (1998516010091938621466824382013/112589990684262400000000000000000000), (198569249305695821312632756669/56294995342131200000000000000000000), (-7379103416148495588662591937/28147497671065600000000000000000000), (-367586460099141234064472423/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial147.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial147.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial147.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial147 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 143900495292840573806093505704839519), (Int.negOfNat 5385432138459134996389965190995348), (Int.ofNat 915158071284990853317843800345847), (Int.ofNat 246539412769893134398231067982926), (Int.negOfNat 165505230373011627024035714486734), (Int.ofNat 7629355186389949151567108549205), (Int.ofNat 3223103823622994116818158992954), (Int.negOfNat 224983892111196992851867850132), (Int.negOfNat 30957506575265519992923046854), (Int.ofNat 2568618192519824941046829278), (Int.ofNat 184078064561149125411192661), (Int.negOfNat 17644337879892102922034535), (Int.negOfNat 750213918867676099350981), (Int.ofNat 83813371307576225899965), (Int.ofNat 2218929053513433951304), (Int.negOfNat 299677666194784356041), (Int.negOfNat 4117057474054832799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(143900495292840573806093505704839519/112589990684262400000000000000000000), (-1346358034614783749097491297748837/28147497671065600000000000000000000), (915158071284990853317843800345847/112589990684262400000000000000000000), (123269706384946567199115533991463/56294995342131200000000000000000000), (-82752615186505813512017857243367/56294995342131200000000000000000000), (1525871037277989830313421709841/22517998136852480000000000000000000), (1611551911811497058409079496477/56294995342131200000000000000000000), (-56245973027799248212966962533/28147497671065600000000000000000000), (-15478753287632759996461523427/56294995342131200000000000000000000), (1284309096259912470523414639/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial147.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial147.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial147.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial147 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 136529655001041925796419918421784173), (Int.negOfNat 2959155157587732763951860558052630), (Int.negOfNat 387079515842112889518093296424986), (Int.negOfNat 422266277697814559134759164819957), (Int.ofNat 18529076915841261139150504758527), (Int.ofNat 19632925809201772722678928806875), (Int.negOfNat 1335177850575323135339428430117), (Int.negOfNat 276203353822993884456996765906), (Int.ofNat 22808287740353942986737150485), (Int.ofNat 2052259659216609946308616368), (Int.negOfNat 203742112292833401844112285), (Int.negOfNat 9539381815918498471815551), (Int.ofNat 1176187492549414881644916), (Int.ofNat 29774295502374347268598), (Int.negOfNat 4848820477273009751491), (Int.negOfNat 62904203724196781353), (Int.ofNat 15905964676449318414), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(136529655001041925796419918421784173/112589990684262400000000000000000000), (-295915515758773276395186055805263/11258999068426240000000000000000000), (-193539757921056444759046648212493/56294995342131200000000000000000000), (-422266277697814559134759164819957/112589990684262400000000000000000000), (18529076915841261139150504758527/112589990684262400000000000000000000), (31412681294722836356286286091/180143985094819840000000000000000), (-1335177850575323135339428430117/112589990684262400000000000000000000), (-138101676911496942228498382953/56294995342131200000000000000000000), (4561657548070788597347430097/22517998136852480000000000000000000), (128266228701038121644288523/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial147.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial147.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial147.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial147 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 126495476336885368981055400285455504), (Int.negOfNat 7764233867305730849528787041436815), (Int.negOfNat 1363600666210521639781305974698284), (Int.ofNat 191491557771697912070336559094328), (Int.ofNat 88244395633969147957293689074346), (Int.negOfNat 7035838347967349897476885368720), (Int.negOfNat 2021651054493558344181381661161), (Int.ofNat 169228315615099937513043967698), (Int.ofNat 20090759997124701287833924593), (Int.negOfNat 2019515724544365285653682610), (Int.negOfNat 111117625400657036060786960), (Int.ofNat 14517722079995295223953572), (Int.ofNat 370677839324044022402435), (Int.negOfNat 71123162681972000025507), (Int.negOfNat 676045794963100304841), (Int.ofNat 260379823225357419591), (Int.negOfNat 1045839748892619201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(7905967271055335561315962517840969/7036874417766400000000000000000000), (-1552846773461146169905757408287363/22517998136852480000000000000000000), (-340900166552630409945326493674571/28147497671065600000000000000000000), (23936444721462239008792069886791/14073748835532800000000000000000000), (44122197816984573978646844537173/56294995342131200000000000000000000), (-87947979349591873718461067109/1407374883553280000000000000000000), (-2021651054493558344181381661161/112589990684262400000000000000000000), (84614157807549968756521983849/56294995342131200000000000000000000), (20090759997124701287833924593/112589990684262400000000000000000000), (-201951572454436528565368261/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial147.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial147.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial147.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial147 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 108127603582592887733600103113807454), (Int.negOfNat 8956607078002693275932286604983107), (Int.ofNat 994711392291334069364901153785839), (Int.ofNat 411389946420686030475967894901031), (Int.negOfNat 42529415977381509118950656337744), (Int.negOfNat 12603736190323512630579876370194), (Int.ofNat 1088280783245490739600245475001), (Int.ofNat 171541321838818222673992569999), (Int.negOfNat 17020982669988442279128438875), (Int.negOfNat 1175312936832664697267828195), (Int.ofNat 155376244430703373198740221), (Int.ofNat 4304045906532367492188297), (Int.negOfNat 921593019564247122236854), (Int.negOfNat 6032579343601256224277), (Int.ofNat 3857559817415039312336), (Int.negOfNat 23077613404129324872), (Int.negOfNat 14095126597092075485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(54063801791296443866800051556903727/56294995342131200000000000000000000), (-8956607078002693275932286604983107/112589990684262400000000000000000000), (994711392291334069364901153785839/112589990684262400000000000000000000), (411389946420686030475967894901031/112589990684262400000000000000000000), (-2658088498586344319934416021109/7036874417766400000000000000000000), (-6301868095161756315289938185097/56294995342131200000000000000000000), (1088280783245490739600245475001/112589990684262400000000000000000000), (171541321838818222673992569999/112589990684262400000000000000000000), (-136167861359907538233027511/900719925474099200000000000000000), (-235062587366532939453565639/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial147.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial147.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial147.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial147 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 96487376638503303167260454395852657), (Int.negOfNat 2143837873981524488521059598065209), (Int.ofNat 1776441193562675123820958896830718), (Int.negOfNat 197161248699708778127277171929447), (Int.negOfNat 76885835730253888163268492294015), (Int.ofNat 6158872678308451087302701377937), (Int.ofNat 1326397103782747608464416923001), (Int.negOfNat 120573125590893295247739058199), (Int.negOfNat 11385358864008441331215789875), (Int.ofNat 1413163306428578585114878995), (Int.ofNat 47392607811394680804597021), (Int.negOfNat 10353400210695783606879097), (Int.negOfNat 39162764355806820206854), (Int.ofNat 51636450404302845477077), (Int.negOfNat 630111909196249404464), (Int.negOfNat 190739765303158145728), (Int.ofNat 4427856338607747915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(96487376638503303167260454395852657/112589990684262400000000000000000000), (-2143837873981524488521059598065209/112589990684262400000000000000000000), (888220596781337561910479448415359/56294995342131200000000000000000000), (-197161248699708778127277171929447/112589990684262400000000000000000000), (-15377167146050777632653698458803/22517998136852480000000000000000000), (6158872678308451087302701377937/112589990684262400000000000000000000), (1326397103782747608464416923001/112589990684262400000000000000000000), (-120573125590893295247739058199/112589990684262400000000000000000000), (-91082870912067530649726319/900719925474099200000000000000000), (282632661285715717022975799/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial147.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial147.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial147.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial147 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 96762378744315473933554535311186586), (Int.ofNat 820731492540643511503974772645369), (Int.negOfNat 535397455443597840228738721085031), (Int.negOfNat 433695296268942286964229136195740), (Int.ofNat 23684957978984230302628149511832), (Int.ofNat 9783709331738551666306404578720), (Int.negOfNat 672857171677369441767699389561), (Int.negOfNat 104284899039281764410295467898), (Int.ofNat 10476453227259657389120856393), (Int.ofNat 513595400464356753449135810), (Int.negOfNat 97470174373922123286070760), (Int.negOfNat 204468974616551827249772), (Int.ofNat 589700230463448713807235), (Int.negOfNat 12358955735204221488493), (Int.negOfNat 2504846180275181614441), (Int.ofNat 84675686271187187409), (Int.ofNat 10593280222877268199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(48381189372157736966777267655593293/56294995342131200000000000000000000), (820731492540643511503974772645369/112589990684262400000000000000000000), (-535397455443597840228738721085031/112589990684262400000000000000000000), (-21684764813447114348211456809787/5629499534213120000000000000000000), (2960619747373028787828518688979/14073748835532800000000000000000000), (61148183323365947914415028617/703687441776640000000000000000000), (-672857171677369441767699389561/112589990684262400000000000000000000), (-52142449519640882205147733949/56294995342131200000000000000000000), (10476453227259657389120856393/112589990684262400000000000000000000), (51359540046435675344913581/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial147.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial147.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial147.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial147 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 93431163218758804557439340628689423), (Int.negOfNat 5149071261012595826624701096972190), (Int.negOfNat 1997949797417007878894157052906949), (Int.ofNat 1166291383827109450561364590672), (Int.ofNat 64504580336873202332898816462555), (Int.negOfNat 2060231737111487889291868400675), (Int.negOfNat 914366434127085975688911678117), (Int.ofNat 55309985832269125730420899506), (Int.ofNat 5677109277450547448892594485), (Int.negOfNat 708719403209115072623135568), (Int.negOfNat 3540575400230601455185885), (Int.ofNat 5421323004143621830050751), (Int.negOfNat 187877390897058660530484), (Int.negOfNat 27592321014258974870598), (Int.ofNat 1505267764982313674709), (Int.ofNat 97674601395688056753), (Int.negOfNat 6058949741215472986), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(93431163218758804557439340628689423/112589990684262400000000000000000000), (-514907126101259582662470109697219/11258999068426240000000000000000000), (-1997949797417007878894157052906949/112589990684262400000000000000000000), (72893211489194340660085286917/7036874417766400000000000000000000), (12900916067374640466579763292511/22517998136852480000000000000000000), (-82409269484459515571674736027/4503599627370496000000000000000000), (-914366434127085975688911678117/112589990684262400000000000000000000), (27654992916134562865210449753/56294995342131200000000000000000000), (1135421855490109489778518897/22517998136852480000000000000000000), (-44294962700569692038945973/7036874417766400000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial147.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial147.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial147.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial147 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 76066354919147800969919856793337174), (Int.negOfNat 11374108888954180319844070481829518), (Int.negOfNat 782937289523544825219281814073495), (Int.ofNat 325978573926213524633190407367600), (Int.ofNat 8177145050366135439642700331923), (Int.negOfNat 7166633737516352959603806814962), (Int.ofNat 71981501391498126724274518354), (Int.ofNat 62302732153171394492246332332), (Int.negOfNat 2838917830079078688943895254), (Int.negOfNat 115853883987958114140537678), (Int.ofNat 32821560462920798132464061), (Int.negOfNat 2190470674558744823701065), (Int.negOfNat 214602894854283773667381), (Int.ofNat 22576811003940792402835), (Int.ofNat 928325804642517483304), (Int.negOfNat 117724948396642438159), (Int.negOfNat 5430382999929816199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(38033177459573900484959928396668587/56294995342131200000000000000000000), (-5687054444477090159922035240914759/56294995342131200000000000000000000), (-156587457904708965043856362814699/22517998136852480000000000000000000), (814946434815533811582976018419/281474976710656000000000000000000), (8177145050366135439642700331923/112589990684262400000000000000000000), (-3583316868758176479801903407481/56294995342131200000000000000000000), (35990750695749063362137259177/56294995342131200000000000000000000), (15575683038292848623061583083/28147497671065600000000000000000000), (-1419458915039539344471947627/56294995342131200000000000000000000), (-57926941993979057070268839/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial147.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial147.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial147.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial147 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 52707542541965705192624923979326527), (Int.negOfNat 10867079745479967531979350861342588), (Int.ofNat 849682505265316575398491998336993), (Int.ofNat 145821307210246741647092451180724), (Int.negOfNat 45041964104848035838051183492579), (Int.negOfNat 2388653064525803268622959724200), (Int.ofNat 618975839623030005216596708170), (Int.ofNat 17388640516724505706730294662), (Int.negOfNat 2599446011954978666361229548), (Int.negOfNat 40264398473829926286745016), (Int.negOfNat 17167434480311757237290231), (Int.negOfNat 222238842488231407979133), (Int.ofNat 282011503666067530148748), (Int.ofNat 2008003647703021566386), (Int.negOfNat 1804454773871454271668), (Int.negOfNat 3615440281785429538), (Int.ofNat 5969077402840714057), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(52707542541965705192624923979326527/112589990684262400000000000000000000), (-2716769936369991882994837715335647/28147497671065600000000000000000000), (849682505265316575398491998336993/112589990684262400000000000000000000), (36455326802561685411773112795181/28147497671065600000000000000000000), (-45041964104848035838051183492579/112589990684262400000000000000000000), (-11943265322629016343114798621/562949953421312000000000000000000), (61897583962303000521659670817/11258999068426240000000000000000000), (8694320258362252853365147331/56294995342131200000000000000000000), (-649861502988744666590307387/28147497671065600000000000000000000), (-5033049809228740785843127/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial147.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial147.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial147.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial147 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 34782712439595804076699776691469974), (Int.negOfNat 7227133833423265637895431349511814), (Int.ofNat 607721271595751276424599511996742), (Int.negOfNat 206403482066176437306789295646020), (Int.negOfNat 30200321838525495604969624846146), (Int.ofNat 5136403906463461195898098630325), (Int.ofNat 499018911388062755280867035776), (Int.negOfNat 41052275318810809660322548307), (Int.negOfNat 4721797698857682310749009952), (Int.negOfNat 21060170743362930810348027), (Int.ofNat 30909840433190994088951218), (Int.ofNat 2708689243122553027617737), (Int.negOfNat 156380379534629954738740), (Int.negOfNat 23490721487777727055200), (Int.ofNat 639822880471563875255), (Int.ofNat 119547817041677891023), (Int.ofNat 267485776982364199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(17391356219797902038349888345734987/56294995342131200000000000000000000), (-3613566916711632818947715674755907/56294995342131200000000000000000000), (303860635797875638212299755998371/56294995342131200000000000000000000), (-10320174103308821865339464782301/5629499534213120000000000000000000), (-15100160919262747802484812423073/56294995342131200000000000000000000), (205456156258538447835923945213/4503599627370496000000000000000000), (3898585245219240275631773717/879609302220800000000000000000000), (-41052275318810809660322548307/112589990684262400000000000000000000), (-147556178089302572210906561/3518437208883200000000000000000000), (-21060170743362930810348027/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial147.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial147.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial147.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial147 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 20814761114480115922318975767931026), (Int.negOfNat 7755868174393459681081249340895367), (Int.negOfNat 860557759410647231868633433071675), (Int.negOfNat 193705452692127930516476190583734), (Int.ofNat 34739274033273517617864903526353), (Int.ofNat 5825159003022715784247527403340), (Int.negOfNat 488447034987142096195320417423), (Int.negOfNat 81747706742935536025428372479), (Int.ofNat 2039994101577522498247331921), (Int.ofNat 722088301751763594284235129), (Int.ofNat 14944548906939586193785368), (Int.negOfNat 4539379371134178331620145), (Int.negOfNat 239152248069998955416475), (Int.ofNat 21604712482105455960343), (Int.ofNat 1527369061205078273632), (Int.negOfNat 83149804196174115417), (Int.negOfNat 5879205064465955128), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(10407380557240057961159487883965513/56294995342131200000000000000000000), (-7755868174393459681081249340895367/112589990684262400000000000000000000), (-34422310376425889274745337322867/4503599627370496000000000000000000), (-96852726346063965258238095291867/56294995342131200000000000000000000), (34739274033273517617864903526353/112589990684262400000000000000000000), (291257950151135789212376370167/5629499534213120000000000000000000), (-488447034987142096195320417423/112589990684262400000000000000000000), (-81747706742935536025428372479/112589990684262400000000000000000000), (2039994101577522498247331921/112589990684262400000000000000000000), (722088301751763594284235129/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial147.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial147.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial147.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial147 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 1012556436277575145694712791627868), (Int.negOfNat 12071526502112297458186349865542430), (Int.negOfNat 888181761006868908434699266664694), (Int.ofNat 200840637107432436381146785046235), (Int.ofNat 45978959538236624851918265821958), (Int.negOfNat 4562922315308015724367876322294), (Int.negOfNat 944556401140125163151200411433), (Int.ofNat 42074026107216227911342113567), (Int.ofNat 10942953653892809563580533828), (Int.negOfNat 86222169300590680865058016), (Int.negOfNat 84235459027893988358098793), (Int.negOfNat 1455480142904669536056698), (Int.ofNat 469646329169235983969399), (Int.ofNat 15471229846008805651079), (Int.negOfNat 1972898639395284947295), (Int.negOfNat 85044598433042599945), (Int.ofNat 4865453999840168158), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(253139109069393786423678197906967/28147497671065600000000000000000000), (-1207152650211229745818634986554243/11258999068426240000000000000000000), (-444090880503434454217349633332347/56294995342131200000000000000000000), (40168127421486487276229357009247/22517998136852480000000000000000000), (22989479769118312425959132910979/56294995342131200000000000000000000), (-2281461157654007862183938161147/56294995342131200000000000000000000), (-944556401140125163151200411433/112589990684262400000000000000000000), (42074026107216227911342113567/112589990684262400000000000000000000), (2735738413473202390895133457/28147497671065600000000000000000000), (-2694442790643458777033063/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial147.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial147.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial147.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial147 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 24539244782925498525430213272123354), (Int.negOfNat 12259807276567490451314948377829732), (Int.ofNat 875138010498493409602673848558383), (Int.ofNat 276434586188123651164237039706939), (Int.negOfNat 33765101457694953833953561445843), (Int.negOfNat 8306589564682997326240582189337), (Int.ofNat 537093039542107161863291845633), (Int.ofNat 128830990554534807171787533567), (Int.negOfNat 3760905148246598091931084228), (Int.negOfNat 1230143025255973080404602816), (Int.ofNat 7314526246051996620442393), (Int.ofNat 8138233675773413712030902), (Int.ofNat 75727887365526189081801), (Int.negOfNat 39694332196857140644321), (Int.negOfNat 738879014826251654905), (Int.ofNat 151630189674913301055), (Int.ofNat 2377358690251147842), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-12269622391462749262715106636061677/56294995342131200000000000000000000), (-3064951819141872612828737094457433/28147497671065600000000000000000000), (875138010498493409602673848558383/112589990684262400000000000000000000), (276434586188123651164237039706939/112589990684262400000000000000000000), (-33765101457694953833953561445843/112589990684262400000000000000000000), (-8306589564682997326240582189337/112589990684262400000000000000000000), (537093039542107161863291845633/112589990684262400000000000000000000), (128830990554534807171787533567/112589990684262400000000000000000000), (-940226287061649522982771057/28147497671065600000000000000000000), (-19220984769624579381321919/1759218604441600000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial147.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial147.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial147.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial147 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 44103587262464315389686686763132537), (Int.negOfNat 7032769061169093469060012199432157), (Int.ofNat 1262236712020415249574280359630319), (Int.negOfNat 180769605238938289681466620046603), (Int.negOfNat 57268080432828385761534650320854), (Int.ofNat 5089411168687505631495729563440), (Int.ofNat 1233332063776799562525237900823), (Int.negOfNat 61000405134701992560025578279), (Int.negOfNat 14893077503049056855825080521), (Int.ofNat 388261919964946031169957329), (Int.ofNat 118602993841885796128135832), (Int.negOfNat 1219504396619008472007945), (Int.negOfNat 676013795823644041128125), (Int.negOfNat 188470170740924220657), (Int.ofNat 2887186067088385471768), (Int.ofNat 26618253553666321983), (Int.negOfNat 8247470589555296872), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-44103587262464315389686686763132537/112589990684262400000000000000000000), (-7032769061169093469060012199432157/112589990684262400000000000000000000), (1262236712020415249574280359630319/112589990684262400000000000000000000), (-180769605238938289681466620046603/112589990684262400000000000000000000), (-28634040216414192880767325160427/56294995342131200000000000000000000), (63617639608593820393696619543/1407374883553280000000000000000000), (1233332063776799562525237900823/112589990684262400000000000000000000), (-61000405134701992560025578279/112589990684262400000000000000000000), (-14893077503049056855825080521/112589990684262400000000000000000000), (388261919964946031169957329/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial147.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial147.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial147.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial147 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 55252135916884147325595346611263787), (Int.negOfNat 5382790319205767258782957287163319), (Int.negOfNat 558266494914694887847750019466037), (Int.negOfNat 295069822624802773777202886662182), (Int.ofNat 36890790081622282495994410621417), (Int.ofNat 9730697190018894462331987930468), (Int.negOfNat 685135183450723225951560952376), (Int.negOfNat 151868410595999574513343869307), (Int.ofNat 7012521583352252417843698952), (Int.ofNat 1477513905041142774173152973), (Int.negOfNat 43814679527631350969325018), (Int.negOfNat 9968157297658751980344263), (Int.ofNat 174982063668536307617140), (Int.ofNat 49315511926566575506400), (Int.negOfNat 446858032473883437855), (Int.negOfNat 185709961481474264177), (Int.ofNat 2815495978821223801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-55252135916884147325595346611263787/112589990684262400000000000000000000), (-5382790319205767258782957287163319/112589990684262400000000000000000000), (-558266494914694887847750019466037/112589990684262400000000000000000000), (-147534911312401386888601443331091/56294995342131200000000000000000000), (36890790081622282495994410621417/112589990684262400000000000000000000), (2432674297504723615582996982617/28147497671065600000000000000000000), (-85641897931340403243945119047/14073748835532800000000000000000000), (-151868410595999574513343869307/112589990684262400000000000000000000), (876565197919031552230462369/14073748835532800000000000000000000), (1477513905041142774173152973/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial147.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial147.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial147.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial147 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 69770506453790742820415226644685411), (Int.negOfNat 9387060883463218131205647876470827), (Int.negOfNat 912729952866280634736957801267739), (Int.ofNat 214065436299908918458104745967352), (Int.ofNat 63407201205745040794643734924323), (Int.negOfNat 5742672129177318038839214467900), (Int.negOfNat 1307204941291142634375681699613), (Int.ofNat 87765070518499997684558093662), (Int.ofNat 15750897599078925785269575148), (Int.negOfNat 803189029864297496197557016), (Int.negOfNat 127373287420253497868057169), (Int.ofNat 4773526689941587943977267), (Int.ofNat 738865218367491442854852), (Int.negOfNat 19633246744182053957614), (Int.negOfNat 3189663506346429077532), (Int.ofNat 55460239835142811662), (Int.ofNat 8157598251180537943), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-69770506453790742820415226644685411/112589990684262400000000000000000000), (-9387060883463218131205647876470827/112589990684262400000000000000000000), (-912729952866280634736957801267739/112589990684262400000000000000000000), (26758179537488614807263093245919/14073748835532800000000000000000000), (63407201205745040794643734924323/112589990684262400000000000000000000), (-57426721291773180388392144679/1125899906842624000000000000000000), (-1307204941291142634375681699613/112589990684262400000000000000000000), (43882535259249998842279046831/56294995342131200000000000000000000), (3937724399769731446317393787/28147497671065600000000000000000000), (-100398628733037187024694627/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial147.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial147.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial147.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial147 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 89721198859034560565568036206595264), (Int.negOfNat 9097546632222223160041315569035586), (Int.ofNat 1202507940252224239511970229039111), (Int.ofNat 353839905034765680954696531763248), (Int.negOfNat 34901906145707154682999441130666), (Int.negOfNat 9440256998274122005800146314048), (Int.ofNat 825617807671360346295434323046), (Int.ofNat 142366222551643894503875693732), (Int.negOfNat 10823241498099564024309679346), (Int.negOfNat 1396617199596015465086662478), (Int.ofNat 87036281669452430421460339), (Int.ofNat 9625853517278606167238135), (Int.negOfNat 468789235197971725982419), (Int.negOfNat 48650393145354363926565), (Int.ofNat 1796964544963566897896), (Int.ofNat 187277190902406611241), (Int.negOfNat 7978393201768675801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1401893732172415008837000565728051/1759218604441600000000000000000000), (-4548773316111111580020657784517793/56294995342131200000000000000000000), (1202507940252224239511970229039111/112589990684262400000000000000000000), (22114994064672855059668533235203/7036874417766400000000000000000000), (-17450953072853577341499720565333/56294995342131200000000000000000000), (-147504015598033156340627286157/1759218604441600000000000000000000), (412808903835680173147717161523/56294995342131200000000000000000000), (35591555637910973625968923433/28147497671065600000000000000000000), (-5411620749049782012154839673/56294995342131200000000000000000000), (-698308599798007732543331239/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial147.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial147.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial147.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial147 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 101068376690698579358424733665638623), (Int.negOfNat 1704979496892086886130759275289850), (Int.ofNat 2001903664452129758810321131477380), (Int.negOfNat 116387072051962238073070601949158), (Int.negOfNat 56156589926269947787883490423256), (Int.ofNat 5686810832250749017155856452468), (Int.ofNat 1066163461197314380646549007317), (Int.negOfNat 113705746118333254053575777894), (Int.negOfNat 12829932177259854630318662685), (Int.ofNat 1244534311959224330132609432), (Int.ofNat 106614268766453813931641285), (Int.negOfNat 8588149197618378917182249), (Int.negOfNat 640173254395501069803516), (Int.ofNat 40758520791108710124202), (Int.ofNat 2863766172827754338691), (Int.negOfNat 137128679551938799047), (Int.negOfNat 8067725912805779014), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-101068376690698579358424733665638623/112589990684262400000000000000000000), (-34099589937841737722615185505797/2251799813685248000000000000000000), (100095183222606487940516056573869/5629499534213120000000000000000000), (-58193536025981119036535300974579/56294995342131200000000000000000000), (-7019573740783743473485436302907/14073748835532800000000000000000000), (1421702708062687254288964113117/28147497671065600000000000000000000), (1066163461197314380646549007317/112589990684262400000000000000000000), (-56852873059166627026787888947/56294995342131200000000000000000000), (-2565986435451970926063732537/22517998136852480000000000000000000), (155566788994903041266576179/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial147.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial147.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial147.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial147 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 98067222892624661183745566366907422), (Int.ofNat 3707852905164967582370875346274161), (Int.ofNat 573931008955082320859375246110080), (Int.negOfNat 246340562245072796393492184739316), (Int.ofNat 24498550274910464320084082719040), (Int.ofNat 6247408281991766968590457787463), (Int.negOfNat 922227844987523757140188575639), (Int.negOfNat 93543184562569583064478201898), (Int.ofNat 14439966266599742407801778607), (Int.ofNat 953200925222672610295690810), (Int.negOfNat 129751371396713747556781840), (Int.negOfNat 6985915959470732270422972), (Int.ofNat 759643883652547303063965), (Int.ofNat 37369500933892559655707), (Int.negOfNat 3140733045764420422359), (Int.negOfNat 151232184164459396191), (Int.ofNat 13141290424716127801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-49033611446312330591872783183453711/56294995342131200000000000000000000), (3707852905164967582370875346274161/112589990684262400000000000000000000), (896767201492316126342773822047/175921860444160000000000000000000), (-61585140561268199098373046184829/28147497671065600000000000000000000), (76557969609095201000262758497/351843720888320000000000000000000), (6247408281991766968590457787463/112589990684262400000000000000000000), (-922227844987523757140188575639/112589990684262400000000000000000000), (-46771592281284791532239100949/56294995342131200000000000000000000), (14439966266599742407801778607/112589990684262400000000000000000000), (95320092522267261029569081/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial147.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial147.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial147.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial147 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 89801578925010791354197008795727151), (Int.ofNat 4128521324293020252154333221629766), (Int.negOfNat 71916856109792600445820446412760), (Int.ofNat 28410235193091088497720539186242), (Int.ofNat 23530382273732839489543538987973), (Int.negOfNat 5453329126424984217301284215306), (Int.negOfNat 462826489992621268468873847401), (Int.ofNat 135105596067824501722850237201), (Int.ofNat 5886338949274507170421970675), (Int.negOfNat 1646839107471587267758616205), (Int.negOfNat 56218304237066781294999021), (Int.ofNat 12109216039502793046300903), (Int.ofNat 385336623889495826616854), (Int.negOfNat 60079949366901679133323), (Int.negOfNat 1888613769762850938536), (Int.ofNat 216604824217305462472), (Int.ofNat 6256887833448536085), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-89801578925010791354197008795727151/112589990684262400000000000000000000), (2064260662146510126077166610814883/56294995342131200000000000000000000), (-1797921402744815011145511160319/2814749767106560000000000000000000), (14205117596545544248860269593121/56294995342131200000000000000000000), (23530382273732839489543538987973/112589990684262400000000000000000000), (-2726664563212492108650642107653/56294995342131200000000000000000000), (-462826489992621268468873847401/112589990684262400000000000000000000), (135105596067824501722850237201/112589990684262400000000000000000000), (235453557970980286816878827/4503599627370496000000000000000000), (-329367821494317453551723241/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial147.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial147.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial147.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial147 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 81414637598222596212562956543252860), (Int.ofNat 4472235209611774023264413307567725), (Int.ofNat 209388983664072108242204421967203), (Int.ofNat 1494741128832154357737881745320), (Int.negOfNat 21208828920078129522026680503014), (Int.negOfNat 418583791557961955501982804737), (Int.ofNat 980106082805041807786926831199), (Int.ofNat 4830058488000901019491565799), (Int.negOfNat 17484951392993499615832820325), (Int.negOfNat 162085219383220367307475395), (Int.ofNat 166863022724774737334202979), (Int.ofNat 2272748335575222368092697), (Int.negOfNat 1008453885134625367280946), (Int.negOfNat 16776559290132473823677), (Int.ofNat 4255452943286995438864), (Int.ofNat 81592126242260122328), (Int.negOfNat 16523307014431256515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-4070731879911129810628147827162643/5629499534213120000000000000000000), (178889408384470960930576532302709/4503599627370496000000000000000000), (209388983664072108242204421967203/112589990684262400000000000000000000), (37368528220803858943447043633/2814749767106560000000000000000000), (-10604414460039064761013340251507/56294995342131200000000000000000000), (-418583791557961955501982804737/112589990684262400000000000000000000), (980106082805041807786926831199/112589990684262400000000000000000000), (4830058488000901019491565799/112589990684262400000000000000000000), (-699398055719739984633312813/4503599627370496000000000000000000), (-32417043876644073461495079/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial147.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial147.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial147.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial147 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 71914432031865017693380404574743968), (Int.ofNat 4788479772169683548328928332544977), (Int.negOfNat 115832770389992848034713615511722), (Int.negOfNat 55058062389658463860175169880748), (Int.ofNat 16736639853296717552621684036882), (Int.ofNat 4897907965840243554650463797423), (Int.negOfNat 485201391424001152206754349439), (Int.negOfNat 151558845530847326062146594102), (Int.ofNat 4794030631061674149482311407), (Int.ofNat 1986538206128896066363987790), (Int.negOfNat 18990282312252753340595240), (Int.negOfNat 14962264050306915547902228), (Int.negOfNat 6629687356461587848035), (Int.ofNat 75081029218334271857693), (Int.ofNat 446917410982445815641), (Int.negOfNat 278202897084363325009), (Int.negOfNat 2755041459233728799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-2247326000995781802918137642960749/3518437208883200000000000000000000), (4788479772169683548328928332544977/112589990684262400000000000000000000), (-57916385194996424017356807755861/56294995342131200000000000000000000), (-13764515597414615965043792470187/28147497671065600000000000000000000), (8368319926648358776310842018441/56294995342131200000000000000000000), (4897907965840243554650463797423/112589990684262400000000000000000000), (-485201391424001152206754349439/112589990684262400000000000000000000), (-75779422765423663031073297051/56294995342131200000000000000000000), (4794030631061674149482311407/112589990684262400000000000000000000), (198653820612889606636398779/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial147.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial147.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial147.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial147 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 62865006320292597440840871386097773), (Int.ofNat 4440024147891068047625402717267410), (Int.ofNat 146151207408872100600559462699255), (Int.ofNat 130614087986974221919534228100513), (Int.ofNat 6685283940787132890216803086617), (Int.negOfNat 8074738954403932633983350500425), (Int.negOfNat 1004416657269600983545161767483), (Int.ofNat 121795425444668371409483462694), (Int.ofNat 20283042165159044168766219515), (Int.negOfNat 896120329795988848778792032), (Int.negOfNat 196745637650578464726041515), (Int.ofNat 3868974948422951894042249), (Int.ofNat 1188266057378094083825484), (Int.negOfNat 10074710384584410760202), (Int.negOfNat 5017430700107883756909), (Int.ofNat 11473037665209966647), (Int.ofNat 18154400417038981586), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-62865006320292597440840871386097773/112589990684262400000000000000000000), (444002414789106804762540271726741/11258999068426240000000000000000000), (29230241481774420120111892539851/22517998136852480000000000000000000), (130614087986974221919534228100513/112589990684262400000000000000000000), (6685283940787132890216803086617/112589990684262400000000000000000000), (-322989558176157305359334020017/4503599627370496000000000000000000), (-1004416657269600983545161767483/112589990684262400000000000000000000), (60897712722334185704741731347/56294995342131200000000000000000000), (4056608433031808833753243903/22517998136852480000000000000000000), (-28003760306124651524337251/3518437208883200000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial147.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial147.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial147.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial147 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 52551015640980414260334010687392386), (Int.ofNat 6039433873644416078318464261784584), (Int.ofNat 315227159251872867718916962380137), (Int.negOfNat 202596097975620947641378628397626), (Int.negOfNat 83459480102598645175233311749223), (Int.negOfNat 3976686215482458395195986127281), (Int.ofNat 1830715270747784689928069751203), (Int.ofNat 175748992929998114530045174068), (Int.negOfNat 18062363875095772513098274146), (Int.negOfNat 2299120488191854209309995522), (Int.ofNat 107537528273011226438136339), (Int.ofNat 16969459754438115368981865), (Int.negOfNat 435641458256793994190019), (Int.negOfNat 83945564612997126700835), (Int.ofNat 1272197378803892289096), (Int.ofNat 304746486746859132959), (Int.negOfNat 2407855763713723201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-26275507820490207130167005343696193/56294995342131200000000000000000000), (754929234205552009789808032723073/14073748835532800000000000000000000), (315227159251872867718916962380137/112589990684262400000000000000000000), (-101298048987810473820689314198813/56294995342131200000000000000000000), (-83459480102598645175233311749223/112589990684262400000000000000000000), (-3976686215482458395195986127281/112589990684262400000000000000000000), (1830715270747784689928069751203/112589990684262400000000000000000000), (43937248232499528632511293517/28147497671065600000000000000000000), (-9031181937547886256549137073/56294995342131200000000000000000000), (-1149560244095927104654997761/56294995342131200000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial147.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial147.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial147.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial147 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 42160610717001502093647841967862535), (Int.ofNat 2287517699954135301836487246097847), (Int.negOfNat 2705324394169293518865687716065813), (Int.negOfNat 680436927008953826834423765989410), (Int.ofNat 8404672790437003520640440091507), (Int.ofNat 21327159339639246098142497911700), (Int.ofNat 1292926459562912379989036363230), (Int.negOfNat 270718714053465215679561758862), (Int.negOfNat 24121354286214629289859270052), (Int.ofNat 2027778813000851591485698816), (Int.ofNat 219986995771727142706637431), (Int.negOfNat 10343125584292178022255467), (Int.negOfNat 1281767547076233918208748), (Int.ofNat 38755498371497267553014), (Int.ofNat 5300751939330947640068), (Int.negOfNat 108785035010592315262), (Int.negOfNat 18064528078664222657), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-8432122143400300418729568393572507/22517998136852480000000000000000000), (2287517699954135301836487246097847/112589990684262400000000000000000000), (-2705324394169293518865687716065813/112589990684262400000000000000000000), (-68043692700895382683442376598941/11258999068426240000000000000000000), (8404672790437003520640440091507/112589990684262400000000000000000000), (213271593396392460981424979117/1125899906842624000000000000000000), (129292645956291237998903636323/11258999068426240000000000000000000), (-135359357026732607839780879431/56294995342131200000000000000000000), (-6030338571553657322464817513/28147497671065600000000000000000000), (7921010988284576529241011/439804651110400000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial147.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial147.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial147.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial147 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 52990266758795046757848053847864239), (Int.negOfNat 14615988128862957663766250129795010), (Int.negOfNat 4783398749127133540287822527676716), (Int.ofNat 265641204919952162668481568674146), (Int.ofNat 206987200527442519518902033946489), (Int.ofNat 8739470465523348930679423597518), (Int.negOfNat 3313438850219983709652745908876), (Int.negOfNat 234257390276618686066562333493), (Int.ofNat 30645314875655633308395180752), (Int.ofNat 2621689838556100261338306627), (Int.negOfNat 190513632606397897014808218), (Int.negOfNat 17973560803634832338119737), (Int.ofNat 860862721240302148937740), (Int.ofNat 85481856002306175902000), (Int.negOfNat 2968000122596709695255), (Int.negOfNat 303316519160414864423), (Int.ofNat 7570752986661175201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-52990266758795046757848053847864239/112589990684262400000000000000000000), (-1461598812886295766376625012979501/11258999068426240000000000000000000), (-1195849687281783385071955631919179/28147497671065600000000000000000000), (132820602459976081334240784337073/56294995342131200000000000000000000), (206987200527442519518902033946489/112589990684262400000000000000000000), (4369735232761674465339711798759/56294995342131200000000000000000000), (-828359712554995927413186477219/28147497671065600000000000000000000), (-234257390276618686066562333493/112589990684262400000000000000000000), (1915332179728477081774698797/7036874417766400000000000000000000), (2621689838556100261338306627/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial147.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial147.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial147.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial147 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 95872335364318331116285200586346692), (Int.negOfNat 23943999592192915485018942937651228), (Int.ofNat 1589019426006255273634973105342553), (Int.ofNat 1675227659123854703891785551958478), (Int.ofNat 71693771876487426348970878248576), (Int.negOfNat 33641179990513183980015228875183), (Int.negOfNat 2238125998023914355698053935377), (Int.ofNat 385263608131364068097090502679), (Int.ofNat 29373280291999675827818074479), (Int.negOfNat 2920223408882451513211068329), (Int.negOfNat 233700165624715425140997768), (Int.ofNat 15805047708533361741585945), (Int.ofNat 1272512590825165281455875), (Int.negOfNat 64205516321960167761143), (Int.negOfNat 5069897681534504858232), (Int.ofNat 198803115720031581617), (Int.ofNat 17974655740289463728), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-23968083841079582779071300146586673/28147497671065600000000000000000000), (-5985999898048228871254735734412807/28147497671065600000000000000000000), (1589019426006255273634973105342553/112589990684262400000000000000000000), (837613829561927351945892775979239/56294995342131200000000000000000000), (560107592785058018351334986317/879609302220800000000000000000000), (-33641179990513183980015228875183/112589990684262400000000000000000000), (-2238125998023914355698053935377/112589990684262400000000000000000000), (385263608131364068097090502679/112589990684262400000000000000000000), (29373280291999675827818074479/112589990684262400000000000000000000), (-2920223408882451513211068329/112589990684262400000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial147.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial147.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial147.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial147 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 124019957227506084328901651171721568), (Int.ofNat 1882953084787944296258150118810829), (Int.ofNat 10428495842658451491579684254584671), (Int.ofNat 794915059502272255824477470404667), (Int.negOfNat 272348145643865181196324566160744), (Int.negOfNat 22178324298154070360172476244606), (Int.ofNat 3989294418347891096963223193476), (Int.ofNat 317207489672166537339639639033), (Int.negOfNat 37724000980820512026776986628), (Int.negOfNat 2853097702534359329904262584), (Int.ofNat 247657863263534886125782993), (Int.ofNat 17612487966181538109247698), (Int.negOfNat 1190232323919350436354399), (Int.negOfNat 78968798245302832162279), (Int.ofNat 4356218173091254463095), (Int.ofNat 265560464320299851945), (Int.negOfNat 12703692763483707558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3875623663359565135278176599116299/3518437208883200000000000000000000), (1882953084787944296258150118810829/112589990684262400000000000000000000), (10428495842658451491579684254584671/112589990684262400000000000000000000), (794915059502272255824477470404667/112589990684262400000000000000000000), (-34043518205483147649540570770093/14073748835532800000000000000000000), (-11089162149077035180086238122303/56294995342131200000000000000000000), (997323604586972774240805798369/28147497671065600000000000000000000), (317207489672166537339639639033/112589990684262400000000000000000000), (-9431000245205128006694246657/28147497671065600000000000000000000), (-356637212816794916238032823/14073748835532800000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial147.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial147.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial147.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial147.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial147 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial147 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial147 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 140024029842736762861258247114828111), (Int.negOfNat 2659739714630392297559238573150431), (Int.ofNat 11094688975560997028429955913318460), (Int.negOfNat 1064486881767076004044746310495763), (Int.negOfNat 287207194125067624989859159955029), (Int.ofNat 30215392415516625323445447668463), (Int.ofNat 4195879776698448264515431779833), (Int.negOfNat 419229037189248317728973357633), (Int.negOfNat 39447464626726839877127555628), (Int.ofNat 3590052303628736877798719384), (Int.ofNat 257028282367200048798764193), (Int.negOfNat 21063217470573647148194298), (Int.negOfNat 1225766045991986721093199), (Int.ofNat 90320617128399890436879), (Int.ofNat 4453803260035646105095), (Int.negOfNat 294835990403617344545), (Int.negOfNat 12703692763483707558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-140024029842736762861258247114828111/112589990684262400000000000000000000), (-2659739714630392297559238573150431/112589990684262400000000000000000000), (554734448778049851421497795665923/5629499534213120000000000000000000), (-1064486881767076004044746310495763/112589990684262400000000000000000000), (-287207194125067624989859159955029/112589990684262400000000000000000000), (30215392415516625323445447668463/112589990684262400000000000000000000), (4195879776698448264515431779833/112589990684262400000000000000000000), (-419229037189248317728973357633/112589990684262400000000000000000000), (-9861866156681709969281888907/28147497671065600000000000000000000), (448756537953592109724839923/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial147.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial147.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial147.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 112902240586417741328085939853358303), (Int.ofNat 22758500219977221836719415558239938), (Int.ofNat 905469556087352995345267535507097), (Int.negOfNat 1765396619279506921801174357019347), (Int.ofNat 122055468695189166514446088510075), (Int.ofNat 36274734954886042849384560674540), (Int.negOfNat 3176772144596491960998509316577), (Int.negOfNat 417620219441654475349938749879), (Int.ofNat 38228705682942771336576262679), (Int.ofNat 3150163321189971180673429729), (Int.negOfNat 284722761419259869047948768), (Int.negOfNat 16873547504124237653905345), (Int.ofNat 1471350214610259117633875), (Int.ofNat 67708820943263827708943), (Int.negOfNat 5632638349580496660432), (Int.negOfNat 208561624414470745817), (Int.ofNat 17974655740289463728), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-112902240586417741328085939853358303/112589990684262400000000000000000000), (11379250109988610918359707779119969/56294995342131200000000000000000000), (905469556087352995345267535507097/112589990684262400000000000000000000), (-1765396619279506921801174357019347/112589990684262400000000000000000000), (4882218747807566660577843540403/4503599627370496000000000000000000), (1813736747744302142469228033727/5629499534213120000000000000000000), (-3176772144596491960998509316577/112589990684262400000000000000000000), (-417620219441654475349938749879/112589990684262400000000000000000000), (38228705682942771336576262679/112589990684262400000000000000000000), (3150163321189971180673429729/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial147.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial147.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial147.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 75018544861467042147924847286892152), (Int.ofNat 11251134101669224964522213346796105), (Int.negOfNat 4819291577265652695288967788486968), (Int.ofNat 421755466870621018213462047049), (Int.ofNat 228446033432572302070227904948460), (Int.negOfNat 16079153461815314459540044210332), (Int.negOfNat 3733897934309996897562328571576), (Int.ofNat 327246450856989902164071027693), (Int.ofNat 34653517377309942546727893752), (Int.negOfNat 3294081451414591476110534827), (Int.negOfNat 213699826907718876609905818), (Int.ofNat 21123815581344045343602337), (Int.ofNat 951369317900274939594740), (Int.negOfNat 95848065507264878592400), (Int.negOfNat 3224974184883607685855), (Int.ofNat 326086372780772914223), (Int.ofNat 7570752986661175201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-9377318107683380268490605910861519/14073748835532800000000000000000000), (2250226820333844992904442669359221/22517998136852480000000000000000000), (-602411447158206586911120973560871/14073748835532800000000000000000000), (421755466870621018213462047049/112589990684262400000000000000000000), (11422301671628615103511395247423/5629499534213120000000000000000000), (-4019788365453828614885011052583/28147497671065600000000000000000000), (-466737241788749612195291071447/14073748835532800000000000000000000), (327246450856989902164071027693/112589990684262400000000000000000000), (4331689672163742818340986719/14073748835532800000000000000000000), (-3294081451414591476110534827/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial147.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial147.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial147.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 68839534987615931615117188818546719), (Int.negOfNat 2540274916624348170683170006408986), (Int.negOfNat 1251513327142430723457521535168416), (Int.ofNat 812735519905794404692654775196538), (Int.negOfNat 41116894518004424737214055516549), (Int.negOfNat 25549381111424803444674895861400), (Int.ofNat 2143002604981439885446694860987), (Int.ofNat 326477295746298495017780959262), (Int.negOfNat 31968177414826463019812112652), (Int.negOfNat 2437805252224737031487139416), (Int.ofNat 264796268244290269069062031), (Int.ofNat 12278591795573873306908667), (Int.negOfNat 1455676911757520485976548), (Int.negOfNat 45138320128625466683414), (Int.ofNat 5791930210284385571468), (Int.ofNat 121796379936511200862), (Int.negOfNat 18064528078664222657), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-68839534987615931615117188818546719/112589990684262400000000000000000000), (-1270137458312174085341585003204493/56294995342131200000000000000000000), (-39109791473200960108047547974013/3518437208883200000000000000000000), (406367759952897202346327387598269/56294995342131200000000000000000000), (-41116894518004424737214055516549/112589990684262400000000000000000000), (-127746905557124017223374479307/562949953421312000000000000000000), (2143002604981439885446694860987/112589990684262400000000000000000000), (163238647873149247508890479631/56294995342131200000000000000000000), (-7992044353706615754953028163/28147497671065600000000000000000000), (-304725656528092128935892427/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial147.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial147.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial147.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 73729905163502894271325865183993719), (Int.negOfNat 632370316804997963169402271704052), (Int.ofNat 1262629683985583287859088753756153), (Int.negOfNat 78446586434663188554696138436926), (Int.negOfNat 118367811965647820331668949820466), (Int.ofNat 10696482524064533024215863423395), (Int.ofNat 2474921682897802083827068478046), (Int.negOfNat 256222521681605204028677377668), (Int.negOfNat 24206542105144712811435928946), (Int.ofNat 2866578707753934685607732522), (Int.ofNat 143143150261853098987458539), (Int.negOfNat 19597527627409507720778665), (Int.negOfNat 574770599741613233761019), (Int.ofNat 92544726973297354927435), (Int.ofNat 1665790562812938578496), (Int.negOfNat 327516340367217182759), (Int.negOfNat 2407855763713723201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-73729905163502894271325865183993719/112589990684262400000000000000000000), (-158092579201249490792350567926013/28147497671065600000000000000000000), (1262629683985583287859088753756153/112589990684262400000000000000000000), (-39223293217331594277348069218463/56294995342131200000000000000000000), (-59183905982823910165834474910233/56294995342131200000000000000000000), (2139296504812906604843172684679/22517998136852480000000000000000000), (1237460841448901041913534239023/56294995342131200000000000000000000), (-64055630420401301007169344417/28147497671065600000000000000000000), (-12103271052572356405717964473/56294995342131200000000000000000000), (1433289353876967342803866261/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial147.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial147.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial147.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 72002323121603830497816851978227973), (Int.ofNat 887455431796126193922270657934430), (Int.negOfNat 800454558999632693686339631478414), (Int.negOfNat 371660447951042034324381113890643), (Int.ofNat 50854608654762686732090535001873), (Int.ofNat 14355116103110162474149400473125), (Int.negOfNat 1718971307992263169231953490683), (Int.negOfNat 201004805079572905751917048094), (Int.ofNat 26601147516107830006794055515), (Int.ofNat 1468468682871008993940809832), (Int.negOfNat 232064796451991473825833715), (Int.negOfNat 6549860558649078702182249), (Int.ofNat 1323978180988750054678484), (Int.ofNat 18889317007127286342802), (Int.negOfNat 5394759702959531439309), (Int.negOfNat 34242891285568016447), (Int.ofNat 18154400417038981586), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-72002323121603830497816851978227973/112589990684262400000000000000000000), (88745543179612619392227065793443/11258999068426240000000000000000000), (-400227279499816346843169815739207/56294995342131200000000000000000000), (-371660447951042034324381113890643/112589990684262400000000000000000000), (50854608654762686732090535001873/112589990684262400000000000000000000), (22968185764976259958639040757/180143985094819840000000000000000), (-1718971307992263169231953490683/112589990684262400000000000000000000), (-100502402539786452875958524047/56294995342131200000000000000000000), (5320229503221566001358811103/22517998136852480000000000000000000), (183558585358876124242601229/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial147.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial147.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial147.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 75257903211945504215921955834477704), (Int.negOfNat 4389230154874632814581744026082185), (Int.negOfNat 1157457073685586174711006062621916), (Int.ofNat 273656184834294662796526739738072), (Int.ofNat 67473868611071011856616835493854), (Int.negOfNat 10209276395768132033930423970280), (Int.negOfNat 1365126010445229354985750636039), (Int.ofNat 212006589244515974073407436102), (Int.ofNat 12868462348751973069979279407), (Int.negOfNat 2400488686187111504154660990), (Int.negOfNat 64942211763380365300946040), (Int.ofNat 16852100823653902338591628), (Int.ofNat 171433596238598304562365), (Int.negOfNat 81221626952403000117293), (Int.negOfNat 54019368665431279959), (Int.ofNat 291214242010282210609), (Int.negOfNat 2755041459233728799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-9407237901493188026990244479309713/14073748835532800000000000000000000), (-877846030974926562916348805216437/22517998136852480000000000000000000), (-289364268421396543677751515655479/28147497671065600000000000000000000), (34207023104286832849565842467259/14073748835532800000000000000000000), (33736934305535505928308417746927/56294995342131200000000000000000000), (-255231909894203300848260599257/2814749767106560000000000000000000), (-1365126010445229354985750636039/112589990684262400000000000000000000), (106003294622257987036703718051/56294995342131200000000000000000000), (12868462348751973069979279407/112589990684262400000000000000000000), (-240048868618711150415466099/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial147.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial147.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial147.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 85782255172517066998729723934780254), (Int.negOfNat 4552383942661022745068823242045093), (Int.ofNat 1113673037075499244402312840139361), (Int.ofNat 315245178762271332035379609342769), (Int.negOfNat 52598992670260717127042689242456), (Int.negOfNat 7890555722690845232443196662006), (Int.ofNat 1454995332436215804304681692799), (Int.ofNat 94713176918203554103416072401), (Int.negOfNat 21561745419409312284939745325), (Int.negOfNat 537908682468410883511523405), (Int.ofNat 189328426206246514586141179), (Int.ofNat 964305523571372399433303), (Int.negOfNat 1094175309456540361250746), (Int.ofNat 6199672501092574985877), (Int.ofNat 4492909988185015101064), (Int.negOfNat 55569436390422351128), (Int.negOfNat 16523307014431256515), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-42891127586258533499364861967390127/56294995342131200000000000000000000), (-4552383942661022745068823242045093/112589990684262400000000000000000000), (1113673037075499244402312840139361/112589990684262400000000000000000000), (315245178762271332035379609342769/112589990684262400000000000000000000), (-6574874083782589640880336155307/14073748835532800000000000000000000), (-3945277861345422616221598331003/56294995342131200000000000000000000), (1454995332436215804304681692799/112589990684262400000000000000000000), (94713176918203554103416072401/112589990684262400000000000000000000), (-862469816776372491397589813/4503599627370496000000000000000000), (-107581736493682176702304681/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial147.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial147.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial147.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 88904811886200456669746269362242257), (Int.ofNat 1670264324242533206490290817852009), (Int.ofNat 1485389495256999691292474254612082), (Int.negOfNat 174030226870314887748542442050153), (Int.negOfNat 41549857400388912555206757167785), (Int.ofNat 8231916458165573574364293401463), (Int.ofNat 594862183641142883639357129199), (Int.negOfNat 166122969192053073549245818601), (Int.negOfNat 3523476765935346073591390725), (Int.ofNat 1858920961165970697896753805), (Int.negOfNat 3444920555576375813734021), (Int.negOfNat 13077257484126305298379303), (Int.ofNat 182242352756133059627254), (Int.ofNat 63232527239972698581323), (Int.negOfNat 1322620265485379414936), (Int.negOfNat 226363332911744626672), (Int.ofNat 6256887833448536085), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-88904811886200456669746269362242257/112589990684262400000000000000000000), (1670264324242533206490290817852009/112589990684262400000000000000000000), (742694747628499845646237127306041/56294995342131200000000000000000000), (-174030226870314887748542442050153/112589990684262400000000000000000000), (-8309971480077782511041351433557/22517998136852480000000000000000000), (8231916458165573574364293401463/112589990684262400000000000000000000), (594862183641142883639357129199/112589990684262400000000000000000000), (-166122969192053073549245818601/112589990684262400000000000000000000), (-140939070637413842943655629/4503599627370496000000000000000000), (371784192233194139579350761/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial147.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial147.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial147.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 81399515340173153114377075359429186), (Int.ofNat 4892725527676004216581469842859831), (Int.ofNat 135562803521734811641754700206831), (Int.negOfNat 171891475034754470114161896988260), (Int.ofNat 32941111996036946556095915551568), (Int.ofNat 3207880787030514373711134172480), (Int.negOfNat 1058067185090440552749065399239), (Int.negOfNat 16511650553723482702233351902), (Int.ofNat 15689280105202808503881904007), (Int.negOfNat 187745236214743423044098210), (Int.negOfNat 136886144184002430733701840), (Int.ofNat 3463907513115188417905772), (Int.ofNat 787350383542757231126365), (Int.negOfNat 25884493271502649135907), (Int.negOfNat 3218801115319933735959), (Int.ofNat 121956658081141903591), (Int.ofNat 13141290424716127801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-40699757670086576557188537679714593/56294995342131200000000000000000000), (4892725527676004216581469842859831/112589990684262400000000000000000000), (135562803521734811641754700206831/112589990684262400000000000000000000), (-8594573751737723505708094849413/5629499534213120000000000000000000), (2058819499752309159755994721973/7036874417766400000000000000000000), (10024627459470357417847294289/351843720888320000000000000000000), (-1058067185090440552749065399239/112589990684262400000000000000000000), (-8255825276861741351116675951/56294995342131200000000000000000000), (15689280105202808503881904007/112589990684262400000000000000000000), (-18774523621474342304409821/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial147.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial147.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial147.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 71883274467524987979850064145994023), (Int.ofNat 4487468023698441030843979097560390), (Int.negOfNat 87782176811426067242266934874251), (Int.ofNat 66643964122985176663161069331928), (Int.ofNat 12121594537692642751500569574445), (Int.negOfNat 5158593472387577865690864606525), (Int.negOfNat 28144672889882164159175841483), (Int.ofNat 110305006849697730878201036494), (Int.negOfNat 3080158202772256091195532485), (Int.negOfNat 1229855714860131214318491832), (Int.ofNat 51865086988710706862337485), (Int.ofNat 8540258808515908368518249), (Int.negOfNat 429351983070443993001716), (Int.negOfNat 40627827777082351856802), (Int.ofNat 2275002814929924765291), (Int.ofNat 137128679551938799047), (Int.negOfNat 8067725912805779014), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-71883274467524987979850064145994023/112589990684262400000000000000000000), (448746802369844103084397909756039/11258999068426240000000000000000000), (-87782176811426067242266934874251/112589990684262400000000000000000000), (8330495515373147082895133666491/14073748835532800000000000000000000), (2424318907538528550300113914889/22517998136852480000000000000000000), (-206343738895503114627634584261/4503599627370496000000000000000000), (-28144672889882164159175841483/112589990684262400000000000000000000), (55152503424848865439100518247/56294995342131200000000000000000000), (-616031640554451218239106497/22517998136852480000000000000000000), (-153731964357516401789811479/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial147.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial147.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial147.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 62686476767628580135217137731080574), (Int.ofNat 4949644951509646094423872018430318), (Int.ofNat 247299244789495531409636161129495), (Int.ofNat 3508329304917717456322781718200), (Int.negOfNat 17684997255681424402580846560323), (Int.ofNat 526512412012050850832950164162), (Int.ofNat 612924006982904118356508571846), (Int.negOfNat 35364274348593604855183834932), (Int.negOfNat 9161969948291389948771978946), (Int.ofNat 642163261598143259731268278), (Int.ofNat 78320940872722156176906739), (Int.negOfNat 6132180187029835894725735), (Int.negOfNat 436341603545697270279019), (Int.ofNat 37224516099898257803365), (Int.ofNat 1709137966713614420096), (Int.negOfNat 158001664819089118641), (Int.negOfNat 7978393201768675801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-31343238383814290067608568865540287/56294995342131200000000000000000000), (2474822475754823047211936009215159/56294995342131200000000000000000000), (49459848957899106281927232225899/22517998136852480000000000000000000), (17541646524588587281613908591/562949953421312000000000000000000), (-17684997255681424402580846560323/112589990684262400000000000000000000), (263256206006025425416475082081/56294995342131200000000000000000000), (306462003491452059178254285923/56294995342131200000000000000000000), (-8841068587148401213795958733/28147497671065600000000000000000000), (-4580984974145694974385989473/56294995342131200000000000000000000), (321081630799071629865634139/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial147.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial147.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial147.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 52003284794985112829726086014167527), (Int.ofNat 5551402209462375144662581436919388), (Int.negOfNat 3385384789265395536364604895593), (Int.negOfNat 50706578489091185041512526529524), (Int.ofNat 7534601039665706718340638765779), (Int.ofNat 2520575285226765076976184973000), (Int.negOfNat 321023474169869505303949004370), (Int.negOfNat 53170245936425067341371447662), (Int.ofNat 6666969360632511054097651148), (Int.ofNat 572553259693500528195695416), (Int.negOfNat 75599494426057777208772969), (Int.negOfNat 3734343850099347892722667), (Int.ofNat 538116299881696340736452), (Int.ofNat 16277076824259967216414), (Int.negOfNat 2626922838300437275332), (Int.negOfNat 45701731140703647462), (Int.ofNat 8157598251180537943), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-52003284794985112829726086014167527/112589990684262400000000000000000000), (1387850552365593786165645359229847/28147497671065600000000000000000000), (-3385384789265395536364604895593/112589990684262400000000000000000000), (-12676644622272796260378131632381/28147497671065600000000000000000000), (7534601039665706718340638765779/112589990684262400000000000000000000), (2520575285226765076976184973/112589990684262400000000000000000), (-32102347416986950530394900437/11258999068426240000000000000000000), (-26585122968212533670685723831/56294995342131200000000000000000000), (1666742340158127763524412787/28147497671065600000000000000000000), (71569157461687566024461927/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial147.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial147.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial147.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 41143896688391910215790076219666574), (Int.ofNat 5294408994979783327923952707715614), (Int.negOfNat 24277017801444162828500446008942), (Int.ofNat 43023819381362039698073806579820), (Int.ofNat 7264395916015925341409894657946), (Int.negOfNat 2319847378011135358397208714925), (Int.negOfNat 209854630890870864619932215176), (Int.ofNat 57896088889085624975094392507), (Int.ofNat 2851028571097622944485518952), (Int.negOfNat 798833547700396570869722373), (Int.negOfNat 20671780636866731659375418), (Int.ofNat 6790516207381099524827063), (Int.ofNat 86280331333794623516140), (Int.negOfNat 38864728679589400059600), (Int.negOfNat 199642478881424611455), (Int.ofNat 162940107861116214377), (Int.ofNat 2815495978821223801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-20571948344195955107895038109833287/56294995342131200000000000000000000), (2647204497489891663961976353857807/56294995342131200000000000000000000), (-12138508900722081414250223004471/56294995342131200000000000000000000), (2151190969068101984903690328991/5629499534213120000000000000000000), (3632197958007962670704947328973/56294995342131200000000000000000000), (-92793895120445414335888348597/4503599627370496000000000000000000), (-26231828861358858077491526897/14073748835532800000000000000000000), (57896088889085624975094392507/112589990684262400000000000000000000), (356378571387202868060689869/14073748835532800000000000000000000), (-798833547700396570869722373/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial147.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial147.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial147.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 30271707356271191232021120142038826), (Int.ofNat 5747154651859617876904234301910567), (Int.ofNat 212545458309933247687946244511475), (Int.ofNat 7972474553871643491864166660934), (Int.negOfNat 12336245427695673035352692470753), (Int.negOfNat 277709315261184541753964383340), (Int.ofNat 410939230554997485604014537623), (Int.ofNat 2577411143468140653602825279), (Int.negOfNat 7113852228297800577162916121), (Int.ofNat 24844825831460983811848271), (Int.ofNat 73699098430236866690069832), (Int.negOfNat 695734771797555674898455), (Int.negOfNat 500876336821111455070525), (Int.ofNat 6450179916339387915657), (Int.ofNat 2389502123671988097568), (Int.negOfNat 39629598479585207583), (Int.negOfNat 8247470589555296872), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-15135853678135595616010560071019413/56294995342131200000000000000000000), (5747154651859617876904234301910567/112589990684262400000000000000000000), (8501818332397329907517849780459/4503599627370496000000000000000000), (3986237276935821745932083330467/56294995342131200000000000000000000), (-12336245427695673035352692470753/112589990684262400000000000000000000), (-13885465763059227087698219167/5629499534213120000000000000000000), (410939230554997485604014537623/112589990684262400000000000000000000), (2577411143468140653602825279/112589990684262400000000000000000000), (-7113852228297800577162916121/112589990684262400000000000000000000), (24844825831460983811848271/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial147.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial147.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial147.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 18044809372265387941241694861831468), (Int.ofNat 6349215049239207153462661524774630), (Int.ofNat 30615014376229227655197726202894), (Int.negOfNat 46196909431202439457975273303035), (Int.ofNat 3299663583090542223736614495042), (Int.ofNat 2260505357858986525469621066894), (Int.negOfNat 122207772148962494195940339967), (Int.negOfNat 51627246656100540755228879567), (Int.ofNat 2385045298301667977038788572), (Int.ofNat 668951276533300373069230216), (Int.negOfNat 27925148131274097820652407), (Int.negOfNat 5502406678016774588520502), (Int.ofNat 212742601886033234240201), (Int.ofNat 31021513732767217648321), (Int.negOfNat 1111038980947095049505), (Int.negOfNat 128860336054555251255), (Int.ofNat 2377358690251147842), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-4511202343066346985310423715457867/28147497671065600000000000000000000), (634921504923920715346266152477463/11258999068426240000000000000000000), (15307507188114613827598863101447/56294995342131200000000000000000000), (-9239381886240487891595054660607/22517998136852480000000000000000000), (1649831791545271111868307247521/56294995342131200000000000000000000), (1130252678929493262734810533447/56294995342131200000000000000000000), (-122207772148962494195940339967/112589990684262400000000000000000000), (-51627246656100540755228879567/112589990684262400000000000000000000), (596261324575416994259697143/28147497671065600000000000000000000), (83618909566662546633653777/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial147.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial147.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial147.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 5481878974350849622583138525957246), (Int.ofNat 6160934274785877855814295114510532), (Int.negOfNat 43658764883662660326004885930983), (Int.ofNat 29397039649459905041639015860661), (Int.ofNat 8914194497466965886669735722043), (Int.negOfNat 1483161891516139193796163255463), (Int.negOfNat 285255589449055507091968225833), (Int.ofNat 35129717791218038505216540433), (Int.ofNat 4797003207344543494610661028), (Int.negOfNat 474969579422082026470314584), (Int.negOfNat 48995784650567893917003993), (Int.ofNat 4091307140661308659567098), (Int.ofNat 332631614648728938810999), (Int.negOfNat 24144048310098728647079), (Int.negOfNat 1600738673274441552695), (Int.ofNat 107814452053400649745), (Int.ofNat 4865453999840168158), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-2740939487175424811291569262978623/56294995342131200000000000000000000), (1540233568696469463953573778627633/28147497671065600000000000000000000), (-43658764883662660326004885930983/112589990684262400000000000000000000), (29397039649459905041639015860661/112589990684262400000000000000000000), (8914194497466965886669735722043/112589990684262400000000000000000000), (-1483161891516139193796163255463/112589990684262400000000000000000000), (-285255589449055507091968225833/112589990684262400000000000000000000), (35129717791218038505216540433/112589990684262400000000000000000000), (1199250801836135873652665257/28147497671065600000000000000000000), (-59371197427760253308789323/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial147.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial147.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial147.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 6982881208325416001676143990915737), (Int.ofNat 6470253765088627067677975875734957), (Int.ofNat 189133494300453761880413966594081), (Int.ofNat 20908322007039267638210223569003), (Int.negOfNat 10192560971847933449146754285746), (Int.negOfNat 1013457149595583372505676099440), (Int.ofNat 333945798234659980725902945777), (Int.ofNat 23324712751701684119005619479), (Int.negOfNat 5739231173173733780414832479), (Int.negOfNat 308981555955356579302429529), (Int.ofNat 59848444318588515631851368), (Int.ofNat 2624140202717614184713745), (Int.negOfNat 414289707072531541474075), (Int.negOfNat 15343002736506992265343), (Int.ofNat 2025053004621475647832), (Int.ofNat 70138459270255229817), (Int.negOfNat 5879205064465955128), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(6982881208325416001676143990915737/112589990684262400000000000000000000), (6470253765088627067677975875734957/112589990684262400000000000000000000), (189133494300453761880413966594081/112589990684262400000000000000000000), (20908322007039267638210223569003/112589990684262400000000000000000000), (-5096280485923966724573377142873/56294995342131200000000000000000000), (-12668214369944792156320951243/1407374883553280000000000000000000), (333945798234659980725902945777/112589990684262400000000000000000000), (23324712751701684119005619479/112589990684262400000000000000000000), (-5739231173173733780414832479/112589990684262400000000000000000000), (-308981555955356579302429529/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial147.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial147.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial147.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 20674473211153784941447903393739387), (Int.ofNat 7138752509204360823561257455252719), (Int.ofNat 73731794483009679768700416905437), (Int.negOfNat 45642521177262689187436319709218), (Int.negOfNat 573927672918764287705485179417), (Int.ofNat 2274445905539980781232250776732), (Int.ofNat 23738358828210393949238298576), (Int.negOfNat 52920046388103139877926928493), (Int.negOfNat 560304686603052837390829952), (Int.ofNat 699740528084109134113778627), (Int.ofNat 7766941542426374779001618), (Int.negOfNat 5886330333400205483134937), (Int.negOfNat 67678647199888270637740), (Int.ofNat 33941504734754902502000), (Int.ofNat 392607326879105048855), (Int.negOfNat 142317670662035940823), (Int.ofNat 267485776982364199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(20674473211153784941447903393739387/112589990684262400000000000000000000), (7138752509204360823561257455252719/112589990684262400000000000000000000), (73731794483009679768700416905437/112589990684262400000000000000000000), (-22821260588631344593718159854609/56294995342131200000000000000000000), (-573927672918764287705485179417/112589990684262400000000000000000000), (568611476384995195308062694183/28147497671065600000000000000000000), (1483647426763149621827393661/7036874417766400000000000000000000), (-52920046388103139877926928493/112589990684262400000000000000000000), (-4377380364086350292115859/879609302220800000000000000000000), (699740528084109134113778627/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial147.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial147.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial147.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 34940320883225902039258285512554611), (Int.ofNat 7031421071487641434301562498902827), (Int.negOfNat 59662062811623033157628586851861), (Int.ofNat 17537550600450983889386787185848), (Int.ofNat 10830636061216024812321351206277), (Int.negOfNat 833443779424545660954741476100), (Int.negOfNat 367205627498183208962886147787), (Int.ofNat 17206184065350424636456351338), (Int.ofNat 6484482226491436064810694452), (Int.negOfNat 190371371696967041715116584), (Int.negOfNat 68941227474507477896574431), (Int.ofNat 1261421682330471459233733), (Int.ofNat 482760422151862632267148), (Int.negOfNat 5364173567625108307586), (Int.negOfNat 2367195441917446073868), (Int.ofNat 13373948976224593738), (Int.ofNat 5969077402840714057), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(34940320883225902039258285512554611/112589990684262400000000000000000000), (7031421071487641434301562498902827/112589990684262400000000000000000000), (-59662062811623033157628586851861/112589990684262400000000000000000000), (2192193825056372986173348398231/14073748835532800000000000000000000), (10830636061216024812321351206277/112589990684262400000000000000000000), (-8334437794245456609547414761/1125899906842624000000000000000000), (-367205627498183208962886147787/112589990684262400000000000000000000), (8603092032675212318228175669/56294995342131200000000000000000000), (1621120556622859016202673613/28147497671065600000000000000000000), (-23796421462120880214389573/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial147.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial147.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial147.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 49031632827823728799876485888520864), (Int.ofNat 7226207208248387181805883281530586), (Int.ofNat 172271405938260898387213046981289), (Int.ofNat 31369660413269869886758977961752), (Int.negOfNat 9039763839677377712748291668134), (Int.negOfNat 1747110848741341153666709687152), (Int.ofNat 284675302079954354663200269554), (Int.ofNat 44699216049878895156445526468), (Int.negOfNat 4500189379887252764481595654), (Int.negOfNat 638600054009914091214856522), (Int.ofNat 41536901259651072377017661), (Int.ofNat 5684144004807515096213465), (Int.negOfNat 247050526506558229370781), (Int.negOfNat 34002688049396898526035), (Int.ofNat 1016152382892469961104), (Int.ofNat 147000474479959930759), (Int.negOfNat 5430382999929816199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1532238525869491524996140184016277/3518437208883200000000000000000000), (3613103604124193590902941640765293/56294995342131200000000000000000000), (172271405938260898387213046981289/112589990684262400000000000000000000), (3921207551658733735844872245219/14073748835532800000000000000000000), (-4519881919838688856374145834067/56294995342131200000000000000000000), (-109194428046333822104169355447/7036874417766400000000000000000000), (142337651039977177331600134777/56294995342131200000000000000000000), (11174804012469723789111381617/28147497671065600000000000000000000), (-2250094689943626382240797827/56294995342131200000000000000000000), (-319300027004957045607428261/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial147.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial147.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial147.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 64246060995675488682735668494955623), (Int.ofNat 7931559787819605530758378138061450), (Int.ofNat 91736043844583434179821024870420), (Int.negOfNat 50909399312913077978331412989642), (Int.negOfNat 3773604127038544280023991609544), (Int.ofNat 2588449096972062455337863833532), (Int.ofNat 179941699960110569116813170683), (Int.negOfNat 58710725100904648905795640906), (Int.negOfNat 4072664697037051090230535715), (Int.ofNat 723398000308208188437253168), (Int.ofNat 51208606377512505614117915), (Int.negOfNat 5469213393246092378714751), (Int.negOfNat 398698662222115737332284), (Int.ofNat 27723014028285333137998), (Int.ofNat 2094031122880143248109), (Int.negOfNat 97674601395688056753), (Int.negOfNat 6058949741215472986), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(64246060995675488682735668494955623/112589990684262400000000000000000000), (158631195756392110615167562761229/2251799813685248000000000000000000), (4586802192229171708991051243521/5629499534213120000000000000000000), (-25454699656456538989165706494821/56294995342131200000000000000000000), (-471700515879818035002998951193/14073748835532800000000000000000000), (647112274243015613834465958383/28147497671065600000000000000000000), (179941699960110569116813170683/112589990684262400000000000000000000), (-29355362550452324452897820453/56294995342131200000000000000000000), (-814532939407410218046107143/22517998136852480000000000000000000), (45212375019263011777328323/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial147.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial147.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial147.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 80094671191947141770189132138437422), (Int.ofNat 7779846940292929383788826096135639), (Int.negOfNat 97029250012082536540299425567480), (Int.ofNat 15463258989245699367486370245716), (Int.ofNat 15242396257854656762193948252360), (Int.negOfNat 328420262719572096523828008863), (Int.negOfNat 537017831574452646158822565961), (Int.negOfNat 5769936077011301356416085902), (Int.ofNat 9227139388656591293040730993), (Int.ofNat 251860288543572433802456790), (Int.negOfNat 90335401586633440109150760), (Int.negOfNat 3317539471738992025267428), (Int.ofNat 561993730573238785744835), (Int.ofNat 23843963397594132008293), (Int.negOfNat 2426778110719668300841), (Int.negOfNat 113951212354504680009), (Int.ofNat 10593280222877268199), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(40047335595973570885094566069218711/56294995342131200000000000000000000), (7779846940292929383788826096135639/112589990684262400000000000000000000), (-2425731250302063413507485639187/2814749767106560000000000000000000), (3865814747311424841871592561429/28147497671065600000000000000000000), (381059906446366419054848706309/2814749767106560000000000000000000), (-328420262719572096523828008863/112589990684262400000000000000000000), (-537017831574452646158822565961/112589990684262400000000000000000000), (-2884968038505650678208042951/56294995342131200000000000000000000), (9227139388656591293040730993/112589990684262400000000000000000000), (25186028854357243380245679/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial147.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial147.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial147.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 95590609599755195120047849595170551), (Int.ofNat 7942623522504182180370701740402834), (Int.ofNat 219134842194907760695756057824760), (Int.ofNat 51541257022556360452466200835358), (Int.negOfNat 11805596056163618182354185873773), (Int.negOfNat 3380285346567597783062114057894), (Int.ofNat 268708430148983456356185946401), (Int.ofNat 89555752466664723421343476799), (Int.negOfNat 1975543148798588087202428475), (Int.negOfNat 1201081452734195154976741395), (Int.negOfNat 5380775870095724676667979), (Int.ofNat 9385358766072271354800697), (Int.ofNat 163931506777555946782746), (Int.negOfNat 48483872531231826029077), (Int.negOfNat 1196105413473720928064), (Int.ofNat 180981256608718981528), (Int.ofNat 4427856338607747915), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(95590609599755195120047849595170551/112589990684262400000000000000000000), (3971311761252091090185350870201417/56294995342131200000000000000000000), (5478371054872694017393901445619/2814749767106560000000000000000000), (25770628511278180226233100417679/56294995342131200000000000000000000), (-11805596056163618182354185873773/112589990684262400000000000000000000), (-1690142673283798891531057028947/56294995342131200000000000000000000), (268708430148983456356185946401/112589990684262400000000000000000000), (89555752466664723421343476799/112589990684262400000000000000000000), (-79021725951943523488097139/4503599627370496000000000000000000), (-240216290546839030995348279/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial147.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial147.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial147.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 112495221156920047486106760273476260), (Int.ofNat 8876458344936641776398730389635875), (Int.ofNat 90427338878887452032716068523997), (Int.negOfNat 94650026529651829430809639699920), (Int.negOfNat 11139252227179885256777928006986), (Int.ofNat 4294596676081355207680544991137), (Int.ofNat 613391533614316743082490613401), (Int.negOfNat 71998086432613767551084931799), (Int.negOfNat 12944188643572629610021513875), (Int.ofNat 475319034981033446448829395), (Int.ofNat 132910840949231595946802021), (Int.negOfNat 1066992047385772724662297), (Int.negOfNat 835871595242332128267054), (Int.negOfNat 4544307445438642613523), (Int.ofNat 3620102772517019650136), (Int.ofNat 49100303255967096072), (Int.negOfNat 14095126597092075485), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(5624761057846002374305338013673813/5629499534213120000000000000000000), (71011666759493134211189843117087/900719925474099200000000000000000), (90427338878887452032716068523997/112589990684262400000000000000000000), (-1183125331620647867885120496249/1407374883553280000000000000000000), (-5569626113589942628388964003493/56294995342131200000000000000000000), (4294596676081355207680544991137/112589990684262400000000000000000000), (613391533614316743082490613401/112589990684262400000000000000000000), (-71998086432613767551084931799/112589990684262400000000000000000000), (-103553509148581036880172111/900719925474099200000000000000000), (95063806996206689289765879/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial147.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial147.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial147.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 129838947516960671433970309643641968), (Int.ofNat 8163483484580076970125737441080423), (Int.negOfNat 321976362915561368600545070468478), (Int.ofNat 27106564673044386024898131208348), (Int.ofNat 37507166876232100550403606945718), (Int.ofNat 1724469918038182116733932643577), (Int.negOfNat 1141726435472330141402385374561), (Int.negOfNat 108780571901431289501783125698), (Int.ofNat 12016328279434402367336956593), (Int.ofNat 1605565244486149847863009410), (Int.negOfNat 65165695949529424100436160), (Int.negOfNat 12627885306648308433264172), (Int.ofNat 192614555728984129992035), (Int.ofNat 64982564947903271765907), (Int.negOfNat 175109015315223209241), (Int.negOfNat 247368478299438533991), (Int.negOfNat 1045839748892619201), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(8114934219810041964623144352727623/7036874417766400000000000000000000), (8163483484580076970125737441080423/112589990684262400000000000000000000), (-160988181457780684300272535234239/56294995342131200000000000000000000), (6776641168261096506224532802087/28147497671065600000000000000000000), (18753583438116050275201803472859/56294995342131200000000000000000000), (1724469918038182116733932643577/112589990684262400000000000000000000), (-1141726435472330141402385374561/112589990684262400000000000000000000), (-54390285950715644750891562849/56294995342131200000000000000000000), (12016328279434402367336956593/112589990684262400000000000000000000), (160556524448614984786300941/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial147.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial147.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial147.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 145666971802305569270308387114477573), (Int.ofNat 8286634737254311653571054608601390), (Int.ofNat 559526250567416196552112696155545), (Int.ofNat 181219917734060770198172796783287), (Int.negOfNat 25640247798155306400821013988417), (Int.negOfNat 13352548660500004126710387097975), (Int.negOfNat 620623199852660949652636706917), (Int.ofNat 196993974188089350114563180506), (Int.ofNat 16490182389405157148709314485), (Int.negOfNat 1479911306141589801146598568), (Int.negOfNat 168422953491420392744320085), (Int.ofNat 6858496205692371663675551), (Int.ofNat 1040475368938758910791916), (Int.negOfNat 20959688879831471685998), (Int.negOfNat 4471491474421362069091), (Int.ofNat 40134350103838731553), (Int.ofNat 15905964676449318414), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(145666971802305569270308387114477573/112589990684262400000000000000000000), (828663473725431165357105460860139/11258999068426240000000000000000000), (111905250113483239310422539231109/22517998136852480000000000000000000), (181219917734060770198172796783287/112589990684262400000000000000000000), (-25640247798155306400821013988417/112589990684262400000000000000000000), (-534101946420000165068415483919/4503599627370496000000000000000000), (-620623199852660949652636706917/112589990684262400000000000000000000), (98496987094044675057281590253/56294995342131200000000000000000000), (3298036477881031429741862897/22517998136852480000000000000000000), (-184988913267698725143324821/14073748835532800000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial147.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial147.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial147.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 165079384815281073553206910259980386), (Int.ofNat 10792495695285747490181743632535016), (Int.negOfNat 32244453446029952457007088001137), (Int.negOfNat 527582097180089063349411316561974), (Int.negOfNat 130596898510006010972796733326577), (Int.negOfNat 909558877809883298718821559119), (Int.ofNat 2578897411473036637811410105397), (Int.ofNat 144510363359589903353235646532), (Int.negOfNat 24813328345216579694585392054), (Int.negOfNat 2001159972957744464749092278), (Int.ofNat 148472442572307252861870461), (Int.ofNat 15016270006920710570237735), (Int.negOfNat 611084777382856859779981), (Int.negOfNat 75214208947275997673365), (Int.ofNat 1825335869504387661904), (Int.ofNat 276907812574426306241), (Int.negOfNat 4117057474054832799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(82539692407640536776603455129990193/56294995342131200000000000000000000), (1349061961910718436272717954066877/14073748835532800000000000000000000), (-32244453446029952457007088001137/112589990684262400000000000000000000), (-263791048590044531674705658280987/56294995342131200000000000000000000), (-130596898510006010972796733326577/112589990684262400000000000000000000), (-909558877809883298718821559119/112589990684262400000000000000000000), (2578897411473036637811410105397/112589990684262400000000000000000000), (36127590839897475838308911633/28147497671065600000000000000000000), (-12406664172608289847292696027/56294995342131200000000000000000000), (-1000579986478872232374546139/56294995342131200000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial147.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial147.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial147.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 180372435017908604171977002681599735), (Int.ofNat 611447251831282760566873925648153), (Int.negOfNat 5740386943160362810684819908213987), (Int.negOfNat 1167588156449438351930622594679790), (Int.ofNat 22172041154894484940596292731093), (Int.ofNat 28582590369166319953221812889900), (Int.ofNat 1148439864673351201116916044970), (Int.negOfNat 341379916918558363287046312938), (Int.negOfNat 21669590535982148624697525148), (Int.ofNat 2530665241569244432514338784), (Int.ofNat 197249574588728796086826569), (Int.negOfNat 12914467066053873246487133), (Int.negOfNat 1154543809344580691244452), (Int.ofNat 48283811922209656711786), (Int.ofNat 4817699270979942049332), (Int.negOfNat 134814134746553604538), (Int.negOfNat 15995837014824077343), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(36074487003581720834395400536319947/22517998136852480000000000000000000), (611447251831282760566873925648153/112589990684262400000000000000000000), (-5740386943160362810684819908213987/112589990684262400000000000000000000), (-116758815644943835193062259467979/11258999068426240000000000000000000), (22172041154894484940596292731093/112589990684262400000000000000000000), (285825903691663199532218128899/1125899906842624000000000000000000), (114843986467335120111691604497/11258999068426240000000000000000000), (-170689958459279181643523156469/56294995342131200000000000000000000), (-5417397633995537156174381287/28147497671065600000000000000000000), (79083288799038888516073087/3518437208883200000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial147.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial147.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial147.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 150588195129760386938793819565769639), (Int.negOfNat 33313003451142934194849793230174190), (Int.negOfNat 9906292024960116325016612012211884), (Int.ofNat 122813971035731009949128421975854), (Int.ofNat 269233007701837438419092732509511), (Int.ofNat 10193820211079128250369052283282), (Int.negOfNat 3939867847032174186719113439924), (Int.negOfNat 224655342119775328975373057907), (Int.ofNat 35952631382664276395827335048), (Int.ofNat 2399923467292279174969766173), (Int.negOfNat 223900761728044785893867182), (Int.negOfNat 16279788209513368824789863), (Int.ofNat 1010716424697924215067660), (Int.ofNat 77674555855829107589600), (Int.negOfNat 3452331873161169334145), (Int.negOfNat 278593419384973680577), (Int.ofNat 9279954697002284799), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(150588195129760386938793819565769639/112589990684262400000000000000000000), (-3331300345114293419484979323017419/11258999068426240000000000000000000), (-2476573006240029081254153003052971/28147497671065600000000000000000000), (61406985517865504974564210987927/56294995342131200000000000000000000), (269233007701837438419092732509511/112589990684262400000000000000000000), (5096910105539564125184526141641/56294995342131200000000000000000000), (-984966961758043546679778359981/28147497671065600000000000000000000), (-224655342119775328975373057907/112589990684262400000000000000000000), (4494078922833034549478416881/14073748835532800000000000000000000), (2399923467292279174969766173/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial147.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial147.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial147.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 49682729570201714489833880486690492), (Int.negOfNat 62849498567521264848274381272682572), (Int.negOfNat 2916319671094904676281506254562153), (Int.ofNat 2001580878340876265067065729170922), (Int.ofNat 118274478058691526373974387792224), (Int.negOfNat 37173752665677999954894472012617), (Int.negOfNat 2365027437453667842131312630023), (Int.ofNat 427513949804639755494017519721), (Int.ofNat 27710503154437204261482188121), (Int.negOfNat 3284506809138436614954794671), (Int.negOfNat 213081895794788366818139832), (Int.ofNat 17897949118343783049630655), (Int.ofNat 1153681364572412366843525), (Int.negOfNat 72528774545823851206057), (Int.negOfNat 4628540719792254924568), (Int.ofNat 223398300598322180983), (Int.ofNat 16085709353198836272), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(12420682392550428622458470121672623/28147497671065600000000000000000000), (-15712374641880316212068595318170643/28147497671065600000000000000000000), (-2916319671094904676281506254562153/112589990684262400000000000000000000), (1000790439170438132533532864585461/56294995342131200000000000000000000), (3696077439334110199186699618507/3518437208883200000000000000000000), (-37173752665677999954894472012617/112589990684262400000000000000000000), (-2365027437453667842131312630023/112589990684262400000000000000000000), (427513949804639755494017519721/112589990684262400000000000000000000), (27710503154437204261482188121/112589990684262400000000000000000000), (-3284506809138436614954794671/112589990684262400000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial147.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial147.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial147.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 71057472884941887024431076682195432), (Int.negOfNat 49927539947774706126844156707678429), (Int.ofNat 8710172046698801943248028975023129), (Int.ofNat 1351418546026366182023589106460333), (Int.negOfNat 259860337229385481842626078950856), (Int.negOfNat 24950128519048037703051637286394), (Int.ofNat 4114623406344334147502727646324), (Int.ofNat 307541512547430626134270010967), (Int.negOfNat 40653270093276629227037250972), (Int.negOfNat 2614807294310224796619116816), (Int.ofNat 272615365926944358476379007), (Int.ofNat 15878000046487359881510702), (Int.negOfNat 1318060033974542967338801), (Int.negOfNat 71320273108654499253121), (Int.ofNat 4805971373135539670105), (Int.ofNat 241260811346932996055), (Int.negOfNat 14472809366074656442), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-8882184110617735878053884585274429/14073748835532800000000000000000000), (-49927539947774706126844156707678429/112589990684262400000000000000000000), (8710172046698801943248028975023129/112589990684262400000000000000000000), (1351418546026366182023589106460333/112589990684262400000000000000000000), (-32482542153673185230328259868857/14073748835532800000000000000000000), (-12475064259524018851525818643197/56294995342131200000000000000000000), (1028655851586083536875681911581/28147497671065600000000000000000000), (307541512547430626134270010967/112589990684262400000000000000000000), (-10163317523319157306759312743/28147497671065600000000000000000000), (-163425455894389049788694801/7036874417766400000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial147.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial147.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial147.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial147.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial147.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial147.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial147.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial147.reflect := by
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

end Bin147
end
end ErdosOverlap.OuterNumerics
