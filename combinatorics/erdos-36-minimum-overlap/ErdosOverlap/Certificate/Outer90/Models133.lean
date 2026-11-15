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

/-! # Exact integer weighted outer models for source bin 133

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin133

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 3679351620719974000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 3191382986946350600)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2234479505375772700)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1387710561259386800)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 846582571994930600)⟩, ⟨(19494472361809/1000000000000), (Int.negOfNat 444994438522335540)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 827361365034530000)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 341284417669533000)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 84790080152295900)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial133.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial133.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 9815203819761827000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 1559383599787610400)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1710999603250935000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 491918986087579700)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 109486143361650040)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 91968133391938190)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 110325950456324500)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 15550571816920237)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 6734928347982703)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial133.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial133.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 9815203819761827000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 1559383599787610400)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1710999603250935000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 491918986087579700)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 109486143361650040)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 91968133391938190)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 110325950456324500)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 15550571816920237)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 6734928347982703)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial133.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial133.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial133.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 11260506354542602231330332003288192), (Int.ofNat 4530004335940796077276536134840000), (Int.ofNat 1003781706898363832412709092407298), (Int.negOfNat 135321488554476362223628056040832), (Int.negOfNat 25873784054305428020747088533525), (Int.ofNat 2520081107358740688900231330394), (Int.ofNat 363322834938048251710205458974), (Int.negOfNat 28780561549673600647885025402), (Int.negOfNat 3215563685178322298698220784), (Int.ofNat 218710920495002911292017521), (Int.ofNat 19630656250531273432306335), (Int.negOfNat 1184928028544344746689108), (Int.negOfNat 88087753436410469892437), (Int.ofNat 4812675440386613272125), (Int.ofNat 304444698603811454605), (Int.negOfNat 14891511789058459053), (Int.negOfNat 821194960335828955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-87972705894864079932268218775689/87960930222080000000000000000000), (113250108398519901931913403371/281474976710656000000000000000), (501890853449181916206354546203649/5629499534213120000000000000000000), (-1057199129331846579872094187819/87960930222080000000000000000000), (-1034951362172217120829883541341/450359962737049600000000000000000), (1260040553679370344450115665197/5629499534213120000000000000000000), (181661417469024125855102729487/5629499534213120000000000000000000), (-14390280774836800323942512701/5629499534213120000000000000000000), (-200972730323645143668638799/703687441776640000000000000000000), (218710920495002911292017521/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial133.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial133.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial133.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial133 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 417594190428113457701980602002308), (Int.ofNat 6349079449358046014433302471516958), (Int.negOfNat 164221388315167688719819772213425), (Int.negOfNat 203837319790872361172859670754097), (Int.ofNat 10552899042785784515953271523462), (Int.ofNat 3578916713332787725941201574979), (Int.negOfNat 208296293251927027485560644186), (Int.negOfNat 37745596382694762688232364700), (Int.ofNat 2234919347894242994052450913), (Int.ofNat 264327298172613837170225152), (Int.negOfNat 15588557534238535728580156), (Int.negOfNat 1324623279458522924160105), (Int.ofNat 77286790585821092003497), (Int.ofNat 5012921215967137834247), (Int.negOfNat 288142526982231728182), (Int.negOfNat 14445001400347749649), (Int.ofNat 892324693526753251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(104398547607028364425495150500577/2814749767106560000000000000000000), (3174539724679023007216651235758479/5629499534213120000000000000000000), (-6568855532606707548792790888537/450359962737049600000000000000000), (-203837319790872361172859670754097/11258999068426240000000000000000000), (5276449521392892257976635761731/5629499534213120000000000000000000), (3578916713332787725941201574979/11258999068426240000000000000000000), (-104148146625963513742780322093/5629499534213120000000000000000000), (-377455963826947626882323647/112589990684262400000000000000000), (2234919347894242994052450913/11258999068426240000000000000000000), (64533031780423300090387/2748779069440000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial133.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial133.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial133.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial133 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 11094067449868649715091497959610821), (Int.ofNat 3816054213233436420444718893363053), (Int.negOfNat 918006524165493974361966059382779), (Int.negOfNat 25581857469163394698995801477403), (Int.ofNat 26590235856131645150091303392596), (Int.negOfNat 712859579536134702493220755423), (Int.negOfNat 375336725795659786149986730557), (Int.ofNat 16481070543437434544153075742), (Int.ofNat 3192474716089825026282663288), (Int.negOfNat 167297754182804502263696614), (Int.negOfNat 18403266564981544173173200), (Int.ofNat 1067338162342402760629337), (Int.ofNat 77449797340160623295648), (Int.negOfNat 4809761741386210302936), (Int.negOfNat 249832026163497178885), (Int.ofNat 16383383181382206391), (Int.ofNat 573559648226923958), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(11094067449868649715091497959610821/11258999068426240000000000000000000), (3816054213233436420444718893363053/11258999068426240000000000000000000), (-918006524165493974361966059382779/11258999068426240000000000000000000), (-25581857469163394698995801477403/11258999068426240000000000000000000), (6647558964032911287522825848149/2814749767106560000000000000000000), (-712859579536134702493220755423/11258999068426240000000000000000000), (-375336725795659786149986730557/11258999068426240000000000000000000), (8240535271718717272076537871/5629499534213120000000000000000000), (399059339511228128285332911/1407374883553280000000000000000000), (-83648877091402251131848307/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial133.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial133.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial133.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial133 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 15230930445993884806309535956110025), (Int.ofNat 569026536952508417230326106867223), (Int.negOfNat 564593864554090804099348807696651), (Int.ofNat 112392263188882927841561689412777), (Int.ofNat 4262754290501904389010603156154), (Int.negOfNat 2850313993307108172187196473399), (Int.ofNat 57852841851355081834669281846), (Int.ofNat 32792536564061269755886739123), (Int.negOfNat 1340435214083057591408182846), (Int.negOfNat 229432273383268616184081129), (Int.ofNat 12288175386513026491336249), (Int.ofNat 1104557732699956110671307), (Int.negOfNat 70176406235234351944190), (Int.negOfNat 3932308054994009928488), (Int.ofNat 284156385136938864788), (Int.ofNat 10196195367496370694), (Int.negOfNat 912529478570701360), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(609237217839755392252381438244401/450359962737049600000000000000000), (569026536952508417230326106867223/11258999068426240000000000000000000), (-564593864554090804099348807696651/11258999068426240000000000000000000), (112392263188882927841561689412777/11258999068426240000000000000000000), (2131377145250952194505301578077/5629499534213120000000000000000000), (-2850313993307108172187196473399/11258999068426240000000000000000000), (28926420925677540917334640923/5629499534213120000000000000000000), (32792536564061269755886739123/11258999068426240000000000000000000), (-670217607041528795704091423/5629499534213120000000000000000000), (-229432273383268616184081129/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial133.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial133.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial133.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial133 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 14994194124398995921647112326519593), (Int.negOfNat 408287702819875708882263512698439), (Int.ofNat 16670087545744183610158968089107), (Int.ofNat 56693099678210585953112139681637), (Int.negOfNat 13811871101191676488683020730475), (Int.negOfNat 340899166974230779847984752744), (Int.ofNat 265484213142678326400133160927), (Int.negOfNat 6137092273558510865153901507), (Int.negOfNat 2457591807776351327907857392), (Int.ofNat 111147060610309598322994209), (Int.ofNat 14176694672154108321186861), (Int.negOfNat 873926389630454594933805), (Int.negOfNat 56965664546688714643837), (Int.ofNat 4376555414328588059541), (Int.ofNat 169733099109208121216), (Int.negOfNat 16330188491204256447), (Int.negOfNat 319189407770036258), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(14994194124398995921647112326519593/11258999068426240000000000000000000), (-408287702819875708882263512698439/11258999068426240000000000000000000), (16670087545744183610158968089107/11258999068426240000000000000000000), (56693099678210585953112139681637/11258999068426240000000000000000000), (-552474844047667059547320829219/450359962737049600000000000000000), (-42612395871778847480998094093/1407374883553280000000000000000000), (265484213142678326400133160927/11258999068426240000000000000000000), (-6137092273558510865153901507/11258999068426240000000000000000000), (-153599487986021957994241087/703687441776640000000000000000000), (111147060610309598322994209/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial133.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial133.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial133.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial133 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 14481590892921699040523966718201815), (Int.negOfNat 84517315458177457549482197436698), (Int.ofNat 53907696127523163368046021313858), (Int.negOfNat 32027810932111346968526661833258), (Int.negOfNat 5166422111514218715359813572007), (Int.ofNat 1536737920029072743201259531174), (Int.ofNat 11399808118679365817978524218), (Int.negOfNat 21373858400479481322025215945), (Int.ofNat 689318694428082091059518979), (Int.ofNat 157776750389381984061102225), (Int.negOfNat 8955058603495430202296233), (Int.negOfNat 743920411084998872407469), (Int.ofNat 58771843171799715792936), (Int.ofNat 2444206543326534768426), (Int.negOfNat 255506997628516078259), (Int.negOfNat 5643110607380745879), (Int.ofNat 932734263614649469), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(2896318178584339808104793343640363/2251799813685248000000000000000000), (-42258657729088728774741098718349/5629499534213120000000000000000000), (26953848063761581684023010656929/5629499534213120000000000000000000), (-16013905466055673484263330916629/5629499534213120000000000000000000), (-5166422111514218715359813572007/11258999068426240000000000000000000), (768368960014536371600629765587/5629499534213120000000000000000000), (5699904059339682908989262109/5629499534213120000000000000000000), (-4274771680095896264405043189/2251799813685248000000000000000000), (689318694428082091059518979/11258999068426240000000000000000000), (6311070015575279362444089/450359962737049600000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial133.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial133.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial133.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial133 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 14236717962742992606581894534908936), (Int.negOfNat 301976766719716433541238010160699), (Int.negOfNat 149099098272582129857198889145030), (Int.negOfNat 20113430054120002048274757055465), (Int.ofNat 6164749183883197617044998103083), (Int.ofNat 417305352176414607534639074419), (Int.negOfNat 141883807314074863752779652210), (Int.ofNat 1491296114746178485880567741), (Int.ofNat 1450368243647785521080847473), (Int.negOfNat 70615657100731022831590607), (Int.negOfNat 8445335156347894545590052), (Int.ofNat 671513937165571132655388), (Int.ofNat 31447857309464489780323), (Int.negOfNat 3662239511613774792069), (Int.negOfNat 77153246549297305269), (Int.ofNat 14122727902762087557), (Int.ofNat 64819167313148558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(1779589745342874075822736816863617/1407374883553280000000000000000000), (-301976766719716433541238010160699/11258999068426240000000000000000000), (-14909909827258212985719888914503/1125899906842624000000000000000000), (-4022686010824000409654951411093/2251799813685248000000000000000000), (6164749183883197617044998103083/11258999068426240000000000000000000), (417305352176414607534639074419/11258999068426240000000000000000000), (-14188380731407486375277965221/1125899906842624000000000000000000), (1491296114746178485880567741/11258999068426240000000000000000000), (1450368243647785521080847473/11258999068426240000000000000000000), (-70615657100731022831590607/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial133.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial133.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial133.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial133 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 12978888640508628620449653856106263), (Int.negOfNat 934364133966305979028002511748796), (Int.negOfNat 119294426931403520946240634032521), (Int.ofNat 26151006357933524082509947287043), (Int.ofNat 3499490218503151279630322761724), (Int.negOfNat 698931167914449846088864714958), (Int.negOfNat 23435880098442744522010346302), (Int.ofNat 10349939756427943282382107492), (Int.negOfNat 359893874438269357567866529), (Int.negOfNat 78961525670106807362662248), (Int.ofNat 6298201039311269781679957), (Int.ofNat 345521671878586111796313), (Int.negOfNat 45664424432721358028408), (Int.negOfNat 870909572287886497757), (Int.ofNat 207327301867615566494), (Int.ofNat 636706396184712404), (Int.negOfNat 868148968506301678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(12978888640508628620449653856106263/11258999068426240000000000000000000), (-233591033491576494757000627937199/2814749767106560000000000000000000), (-119294426931403520946240634032521/11258999068426240000000000000000000), (26151006357933524082509947287043/11258999068426240000000000000000000), (874872554625787819907580690431/2814749767106560000000000000000000), (-349465583957224923044432357479/5629499534213120000000000000000000), (-11717940049221372261005173151/5629499534213120000000000000000000), (2587484939106985820595526873/2814749767106560000000000000000000), (-359893874438269357567866529/11258999068426240000000000000000000), (-9870190708763350920332781/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial133.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial133.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial133.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial133 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 10875516062872214587651298507676878), (Int.negOfNat 1042038952621668220275647619839976), (Int.ofNat 66085783703139777284312937395009), (Int.ofNat 27272570174038603296579200854885), (Int.negOfNat 2626096953571103357084967074987), (Int.negOfNat 374886600274573926980104183126), (Int.ofNat 51628374347454607706034794460), (Int.negOfNat 72094985366775364344296190), (Int.negOfNat 550379232821283063206617861), (Int.ofNat 45356349354078561847631022), (Int.ofNat 2943267783182030671559781), (Int.negOfNat 484092216154094910275693), (Int.negOfNat 6927710838293830851344), (Int.ofNat 2773635421641436663689), (Int.negOfNat 8226531890781650346), (Int.negOfNat 11243956263795447820), (Int.ofNat 118230849687408648), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(5437758031436107293825649253838439/5629499534213120000000000000000000), (-130254869077708527534455952479997/1407374883553280000000000000000000), (66085783703139777284312937395009/11258999068426240000000000000000000), (5454514034807720659315840170977/2251799813685248000000000000000000), (-2626096953571103357084967074987/11258999068426240000000000000000000), (-187443300137286963490052091563/5629499534213120000000000000000000), (2581418717372730385301739723/562949953421312000000000000000000), (-7209498536677536434429619/1125899906842624000000000000000000), (-550379232821283063206617861/11258999068426240000000000000000000), (22678174677039280923815511/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial133.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial133.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial133.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial133 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9223127260891749123634964801967519), (Int.negOfNat 555020153566989005957324370088222), (Int.ofNat 148289271715413545461628606236570), (Int.negOfNat 1229179255900440740520710998233), (Int.negOfNat 3711784854626243650406356528019), (Int.ofNat 93059414856306222830316893412), (Int.ofNat 22356215746064093087015652792), (Int.negOfNat 1968188460979582648169093943), (Int.ofNat 206565607950423092678910781), (Int.ofNat 13664338547141093325995233), (Int.negOfNat 4217016866802172808218308), (Int.negOfNat 4075814783707392016688), (Int.ofNat 31948342022639248705847), (Int.negOfNat 467273589114429185843), (Int.negOfNat 148440756186473013369), (Int.ofNat 3459975706751493519), (Int.ofNat 712038664897675284), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(9223127260891749123634964801967519/11258999068426240000000000000000000), (-277510076783494502978662185044111/5629499534213120000000000000000000), (14828927171541354546162860623657/1125899906842624000000000000000000), (-1229179255900440740520710998233/11258999068426240000000000000000000), (-3711784854626243650406356528019/11258999068426240000000000000000000), (23264853714076555707579223353/2814749767106560000000000000000000), (2794526968258011635876956599/1407374883553280000000000000000000), (-1968188460979582648169093943/11258999068426240000000000000000000), (206565607950423092678910781/11258999068426240000000000000000000), (13664338547141093325995233/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial133.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial133.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial133.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial133 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 8641234494955285982033058644880534), (Int.negOfNat 84312821897711248625208801163956), (Int.ofNat 63705450832268677000007239094702), (Int.negOfNat 24344233921626695997342866180431), (Int.negOfNat 1757573858538515014172553192160), (Int.ofNat 284914754549854999123080259184), (Int.ofNat 14574255215989662716792308176), (Int.negOfNat 64330148084841174880310177), (Int.negOfNat 102597086696950133664772309), (Int.negOfNat 28547927634424174283007579), (Int.ofNat 1202222274737698062129503), (Int.ofNat 310402639124319535933469), (Int.negOfNat 11707132807732071329968), (Int.negOfNat 1791782505208266513618), (Int.ofNat 73102710481235346101), (Int.ofNat 6794950370911198495), (Int.negOfNat 223225714883652657), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(4320617247477642991016529322440267/5629499534213120000000000000000000), (-21078205474427812156302200290989/2814749767106560000000000000000000), (31852725416134338500003619547351/5629499534213120000000000000000000), (-24344233921626695997342866180431/11258999068426240000000000000000000), (-10984836615865718838578457451/70368744177664000000000000000000), (17807172159365937445192516199/703687441776640000000000000000000), (910890950999353919799519261/703687441776640000000000000000000), (-64330148084841174880310177/11258999068426240000000000000000000), (-102597086696950133664772309/11258999068426240000000000000000000), (-28547927634424174283007579/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial133.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial133.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial133.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial133 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8514558315732093215792261595332016), (Int.negOfNat 152463127118202942042566761381030), (Int.negOfNat 98587811265053150944901119437424), (Int.negOfNat 25019907342373337322155519160248), (Int.ofNat 1745222834425105421504766731451), (Int.ofNat 368073414362027337538275629520), (Int.negOfNat 9388664452799443735246130635), (Int.negOfNat 3476245600321243488755802891), (Int.negOfNat 138473843110315948007585800), (Int.ofNat 28983979447010306986194645), (Int.ofNat 2470412612318858618755037), (Int.negOfNat 221520620489488179648995), (Int.negOfNat 18198655214361229140101), (Int.ofNat 1338486100241388418891), (Int.ofNat 82808762639175634036), (Int.negOfNat 6340929129991932709), (Int.negOfNat 457668424440787584), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(532159894733255825987016349708251/703687441776640000000000000000000), (-15246312711820294204256676138103/1125899906842624000000000000000000), (-6161738204065821934056319964839/703687441776640000000000000000000), (-3127488417796667165269439895031/1407374883553280000000000000000000), (1745222834425105421504766731451/11258999068426240000000000000000000), (4600917679525341719228445369/140737488355328000000000000000000), (-1877732890559888747049226127/2251799813685248000000000000000000), (-3476245600321243488755802891/11258999068426240000000000000000000), (-692369215551579740037929/56294995342131200000000000000000), (5796795889402061397238929/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial133.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial133.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial133.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial133 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 7653759042454536417553399889434781), (Int.negOfNat 765185470814808874288731637487335), (Int.negOfNat 182058706966857239920322274122803), (Int.ofNat 150581617354710822812890955576), (Int.ofNat 3873157557595563018493137083134), (Int.negOfNat 28166880777149911264931722559), (Int.negOfNat 49797377935035753073717443429), (Int.negOfNat 604781574837759226807449581), (Int.ofNat 456959427139746552286577962), (Int.ofNat 16098461768308780457340443), (Int.negOfNat 3470681043501554646514707), (Int.negOfNat 149258910648385885947607), (Int.ofNat 21660533186897286370714), (Int.ofNat 798494601721231267200), (Int.negOfNat 104253543035188952172), (Int.negOfNat 2529866795188049710), (Int.ofNat 243430499927600766), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(7653759042454536417553399889434781/11258999068426240000000000000000000), (-153037094162961774857746327497467/2251799813685248000000000000000000), (-182058706966857239920322274122803/11258999068426240000000000000000000), (18822702169338852851611369447/1407374883553280000000000000000000), (1936578778797781509246568541567/5629499534213120000000000000000000), (-28166880777149911264931722559/11258999068426240000000000000000000), (-49797377935035753073717443429/11258999068426240000000000000000000), (-604781574837759226807449581/11258999068426240000000000000000000), (228479713569873276143288981/5629499534213120000000000000000000), (16098461768308780457340443/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial133.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial133.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial133.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial133 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 5454284120233088278851334141026268), (Int.negOfNat 1379271538187837364160432497938557), (Int.negOfNat 101960152166724460455163484773766), (Int.ofNat 22551302602335325107956263681362), (Int.ofNat 960984340384681709012288539512), (Int.negOfNat 469419717555634703607444732173), (Int.negOfNat 8763392812848989453567061995), (Int.ofNat 5492943356893430998111273076), (Int.ofNat 108204697107015316136526336), (Int.negOfNat 45949837965072673675837880), (Int.negOfNat 959974290496577779805776), (Int.ofNat 307231976121240528562543), (Int.ofNat 5248078749966932178012), (Int.negOfNat 1627184332282337786836), (Int.negOfNat 18499192051438609165), (Int.ofNat 6649561929837748225), (Int.ofNat 203298183983899884), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(1363571030058272069712833535256567/2814749767106560000000000000000000), (-1379271538187837364160432497938557/11258999068426240000000000000000000), (-50980076083362230227581742386883/5629499534213120000000000000000000), (11275651301167662553978131840681/5629499534213120000000000000000000), (120123042548085213626536067439/1407374883553280000000000000000000), (-469419717555634703607444732173/11258999068426240000000000000000000), (-1752678562569797890713412399/2251799813685248000000000000000000), (1373235839223357749527818269/2814749767106560000000000000000000), (211337299037139289329153/21990232555520000000000000000000), (-1148745949126816841895947/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial133.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial133.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial133.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial133 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 2468811242476454564527800357314598), (Int.negOfNat 1522516806247400788284598426541931), (Int.ofNat 20425606375547075815607510063092), (Int.ofNat 13081516417228405775706564996840), (Int.negOfNat 2784927846732287692367747546915), (Int.negOfNat 155991537525837772926519252301), (Int.ofNat 50651039388770823593215598752), (Int.ofNat 1265238405956043817613339518), (Int.negOfNat 509694583687905267763966235), (Int.negOfNat 6028596318196894178529006), (Int.ofNat 3782093363774036959248420), (Int.ofNat 7936736151700686329265), (Int.negOfNat 22157992592121964984167), (Int.ofNat 108684850473707037721), (Int.ofNat 101563554189080633638), (Int.negOfNat 1700335187190161335), (Int.negOfNat 263635284971548875), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(1234405621238227282263900178657299/5629499534213120000000000000000000), (-1522516806247400788284598426541931/11258999068426240000000000000000000), (5106401593886768953901877515773/2814749767106560000000000000000000), (327037910430710144392664124921/281474976710656000000000000000000), (-556985569346457538473549509383/2251799813685248000000000000000000), (-155991537525837772926519252301/11258999068426240000000000000000000), (1582844980899088237287987461/351843720888320000000000000000000), (632619202978021908806669759/5629499534213120000000000000000000), (-101938916737581053552793247/2251799813685248000000000000000000), (-3014298159098447089264503/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial133.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial133.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial133.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial133 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 436144538480462062776365441541422), (Int.negOfNat 1375658262394971864565898134329100), (Int.ofNat 31704800244333251633068679438821), (Int.negOfNat 7514613809721387948287412377228), (Int.negOfNat 1498181749557734643558360555487), (Int.ofNat 346225440785301843376426318722), (Int.ofNat 18839067854613827284837936492), (Int.negOfNat 4593758689763379997352164136), (Int.negOfNat 80298296498280019957807212), (Int.ofNat 39337544966522314371688153), (Int.negOfNat 270856690310294678331429), (Int.negOfNat 257983707574578946538932), (Int.ofNat 5593241261535398404339), (Int.ofNat 1334357639163334952107), (Int.negOfNat 37499002747135400195), (Int.negOfNat 5556652044615760563), (Int.ofNat 57806984820970519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-218072269240231031388182720770711/5629499534213120000000000000000000), (-13756582623949718645658981343291/112589990684262400000000000000000), (31704800244333251633068679438821/11258999068426240000000000000000000), (-1878653452430346987071853094307/2814749767106560000000000000000000), (-1498181749557734643558360555487/11258999068426240000000000000000000), (173112720392650921688213159361/5629499534213120000000000000000000), (4709766963653456821209484123/2814749767106560000000000000000000), (-574219836220422499669020517/1407374883553280000000000000000000), (-20074574124570004989451803/2814749767106560000000000000000000), (39337544966522314371688153/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial133.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial133.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial133.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial133 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 3133033955619222057700514536454542), (Int.negOfNat 1357694792237564462905900700702069), (Int.negOfNat 20179278310093816617744238156400), (Int.negOfNat 5155794224263889362342128551344), (Int.ofNat 1863446524250817813625448564005), (Int.ofNat 220890231990763457514027771948), (Int.negOfNat 32173594789967813066436283252), (Int.negOfNat 1572058707379521433959822996), (Int.ofNat 326745268096083794722226132), (Int.negOfNat 1548101186323211196171847), (Int.negOfNat 2421869552990452333177951), (Int.ofNat 98292132628517384946328), (Int.ofNat 14192450660253380498721), (Int.negOfNat 809513642207368658333), (Int.negOfNat 65860672042104227225), (Int.ofNat 4468028721774850637), (Int.ofNat 107524981362922481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-1566516977809611028850257268227271/5629499534213120000000000000000000), (-1357694792237564462905900700702069/11258999068426240000000000000000000), (-50448195775234541544360595391/28147497671065600000000000000000), (-322237139016493085146383034459/703687441776640000000000000000000), (372689304850163562725089712801/2251799813685248000000000000000000), (55222557997690864378506942987/2814749767106560000000000000000000), (-8043398697491953266609070813/2814749767106560000000000000000000), (-393014676844880358489955749/2814749767106560000000000000000000), (81686317024020948680556533/2814749767106560000000000000000000), (-1548101186323211196171847/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial133.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial133.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial133.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial133 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 5935683082866276805048793003218914), (Int.negOfNat 1429541514611277816402787774685792), (Int.ofNat 3055876211293888800749418783094), (Int.ofNat 13104736782326823182532891460417), (Int.ofNat 2034518504231112377698848390533), (Int.negOfNat 169490153616320447003532943188), (Int.negOfNat 24689065872287125207943046792), (Int.ofNat 1876387045463016054635839038), (Int.ofNat 62945967682543688147614355), (Int.negOfNat 15344205684341889220689846), (Int.ofNat 1043054304862569945422040), (Int.ofNat 101481681061515686261905), (Int.negOfNat 12730451303606256924873), (Int.negOfNat 555533124271625144179), (Int.ofNat 75544794430570719662), (Int.ofNat 3026281736781246065), (Int.negOfNat 240857001821527725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-2967841541433138402524396501609457/5629499534213120000000000000000000), (-44673172331602431762587117958931/351843720888320000000000000000000), (1527938105646944400374709391547/5629499534213120000000000000000000), (13104736782326823182532891460417/11258999068426240000000000000000000), (2034518504231112377698848390533/11258999068426240000000000000000000), (-42372538404080111750883235797/2814749767106560000000000000000000), (-3086133234035890650992880849/1407374883553280000000000000000000), (938193522731508027317919519/5629499534213120000000000000000000), (12589193536508737629522871/2251799813685248000000000000000000), (-7672102842170944610344923/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial133.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial133.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial133.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial133 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 8651906546052581457341647139076912), (Int.negOfNat 1212380214010471736130676359019491), (Int.ofNat 112345132213729024541254762129111), (Int.ofNat 19750884099599058481563880828446), (Int.negOfNat 591136591835492503901803151316), (Int.negOfNat 300856395537734619768729726402), (Int.ofNat 2510760380298570933446793555), (Int.ofNat 1862777156087145185804168836), (Int.ofNat 226072035857535976196484), (Int.ofNat 4236404285053933102991080), (Int.negOfNat 75072228971728009278244), (Int.negOfNat 148594993375252501780517), (Int.negOfNat 35410596918584480932), (Int.ofNat 1183054658574376469124), (Int.ofNat 4446266910395812165), (Int.negOfNat 5959900114098597975), (Int.ofNat 140110330745982516), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-540744159128286341083852946192307/703687441776640000000000000000000), (-1212380214010471736130676359019491/11258999068426240000000000000000000), (112345132213729024541254762129111/11258999068426240000000000000000000), (9875442049799529240781940414223/5629499534213120000000000000000000), (-147784147958873125975450787829/2814749767106560000000000000000000), (-150428197768867309884364863201/5629499534213120000000000000000000), (502152076059714186689358711/2251799813685248000000000000000000), (465694289021786296451042209/2814749767106560000000000000000000), (56518008964383994049121/2814749767106560000000000000000000), (105910107126348327574777/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial133.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial133.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial133.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial133 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 10487963983248995505679055870070580), (Int.negOfNat 567649373045937138415160521123865), (Int.ofNat 194464076517708065103895730422409), (Int.ofNat 4448498424853583789015258127893), (Int.negOfNat 2917010483875548133180227527925), (Int.negOfNat 110237002869167089284546724062), (Int.ofNat 29260107766480986271766589892), (Int.ofNat 1741894494782803681620722359), (Int.negOfNat 88302169336174567418666822), (Int.negOfNat 17907240398224092484411577), (Int.negOfNat 1081304456876255248289893), (Int.ofNat 120399616612638706797293), (Int.ofNat 14517894793863750125766), (Int.negOfNat 538826130694035125360), (Int.negOfNat 89021490732358268488), (Int.ofNat 1222524296070132890), (Int.ofNat 261061786865475834), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-524398199162449775283952793503529/562949953421312000000000000000000), (-113529874609187427683032104224773/2251799813685248000000000000000000), (194464076517708065103895730422409/11258999068426240000000000000000000), (4448498424853583789015258127893/11258999068426240000000000000000000), (-116680419355021925327209101117/450359962737049600000000000000000), (-55118501434583544642273362031/5629499534213120000000000000000000), (7315026941620246567941647473/2814749767106560000000000000000000), (1741894494782803681620722359/11258999068426240000000000000000000), (-44151084668087283709333411/5629499534213120000000000000000000), (-17907240398224092484411577/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial133.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial133.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial133.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial133 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 10857955159182733264295871754524409), (Int.ofNat 167688386510384507556680342132997), (Int.ofNat 150271877976675861771436207202618), (Int.negOfNat 17904601603543216231532656735701), (Int.negOfNat 1955032722082265163090231579365), (Int.ofNat 307594466200095790038289780452), (Int.ofNat 30548629983587466680967861635), (Int.negOfNat 2377615811055446580838612691), (Int.negOfNat 368225406771865892403012540), (Int.ofNat 1637520552596019872444345), (Int.ofNat 3061516670160164444543143), (Int.ofNat 120301964401687172009545), (Int.negOfNat 17368258444544688414879), (Int.negOfNat 1129253742134773384049), (Int.ofNat 68909692024808511524), (Int.ofNat 5906705423920648031), (Int.negOfNat 394480571202870216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-10857955159182733264295871754524409/11258999068426240000000000000000000), (167688386510384507556680342132997/11258999068426240000000000000000000), (75135938988337930885718103601309/5629499534213120000000000000000000), (-17904601603543216231532656735701/11258999068426240000000000000000000), (-391006544416453032618046315873/2251799813685248000000000000000000), (76898616550023947509572445113/2814749767106560000000000000000000), (6109725996717493336193572327/2251799813685248000000000000000000), (-2377615811055446580838612691/11258999068426240000000000000000000), (-18411270338593294620150627/562949953421312000000000000000000), (327504110519203974488869/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial133.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial133.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial133.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial133 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 10084604535226729507466792317932091), (Int.ofNat 520410616784955033098364763231763), (Int.ofNat 25649971941501130983141290550040), (Int.negOfNat 18285944759776916000309797206046), (Int.ofNat 1925986658074450729887392238598), (Int.ofNat 338993420403741449260144608484), (Int.negOfNat 32022782299588575593498898816), (Int.negOfNat 4984973045198664473729893257), (Int.ofNat 204236741192683945187113069), (Int.ofNat 51728136821711867178236981), (Int.ofNat 56532258469244014062237), (Int.negOfNat 362684618018939707163671), (Int.negOfNat 9578227855681199864872), (Int.ofNat 1757535120455352283422), (Int.ofNat 74294367273127006219), (Int.negOfNat 5775609056185757705), (Int.negOfNat 281266571909423943), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-10084604535226729507466792317932091/11258999068426240000000000000000000), (520410616784955033098364763231763/11258999068426240000000000000000000), (641249298537528274578532263751/281474976710656000000000000000000), (-9142972379888458000154898603023/5629499534213120000000000000000000), (962993329037225364943696119299/5629499534213120000000000000000000), (84748355100935362315036152121/2814749767106560000000000000000000), (-250177986715535746824210147/87960930222080000000000000000000), (-4984973045198664473729893257/11258999068426240000000000000000000), (204236741192683945187113069/11258999068426240000000000000000000), (51728136821711867178236981/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial133.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial133.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial133.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial133 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 9048416869918145556018684865671740), (Int.ofNat 484272961266520388974398415599257), (Int.negOfNat 21163464025807807192478597622599), (Int.ofNat 3395564894270783782441577339198), (Int.ofNat 2421000869062121582270447026364), (Int.negOfNat 278841042040023103388073755767), (Int.negOfNat 49489976860019311130772213352), (Int.ofNat 3842068347016469195985336437), (Int.ofNat 671604207489685504792992999), (Int.negOfNat 21277545447289400498147847), (Int.negOfNat 5956552393308681546072052), (Int.ofNat 6741961138723588041152), (Int.ofNat 35192934034983128595313), (Int.ofNat 593351235353869372617), (Int.negOfNat 146174556725296010171), (Int.negOfNat 4144239274000814681), (Int.ofNat 648850811659757916), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-452420843495907277800934243283587/562949953421312000000000000000000), (484272961266520388974398415599257/11258999068426240000000000000000000), (-21163464025807807192478597622599/11258999068426240000000000000000000), (1697782447135391891220788669599/5629499534213120000000000000000000), (605250217265530395567611756591/2814749767106560000000000000000000), (-278841042040023103388073755767/11258999068426240000000000000000000), (-6186247107502413891346526669/1407374883553280000000000000000000), (3842068347016469195985336437/11258999068426240000000000000000000), (671604207489685504792992999/11258999068426240000000000000000000), (-21277545447289400498147847/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial133.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial133.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial133.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial133 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 8110067660142876508866497788061247), (Int.ofNat 488358956117911265096228097535660), (Int.ofNat 26750392967340134249707497323173), (Int.ofNat 6845034882040969540621826523548), (Int.negOfNat 1669874995030000544298544751918), (Int.negOfNat 336232659524408293150893123906), (Int.ofNat 47398638092511194565557743920), (Int.ofNat 6730168788461479208117495670), (Int.negOfNat 501323592110450594592341799), (Int.negOfNat 80142325374484763369353458), (Int.ofNat 2362446027377286896264139), (Int.ofNat 591844624732145739186807), (Int.negOfNat 2718804659107748657716), (Int.negOfNat 2939142913709048803111), (Int.negOfNat 28640085038596240314), (Int.ofNat 10782013267381791180), (Int.ofNat 216681276801076152), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-8110067660142876508866497788061247/11258999068426240000000000000000000), (24417947805895563254811404876783/562949953421312000000000000000000), (26750392967340134249707497323173/11258999068426240000000000000000000), (1711258720510242385155456630887/2814749767106560000000000000000000), (-834937497515000272149272375959/5629499534213120000000000000000000), (-168116329762204146575446561953/5629499534213120000000000000000000), (592482976156389932069471799/140737488355328000000000000000000), (673016878846147920811749567/1125899906842624000000000000000000), (-501323592110450594592341799/11258999068426240000000000000000000), (-40071162687242381684676729/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial133.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial133.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial133.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial133 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 7005336143370425468969003328562040), (Int.ofNat 608602523073878895963017270593348), (Int.ofNat 15518895388428267349992922435589), (Int.negOfNat 9879693668510997349791699502018), (Int.negOfNat 1133121435618882616035097993240), (Int.ofNat 447035431701747164460099528351), (Int.ofNat 47504046814309869585753745322), (Int.negOfNat 7825065692146806100372863448), (Int.negOfNat 876567660003827532732764731), (Int.ofNat 60538284028998239975737352), (Int.ofNat 8518889097193577439291263), (Int.negOfNat 240411401720442125209107), (Int.negOfNat 51550284138381444406592), (Int.ofNat 397409442068497417783), (Int.ofNat 215232853361932785626), (Int.ofNat 1265467635034174944), (Int.negOfNat 831900828660315122), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-175133403584260636724225083214051/281474976710656000000000000000000), (152150630768469723990754317648337/2814749767106560000000000000000000), (15518895388428267349992922435589/11258999068426240000000000000000000), (-4939846834255498674895849751009/5629499534213120000000000000000000), (-28328035890472065400877449831/281474976710656000000000000000000), (447035431701747164460099528351/11258999068426240000000000000000000), (23752023407154934792876872661/5629499534213120000000000000000000), (-978133211518350762546607931/1407374883553280000000000000000000), (-876567660003827532732764731/11258999068426240000000000000000000), (7567285503624779996967169/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial133.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial133.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial133.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial133 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 5807064602687650354154276676721792), (Int.ofNat 556521439341194535956576947610638), (Int.negOfNat 30252641104250540167467758774424), (Int.ofNat 1025172049042113900843443896079), (Int.ofNat 3356962819674699987073870191883), (Int.ofNat 145832363905827717609530044669), (Int.negOfNat 97269840973819078239245892750), (Int.negOfNat 7394308327780395269078122139), (Int.ofNat 1077289670050976466058763867), (Int.ofNat 104977927686575031116724493), (Int.negOfNat 6270038532566590362762908), (Int.negOfNat 798533106603895570230812), (Int.ofNat 21502830726570779661617), (Int.ofNat 3967377406542292408631), (Int.negOfNat 40201513487971790991), (Int.negOfNat 14878695370317997103), (Int.negOfNat 60570973192449758), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-45367692208497268391830286536889/87960930222080000000000000000000), (278260719670597267978288473805319/5629499534213120000000000000000000), (-3781580138031317520933469846803/1407374883553280000000000000000000), (1025172049042113900843443896079/11258999068426240000000000000000000), (3356962819674699987073870191883/11258999068426240000000000000000000), (145832363905827717609530044669/11258999068426240000000000000000000), (-389079363895276312956983571/45035996273704960000000000000000), (-7394308327780395269078122139/11258999068426240000000000000000000), (1077289670050976466058763867/11258999068426240000000000000000000), (104977927686575031116724493/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial133.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial133.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial133.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial133 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 4755303014181977672918043846134622), (Int.ofNat 546218527266089005907053847559456), (Int.ofNat 42139934353006163368782999263913), (Int.ofNat 16378535714857238639496097526934), (Int.negOfNat 1575378242890053612407099786180), (Int.negOfNat 1019036858429043690327206582429), (Int.negOfNat 40385399414637700591176457718), (Int.ofNat 15663671954207187351489757115), (Int.ofNat 1098820286813337012775363461), (Int.negOfNat 119798727884974744249398035), (Int.negOfNat 11006355681259393285736867), (Int.ofNat 557027526015191341690031), (Int.ofNat 65719800770787126882464), (Int.negOfNat 1708321935944393423954), (Int.negOfNat 271527321506902999881), (Int.ofNat 3628532696372409921), (Int.ofNat 936895693856559131), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-2377651507090988836459021923067311/5629499534213120000000000000000000), (17069328977065281434595432736233/351843720888320000000000000000000), (42139934353006163368782999263913/11258999068426240000000000000000000), (8189267857428619319748048763467/5629499534213120000000000000000000), (-78768912144502680620354989309/562949953421312000000000000000000), (-1019036858429043690327206582429/11258999068426240000000000000000000), (-20192699707318850295588228859/5629499534213120000000000000000000), (3132734390841437470297951423/2251799813685248000000000000000000), (1098820286813337012775363461/11258999068426240000000000000000000), (-23959745576994948849879607/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial133.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial133.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial133.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial133 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 3421462801177030178904979196144149), (Int.ofNat 779449561024806701752584313026140), (Int.ofNat 23222632095232233329986568383609), (Int.negOfNat 33489742736002450326626789132996), (Int.negOfNat 9172348891668662705599192856325), (Int.negOfNat 3601898184217864969399096361), (Int.ofNat 196040757105694219786537194596), (Int.ofNat 9737862493312872718015654393), (Int.negOfNat 1900003591698057431514316548), (Int.negOfNat 136392523475569778978243331), (Int.ofNat 11070769301627553773326499), (Int.ofNat 992351241412047021657035), (Int.negOfNat 43565642230871698640483), (Int.negOfNat 4765354730541166817179), (Int.ofNat 122851350743827247004), (Int.ofNat 17314654355036100753), (Int.negOfNat 193799267264437942), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-3421462801177030178904979196144149/11258999068426240000000000000000000), (38972478051240335087629215651307/562949953421312000000000000000000), (23222632095232233329986568383609/11258999068426240000000000000000000), (-8372435684000612581656697283249/2814749767106560000000000000000000), (-366893955666746508223967714253/450359962737049600000000000000000), (-3601898184217864969399096361/11258999068426240000000000000000000), (49010189276423554946634298649/2814749767106560000000000000000000), (9737862493312872718015654393/11258999068426240000000000000000000), (-475000897924514357878579137/2814749767106560000000000000000000), (-136392523475569778978243331/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial133.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial133.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial133.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial133 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 2171213960843300553229184999617212), (Int.ofNat 216468949555228017889301069974588), (Int.negOfNat 348428194024108187599033163650862), (Int.negOfNat 74125156686125036943313491972556), (Int.ofNat 2786352560159191021384277336916), (Int.ofNat 2153502089499261385594846301944), (Int.ofNat 76294138627326548260514585191), (Int.negOfNat 25983630303962481464578761637), (Int.negOfNat 1557763146091712999340771654), (Int.ofNat 184724993161038647775516391), (Int.ofNat 13834971118692883099985371), (Int.negOfNat 885705808747671912863913), (Int.negOfNat 77296842785919654188770), (Int.ofNat 3085315525495466587452), (Int.ofNat 307196149987329662232), (Int.negOfNat 7893616272095558706), (Int.negOfNat 957100478900507240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-542803490210825138307296249904303/2814749767106560000000000000000000), (54117237388807004472325267493647/2814749767106560000000000000000000), (-174214097012054093799516581825431/5629499534213120000000000000000000), (-18531289171531259235828372993139/2814749767106560000000000000000000), (696588140039797755346069334229/2814749767106560000000000000000000), (269187761187407673199355787743/1407374883553280000000000000000000), (76294138627326548260514585191/11258999068426240000000000000000000), (-25983630303962481464578761637/11258999068426240000000000000000000), (-778881573045856499670385827/5629499534213120000000000000000000), (184724993161038647775516391/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial133.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial133.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial133.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial133 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 3610231605007730498496554788917174), (Int.negOfNat 1803404836659710928487992795156043), (Int.negOfNat 554987398638022277843363767121063), (Int.ofNat 30331046173509035759372521939027), (Int.ofNat 20763871503751290087254658597489), (Int.ofNat 639773642524155743014297394337), (Int.negOfNat 308104916704200793303954920483), (Int.negOfNat 17206071993270727256275059298), (Int.ofNat 2652862928339890248076750652), (Int.ofNat 181676404885399853331202966), (Int.negOfNat 15275355894165686099850460), (Int.negOfNat 1170560949904101615845263), (Int.ofNat 63631673865820946661692), (Int.ofNat 5264045004036250298664), (Int.negOfNat 201528179819278131675), (Int.negOfNat 18068281593404251809), (Int.ofNat 448169507721325642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-1805115802503865249248277394458587/5629499534213120000000000000000000), (-1803404836659710928487992795156043/11258999068426240000000000000000000), (-554987398638022277843363767121063/11258999068426240000000000000000000), (30331046173509035759372521939027/11258999068426240000000000000000000), (20763871503751290087254658597489/11258999068426240000000000000000000), (639773642524155743014297394337/11258999068426240000000000000000000), (-308104916704200793303954920483/11258999068426240000000000000000000), (-8603035996635363628137529649/5629499534213120000000000000000000), (663215732084972562019187663/2814749767106560000000000000000000), (90838202442699926665601483/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial133.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial133.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial133.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial133 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 8862814482891303576702190419701869), (Int.negOfNat 3007575025904593851708526217954318), (Int.ofNat 96393237708960793879184444838319), (Int.ofNat 168555854044921704659975058608687), (Int.ofNat 7316331816739599292576983153934), (Int.negOfNat 3097915541625022846719515721801), (Int.negOfNat 193689724480118263122511612694), (Int.ofNat 32632961688690970690848659320), (Int.ofNat 2297882556371608095149199547), (Int.negOfNat 226754267901420743205731908), (Int.negOfNat 16761391102949955081746524), (Int.ofNat 1125840907905442922575055), (Int.ofNat 84697810623666341398203), (Int.negOfNat 4215633544917865059053), (Int.negOfNat 317596176808032983298), (Int.ofNat 12123818254473769751), (Int.ofNat 977305263944455349), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-8862814482891303576702190419701869/11258999068426240000000000000000000), (-1503787512952296925854263108977159/5629499534213120000000000000000000), (96393237708960793879184444838319/11258999068426240000000000000000000), (168555854044921704659975058608687/11258999068426240000000000000000000), (3658165908369799646288491576967/5629499534213120000000000000000000), (-3097915541625022846719515721801/11258999068426240000000000000000000), (-96844862240059131561255806347/5629499534213120000000000000000000), (815824042217274267271216483/281474976710656000000000000000000), (2297882556371608095149199547/11258999068426240000000000000000000), (-56688566975355185801432977/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial133.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial133.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial133.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial133 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 13133778253581779666752627573309984), (Int.negOfNat 633852034771348067105005026373457), (Int.ofNat 1013847377812511463098260996452821), (Int.ofNat 93150960860432501257314574288146), (Int.negOfNat 24656434868893633728301180620387), (Int.negOfNat 2203666063222649941516222611569), (Int.ofNat 332359072378230759314200659403), (Int.ofNat 28169265324064204455922699518), (Int.negOfNat 2865648595744093779921806436), (Int.negOfNat 228699674177558517896422339), (Int.ofNat 17207757572622348197292185), (Int.ofNat 1287842880538242283816932), (Int.negOfNat 76395325597580875187963), (Int.negOfNat 5344522555096342956135), (Int.ofNat 262276760336833564595), (Int.ofNat 16975371708182264147), (Int.negOfNat 709274676526196045), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-410430570424430614586019611665937/351843720888320000000000000000000), (-633852034771348067105005026373457/11258999068426240000000000000000000), (1013847377812511463098260996452821/11258999068426240000000000000000000), (46575480430216250628657287144073/5629499534213120000000000000000000), (-24656434868893633728301180620387/11258999068426240000000000000000000), (-2203666063222649941516222611569/11258999068426240000000000000000000), (332359072378230759314200659403/11258999068426240000000000000000000), (14084632662032102227961349759/5629499534213120000000000000000000), (-716412148936023444980451609/2814749767106560000000000000000000), (-228699674177558517896422339/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial133.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial133.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial133.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial133.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial133 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial133 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial133 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 15691415887972511979640553781817648), (Int.ofNat 158379277665804165909225847911400), (Int.ofNat 1093154155163365597621256284808902), (Int.negOfNat 104820842975472221366914976579968), (Int.negOfNat 25398631450641449445562493731835), (Int.ofNat 2559038133125868288561867214806), (Int.ofNat 336609412110462412355013535026), (Int.negOfNat 31669029170609371652954705718), (Int.negOfNat 2882814163009765295659935056), (Int.ofNat 247422499732523044706499999), (Int.ofNat 17261093878943688105083105), (Int.negOfNat 1351919493696386767736932), (Int.negOfNat 76526211006383026406723), (Int.ofNat 5496256151319695280275), (Int.ofNat 262276760336833564595), (Int.negOfNat 16975371708182264147), (Int.negOfNat 709274676526196045), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-980713492998281998727534611363603/703687441776640000000000000000000), (791896388329020829546129239557/56294995342131200000000000000000), (546577077581682798810628142404451/5629499534213120000000000000000000), (-818912835745876729429023254531/87960930222080000000000000000000), (-5079726290128289889112498746367/2251799813685248000000000000000000), (1279519066562934144280933607403/5629499534213120000000000000000000), (168304706055231206177506767513/5629499534213120000000000000000000), (-15834514585304685826477352859/5629499534213120000000000000000000), (-180175885188110330978745941/703687441776640000000000000000000), (247422499732523044706499999/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial133.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial133.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial133.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 12148203650304886272057438552642028), (Int.ofNat 2713243554914526511232869091361442), (Int.ofNat 115020349882502377922294492493505), (Int.negOfNat 173160203669480762319880364174223), (Int.ofNat 9457256770601405901924268458738), (Int.ofNat 3238938763846894022787150647901), (Int.negOfNat 228519521572430684030817686654), (Int.negOfNat 33985211518975554933825705140), (Int.ofNat 2547855528863633516778892807), (Int.ofNat 233901962583958487917714808), (Int.negOfNat 17822787800976265469683924), (Int.negOfNat 1150183237173100807495215), (Int.ofNat 87717002815912747087103), (Int.ofNat 4273927816364291014793), (Int.negOfNat 323826098947345680858), (Int.negOfNat 12123818254473769751), (Int.ofNat 977305263944455349), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-3037050912576221568014359638160507/2814749767106560000000000000000000), (1356621777457263255616434545680721/5629499534213120000000000000000000), (23004069976500475584458898498701/2251799813685248000000000000000000), (-173160203669480762319880364174223/11258999068426240000000000000000000), (4728628385300702950962134229369/5629499534213120000000000000000000), (3238938763846894022787150647901/11258999068426240000000000000000000), (-114259760786215342015408843327/5629499534213120000000000000000000), (-1699260575948777746691285257/562949953421312000000000000000000), (2547855528863633516778892807/11258999068426240000000000000000000), (29237745322994810989714351/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial133.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial133.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial133.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 7410178186613467607178326532106141), (Int.ofNat 1601094754804076935519197495141027), (Int.negOfNat 510122004484680215741162884247461), (Int.negOfNat 18027696206865479461871185264317), (Int.ofNat 22140503919531392634541748015684), (Int.negOfNat 912859632218232375271280841937), (Int.negOfNat 332805841443330870246666121003), (Int.ofNat 19815240507558254420285431698), (Int.ofNat 2833369810243388942535459992), (Int.negOfNat 195549119161631418687019546), (Int.negOfNat 16046218885213223433232240), (Int.ofNat 1217945853893734366203783), (Int.ofNat 65828525842990840367672), (Int.negOfNat 5377963580297968196904), (Int.negOfNat 205978124204501487075), (Int.ofNat 18068281593404251809), (Int.ofNat 448169507721325642), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-7410178186613467607178326532106141/11258999068426240000000000000000000), (1601094754804076935519197495141027/11258999068426240000000000000000000), (-510122004484680215741162884247461/11258999068426240000000000000000000), (-18027696206865479461871185264317/11258999068426240000000000000000000), (5535125979882848158635437003921/2814749767106560000000000000000000), (-912859632218232375271280841937/11258999068426240000000000000000000), (-332805841443330870246666121003/11258999068426240000000000000000000), (9907620253779127210142715849/5629499534213120000000000000000000), (354171226280423617816932499/1407374883553280000000000000000000), (-97774559580815709343509773/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial133.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial133.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial133.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 6085813425827651713333838424142625), (Int.negOfNat 72896056385680226268855429489063), (Int.negOfNat 222473136185563115045830350789349), (Int.ofNat 84266373845971316095509215328343), (Int.ofNat 818743766770559790363793175766), (Int.negOfNat 2455563038129104834842691310201), (Int.ofNat 97228458249863058796138570914), (Int.ofNat 29035027620436185379779881397), (Int.negOfNat 1691119013154095285451011594), (Int.negOfNat 201235556116008125157804671), (Int.ofNat 14377333868686232527006711), (Int.ofNat 942468500972314663814013), (Int.negOfNat 78812512858152257228010), (Int.negOfNat 3221928818121823598232), (Int.ofNat 310311111056986011012), (Int.ofNat 7893616272095558706), (Int.negOfNat 957100478900507240), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-48686507406621213706670707393141/90071992547409920000000000000000), (-72896056385680226268855429489063/11258999068426240000000000000000000), (-222473136185563115045830350789349/11258999068426240000000000000000000), (84266373845971316095509215328343/11258999068426240000000000000000000), (409371883385279895181896587883/5629499534213120000000000000000000), (-2455563038129104834842691310201/11258999068426240000000000000000000), (48614229124931529398069285457/5629499534213120000000000000000000), (29035027620436185379779881397/11258999068426240000000000000000000), (-845559506577047642725505797/5629499534213120000000000000000000), (-201235556116008125157804671/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial133.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial133.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial133.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 6503425755076375142829563853523993), (Int.negOfNat 92274997075159203306982477433321), (Int.ofNat 145404950848938993470656674411213), (Int.ofNat 20548711130988311596604148889883), (Int.negOfNat 12256597099554349963254722819525), (Int.ofNat 121898680485960570654333206304), (Int.ofNat 236208569915304355257410316153), (Int.negOfNat 10428967341461214420524794093), (Int.negOfNat 2174840832389748920805782008), (Int.ofNat 139257263320544723488311431), (Int.ofNat 12219631133355189622579379), (Int.negOfNat 1001079354410166923525355), (Int.negOfNat 46812264610454074170323), (Int.ofNat 4786723970903003018099), (Int.ofNat 129526267321662280104), (Int.negOfNat 17314654355036100753), (Int.negOfNat 193799267264437942), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-6503425755076375142829563853523993/11258999068426240000000000000000000), (-92274997075159203306982477433321/11258999068426240000000000000000000), (145404950848938993470656674411213/11258999068426240000000000000000000), (20548711130988311596604148889883/11258999068426240000000000000000000), (-490263883982173998530188912781/450359962737049600000000000000000), (3809333765186267832947912697/351843720888320000000000000000000), (236208569915304355257410316153/11258999068426240000000000000000000), (-10428967341461214420524794093/11258999068426240000000000000000000), (-271855104048718615100722751/1407374883553280000000000000000000), (139257263320544723488311431/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial133.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial133.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial133.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 6120863759764345404063044136276615), (Int.ofNat 392294210312344305888715164257138), (Int.ofNat 30827169229671326720738936889062), (Int.negOfNat 43682035260052058683957791100182), (Int.negOfNat 1541692003978451997255454396953), (Int.ofNat 1452633012877971774068355780626), (Int.negOfNat 35201378297633040154089259178), (Int.negOfNat 19360168923108320963487435575), (Int.ofNat 1047129365908637814318221221), (Int.ofNat 138630824905675140544794255), (Int.negOfNat 10763558451313357677052247), (Int.negOfNat 620282059093220911003331), (Int.ofNat 65005244282960661050224), (Int.ofNat 1858285061726420500934), (Int.negOfNat 270192338191335993261), (Int.negOfNat 3628532696372409921), (Int.ofNat 936895693856559131), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-1224172751952869080812608827255323/2251799813685248000000000000000000), (196147105156172152944357582128569/5629499534213120000000000000000000), (15413584614835663360369468444531/5629499534213120000000000000000000), (-21841017630026029341978895550091/5629499534213120000000000000000000), (-1541692003978451997255454396953/11258999068426240000000000000000000), (726316506438985887034177890313/5629499534213120000000000000000000), (-17600689148816520077044629589/5629499534213120000000000000000000), (-774406756924332838539497423/450359962737049600000000000000000), (1047129365908637814318221221/11258999068426240000000000000000000), (27726164981135028108958851/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial133.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial133.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial133.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 5545009720914865938742520659974776), (Int.ofNat 44194175384135688975512066800779), (Int.negOfNat 171134982448932641474951863381490), (Int.negOfNat 11946297798494879190537030053135), (Int.ofNat 7021226217404797240252847928517), (Int.ofNat 54339452396076424505253858061), (Int.negOfNat 137099259103016378614342071870), (Int.ofNat 5480233183251603343644037539), (Int.ofNat 1325361603352486898253584407), (Int.negOfNat 94738910099037482455726993), (Int.negOfNat 7266191590958617161366268), (Int.ofNat 763459276140730293496932), (Int.ofNat 24273006672187195253117), (Int.negOfNat 3883273457661570991571), (Int.negOfNat 45986441188762153011), (Int.ofNat 14433700931795661563), (Int.negOfNat 60570973192449758), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-693126215114358242342815082496847/1407374883553280000000000000000000), (44194175384135688975512066800779/11258999068426240000000000000000000), (-17113498244893264147495186338149/1125899906842624000000000000000000), (-2389259559698975838107406010627/2251799813685248000000000000000000), (7021226217404797240252847928517/11258999068426240000000000000000000), (54339452396076424505253858061/11258999068426240000000000000000000), (-13709925910301637861434207187/1125899906842624000000000000000000), (5480233183251603343644037539/11258999068426240000000000000000000), (1325361603352486898253584407/11258999068426240000000000000000000), (-94738910099037482455726993/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial133.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial133.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial133.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 6130441106576348900975164107717943), (Int.negOfNat 577432169775571573909061738065884), (Int.negOfNat 97299991074860376396562076186959), (Int.ofNat 29318098428565825853314676738917), (Int.ofNat 1911784161588465132465920879396), (Int.negOfNat 762588520319085875755536607682), (Int.ofNat 11854292933023457752825520982), (Int.ofNat 10289836367184463990803304388), (Int.negOfNat 645571819610892658177466911), (Int.negOfNat 72496478000556407100516712), (Int.ofNat 7575034174947833599160043), (Int.ofNat 279722080754643516293927), (Int.negOfNat 48906098662743434342912), (Int.negOfNat 489523290842620874563), (Int.ofNat 209892920099664759146), (Int.negOfNat 820473196511839404), (Int.negOfNat 831900828660315122), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-6130441106576348900975164107717943/11258999068426240000000000000000000), (-144358042443892893477265434516471/2814749767106560000000000000000000), (-97299991074860376396562076186959/11258999068426240000000000000000000), (29318098428565825853314676738917/11258999068426240000000000000000000), (477946040397116283116480219849/2814749767106560000000000000000000), (-381294260159542937877768303841/5629499534213120000000000000000000), (5927146466511728876412760491/5629499534213120000000000000000000), (2572459091796115997700826097/2814749767106560000000000000000000), (-645571819610892658177466911/11258999068426240000000000000000000), (-9062059750069550887564589/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial133.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial133.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial133.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 7431893391080478526100364305735918), (Int.negOfNat 608546437232658016660585715850784), (Int.ofNat 71845044254796549922607647264271), (Int.ofNat 20343889217736358442511448350115), (Int.negOfNat 3029578646848152067596564483053), (Int.negOfNat 126914670996899658936089065914), (Int.ofNat 61633467908458551025735751260), (Int.negOfNat 2935198326018169959003129210), (Int.negOfNat 587327598950648367477384579), (Int.ofNat 61267794168019925095303498), (Int.ofNat 2702740514803005352097379), (Int.negOfNat 529115906059087020348947), (Int.negOfNat 3659125444269264128736), (Int.ofNat 2791404760119633403831), (Int.negOfNat 26415112845984562614), (Int.negOfNat 10782013267381791180), (Int.ofNat 216681276801076152), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-3715946695540239263050182152867959/5629499534213120000000000000000000), (-19017076163520563020643303620337/351843720888320000000000000000000), (71845044254796549922607647264271/11258999068426240000000000000000000), (4068777843547271688502289670023/2251799813685248000000000000000000), (-3029578646848152067596564483053/11258999068426240000000000000000000), (-63457335498449829468044532957/5629499534213120000000000000000000), (3081673395422927551286787563/562949953421312000000000000000000), (-293519832601816995900312921/1125899906842624000000000000000000), (-587327598950648367477384579/11258999068426240000000000000000000), (30633897084009962547651749/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial133.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial133.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial133.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 8247937961704163118365017564149639), (Int.negOfNat 174072954137191947866679476222858), (Int.ofNat 123111144307890220112931935959630), (Int.negOfNat 1455266641614666251181350570807), (Int.negOfNat 1818868843042792520150069769541), (Int.ofNat 233165700160721853931033915228), (Int.negOfNat 2457037466667374008421287792), (Int.negOfNat 3522091792792063886089908937), (Int.ofNat 376922778961529705555084219), (Int.ofNat 19856432984254269281639047), (Int.negOfNat 4770572089403008796606012), (Int.negOfNat 2275055729749783156712), (Int.ofNat 31891870216896802609593), (Int.negOfNat 603586107439883090037), (Int.negOfNat 139499640147460977071), (Int.ofNat 4144239274000814681), (Int.ofNat 648850811659757916), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-8247937961704163118365017564149639/11258999068426240000000000000000000), (-87036477068595973933339738111429/5629499534213120000000000000000000), (12311114430789022011293193595963/1125899906842624000000000000000000), (-1455266641614666251181350570807/11258999068426240000000000000000000), (-1818868843042792520150069769541/11258999068426240000000000000000000), (58291425040180463482758478807/2814749767106560000000000000000000), (-153564841666710875526330487/703687441776640000000000000000000), (-3522091792792063886089908937/11258999068426240000000000000000000), (376922778961529705555084219/11258999068426240000000000000000000), (19856432984254269281639047/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial133.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial133.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial133.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 8137428210570302806403997846504294), (Int.ofNat 259716232036720611201630724523276), (Int.ofNat 87137347480417957402453783002698), (Int.negOfNat 8332944721722934380742622533209), (Int.negOfNat 179126768971083989701701012600), (Int.ofNat 81086919090499200797062968936), (Int.negOfNat 10610903033255435587197213216), (Int.ofNat 1465653944742476328237249337), (Int.ofNat 78048567290143103443710189), (Int.negOfNat 33954529823406096756284061), (Int.ofNat 549572893460919740239737), (Int.ofNat 303206608281696348023891), (Int.negOfNat 10931986503481021432552), (Int.negOfNat 1616916877882294252782), (Int.ofNat 76964333904261019459), (Int.ofNat 5775609056185757705), (Int.negOfNat 281266571909423943), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-4068714105285151403201998923252147/5629499534213120000000000000000000), (64929058009180152800407681130819/2814749767106560000000000000000000), (43568673740208978701226891501349/5629499534213120000000000000000000), (-8332944721722934380742622533209/11258999068426240000000000000000000), (-895633844855419948508505063/56294995342131200000000000000000), (10135864886312400099632871117/1407374883553280000000000000000000), (-331590719789232362099912913/351843720888320000000000000000000), (1465653944742476328237249337/11258999068426240000000000000000000), (78048567290143103443710189/11258999068426240000000000000000000), (-33954529823406096756284061/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial133.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial133.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial133.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 7336868932501980348280473426640416), (Int.ofNat 507652076610291669282188940893550), (Int.ofNat 37763198370582751728586738530144), (Int.negOfNat 7422527045675592827297013893472), (Int.ofNat 374289195017615797904167445109), (Int.ofNat 55233249322183578015009487480), (Int.ofNat 1230409149552171002663784035), (Int.negOfNat 460118477515502916892769989), (Int.negOfNat 168864368764939884972756280), (Int.ofNat 12231968069292097026449955), (Int.ofNat 2229649308515329521137803), (Int.negOfNat 166067675717216977867605), (Int.negOfNat 15019170832836335479219), (Int.ofNat 1236497401818656249189), (Int.ofNat 64459747639585156124), (Int.negOfNat 6351699862442983571), (Int.negOfNat 394480571202870216), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-229277154140686885883764794582513/351843720888320000000000000000000), (10153041532205833385643778817871/225179981368524800000000000000000), (1180099949080710991518335579067/351843720888320000000000000000000), (-231953970177362275853031684171/351843720888320000000000000000000), (374289195017615797904167445109/11258999068426240000000000000000000), (1380831233054589450375237187/281474976710656000000000000000000), (246081829910434200532756807/2251799813685248000000000000000000), (-460118477515502916892769989/11258999068426240000000000000000000), (-4221609219123497124318907/281474976710656000000000000000000), (2446393613858419405289991/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial133.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial133.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial133.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 6222151334035566114481963037990461), (Int.ofNat 585925078387651643648308149562055), (Int.ofNat 6389705575005960618649702799323), (Int.negOfNat 2490590629871033073265802383856), (Int.ofNat 753354238678420847607266445906), (Int.negOfNat 7642066185525368288717461601), (Int.negOfNat 11450801836257810892247088091), (Int.negOfNat 363854240923626824470033859), (Int.ofNat 172565366120316723063797878), (Int.ofNat 10085032210957552073824757), (Int.negOfNat 2143545881816726771807453), (Int.negOfNat 93025927924884274160953), (Int.ofNat 17488715694689918570806), (Int.ofNat 472076964915684794360), (Int.negOfNat 94806418433148630508), (Int.negOfNat 1222524296070132890), (Int.ofNat 261061786865475834), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-6222151334035566114481963037990461/11258999068426240000000000000000000), (117185015677530328729661629912411/2251799813685248000000000000000000), (6389705575005960618649702799323/11258999068426240000000000000000000), (-155661914366939567079112648991/703687441776640000000000000000000), (376677119339210423803633222953/5629499534213120000000000000000000), (-7642066185525368288717461601/11258999068426240000000000000000000), (-11450801836257810892247088091/11258999068426240000000000000000000), (-363854240923626824470033859/11258999068426240000000000000000000), (86282683060158361531898939/5629499534213120000000000000000000), (10085032210957552073824757/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial133.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial133.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial133.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 5033590354293355549365802024881228), (Int.ofNat 602919586629001592659852740609477), (Int.ofNat 6252212497426505433675835201726), (Int.ofNat 1523309564077518233432427937278), (Int.ofNat 91492987139589304811982680888), (Int.negOfNat 96181902971674879420151263827), (Int.ofNat 2045568083839605888335805795), (Int.ofNat 1753174735181088834665254924), (Int.negOfNat 14998589642251137115328576), (Int.negOfNat 23144273571862325755117400), (Int.ofNat 16967071919103513395976), (Int.ofNat 212767882996906206085537), (Int.negOfNat 326341886584550974092), (Int.negOfNat 1336132745426059894884), (Int.ofNat 5336255787440483245), (Int.ofNat 5959900114098597975), (Int.ofNat 140110330745982516), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-1258397588573338887341450506220307/2814749767106560000000000000000000), (602919586629001592659852740609477/11258999068426240000000000000000000), (3126106248713252716837917600863/5629499534213120000000000000000000), (761654782038759116716213968639/5629499534213120000000000000000000), (11436623392448663101497835111/1407374883553280000000000000000000), (-96181902971674879420151263827/11258999068426240000000000000000000), (409113616767921177667161159/2251799813685248000000000000000000), (438293683795272208666313731/2814749767106560000000000000000000), (-234352963160174017427009/175921860444160000000000000000000), (-115721367859311628775587/56294995342131200000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial133.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial133.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial133.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 3791829713277806780036632812652678), (Int.ofNat 642553269617224799864208140699491), (Int.ofNat 11434851649570019135689466883348), (Int.negOfNat 425419773854344014635903401720), (Int.negOfNat 358112003583121230650286813925), (Int.ofNat 28231719502200926456324827381), (Int.ofNat 12266092771871439684785634328), (Int.negOfNat 823065350415443370651375558), (Int.negOfNat 199622795795522586823582365), (Int.ofNat 10254041375134355776221406), (Int.ofNat 2154345627801173163863420), (Int.negOfNat 84751324189047671621145), (Int.negOfNat 15886256788479019624553), (Int.ofNat 516818608120181952199), (Int.ofNat 82219711008405752762), (Int.negOfNat 3026281736781246065), (Int.negOfNat 240857001821527725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-1895914856638903390018316406326339/5629499534213120000000000000000000), (642553269617224799864208140699491/11258999068426240000000000000000000), (2858712912392504783922366720837/2814749767106560000000000000000000), (-10635494346358600365897585043/281474976710656000000000000000000), (-14324480143324849226011472557/450359962737049600000000000000000), (28231719502200926456324827381/11258999068426240000000000000000000), (1533261596483929960598204291/1407374883553280000000000000000000), (-411532675207721685325687779/5629499534213120000000000000000000), (-39924559159104517364716473/2251799813685248000000000000000000), (5127020687567177888110703/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial133.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial133.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial133.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 2468577705565544069176514029904018), (Int.ofNat 675801881916393310059607123710380), (Int.ofNat 4647939915587859503091707161779), (Int.negOfNat 934058558596164525743396587732), (Int.ofNat 271105599546929758870458329127), (Int.ofNat 51029673596682652387474936518), (Int.negOfNat 9509156822774568729227022972), (Int.negOfNat 1234944540772439909093822984), (Int.ofNat 169317202832323994171544052), (Int.ofNat 16780178917906957057493767), (Int.negOfNat 1760964918748468986514891), (Int.negOfNat 150696691931963843042668), (Int.ofNat 12321287075518015933021), (Int.ofNat 935892062747711951693), (Int.negOfNat 61855722095403207365), (Int.negOfNat 4468028721774850637), (Int.ofNat 107524981362922481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1234288852782772034588257014952009/5629499534213120000000000000000000), (33790094095819665502980356185519/562949953421312000000000000000000), (4647939915587859503091707161779/11258999068426240000000000000000000), (-233514639649041131435849146933/2814749767106560000000000000000000), (271105599546929758870458329127/11258999068426240000000000000000000), (25514836798341326193737468259/5629499534213120000000000000000000), (-2377289205693642182306755743/2814749767106560000000000000000000), (-154368067596554988636727873/1407374883553280000000000000000000), (42329300708080998542886013/2814749767106560000000000000000000), (16780178917906957057493767/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial133.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial133.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial133.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 1100600788530582602080078433829698), (Int.ofNat 693765352074159391063455516812069), (Int.ofNat 6877582018821542230494650561160), (Int.ofNat 1424761026848561397722100399344), (Int.ofNat 94159175144791600418711156795), (Int.negOfNat 74305535197617450287073086188), (Int.negOfNat 3825370112579417052371323788), (Int.ofNat 1786755441611418654298518156), (Int.ofNat 77129768765479780592874868), (Int.negOfNat 24105467234938568510366233), (Int.negOfNat 931761324552278024994489), (Int.ofNat 205579148271132488442592), (Int.ofNat 7464404846270762970039), (Int.negOfNat 1207979218622991658747), (Int.negOfNat 41503952693836420055), (Int.ofNat 5556652044615760563), (Int.ofNat 57806984820970519), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-550300394265291301040039216914849/5629499534213120000000000000000000), (693765352074159391063455516812069/11258999068426240000000000000000000), (171939550470538555762366264029/281474976710656000000000000000000), (89047564178035087357631274959/703687441776640000000000000000000), (18831835028958320083742231359/2251799813685248000000000000000000), (-18576383799404362571768271547/2814749767106560000000000000000000), (-956342528144854263092830947/2814749767106560000000000000000000), (446688860402854663574629539/2814749767106560000000000000000000), (19282442191369945148218717/2814749767106560000000000000000000), (-24105467234938568510366233/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial133.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial133.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial133.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 324957872892753686054463928129394), (Int.ofNat 735528561254114649248816323101872), (Int.ofNat 12046630937313290811579845684386), (Int.negOfNat 402199408777844753741084965577), (Int.negOfNat 392297338916801918852345063653), (Int.ofNat 14733103412153941690641502348), (Int.ofNat 13695880744612258700486917632), (Int.negOfNat 211916710908471133628876038), (Int.negOfNat 247125820209838992792769515), (Int.ofNat 938432008989360734060566), (Int.ofNat 2670802040835433740807040), (Int.ofNat 8793620720767328311495), (Int.negOfNat 19002187107249202284487), (Int.negOfNat 147399366625150229701), (Int.ofNat 94888637611245600538), (Int.ofNat 1700335187190161335), (Int.negOfNat 263635284971548875), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(162478936446376843027231964064697/5629499534213120000000000000000000), (45970535078382165578051020193867/703687441776640000000000000000000), (6023315468656645405789922842193/5629499534213120000000000000000000), (-402199408777844753741084965577/11258999068426240000000000000000000), (-392297338916801918852345063653/11258999068426240000000000000000000), (3683275853038485422660375587/2814749767106560000000000000000000), (26749767079320817774388511/21990232555520000000000000000000), (-105958355454235566814438019/5629499534213120000000000000000000), (-49425164041967798558553903/2251799813685248000000000000000000), (469216004494680367030283/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial133.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial133.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial133.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 1835967928480197396180360874178672), (Int.ofNat 769810910807101356440577277491731), (Int.ofNat 4132767549524421634461185646329), (Int.negOfNat 1277108938664089736797134896846), (Int.ofNat 278354761412193140662900969116), (Int.ofNat 72381419046176471987992026402), (Int.negOfNat 8298200516390024408456074235), (Int.negOfNat 1876991465625196977641849316), (Int.ofNat 123429358785123989228051396), (Int.ofNat 27041968678264281023711560), (Int.negOfNat 1052013591387409302479996), (Int.negOfNat 243059086499586824257523), (Int.ofNat 5539010039632898671172), (Int.ofNat 1474106245430654361076), (Int.negOfNat 19389180928483280245), (Int.negOfNat 6649561929837748225), (Int.ofNat 203298183983899884), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(114747995530012337261272554636167/703687441776640000000000000000000), (769810910807101356440577277491731/11258999068426240000000000000000000), (4132767549524421634461185646329/11258999068426240000000000000000000), (-638554469332044868398567448423/5629499534213120000000000000000000), (69588690353048285165725242279/2814749767106560000000000000000000), (36190709523088235993996013201/5629499534213120000000000000000000), (-1659640103278004881691214847/2251799813685248000000000000000000), (-469247866406299244410462329/2814749767106560000000000000000000), (30857339696280997307012849/2814749767106560000000000000000000), (676049216956607025592789/281474976710656000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial133.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial133.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial133.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 3387946393248637047142650855382500), (Int.ofNat 783461176157006630333378627638225), (Int.ofNat 6015663975785055549729881508431), (Int.ofNat 1807326177632444402363803776787), (Int.ofNat 202792835041569106899161372045), (Int.negOfNat 89712188277794299352878952578), (Int.negOfNat 9086468332310425766399730852), (Int.ofNat 1982821828696936083958138081), (Int.ofNat 196091891683255261804113262), (Int.negOfNat 23920669955575320867927263), (Int.negOfNat 2408439618561083122997147), (Int.ofNat 176632599336140318583947), (Int.ofNat 18689712286071117925674), (Int.negOfNat 865243767499581598200), (Int.negOfNat 98468615334398590152), (Int.ofNat 2529866795188049710), (Int.ofNat 243430499927600766), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(1355178557299454818857060342153/4503599627370496000000000000000), (31338447046280265213335145105529/450359962737049600000000000000000), (6015663975785055549729881508431/11258999068426240000000000000000000), (1807326177632444402363803776787/11258999068426240000000000000000000), (40558567008313821379832274409/2251799813685248000000000000000000), (-44856094138897149676439476289/5629499534213120000000000000000000), (-2271617083077606441599932713/2814749767106560000000000000000000), (1982821828696936083958138081/11258999068426240000000000000000000), (98045945841627630902056631/5629499534213120000000000000000000), (-23920669955575320867927263/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial133.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial133.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial133.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 4993472089059623719574269016695729), (Int.ofNat 827803590239148664783937873188963), (Int.ofNat 13920868340993862046070703071502), (Int.negOfNat 307221306850486618741996995299), (Int.negOfNat 584099082678222560986205699475), (Int.negOfNat 5245698839712706911100611452), (Int.ofNat 19929556381235851943057946965), (Int.ofNat 638511311750293991024420211), (Int.negOfNat 337834881117241955437842060), (Int.negOfNat 15114490825122190087300345), (Int.ofNat 3302279973963693542160377), (Int.ofNat 175754909173958373790935), (Int.negOfNat 20547742826069582075761), (Int.negOfNat 1231242440557505553751), (Int.ofNat 87258707024398989436), (Int.ofNat 5895934691469597169), (Int.negOfNat 457668424440787584), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(4993472089059623719574269016695729/11258999068426240000000000000000000), (827803590239148664783937873188963/11258999068426240000000000000000000), (6960434170496931023035351535751/5629499534213120000000000000000000), (-307221306850486618741996995299/11258999068426240000000000000000000), (-23363963307128902439448227979/450359962737049600000000000000000), (-1311424709928176727775152863/2814749767106560000000000000000000), (3985911276247170388611589393/2251799813685248000000000000000000), (638511311750293991024420211/11258999068426240000000000000000000), (-16891744055862097771892103/562949953421312000000000000000000), (-3022898165024438017460069/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial133.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial133.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial133.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 6694058170307417188038285289474171), (Int.ofNat 864439670719310913245969221398597), (Int.ofNat 2218075293215512679258462084120), (Int.negOfNat 2274655559894206405049567869914), (Int.ofNat 347539568509634213316697808322), (Int.ofNat 135165584944871525736282422116), (Int.negOfNat 6837624050343477289509377424), (Int.negOfNat 3454988952371346970612333743), (Int.ofNat 23591087205590708078630571), (Int.ofNat 46321534632729944704960499), (Int.ofNat 709181639746022335952003), (Int.negOfNat 369880648861562895073249), (Int.negOfNat 10353374159932249762288), (Int.ofNat 1932400747781324544258), (Int.ofNat 70432743850101332861), (Int.negOfNat 6794950370911198495), (Int.negOfNat 223225714883652657), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(6694058170307417188038285289474171/11258999068426240000000000000000000), (864439670719310913245969221398597/11258999068426240000000000000000000), (55451882330387816981461552103/281474976710656000000000000000000), (-1137327779947103202524783934957/5629499534213120000000000000000000), (173769784254817106658348904161/5629499534213120000000000000000000), (33791396236217881434070605529/2814749767106560000000000000000000), (-427351503146467330594336089/703687441776640000000000000000000), (-3454988952371346970612333743/11258999068426240000000000000000000), (23591087205590708078630571/11258999068426240000000000000000000), (46321534632729944704960499/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial133.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial133.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial133.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 8422648352685451647901178594534660), (Int.ofNat 865220160695485334819585823619143), (Int.ofNat 4014663381490616370184071167319), (Int.ofNat 3169477508551606604415377448602), (Int.ofNat 528084857480806172575078658396), (Int.negOfNat 138734756735472268451144573113), (Int.negOfNat 24676723647287844035335272768), (Int.ofNat 2288165015203987958064521443), (Int.ofNat 501247036478578891916819561), (Int.negOfNat 15085451010176224542504033), (Int.negOfNat 5402997170707845557684348), (Int.ofNat 8542720192681196901128), (Int.ofNat 35249405840725574691567), (Int.ofNat 457038717028415468423), (Int.negOfNat 155115672764308046469), (Int.negOfNat 3459975706751493519), (Int.ofNat 712038664897675284), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(421132417634272582395058929726733/562949953421312000000000000000000), (865220160695485334819585823619143/11258999068426240000000000000000000), (4014663381490616370184071167319/11258999068426240000000000000000000), (1584738754275803302207688724301/5629499534213120000000000000000000), (132021214370201543143769664599/2814749767106560000000000000000000), (-138734756735472268451144573113/11258999068426240000000000000000000), (-385573806988872563052113637/175921860444160000000000000000000), (2288165015203987958064521443/11258999068426240000000000000000000), (501247036478578891916819561/11258999068426240000000000000000000), (-15085451010176224542504033/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial133.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial133.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial133.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 10197341793814967000143595316344807), (Int.ofNat 921851471505271075859771141528380), (Int.ofNat 20991132415523870850361788236187), (Int.negOfNat 83646074240229746083156840548), (Int.negOfNat 1266393301751459141000432468922), (Int.negOfNat 88260730246999248008120461574), (Int.ofNat 37393544531507251245856787120), (Int.ofNat 3867065447810084613458662650), (Int.negOfNat 464375225981085290321575081), (Int.negOfNat 64230880560543400121680982), (Int.ofNat 2602973295756312215726541), (Int.ofNat 546820934827153629113553), (Int.negOfNat 5987390053132315380324), (Int.negOfNat 2921373575230852062969), (Int.negOfNat 10451504083393328046), (Int.ofNat 11243956263795447820), (Int.ofNat 118230849687408648), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(10197341793814967000143595316344807/11258999068426240000000000000000000), (46092573575263553792988557076419/562949953421312000000000000000000), (20991132415523870850361788236187/11258999068426240000000000000000000), (-20911518560057436520789210137/2814749767106560000000000000000000), (-633196650875729570500216234461/5629499534213120000000000000000000), (-44130365123499624004060230787/5629499534213120000000000000000000), (467419306643840640573209839/140737488355328000000000000000000), (77341308956201692269173253/225179981368524800000000000000000), (-464375225981085290321575081/11258999068426240000000000000000000), (-32115440280271700060840491/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial133.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial133.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial133.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 12103993603715938442453070053271440), (Int.ofNat 965534487262588942199175325042292), (Int.negOfNat 6475540468131401055705063586349), (Int.negOfNat 6712601597857178672218277735382), (Int.ofNat 454584621295685638207108267400), (Int.ofNat 383378079296939215323086702169), (Int.ofNat 12213873782843667310917878038), (Int.negOfNat 7885169081390285391951666552), (Int.negOfNat 590889714831204232123164349), (Int.ofNat 67003331698548640237882888), (Int.ofNat 7242055961557013621811177), (Int.negOfNat 306210992844384720711493), (Int.negOfNat 48308609908359368092088), (Int.ofNat 778795723513763040977), (Int.ofNat 212667235129883592974), (Int.negOfNat 191711957662376864), (Int.negOfNat 868148968506301678), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(151299920046449230530663375665893/140737488355328000000000000000000), (241383621815647235549793831260573/2814749767106560000000000000000000), (-6475540468131401055705063586349/11258999068426240000000000000000000), (-3356300798928589336109138867691/5629499534213120000000000000000000), (2272923106478428191035541337/56294995342131200000000000000000), (383378079296939215323086702169/11258999068426240000000000000000000), (6106936891421833655458939019/5629499534213120000000000000000000), (-985646135173785673993958319/1407374883553280000000000000000000), (-590889714831204232123164349/11258999068426240000000000000000000), (8375416462318580029735361/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial133.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial133.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial133.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 13974663080967643081681329896915352), (Int.ofNat 902692381443212142694089348019962), (Int.negOfNat 8216756927792451232634764123856), (Int.ofNat 9192304304673246312742557092681), (Int.ofNat 2500485786151125490213309511237), (Int.negOfNat 217133535874429178785396593189), (Int.negOfNat 102054389184877563377683473090), (Int.negOfNat 3405371259274970411314652341), (Int.ofNat 1202296310346275088886026933), (Int.ofNat 80854674688268571492588107), (Int.negOfNat 7449182097955867746986692), (Int.negOfNat 706587767628736409389268), (Int.ofNat 28677681363848074188823), (Int.ofNat 3746343460494496209129), (Int.negOfNat 71368318848506943249), (Int.negOfNat 14567722341284423097), (Int.ofNat 64819167313148558), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(1746832885120955385210166237114419/1407374883553280000000000000000000), (451346190721606071347044674009981/5629499534213120000000000000000000), (-513547307987028202039672757741/703687441776640000000000000000000), (9192304304673246312742557092681/11258999068426240000000000000000000), (2500485786151125490213309511237/11258999068426240000000000000000000), (-217133535874429178785396593189/11258999068426240000000000000000000), (-10205438918487756337768347309/1125899906842624000000000000000000), (-3405371259274970411314652341/11258999068426240000000000000000000), (1202296310346275088886026933/11258999068426240000000000000000000), (80854674688268571492588107/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial133.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial133.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial133.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 15847151638498282354145491279959582), (Int.ofNat 1023030053035235090709881509768984), (Int.ofNat 65220461250983329464985012988647), (Int.ofNat 4724311386912689894600168866866), (Int.negOfNat 5200108350428744513669302225860), (Int.negOfNat 1103141765579955108702831524451), (Int.ofNat 6215787001674705380891325678), (Int.ofNat 17677361431578347710027537485), (Int.ofNat 741009615332781289516661219), (Int.negOfNat 138944653368681587765706005), (Int.negOfNat 9197855833441465810980853), (Int.ofNat 680665878006969303094169), (Int.ofNat 59486399659626181625176), (Int.negOfNat 2294243417544507691446), (Int.negOfNat 256841980944083084879), (Int.ofNat 5643110607380745879), (Int.ofNat 932734263614649469), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(7923575819249141177072745639979791/5629499534213120000000000000000000), (127878756629404386338735188721123/1407374883553280000000000000000000), (65220461250983329464985012988647/11258999068426240000000000000000000), (2362155693456344947300084433433/5629499534213120000000000000000000), (-260005417521437225683465111293/562949953421312000000000000000000), (-1103141765579955108702831524451/11258999068426240000000000000000000), (3107893500837352690445662839/5629499534213120000000000000000000), (3535472286315669542005507497/2251799813685248000000000000000000), (741009615332781289516661219/11258999068426240000000000000000000), (-27788930673736317553141201/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial133.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial133.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial133.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 18076157078290318341921143149232229), (Int.ofNat 1095462266768648373737890035316940), (Int.negOfNat 105512231207830820032679410299409), (Int.negOfNat 69634131283224437276202379215844), (Int.negOfNat 10727622893304233088721156752515), (Int.ofNat 459195949275915444675893091401), (Int.ofNat 225316400333054721072564073964), (Int.ofNat 5445987425410169162644761807), (Int.negOfNat 2182754567084659838616391932), (Int.negOfNat 108282320765334653812926109), (Int.ofNat 13027832840426472471933981), (Int.ofNat 865198276632334693065485), (Int.negOfNat 53719042167106339113997), (Int.negOfNat 4355186173966751858621), (Int.ofNat 163058182531373088116), (Int.ofNat 16330188491204256447), (Int.negOfNat 319189407770036258), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(18076157078290318341921143149232229/11258999068426240000000000000000000), (54773113338432418686894501765847/562949953421312000000000000000000), (-105512231207830820032679410299409/11258999068426240000000000000000000), (-17408532820806109319050594803961/2814749767106560000000000000000000), (-2145524578660846617744231350503/2251799813685248000000000000000000), (459195949275915444675893091401/11258999068426240000000000000000000), (56329100083263680268141018491/2814749767106560000000000000000000), (5445987425410169162644761807/11258999068426240000000000000000000), (-545688641771164959654097983/2814749767106560000000000000000000), (-108282320765334653812926109/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial133.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial133.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial133.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 19145529910968940011689426576655212), (Int.negOfNat 425453643783357514469645388794988), (Int.negOfNat 690548922392504911354533544397538), (Int.negOfNat 102251046029038583072266678496924), (Int.ofNat 6230363083889599802223970236244), (Int.ofNat 2548253044677075172182072656616), (Int.ofNat 36918522228832041155741261529), (Int.negOfNat 29741139247587565840685619363), (Int.negOfNat 1207079347020675305297942906), (Int.ofNat 212921710428299138801792849), (Int.ofNat 11745812636519677064314909), (Int.negOfNat 1047795040475313359721207), (Int.negOfNat 68660736163001748904950), (Int.ofNat 3795694762367652917708), (Int.ofNat 281041424067282516008), (Int.negOfNat 10196195367496370694), (Int.negOfNat 912529478570701360), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(4786382477742235002922356644163803/2814749767106560000000000000000000), (-106363410945839378617411347198747/2814749767106560000000000000000000), (-345274461196252455677266772198769/5629499534213120000000000000000000), (-25562761507259645768066669624231/2814749767106560000000000000000000), (1557590770972399950555992559061/2814749767106560000000000000000000), (318531630584634396522759082077/1407374883553280000000000000000000), (36918522228832041155741261529/11258999068426240000000000000000000), (-29741139247587565840685619363/11258999068426240000000000000000000), (-603539673510337652648971453/5629499534213120000000000000000000), (212921710428299138801792849/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial133.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial133.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial133.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 14894014031464760273375594639499934), (Int.negOfNat 4018364295089002051903686299897517), (Int.negOfNat 962871918318742372174426126857697), (Int.ofNat 37885207435794839914401672185373), (Int.ofNat 25213603440350397763215510382551), (Int.ofNat 439773589842147212236896919583), (Int.negOfNat 350635801056529709207275530037), (Int.negOfNat 13871902029149907380142703342), (Int.ofNat 3011967834186326331823953948), (Int.ofNat 153425039906572936907880034), (Int.negOfNat 17632403573934006839791420), (Int.negOfNat 1019953258352770010270817), (Int.ofNat 75252945362990729589668), (Int.ofNat 4695843165124492404696), (Int.negOfNat 245382081778273823485), (Int.negOfNat 16383383181382206391), (Int.ofNat 573559648226923958), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(7447007015732380136687797319749967/5629499534213120000000000000000000), (-4018364295089002051903686299897517/11258999068426240000000000000000000), (-962871918318742372174426126857697/11258999068426240000000000000000000), (37885207435794839914401672185373/11258999068426240000000000000000000), (25213603440350397763215510382551/11258999068426240000000000000000000), (439773589842147212236896919583/11258999068426240000000000000000000), (-350635801056529709207275530037/11258999068426240000000000000000000), (-6935951014574953690071351671/5629499534213120000000000000000000), (752991958546581582955988487/2814749767106560000000000000000000), (76712519953286468453940017/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial133.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial133.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial133.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 3702983357832482002837589514502749), (Int.negOfNat 6643410920347823797838061634894682), (Int.negOfNat 182848500488678249038015177289199), (Int.ofNat 199232970166296788003518114317913), (Int.ofNat 8411974088924637272530870980546), (Int.negOfNat 3437893491110740468972983805759), (Int.negOfNat 173466496159614606577254570226), (Int.ofNat 36393346552410178445255318880), (Int.ofNat 1984946375402217572422757653), (Int.negOfNat 257179603490076092458242252), (Int.negOfNat 14527160836212225340642756), (Int.ofNat 1300280950190865039239945), (Int.ofNat 74267598393574686314597), (Int.negOfNat 4954626944520711878507), (Int.negOfNat 281912604842919030622), (Int.ofNat 14445001400347749649), (Int.ofNat 892324693526753251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(3702983357832482002837589514502749/11258999068426240000000000000000000), (-3321705460173911898919030817447341/5629499534213120000000000000000000), (-182848500488678249038015177289199/11258999068426240000000000000000000), (199232970166296788003518114317913/11258999068426240000000000000000000), (4205987044462318636265435490273/5629499534213120000000000000000000), (-3437893491110740468972983805759/11258999068426240000000000000000000), (-86733248079807303288627285113/5629499534213120000000000000000000), (227458415952563615282845743/70368744177664000000000000000000), (1984946375402217572422757653/11258999068426240000000000000000000), (-64294900872519023114560563/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial133.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial133.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial133.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 8702868720160602329081064581631456), (Int.negOfNat 5005477093046195600296739379393663), (Int.ofNat 924474929547439602309855078979539), (Int.ofNat 123651606439428501337845755957094), (Int.negOfNat 25131587472556782872289139023133), (Int.negOfNat 2164709037455377362097637724511), (Int.ofNat 359072495205830068526088548757), (Int.ofNat 25280797703128433450853019202), (Int.negOfNat 3198398117912650782960092164), (Int.negOfNat 199988094940038384481939861), (Int.ofNat 19577319944209933524515415), (Int.ofNat 1120851415386200262769108), (Int.negOfNat 87956868027608318673677), (Int.negOfNat 4660941844163260947985), (Int.ofNat 304444698603811454605), (Int.ofNat 14891511789058459053), (Int.negOfNat 821194960335828955), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-271964647505018822783783268175983/351843720888320000000000000000000), (-5005477093046195600296739379393663/11258999068426240000000000000000000), (924474929547439602309855078979539/11258999068426240000000000000000000), (61825803219714250668922877978547/5629499534213120000000000000000000), (-25131587472556782872289139023133/11258999068426240000000000000000000), (-2164709037455377362097637724511/11258999068426240000000000000000000), (359072495205830068526088548757/11258999068426240000000000000000000), (12640398851564216725426509601/5629499534213120000000000000000000), (-799599529478162695740023041/2814749767106560000000000000000000), (-199988094940038384481939861/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial133.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial133.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial133.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial133.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial133.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial133.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial133.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial133.reflect := by
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

end Bin133
end
end ErdosOverlap.OuterNumerics
