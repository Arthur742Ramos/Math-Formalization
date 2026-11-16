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

/-! # Exact integer weighted outer models for source bin 129

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin129

def weightDenominator : ℤ := (Int.ofNat 10000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 5009615861926541000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2999415523775111000)⟩, ⟨(12362311557789/1000000000000), (Int.negOfNat 2533124955430468600)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 1571432064032144700)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 713296833364189700)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 493536143544390860)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 592112120846489950)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 557430720587515800)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 82120678752352630)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial129.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial129.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 7880354122318619000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 755925370754764300)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 1552578240563847000)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 197664972093704140)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 233637558304876960)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 289921204853263140)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 42941149357934695)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 117656474248316910)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 11066668417528183)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial129.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial129.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 7880354122318619000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 755925370754764300)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 1552578240563847000)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 197664972093704140)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 233637558304876960)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 289921204853263140)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 42941149357934695)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 117656474248316910)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 11066668417528183)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial129.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial129.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial129.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 13816578429409997452678300011551396), (Int.ofNat 3820662787835752305279246034494539), (Int.ofNat 1157405183033161886894438352135700), (Int.negOfNat 129231091964749300159137677161483), (Int.negOfNat 31378300644417651458505479592774), (Int.ofNat 2710115458625896153671213096398), (Int.ofNat 473473969822517363386823793538), (Int.negOfNat 33525041970305244898175020353), (Int.negOfNat 4440763940988344593675720343), (Int.ofNat 265084242915733624352432574), (Int.ofNat 28052752301596354007576898), (Int.negOfNat 1447484799435591728575248), (Int.negOfNat 127194187767060048905179), (Int.ofNat 5797852557666397264149), (Int.ofNat 435652965348483638650), (Int.negOfNat 17905910187940832335), (Int.negOfNat 1152090599102764958), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-3454144607352499363169575002887849/2814749767106560000000000000000000), (3820662787835752305279246034494539/11258999068426240000000000000000000), (11574051830331618868944383521357/112589990684262400000000000000000), (-129231091964749300159137677161483/11258999068426240000000000000000000), (-15689150322208825729252739796387/5629499534213120000000000000000000), (1355057729312948076835606548199/5629499534213120000000000000000000), (236736984911258681693411896769/5629499534213120000000000000000000), (-33525041970305244898175020353/11258999068426240000000000000000000), (-4440763940988344593675720343/11258999068426240000000000000000000), (132542121457866812176216287/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial129.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial129.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial129.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial129 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.negOfNat 2969774662139908671681976600140863), (Int.ofNat 6184289781106896417931853221485253), (Int.negOfNat 69607882477972217710691657176498), (Int.negOfNat 221046417346542171297585543651217), (Int.ofNat 11141724707758282352361709682165), (Int.ofNat 4293463245547297851538863188500), (Int.negOfNat 248215629898437588938534543427), (Int.negOfNat 49548119703497020211365306234), (Int.ofNat 2766697994668615378293948949), (Int.ofNat 370933272320566405486411239), (Int.negOfNat 19318174524251313925661893), (Int.negOfNat 1934264164371334155230915), (Int.ofNat 93954129280234124126545), (Int.ofNat 7429251979620553423553), (Int.negOfNat 340183932428704109042), (Int.negOfNat 21776041604680949852), (Int.ofNat 970352323935554568), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-2969774662139908671681976600140863/11258999068426240000000000000000000), (6184289781106896417931853221485253/11258999068426240000000000000000000), (-34803941238986108855345828588249/5629499534213120000000000000000000), (-221046417346542171297585543651217/11258999068426240000000000000000000), (2228344941551656470472341936433/2251799813685248000000000000000000), (8586926491094595703077726377/22517998136852480000000000000000), (-248215629898437588938534543427/11258999068426240000000000000000000), (-24774059851748510105682653117/5629499534213120000000000000000000), (2766697994668615378293948949/11258999068426240000000000000000000), (370933272320566405486411239/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial129.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial129.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial129.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial129 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 7646307379745040658488216624190978), (Int.ofNat 3887028227918334097476368619571550), (Int.negOfNat 871478459439222914526427444462838), (Int.negOfNat 21049438783227313478189715671246), (Int.ofNat 29577134769449727486762367802635), (Int.negOfNat 1061292032727406165807887408392), (Int.negOfNat 469377848125272848824552389216), (Int.ofNat 22393193203982837976906137233), (Int.ofNat 4383377966864309416619104392), (Int.negOfNat 217757042458360911270329382), (Int.negOfNat 27030479346138624556902118), (Int.ofNat 1333968697911268246177922), (Int.ofNat 118538970747535545853765), (Int.negOfNat 5774909405801921195445), (Int.negOfNat 389324912409542529415), (Int.ofNat 18747292369360639048), (Int.ofNat 916795231263235251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(3823153689872520329244108312095489/5629499534213120000000000000000000), (77740564558366681949527372391431/225179981368524800000000000000000), (-435739229719611457263213722231419/5629499534213120000000000000000000), (-10524719391613656739094857835623/5629499534213120000000000000000000), (5915426953889945497352473560527/2251799813685248000000000000000000), (-132661504090925770725985926049/1407374883553280000000000000000000), (-14668057753914776525767262163/351843720888320000000000000000000), (22393193203982837976906137233/11258999068426240000000000000000000), (547922245858038677077388049/1407374883553280000000000000000000), (-108878521229180455635164691/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial129.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial129.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial129.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial129 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 12179139583698854920596755571412131), (Int.ofNat 933863741147083328835991856668039), (Int.negOfNat 463844954299914797983430275051876), (Int.ofNat 116892610030738110102458557963493), (Int.ofNat 808648274838929243897846552311), (Int.negOfNat 3456793749575353402408016321735), (Int.ofNat 123128214716698330743248125372), (Int.ofNat 44498849680204960854843242587), (Int.negOfNat 1996713959707748645262380137), (Int.negOfNat 340153668267682969489028671), (Int.ofNat 16338065551696936544952771), (Int.ofNat 1748532511087309816956887), (Int.negOfNat 87099280776096121349758), (Int.negOfNat 6503168090824105698109), (Int.ofNat 334684705040118542543), (Int.ofNat 17793066543968306402), (Int.negOfNat 1003552329188139117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(12179139583698854920596755571412131/11258999068426240000000000000000000), (933863741147083328835991856668039/11258999068426240000000000000000000), (-115961238574978699495857568762969/2814749767106560000000000000000000), (116892610030738110102458557963493/11258999068426240000000000000000000), (808648274838929243897846552311/11258999068426240000000000000000000), (-691358749915070680481603264347/2251799813685248000000000000000000), (30782053679174582685812031343/2814749767106560000000000000000000), (44498849680204960854843242587/11258999068426240000000000000000000), (-1996713959707748645262380137/11258999068426240000000000000000000), (-340153668267682969489028671/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial129.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial129.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial129.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial129 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 13041859749670396559906533818058831), (Int.ofNat 271377143855010550763496763367183), (Int.ofNat 34913890115556744277784981769998), (Int.ofNat 24616513622075566775377317764694), (Int.negOfNat 17239326721309371025079965613366), (Int.ofNat 351239594031809206427288292805), (Int.ofNat 368359982446348105263452718481), (Int.negOfNat 14264384190749535413527294593), (Int.negOfNat 3752279376277077881583655836), (Int.ofNat 169324736666283263387377362), (Int.ofNat 23488975264469038002850989), (Int.negOfNat 1153121105081195256946380), (Int.negOfNat 101026846058241842931629), (Int.ofNat 5337686723989229880685), (Int.ofNat 318534185051155455491), (Int.negOfNat 18647714256442986904), (Int.negOfNat 670433195006177361), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(13041859749670396559906533818058831/11258999068426240000000000000000000), (271377143855010550763496763367183/11258999068426240000000000000000000), (17456945057778372138892490884999/5629499534213120000000000000000000), (12308256811037783387688658882347/5629499534213120000000000000000000), (-8619663360654685512539982806683/5629499534213120000000000000000000), (70247918806361841285457658561/2251799813685248000000000000000000), (368359982446348105263452718481/11258999068426240000000000000000000), (-14264384190749535413527294593/11258999068426240000000000000000000), (-938069844069269470395913959/2814749767106560000000000000000000), (84662368333141631693688681/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial129.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial129.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial129.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial129 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 13677508780340346513447959917980487), (Int.ofNat 243859150693886970726951426684885), (Int.negOfNat 129922560928971846434861599233529), (Int.negOfNat 53810302356453062475166602601013), (Int.ofNat 1117211758717795787523673090193), (Int.ofNat 2380790141309132673708204792650), (Int.negOfNat 80543853506178538286295280538), (Int.negOfNat 35324843084270253428749490739), (Int.ofNat 1465526747889327059164476050), (Int.ofNat 282458941098706543083977202), (Int.negOfNat 13246681512939317988045570), (Int.negOfNat 1447682773632893195633059), (Int.ofNat 75598787628170406683199), (Int.ofNat 5202369560904878269102), (Int.negOfNat 304744898064936211474), (Int.negOfNat 14016628878246883982), (Int.ofNat 1036752334440723666), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(13677508780340346513447959917980487/11258999068426240000000000000000000), (48771830138777394145390285336977/2251799813685248000000000000000000), (-129922560928971846434861599233529/11258999068426240000000000000000000), (-53810302356453062475166602601013/11258999068426240000000000000000000), (1117211758717795787523673090193/11258999068426240000000000000000000), (47615802826182653474164095853/225179981368524800000000000000000), (-40271926753089269143147640269/5629499534213120000000000000000000), (-35324843084270253428749490739/11258999068426240000000000000000000), (29310534957786541183289521/225179981368524800000000000000000), (141229470549353271541988601/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial129.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial129.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial129.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial129 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 13299942316542569019749910229532371), (Int.negOfNat 724561231103400330459088289386340), (Int.negOfNat 274836657954182506967035832142061), (Int.ofNat 21579963344816617018972314429987), (Int.ofNat 12753745486186079113337203515744), (Int.negOfNat 467624137177882021270182431240), (Int.negOfNat 281699920895894297791460157084), (Int.ofNat 10773592284030661872347626312), (Int.ofNat 3000774431458393793366903502), (Int.negOfNat 130877962447953760872823355), (Int.negOfNat 18926792897259687782067530), (Int.ofNat 942312748815388014291813), (Int.ofNat 79305691015719542347690), (Int.negOfNat 4564279213192705183043), (Int.negOfNat 234798046067876688939), (Int.ofNat 16291477110796735844), (Int.ofNat 424071158749119471), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(13299942316542569019749910229532371/11258999068426240000000000000000000), (-36228061555170016522954414469317/562949953421312000000000000000000), (-274836657954182506967035832142061/11258999068426240000000000000000000), (21579963344816617018972314429987/11258999068426240000000000000000000), (398554546443314972291787609867/351843720888320000000000000000000), (-11690603429447050531754560781/281474976710656000000000000000000), (-70424980223973574447865039271/2814749767106560000000000000000000), (1346699035503832734043453289/1407374883553280000000000000000000), (1500387215729196896683451751/5629499534213120000000000000000000), (-26175592489590752174564671/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial129.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial129.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial129.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial129 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 11097243131232645077179198187657696), (Int.negOfNat 1240811551362287255236664746183348), (Int.ofNat 67542314179831005832152518200051), (Int.ofNat 70296513912368207150694162809954), (Int.negOfNat 3181105868482800683185803573711), (Int.negOfNat 1980960817690098421645275779936), (Int.ofNat 71154473466605082678434791214), (Int.ofNat 28178889980884125941565919581), (Int.negOfNat 1108825118240082968381468325), (Int.negOfNat 224228271832738517383089080), (Int.ofNat 10217308171520692760971589), (Int.ofNat 1122322771744179764283243), (Int.negOfNat 60591541172288305192246), (Int.negOfNat 3814824131843911526118), (Int.ofNat 250827937853084615014), (Int.ofNat 8833821531451642922), (Int.negOfNat 987831660940955585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(346788847851020158661849943364303/351843720888320000000000000000000), (-310202887840571813809166186545837/2814749767106560000000000000000000), (67542314179831005832152518200051/11258999068426240000000000000000000), (35148256956184103575347081404977/5629499534213120000000000000000000), (-3181105868482800683185803573711/11258999068426240000000000000000000), (-61905025552815575676414868123/351843720888320000000000000000000), (35577236733302541339217395607/5629499534213120000000000000000000), (28178889980884125941565919581/11258999068426240000000000000000000), (-44353004729603318735258733/450359962737049600000000000000000), (-5605706795818462934577227/281474976710656000000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial129.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial129.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial129.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial129 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 9341647562561927062953634828950753), (Int.negOfNat 362659345171231670109617230746686), (Int.ofNat 287635724462357410914458773571232), (Int.negOfNat 10221733543254889592012819147213), (Int.negOfNat 12801398049905556976429796572615), (Int.ofNat 399579011668771643233016458453), (Int.ofNat 237501345441367491768429828014), (Int.negOfNat 7950169513791703343874311481), (Int.negOfNat 2408011400598673633637555305), (Int.ofNat 94644207390217230642729870), (Int.ofNat 14685443762422604260128799), (Int.negOfNat 701534445140264282370623), (Int.negOfNat 58253513813553883165306), (Int.ofNat 3507091419407673584698), (Int.ofNat 156317279394889927204), (Int.negOfNat 12910400323302455812), (Int.negOfNat 237696464409357845), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(9341647562561927062953634828950753/11258999068426240000000000000000000), (-181329672585615835054808615373343/5629499534213120000000000000000000), (8988616389448669091076836674101/351843720888320000000000000000000), (-10221733543254889592012819147213/11258999068426240000000000000000000), (-2560279609981111395285959314523/2251799813685248000000000000000000), (399579011668771643233016458453/11258999068426240000000000000000000), (118750672720683745884214914007/5629499534213120000000000000000000), (-7950169513791703343874311481/11258999068426240000000000000000000), (-481602280119734726727511061/2251799813685248000000000000000000), (9464420739021723064272987/1125899906842624000000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial129.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial129.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial129.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial129 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 9506689926033569776594585772317759), (Int.ofNat 327401229683340091105068671250726), (Int.negOfNat 1037044580838036442955750667129), (Int.negOfNat 66717493006980470271670238964960), (Int.ofNat 1064823329065804106922342463173), (Int.ofNat 1786845015767987613666583831750), (Int.negOfNat 43513736326825365688979909894), (Int.negOfNat 23499841135047079212045375102), (Int.ofNat 715203947493601307166166972), (Int.ofNat 177397896114409073936358365), (Int.negOfNat 6868416754811977656035710), (Int.negOfNat 837871016361716405810363), (Int.ofNat 42393509533203237912490), (Int.ofNat 2589380231262564053943), (Int.negOfNat 181736041378697449839), (Int.negOfNat 5051507755850672444), (Int.ofNat 845723640271306691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(9506689926033569776594585772317759/11258999068426240000000000000000000), (163700614841670045552534335625363/5629499534213120000000000000000000), (-1037044580838036442955750667129/11258999068426240000000000000000000), (-416984331293627939197938993531/70368744177664000000000000000000), (1064823329065804106922342463173/11258999068426240000000000000000000), (7147380063071950454666335327/45035996273704960000000000000000), (-21756868163412682844489954947/5629499534213120000000000000000000), (-11749920567523539606022687551/5629499534213120000000000000000000), (178800986873400326791541743/2814749767106560000000000000000000), (35479579222881814787271673/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial129.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial129.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial129.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial129 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 9692292980455797484304917649071672), (Int.negOfNat 318119835723458916499071559546660), (Int.negOfNat 257074247468690414236298992547606), (Int.negOfNat 4747377728930567353150037078062), (Int.ofNat 11137210658495433452239214327560), (Int.negOfNat 106468463921057994233978815445), (Int.negOfNat 205734878834407851196992095628), (Int.ofNat 3744847573473839404714741849), (Int.ofNat 1971156800881493731479613790), (Int.negOfNat 52524900602661745323011182), (Int.negOfNat 11298627433101541349463790), (Int.ofNat 424980347847742389980969), (Int.ofNat 41081657172998022126779), (Int.negOfNat 2234369532986726102092), (Int.negOfNat 92423655267637995084), (Int.ofNat 7774696575253003342), (Int.ofNat 122375780404420666), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(1211536622556974685538114706133959/1407374883553280000000000000000000), (-15905991786172945824953577977333/562949953421312000000000000000000), (-128537123734345207118149496273803/5629499534213120000000000000000000), (-2373688864465283676575018539031/5629499534213120000000000000000000), (278430266462385836305980358189/281474976710656000000000000000000), (-21293692784211598846795763089/2251799813685248000000000000000000), (-51433719708601962799248023907/2814749767106560000000000000000000), (3744847573473839404714741849/11258999068426240000000000000000000), (197115680088149373147961379/1125899906842624000000000000000000), (-26262450301330872661505591/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial129.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial129.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial129.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial129 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 8152345157895955100387619234325781), (Int.negOfNat 1091490232268467229582474108293907), (Int.negOfNat 70468291201973348233786341294710), (Int.ofNat 52369365243384805602755202358040), (Int.ofNat 643318841560880856415966160912), (Int.negOfNat 1558719652542978440860026960548), (Int.ofNat 2373572713126207954717570901), (Int.ofNat 19885517869520247996837054983), (Int.negOfNat 224789073934926428902236466), (Int.negOfNat 141572249568449623588403422), (Int.ofNat 3084620774179259933411419), (Int.ofNat 620576289850344460731420), (Int.negOfNat 21957152412055797084909), (Int.negOfNat 1679479214977753984355), (Int.ofNat 100103528199412798401), (Int.ofNat 2180715889298093034), (Int.negOfNat 599361604014248801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(8152345157895955100387619234325781/11258999068426240000000000000000000), (-1091490232268467229582474108293907/11258999068426240000000000000000000), (-7046829120197334823378634129471/1125899906842624000000000000000000), (1309234131084620140068880058951/281474976710656000000000000000000), (40207427597555053525997885057/703687441776640000000000000000000), (-389679913135744610215006740137/2814749767106560000000000000000000), (2373572713126207954717570901/11258999068426240000000000000000000), (19885517869520247996837054983/11258999068426240000000000000000000), (-112394536967463214451118233/5629499534213120000000000000000000), (-70786124784224811794201711/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial129.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial129.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial129.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial129 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 6069432074637348732750616430921548), (Int.negOfNat 840212145566165079235312152262227), (Int.ofNat 147418815771598483455455741254727), (Int.ofNat 5589582904743623929792303808396), (Int.negOfNat 9991720829678320678841765356931), (Int.negOfNat 205416700903606848638455440335), (Int.ofNat 178410091426361271255339816965), (Int.ofNat 1445529389179811414752427513), (Int.negOfNat 1621602786167105558024834727), (Int.ofNat 5500699606049275739163061), (Int.ofNat 8768691726177622205566121), (Int.negOfNat 129994635627920395976657), (Int.negOfNat 29170286802477621593208), (Int.ofNat 875149918204456722999), (Int.ofNat 53123085556014365793), (Int.negOfNat 3010583650729752242), (Int.negOfNat 89175775151836117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(1517358018659337183187654107730387/2814749767106560000000000000000000), (-840212145566165079235312152262227/11258999068426240000000000000000000), (147418815771598483455455741254727/11258999068426240000000000000000000), (1397395726185905982448075952099/2814749767106560000000000000000000), (-9991720829678320678841765356931/11258999068426240000000000000000000), (-41083340180721369727691088067/2251799813685248000000000000000000), (35682018285272254251067963393/2251799813685248000000000000000000), (1445529389179811414752427513/11258999068426240000000000000000000), (-1621602786167105558024834727/11258999068426240000000000000000000), (5500699606049275739163061/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial129.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial129.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial129.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial129 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 4868158403118307133470347954416686), (Int.negOfNat 486333036908658834409832329005611), (Int.negOfNat 34273530612903405328165373569212), (Int.negOfNat 55955882013698351147923870505285), (Int.negOfNat 2621522393247509994516384397094), (Int.ofNat 1405781470771003669704375792425), (Int.ofNat 46764119136787506125414299124), (Int.negOfNat 16602193377641582084246755743), (Int.negOfNat 303495891174572116159249338), (Int.ofNat 113245551986457759254794812), (Int.ofNat 737251591712127605817952), (Int.negOfNat 473638849968012540477292), (Int.ofNat 1582666913883773664145), (Int.ofNat 1158200233707687534605), (Int.negOfNat 18365982768306339245), (Int.negOfNat 338092140111019908), (Int.ofNat 352999567757190911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(2434079201559153566735173977208343/5629499534213120000000000000000000), (-486333036908658834409832329005611/11258999068426240000000000000000000), (-8568382653225851332041343392303/2814749767106560000000000000000000), (-11191176402739670229584774101057/2251799813685248000000000000000000), (-1310761196623754997258192198547/5629499534213120000000000000000000), (56231258830840146788175031697/450359962737049600000000000000000), (11691029784196876531353574781/2814749767106560000000000000000000), (-16602193377641582084246755743/11258999068426240000000000000000000), (-151747945587286058079624669/5629499534213120000000000000000000), (28311387996614439813698703/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial129.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial129.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial129.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial129 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 3314639709753645795670995674566939), (Int.negOfNat 1264834338201003188720263124943073), (Int.negOfNat 320422716663908570025567988441550), (Int.negOfNat 22455007392505668792935840716746), (Int.ofNat 9700722640116201915382984067177), (Int.ofNat 657165926008595894654865129785), (Int.negOfNat 147749657943497095575514112197), (Int.negOfNat 6785457246404771841770143126), (Int.ofNat 1298673886553597027172183759), (Int.ofNat 38466368550595341335522281), (Int.negOfNat 6964865384434857017724783), (Int.negOfNat 140579249953165251661965), (Int.ofNat 22858134354393341349035), (Int.ofNat 387655606310425778297), (Int.negOfNat 38986380512798381462), (Int.negOfNat 1218509163792867308), (Int.ofNat 55975769899251568), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(3314639709753645795670995674566939/11258999068426240000000000000000000), (-1264834338201003188720263124943073/11258999068426240000000000000000000), (-6408454333278171400511359768831/225179981368524800000000000000000), (-11227503696252834396467920358373/5629499534213120000000000000000000), (9700722640116201915382984067177/11258999068426240000000000000000000), (131433185201719178930973025957/2251799813685248000000000000000000), (-147749657943497095575514112197/11258999068426240000000000000000000), (-3392728623202385920885071563/5629499534213120000000000000000000), (1298673886553597027172183759/11258999068426240000000000000000000), (38466368550595341335522281/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial129.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial129.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial129.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial129 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.negOfNat 510098705692853519574612150292638), (Int.negOfNat 2483014911417500707010131925852825), (Int.negOfNat 207360014433427313483622626490556), (Int.ofNat 56421367671127138752836157517345), (Int.ofNat 7020536025324062464393898333797), (Int.negOfNat 1084373110798742567521267954026), (Int.negOfNat 95520743302931501842222498552), (Int.ofNat 12707251674158868433877758343), (Int.ofNat 740583541627116423247084387), (Int.negOfNat 89890282377368781470445994), (Int.negOfNat 3851488648462656606007272), (Int.ofNat 394796692567456873082608), (Int.ofNat 15419744445605824397091), (Int.negOfNat 1042564794829911249259), (Int.negOfNat 53288511821323545740), (Int.ofNat 839335246680593125), (Int.negOfNat 95570863082604838), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-255049352846426759787306075146319/5629499534213120000000000000000000), (-99320596456700028280405277034113/450359962737049600000000000000000), (-51840003608356828370905656622639/2814749767106560000000000000000000), (11284273534225427750567231503469/2251799813685248000000000000000000), (7020536025324062464393898333797/11258999068426240000000000000000000), (-542186555399371283760633977013/5629499534213120000000000000000000), (-11940092912866437730277812319/1407374883553280000000000000000000), (12707251674158868433877758343/11258999068426240000000000000000000), (740583541627116423247084387/11258999068426240000000000000000000), (-44945141188684390735222997/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial129.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial129.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial129.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial129 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 5780915323409000993314614105944976), (Int.negOfNat 2509602091676330030069899576257248), (Int.ofNat 199406018822527703123548159325567), (Int.ofNat 61846261266250095315728872879826), (Int.negOfNat 5562958657026331184412745795132), (Int.negOfNat 1030864998666118582446869566888), (Int.ofNat 98461919888704290818139874592), (Int.ofNat 10255343084445906728921691363), (Int.negOfNat 979091967698640017346282627), (Int.negOfNat 67639486257014146703000364), (Int.ofNat 5865537901691762584501132), (Int.ofNat 333309529918383682362908), (Int.negOfNat 22081652289903435884331), (Int.negOfNat 1343882739534750199119), (Int.ofNat 49680935873534477870), (Int.ofNat 5017358546779447755), (Int.negOfNat 198083790568900462), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-361307207713062562082163381621561/703687441776640000000000000000000), (-78425065364885313439684361758039/351843720888320000000000000000000), (199406018822527703123548159325567/11258999068426240000000000000000000), (30923130633125047657864436439913/5629499534213120000000000000000000), (-1390739664256582796103186448783/2814749767106560000000000000000000), (-128858124833264822805858695861/1407374883553280000000000000000000), (3076934996522009088066871081/351843720888320000000000000000000), (10255343084445906728921691363/11258999068426240000000000000000000), (-979091967698640017346282627/11258999068426240000000000000000000), (-16909871564253536675750091/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial129.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial129.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial129.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial129 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 9622384803540005316554136666152003), (Int.negOfNat 1207932928758054400603078893839288), (Int.ofNat 383034887057044835236091359713346), (Int.negOfNat 4411932730283613688211650783627), (Int.negOfNat 8372017208064813256082430065486), (Int.ofNat 491671201083918653050466567150), (Int.ofNat 110009379877184371806355773777), (Int.negOfNat 8437455895682594670370114316), (Int.negOfNat 917907514711812911154527519), (Int.ofNat 73315067373240059562518461), (Int.ofNat 5486869688911640543115423), (Int.negOfNat 385544753787861556461145), (Int.negOfNat 25841359338631875206135), (Int.ofNat 1311952161378212870667), (Int.ofNat 100691394047460216032), (Int.negOfNat 2195197113451656668), (Int.negOfNat 90803831257156788), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-9622384803540005316554136666152003/11258999068426240000000000000000000), (-150991616094756800075384861729911/1407374883553280000000000000000000), (191517443528522417618045679856673/5629499534213120000000000000000000), (-4411932730283613688211650783627/11258999068426240000000000000000000), (-4186008604032406628041215032743/5629499534213120000000000000000000), (9833424021678373061009331343/225179981368524800000000000000000), (110009379877184371806355773777/11258999068426240000000000000000000), (-2109363973920648667592528579/2814749767106560000000000000000000), (-917907514711812911154527519/11258999068426240000000000000000000), (73315067373240059562518461/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial129.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial129.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial129.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial129 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 10653857477237750138095664350649803), (Int.ofNat 59286568794628799303146819405314), (Int.ofNat 214444649154023340417121984619712), (Int.negOfNat 40029911343643712915576050644453), (Int.ofNat 105075703493358626106985680418), (Int.ofNat 870367821541550591270102426592), (Int.negOfNat 50089899878127571421177852284), (Int.negOfNat 9808271476993564285574428103), (Int.ofNat 745741920396972729919658318), (Int.ofNat 72827683386750493404997502), (Int.negOfNat 5633785515475362167096532), (Int.negOfNat 406164690223747766602552), (Int.ofNat 26574113013946918939945), (Int.ofNat 1817263357051272392045), (Int.negOfNat 85074846208267459575), (Int.negOfNat 6450852849045744418), (Int.ofNat 433379158408430169), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-10653857477237750138095664350649803/11258999068426240000000000000000000), (29643284397314399651573409702657/5629499534213120000000000000000000), (3350697643031614694017531009683/175921860444160000000000000000000), (-40029911343643712915576050644453/11258999068426240000000000000000000), (52537851746679313053492840209/5629499534213120000000000000000000), (27198994423173455977190700831/351843720888320000000000000000000), (-12522474969531892855294463071/2814749767106560000000000000000000), (-9808271476993564285574428103/11258999068426240000000000000000000), (372870960198486364959829159/5629499534213120000000000000000000), (36413841693375246702498751/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial129.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial129.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial129.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial129 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 9972451545549548957974826952994584), (Int.ofNat 496585464441348696548467265138897), (Int.ofNat 29401359454457641300841900523384), (Int.negOfNat 16253957914830668935206401793627), (Int.ofNat 4096970836499767962443916937062), (Int.negOfNat 127945367518794689569267354640), (Int.negOfNat 77986043517050355985638477512), (Int.ofNat 5884247730267745774864922533), (Int.ofNat 770850742465002128021699187), (Int.negOfNat 68803358534731601482318519), (Int.negOfNat 5248645515133541336330971), (Int.ofNat 447123018288590442030453), (Int.ofNat 27616662257283363786208), (Int.negOfNat 1903258543468234921661), (Int.negOfNat 115606240787314688603), (Int.ofNat 5586060053317810168), (Int.ofNat 124003836509741337), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-1246556443193693619746853369124323/1407374883553280000000000000000000), (496585464441348696548467265138897/11258999068426240000000000000000000), (3675169931807205162605237565423/1407374883553280000000000000000000), (-16253957914830668935206401793627/11258999068426240000000000000000000), (2048485418249883981221958468531/5629499534213120000000000000000000), (-1599317093984933619615841933/140737488355328000000000000000000), (-9748255439631294498204809689/1407374883553280000000000000000000), (5884247730267745774864922533/11258999068426240000000000000000000), (770850742465002128021699187/11258999068426240000000000000000000), (-68803358534731601482318519/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial129.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial129.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial129.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial129 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 8934329736216779335504739145162766), (Int.ofNat 528283224484393069422816314501371), (Int.ofNat 6224816727161191087130724681679), (Int.ofNat 3173629998183314962568500422177), (Int.ofNat 322928891949731320975993700716), (Int.negOfNat 389897612410347640213475931092), (Int.ofNat 34611089542208486186982834929), (Int.ofNat 6083631995485422239616595623), (Int.negOfNat 698317448962586643256568314), (Int.negOfNat 53707924659644867508252272), (Int.ofNat 6373369659604437191621441), (Int.ofNat 343815794599476052253460), (Int.negOfNat 35504628661661251115361), (Int.negOfNat 1717025563949749095835), (Int.ofNat 134825632313432095549), (Int.ofNat 6943386856974582224), (Int.negOfNat 679741194665488059), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-4467164868108389667752369572581383/5629499534213120000000000000000000), (528283224484393069422816314501371/11258999068426240000000000000000000), (6224816727161191087130724681679/11258999068426240000000000000000000), (3173629998183314962568500422177/11258999068426240000000000000000000), (80732222987432830243998425179/2814749767106560000000000000000000), (-97474403102586910053368982773/2814749767106560000000000000000000), (34611089542208486186982834929/11258999068426240000000000000000000), (6083631995485422239616595623/11258999068426240000000000000000000), (-349158724481293321628284157/5629499534213120000000000000000000), (-3356745291227804219265767/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial129.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial129.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial129.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial129 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 7831990221398456591698160666031737), (Int.ofNat 578975500455307620974264305150585), (Int.ofNat 12801556904316300953820133194650), (Int.negOfNat 2326326805188793420696547097862), (Int.negOfNat 699423457630232723540883534129), (Int.ofNat 172890361484981163717133065312), (Int.ofNat 29617066852512638974252373268), (Int.negOfNat 5910058595259693084733180541), (Int.negOfNat 385837783109517353196233380), (Int.ofNat 77437087370450511115113318), (Int.ofNat 3216641984775692798889900), (Int.negOfNat 567731404660236322143511), (Int.negOfNat 20210816405605857307909), (Int.ofNat 2712034493244757209978), (Int.ofNat 97947390364057082934), (Int.negOfNat 8770385598192742638), (Int.negOfNat 157203841762325886), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-7831990221398456591698160666031737/11258999068426240000000000000000000), (115795100091061524194852861030117/2251799813685248000000000000000000), (256031138086326019076402663893/225179981368524800000000000000000), (-1163163402594396710348273548931/5629499534213120000000000000000000), (-699423457630232723540883534129/11258999068426240000000000000000000), (5402823796405661366160408291/351843720888320000000000000000000), (7404266713128159743563093317/2814749767106560000000000000000000), (-5910058595259693084733180541/11258999068426240000000000000000000), (-19291889155475867659811669/562949953421312000000000000000000), (38718543685225255557556659/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial129.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial129.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial129.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial129 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 6646019941135254731900422500811543), (Int.ofNat 596547303180903229493909309986619), (Int.negOfNat 1289228995529482153294888974320), (Int.ofNat 171876859024995338511911469836), (Int.ofNat 1049530159460445922669664372840), (Int.ofNat 23174034083537166124055458127), (Int.negOfNat 42435799608499328507713973826), (Int.negOfNat 1030534326402420714361455152), (Int.ofNat 799504292631519889066735578), (Int.ofNat 15245667632226954164072635), (Int.negOfNat 7848222086000654486323590), (Int.negOfNat 153102007504885976669603), (Int.ofNat 47239133418217185349170), (Int.ofNat 1038973976242167548153), (Int.negOfNat 194027451744625320721), (Int.negOfNat 5179261832174821114), (Int.ofNat 926103230922545949), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-6646019941135254731900422500811543/11258999068426240000000000000000000), (596547303180903229493909309986619/11258999068426240000000000000000000), (-16115362444118526916186112179/140737488355328000000000000000000), (42969214756248834627977867459/2814749767106560000000000000000000), (26238253986511148066741609321/281474976710656000000000000000000), (23174034083537166124055458127/11258999068426240000000000000000000), (-21217899804249664253856986913/5629499534213120000000000000000000), (-64408395400151294647590947/703687441776640000000000000000000), (399752146315759944533367789/5629499534213120000000000000000000), (3049133526445390832814527/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial129.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial129.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial129.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial129 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 5441816656344533353382804088171644), (Int.ofNat 621095548626700416089221558475544), (Int.ofNat 17319092065501348069233280814135), (Int.ofNat 3521383719936796337833957358898), (Int.negOfNat 702299974216732602568124596653), (Int.negOfNat 246599108570792746923566380589), (Int.ofNat 17158104250509697074482953126), (Int.ofNat 6835995849773105053542842549), (Int.negOfNat 163163475062722672505731005), (Int.negOfNat 93447281746731791697389750), (Int.ofNat 378286597010654734641291), (Int.ofNat 721603154303722393929277), (Int.ofNat 4327537131799074796166), (Int.negOfNat 3610949751982350057702), (Int.negOfNat 44453791114856358944), (Int.ofNat 12768968703295003798), (Int.ofNat 108283168262557805), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-1360454164086133338345701022042911/2814749767106560000000000000000000), (77636943578337552011152694809443/1407374883553280000000000000000000), (3463818413100269613846656162827/2251799813685248000000000000000000), (1760691859968398168916978679449/5629499534213120000000000000000000), (-702299974216732602568124596653/11258999068426240000000000000000000), (-246599108570792746923566380589/11258999068426240000000000000000000), (8579052125254848537241476563/5629499534213120000000000000000000), (6835995849773105053542842549/11258999068426240000000000000000000), (-32632695012544534501146201/2251799813685248000000000000000000), (-373789126986927166789559/45035996273704960000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial129.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial129.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial129.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial129 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 4119420727808925315149465249710665), (Int.ofNat 696411470960012058893312982888605), (Int.ofNat 9877394814318520932875775132232), (Int.negOfNat 6146575829442487124140282609055), (Int.negOfNat 749466761536325288228320828311), (Int.ofNat 295665047179944369809804156262), (Int.ofNat 43192368200124502905758258466), (Int.negOfNat 5342710575703671882406362889), (Int.negOfNat 936814288452765912509599765), (Int.ofNat 40519127597054691359130500), (Int.ofNat 9674157279937260572963821), (Int.negOfNat 148869559881650719197957), (Int.negOfNat 59863182300284247908164), (Int.ofNat 139980068996557229232), (Int.ofNat 251115480339094571976), (Int.ofNat 1798185044680541082), (Int.negOfNat 1112477925262307575), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-823884145561785063029893049942133/2251799813685248000000000000000000), (139282294192002411778662596577721/2251799813685248000000000000000000), (1234674351789815116609471891529/1407374883553280000000000000000000), (-1229315165888497424828056521811/2251799813685248000000000000000000), (-749466761536325288228320828311/11258999068426240000000000000000000), (147832523589972184904902078131/5629499534213120000000000000000000), (21596184100062251452879129233/5629499534213120000000000000000000), (-5342710575703671882406362889/11258999068426240000000000000000000), (-187362857690553182501919953/2251799813685248000000000000000000), (81038255194109382718261/22517998136852480000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial129.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial129.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial129.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial129 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 2736920272473330635313685440264482), (Int.ofNat 666912286164210846327241902249293), (Int.negOfNat 15948926631200370494926699615703), (Int.ofNat 2278004133515906589590878901408), (Int.ofNat 2533361916089820906330709765913), (Int.ofNat 95022924744849075295869780792), (Int.negOfNat 82314313486087360216122249746), (Int.negOfNat 7389357435503332485557357288), (Int.ofNat 915950573711300650235902698), (Int.ofNat 112914004622969041570217765), (Int.negOfNat 5320443843405901596004870), (Int.negOfNat 886940581844044842490277), (Int.ofNat 18262172075665968373650), (Int.ofNat 4470519028906643261117), (Int.negOfNat 33498331211152318401), (Int.negOfNat 16551282478895974276), (Int.ofNat 33824852407091089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-1368460136236665317656842720132241/5629499534213120000000000000000000), (666912286164210846327241902249293/11258999068426240000000000000000000), (-15948926631200370494926699615703/11258999068426240000000000000000000), (71187629172372080924714965669/351843720888320000000000000000000), (2533361916089820906330709765913/11258999068426240000000000000000000), (11877865593106134411983722599/1407374883553280000000000000000000), (-41157156743043680108061124873/5629499534213120000000000000000000), (-923669679437916560694669661/1407374883553280000000000000000000), (457975286855650325117951349/5629499534213120000000000000000000), (22582800924593808314043553/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial129.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial129.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial129.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial129 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 1411021662113632789525125651255272), (Int.ofNat 701168799218143889202767052148345), (Int.ofNat 43477879759229432601730749814135), (Int.ofNat 11170019595566505682356454857307), (Int.negOfNat 2148254088023133175365092917012), (Int.negOfNat 941363272535005335195784367015), (Int.negOfNat 36294782357941316211760023202), (Int.ofNat 14647753764328080147338911771), (Int.ofNat 1129362599431317362766420990), (Int.negOfNat 112427771211274516995176448), (Int.negOfNat 11771847194305600762558140), (Int.ofNat 529106199020128902313761), (Int.ofNat 71914070753687264559631), (Int.negOfNat 1659286363801480995928), (Int.negOfNat 301074537995002053726), (Int.ofNat 3337518703368911388), (Int.ofNat 1227798609267244754), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-176377707764204098690640706406909/1407374883553280000000000000000000), (140233759843628777840553410429669/2251799813685248000000000000000000), (8695575951845886520346149962827/2251799813685248000000000000000000), (11170019595566505682356454857307/11258999068426240000000000000000000), (-537063522005783293841273229253/2814749767106560000000000000000000), (-188272654507001067039156873403/2251799813685248000000000000000000), (-18147391178970658105880011601/5629499534213120000000000000000000), (14647753764328080147338911771/11258999068426240000000000000000000), (112936259943131736276642099/1125899906842624000000000000000000), (-54896372661755135251551/5497558138880000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial129.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial129.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial129.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial129 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.ofNat 189864827676444550975982426443076), (Int.ofNat 865505723880000840887136486517341), (Int.negOfNat 13847093247643518051358940782612), (Int.negOfNat 40006626012507834057472847825339), (Int.negOfNat 8954275631018584667697071230047), (Int.ofNat 59981440922816338592455976201), (Int.ofNat 191653203432003379111249660972), (Int.ofNat 9539889768590332143767659747), (Int.negOfNat 1865635715654813039386802484), (Int.negOfNat 140741313163616496006928088), (Int.ofNat 11018410670999301597334701), (Int.ofNat 1055871957057541532236360), (Int.negOfNat 44234969715411039737801), (Int.negOfNat 5175353591799822280045), (Int.ofNat 127847460947872639559), (Int.ofNat 18237850103755573786), (Int.negOfNat 280186888664148979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(47466206919111137743995606610769/2814749767106560000000000000000000), (865505723880000840887136486517341/11258999068426240000000000000000000), (-3461773311910879512839735195653/2814749767106560000000000000000000), (-40006626012507834057472847825339/11258999068426240000000000000000000), (-8954275631018584667697071230047/11258999068426240000000000000000000), (59981440922816338592455976201/11258999068426240000000000000000000), (47913300858000844777812415243/2814749767106560000000000000000000), (9539889768590332143767659747/11258999068426240000000000000000000), (-466408928913703259846700621/2814749767106560000000000000000000), (-17592664145452062000866011/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial129.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial129.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial129.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial129 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.ofNat 1417036363317730003108567673053630), (Int.ofNat 87203104284782448875092732830743), (Int.negOfNat 415422218176602199978521056525557), (Int.negOfNat 77127095528674591540244003431665), (Int.ofNat 3344285159581392304221521143348), (Int.ofNat 2155697470820653884961350358130), (Int.ofNat 70702964527694146039980867255), (Int.negOfNat 26030181133492572359803859993), (Int.negOfNat 1547273007334788066673947173), (Int.ofNat 188216470137829650467467299), (Int.ofNat 14280509618199063262891979), (Int.negOfNat 922034903129867502985453), (Int.negOfNat 82202289120488836730192), (Int.ofNat 3275228760394655632231), (Int.ofNat 332993667159216603367), (Int.negOfNat 8693743748738652438), (Int.negOfNat 1260998614519829303), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(141703636331773000310856767305363/1125899906842624000000000000000000), (87203104284782448875092732830743/11258999068426240000000000000000000), (-415422218176602199978521056525557/11258999068426240000000000000000000), (-15425419105734918308048800686333/2251799813685248000000000000000000), (836071289895348076055380285837/2814749767106560000000000000000000), (215569747082065388496135035813/1125899906842624000000000000000000), (14140592905538829207996173451/2251799813685248000000000000000000), (-26030181133492572359803859993/11258999068426240000000000000000000), (-1547273007334788066673947173/11258999068426240000000000000000000), (188216470137829650467467299/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial129.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial129.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial129.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial129 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 563866361786335152551354227421591), (Int.negOfNat 2219714380591096618413443732739500), (Int.negOfNat 627761502406762859133401694381014), (Int.ofNat 31002125521884537276713974920364), (Int.ofNat 21025005678168877441162393513681), (Int.ofNat 584811138057894918633998643712), (Int.negOfNat 310097252262256222891518861834), (Int.negOfNat 16439588782796467234955267477), (Int.ofNat 2731660857532974261437184878), (Int.ofNat 180985241918044023180217108), (Int.negOfNat 16170319110573782676811802), (Int.negOfNat 1213330002953662375000688), (Int.ofNat 68829219086737422025745), (Int.ofNat 5629405829484902157895), (Int.negOfNat 220681738689210844215), (Int.negOfNat 19488361732096156962), (Int.ofNat 526548924921206869), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-563866361786335152551354227421591/11258999068426240000000000000000000), (-4439428761182193236826887465479/22517998136852480000000000000000), (-313880751203381429566700847190507/5629499534213120000000000000000000), (7750531380471134319178493730091/2814749767106560000000000000000000), (21025005678168877441162393513681/11258999068426240000000000000000000), (1142209254019326012957028601/21990232555520000000000000000000), (-155048626131128111445759430917/5629499534213120000000000000000000), (-16439588782796467234955267477/11258999068426240000000000000000000), (1365830428766487130718592439/5629499534213120000000000000000000), (45246310479511005795054277/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial129.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial129.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial129.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial129 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 6932387322507841130538358304454093), (Int.negOfNat 3702933706090215809100318058860527), (Int.ofNat 29679654102109329717535866177592), (Int.ofNat 169350576279397792281190213567132), (Int.ofNat 7195317246378611989331297277974), (Int.negOfNat 3086351374176027986801745101922), (Int.negOfNat 179860252061162645284002658153), (Int.ofNat 33636977294325778949412042226), (Int.ofNat 2198155696297600367142665361), (Int.negOfNat 243058317172541666195342231), (Int.negOfNat 16812655704674595822916597), (Int.ofNat 1241232082379178691863255), (Int.ofNat 88771899971383129485755), (Int.negOfNat 4706088044862402765977), (Int.negOfNat 343835422074733101428), (Int.ofNat 13514948684107761938), (Int.ofNat 1294198619772413852), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-6932387322507841130538358304454093/11258999068426240000000000000000000), (-3702933706090215809100318058860527/11258999068426240000000000000000000), (3709956762763666214691983272199/1407374883553280000000000000000000), (42337644069849448070297553391783/2814749767106560000000000000000000), (3597658623189305994665648638987/5629499534213120000000000000000000), (-1543175687088013993400872550961/5629499534213120000000000000000000), (-179860252061162645284002658153/11258999068426240000000000000000000), (16818488647162889474706021113/5629499534213120000000000000000000), (2198155696297600367142665361/11258999068426240000000000000000000), (-243058317172541666195342231/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial129.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial129.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial129.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial129 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 12855151271287622530986268093303692), (Int.negOfNat 1586509233885191636865401869365984), (Int.ofNat 953665691017557059179780446116799), (Int.ofNat 95953121821575985546271419992018), (Int.negOfNat 23723847625523857949885443201466), (Int.negOfNat 2016129506698776007642687092464), (Int.ofNat 339769975652084811046268044039), (Int.ofNat 25830546181682852301420636617), (Int.negOfNat 3107323460992583168200920467), (Int.negOfNat 220201873962299711297365046), (Int.ofNat 19401938635183623834379542), (Int.ofNat 1312431536780953634974202), (Int.negOfNat 87532853575581397559581), (Int.negOfNat 5713042590348045563161), (Int.ofNat 299864939691649481070), (Int.ofNat 18395006504680093795), (Int.negOfNat 783977629595792942), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-3213787817821905632746567023325923/2814749767106560000000000000000000), (-49578413558912238652043808417687/351843720888320000000000000000000), (953665691017557059179780446116799/11258999068426240000000000000000000), (47976560910787992773135709996009/5629499534213120000000000000000000), (-11861923812761928974942721600733/5629499534213120000000000000000000), (-126008094168673500477667943279/703687441776640000000000000000000), (339769975652084811046268044039/11258999068426240000000000000000000), (25830546181682852301420636617/11258999068426240000000000000000000), (-3107323460992583168200920467/11258999068426240000000000000000000), (-110100936981149855648682523/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial129.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial129.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial129.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial129.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial129 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial129 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial129 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 16349858931874616530906474829096144), (Int.ofNat 1239740868665446749794665463308741), (Int.ofNat 1090241087696723911203170973845800), (Int.negOfNat 144576656430306982887100890331297), (Int.negOfNat 26306064454504357065178796644546), (Int.ofNat 3518504558689063173079266822282), (Int.ofNat 374553383635361204086393192522), (Int.negOfNat 44773492836195436450349109467), (Int.negOfNat 3404285067395497896181091117), (Int.ofNat 355883179544785146901797246), (Int.ofNat 21055451121289370217951042), (Int.negOfNat 1944295313381260914610052), (Int.negOfNat 93896678485030045615081), (Int.ofNat 7782309776234483429611), (Int.ofNat 317628303317044179570), (Int.negOfNat 23724015592298503345), (Int.negOfNat 783977629595792942), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-1021866183242163533181654676818509/703687441776640000000000000000000), (1239740868665446749794665463308741/11258999068426240000000000000000000), (5451205438483619556015854869229/56294995342131200000000000000000), (-144576656430306982887100890331297/11258999068426240000000000000000000), (-13153032227252178532589398322273/5629499534213120000000000000000000), (1759252279344531586539633411141/5629499534213120000000000000000000), (187276691817680602043196596261/5629499534213120000000000000000000), (-44773492836195436450349109467/11258999068426240000000000000000000), (-3404285067395497896181091117/11258999068426240000000000000000000), (177941589772392573450898623/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial129.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial129.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial129.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 10956762593526136787991590173622557), (Int.ofNat 3354745376535026278671592726059387), (Int.negOfNat 71556776392893448158451608584622), (Int.negOfNat 183383679237897720074190614706483), (Int.ofNat 16629789471281102960276272775355), (Int.ofNat 3550105365040702951086014286140), (Int.negOfNat 356066351563499537970536754053), (Int.negOfNat 39476412491312881985751602826), (Int.ofNat 3841189305263079668752351811), (Int.ofNat 284823339608343698640216981), (Int.negOfNat 26196289276445115324943747), (Int.negOfNat 1435634386025695328957905), (Int.ofNat 125155543032679491825255), (Int.ofNat 5343792799014072442127), (Int.negOfNat 446270818981175862778), (Int.negOfNat 15291285046647231788), (Int.ofNat 1294198619772413852), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-10956762593526136787991590173622557/11258999068426240000000000000000000), (3354745376535026278671592726059387/11258999068426240000000000000000000), (-35778388196446724079225804292311/5629499534213120000000000000000000), (-183383679237897720074190614706483/11258999068426240000000000000000000), (3325957894256220592055254555071/2251799813685248000000000000000000), (177505268252035147554300714307/562949953421312000000000000000000), (-356066351563499537970536754053/11258999068426240000000000000000000), (-19738206245656440992875801413/5629499534213120000000000000000000), (3841189305263079668752351811/11258999068426240000000000000000000), (284823339608343698640216981/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial129.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial129.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial129.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 5647629646483191220561611260713538), (Int.ofNat 1602468261085494125596225838314190), (Int.negOfNat 592856745063213682792585135028442), (Int.ofNat 20548356770689966672958798929786), (Int.ofNat 24768612782847994898695976434865), (Int.negOfNat 1983392577831843630050956337628), (Int.negOfNat 388161890300350016519486020724), (Int.ofNat 33814032507316777494397388627), (Int.ofNat 3475007685114613125853699328), (Int.negOfNat 305055299030947221133561958), (Int.negOfNat 20439132392313575671590202), (Int.ofNat 1790657279253929159916738), (Int.ofNat 85406284270069893556595), (Int.negOfNat 7521796167710284038095), (Int.negOfNat 267458596236083550265), (Int.ofNat 23633146578021586612), (Int.ofNat 526548924921206869), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-2823814823241595610280805630356769/5629499534213120000000000000000000), (160246826108549412559622583831419/1125899906842624000000000000000000), (-296428372531606841396292567514221/5629499534213120000000000000000000), (10274178385344983336479399464893/5629499534213120000000000000000000), (4953722556569598979739195286973/2251799813685248000000000000000000), (-495848144457960907512739084407/2814749767106560000000000000000000), (-97040472575087504129871505181/2814749767106560000000000000000000), (33814032507316777494397388627/11258999068426240000000000000000000), (13574248769978957522866013/43980465111040000000000000000000), (-152527649515473610566780979/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial129.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial129.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial129.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 4336701737294487442751710220249571), (Int.ofNat 54940124480612501397663792050301), (Int.negOfNat 99586150281620602520952550219364), (Int.ofNat 100547705128039552171238474999827), (Int.negOfNat 6416270928361283185080883149171), (Int.negOfNat 2965036133660442905362651442725), (Int.ofNat 230493655038696831687189309988), (Int.ofNat 36582204428492397717519424093), (Int.negOfNat 2995068284385844092151965023), (Int.negOfNat 264537983925140299299327249), (Int.ofNat 22485282089066071094505729), (Int.ofNat 1278473112161320167423753), (Int.negOfNat 113942788711409019517542), (Int.negOfNat 4445242311187319773431), (Int.ofNat 422402597407036585817), (Int.ofNat 11062192232124612238), (Int.negOfNat 1260998614519829303), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-4336701737294487442751710220249571/11258999068426240000000000000000000), (54940124480612501397663792050301/11258999068426240000000000000000000), (-24896537570405150630238137554841/2814749767106560000000000000000000), (100547705128039552171238474999827/11258999068426240000000000000000000), (-6416270928361283185080883149171/11258999068426240000000000000000000), (-118601445346417716214506057709/450359962737049600000000000000000), (57623413759674207921797327497/2814749767106560000000000000000000), (36582204428492397717519424093/11258999068426240000000000000000000), (-2995068284385844092151965023/11258999068426240000000000000000000), (-264537983925140299299327249/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial129.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial129.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial129.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 3999768857059621439028946979071051), (Int.ofNat 477738127524168937606376662458037), (Int.ofNat 186109039346234161061602658760542), (Int.negOfNat 18422635422220884848289872621714), (Int.negOfNat 16074493908845399202952898383214), (Int.ofNat 1205259334291760263554472114335), (Int.ofNat 316508941041584555103421963619), (Int.negOfNat 24274549449099713176295185847), (Int.negOfNat 3020616176103025165064503184), (Int.ofNat 244007420973968087759099138), (Int.ofNat 17603604090722267813632851), (Int.negOfNat 1533771495580698472028760), (Int.negOfNat 69754606177183336019951), (Int.ofNat 6740470603669139726695), (Int.ofNat 199493027570297923509), (Int.negOfNat 22382634949681003436), (Int.negOfNat 280186888664148979), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-3999768857059621439028946979071051/11258999068426240000000000000000000), (477738127524168937606376662458037/11258999068426240000000000000000000), (93054519673117080530801329380271/5629499534213120000000000000000000), (-9211317711110442424144936310857/5629499534213120000000000000000000), (-8037246954422699601476449191607/5629499534213120000000000000000000), (241051866858352052710894422867/2251799813685248000000000000000000), (316508941041584555103421963619/11258999068426240000000000000000000), (-24274549449099713176295185847/11258999068426240000000000000000000), (-188788511006439072816531449/703687441776640000000000000000000), (122003710486984043879549569/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial129.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial129.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial129.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 2649345390952062423236644833789947), (Int.ofNat 630574918057329490856854466036915), (Int.negOfNat 158276770075790670760954234203751), (Int.negOfNat 65661863063625778237065655722387), (Int.ofNat 5938084418422636191129486390947), (Int.ofNat 2194875649183345941888565939190), (Int.negOfNat 163747798564300158829751372002), (Int.negOfNat 29643926017201581372782447521), (Int.ofNat 2260179850320424112157298990), (Int.ofNat 218428489048227326305634498), (Int.negOfNat 18136443273623507003383590), (Int.negOfNat 1020914148727974877764161), (Int.ofNat 96487943097888240591481), (Int.ofNat 3269239220383087169978), (Int.negOfNat 369759544013194887926), (Int.negOfNat 7482303549294341038), (Int.ofNat 1227798609267244754), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-2649345390952062423236644833789947/11258999068426240000000000000000000), (126114983611465898171370893207383/2251799813685248000000000000000000), (-158276770075790670760954234203751/11258999068426240000000000000000000), (-65661863063625778237065655722387/11258999068426240000000000000000000), (5938084418422636191129486390947/11258999068426240000000000000000000), (219487564918334594188856593919/1125899906842624000000000000000000), (-81873899282150079414875686001/5629499534213120000000000000000000), (-29643926017201581372782447521/11258999068426240000000000000000000), (226017985032042411215729899/1125899906842624000000000000000000), (109214244524113663152817249/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial129.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial129.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial129.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 2394956255170555010402403052085211), (Int.negOfNat 466869994891521852510092790863660), (Int.negOfNat 288538079125562856262914505361139), (Int.ofNat 31751948081998325291108216315533), (Int.ofNat 12899933895792413142762389659996), (Int.negOfNat 973247217803091053559614498540), (Int.negOfNat 248740555768358070293629544596), (Int.ofNat 17807450420564530532160642188), (Int.ofNat 2404979506531072074107671898), (Int.negOfNat 186152637855516111613110465), (Int.negOfNat 13723746081344795000627170), (Int.ofNat 1226129345012562253748227), (Int.ofNat 50730345974169105891250), (Int.negOfNat 5580137143372965427417), (Int.negOfNat 124683597821511770701), (Int.ofNat 18919730962281934076), (Int.ofNat 33824852407091089), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-2394956255170555010402403052085211/11258999068426240000000000000000000), (-23343499744576092625504639543183/562949953421312000000000000000000), (-288538079125562856262914505361139/11258999068426240000000000000000000), (31751948081998325291108216315533/11258999068426240000000000000000000), (3224983473948103285690597414999/2814749767106560000000000000000000), (-48662360890154552677980724927/562949953421312000000000000000000), (-62185138942089517573407386149/2814749767106560000000000000000000), (4451862605141132633040160547/2814749767106560000000000000000000), (1202489753265536037053835949/5629499534213120000000000000000000), (-37230527571103222322622093/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial129.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial129.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial129.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 4066709004109618999086681058729276), (Int.negOfNat 942862987338388720014788550434212), (Int.ofNat 89311987556821366065482050631489), (Int.ofNat 69349197224649429419827433222606), (Int.negOfNat 4956221378582588035789445048189), (Int.negOfNat 1831341260492538446873750117444), (Int.ofNat 118568393607018176386432798866), (Int.ofNat 23429090275124395356318868239), (Int.negOfNat 1634225334902202028121765615), (Int.negOfNat 167480764407402925107260400), (Int.ofNat 13649230096128302721722971), (Int.ofNat 736643469876406768471857), (Int.negOfNat 75266485094689550431014), (Int.negOfNat 2062568125385110096882), (Int.ofNat 294339665160888338326), (Int.ofNat 2938711922091378518), (Int.negOfNat 1112477925262307575), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-1016677251027404749771670264682319/2814749767106560000000000000000000), (-235715746834597180003697137608553/2814749767106560000000000000000000), (89311987556821366065482050631489/11258999068426240000000000000000000), (34674598612324714709913716611303/5629499534213120000000000000000000), (-4956221378582588035789445048189/11258999068426240000000000000000000), (-457835315123134611718437529361/2814749767106560000000000000000000), (59284196803509088193216399433/5629499534213120000000000000000000), (23429090275124395356318868239/11258999068426240000000000000000000), (-326845066980440405624353123/2251799813685248000000000000000000), (-418701911018507312768151/28147497671065600000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial129.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial129.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial129.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 5168197559088538137526404617110973), (Int.negOfNat 27252757515250708356213400616974), (Int.ofNat 280623714922855670315224173935208), (Int.negOfNat 15059990674763554790045363755007), (Int.negOfNat 11896425507744536463550531925785), (Int.ofNat 613593029744309578487403478467), (Int.ofNat 203072010438167405561702948106), (Int.negOfNat 11846752256742314625142808899), (Int.negOfNat 1843948725840211829258510755), (Int.ofNat 130270760228107463340299950), (Int.ofNat 9893144838987634753805941), (Int.negOfNat 894393090878391947291077), (Int.negOfNat 32469501888445419200634), (Int.ofNat 4179377387994980409702), (Int.ofNat 58573717912432892356), (Int.negOfNat 14545305065834473648), (Int.ofNat 108283168262557805), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-5168197559088538137526404617110973/11258999068426240000000000000000000), (-13626378757625354178106700308487/5629499534213120000000000000000000), (35077964365356958789403021741901/1407374883553280000000000000000000), (-15059990674763554790045363755007/11258999068426240000000000000000000), (-2379285101548907292710106385157/2251799813685248000000000000000000), (613593029744309578487403478467/11258999068426240000000000000000000), (101536005219083702780851474053/5629499534213120000000000000000000), (-11846752256742314625142808899/11258999068426240000000000000000000), (-368789745168042365851702151/2251799813685248000000000000000000), (2605415204562149266805999/225179981368524800000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial129.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial129.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial129.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 4380312898254761600196383932208479), (Int.ofNat 615058467869247226797357428890774), (Int.negOfNat 8003536378693111320262859803431), (Int.negOfNat 62322589650986486664183776462140), (Int.ofNat 1659385445581215810376757100707), (Int.ofNat 1543302669990687098146095729190), (Int.negOfNat 62736901817798833788604015526), (Int.negOfNat 18176652943583240286551711098), (Int.ofNat 1016107724216146985881321928), (Int.ofNat 121467463560596417917689915), (Int.negOfNat 9131720368218698020888790), (Int.negOfNat 482479708750079481867097), (Int.ofNat 52268071232208518876370), (Int.ofNat 1043484352774937605997), (Int.negOfNat 208238142644941079521), (Int.negOfNat 149747255443588436), (Int.ofNat 926103230922545949), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-4380312898254761600196383932208479/11258999068426240000000000000000000), (307529233934623613398678714445387/5629499534213120000000000000000000), (-8003536378693111320262859803431/11258999068426240000000000000000000), (-3116129482549324333209188823107/562949953421312000000000000000000), (1659385445581215810376757100707/11258999068426240000000000000000000), (154330266999068709814609572919/1125899906842624000000000000000000), (-31368450908899416894302007763/5629499534213120000000000000000000), (-9088326471791620143275855549/5629499534213120000000000000000000), (127013465527018373235165241/1407374883553280000000000000000000), (24293492712119283583537983/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial129.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial129.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial129.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 3610884550799803858247221045633012), (Int.negOfNat 7181348590511508122992343597420), (Int.negOfNat 243655751865210633961064384581154), (Int.negOfNat 5212958598222568907700481766358), (Int.ofNat 9730217566812917102723054027360), (Int.negOfNat 118755352215409104536293011975), (Int.negOfNat 156431483679573993498140166732), (Int.ofNat 5609109628583784529859228591), (Int.ofNat 1340505030982710252298856570), (Int.negOfNat 75980248896238480525054118), (Int.negOfNat 6633792298549509902492050), (Int.ofNat 561866767935288046991911), (Int.ofNat 17973604291656725478341), (Int.negOfNat 2693679017498516021528), (Int.negOfNat 9224903509157598016), (Int.ofNat 8770385598192742638), (Int.negOfNat 157203841762325886), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-902721137699950964561805261408253/2814749767106560000000000000000000), (-359067429525575406149617179871/562949953421312000000000000000000), (-121827875932605316980532192290577/5629499534213120000000000000000000), (-2606479299111284453850240883179/5629499534213120000000000000000000), (60813859792580731892019087671/70368744177664000000000000000000), (-4750214088616364181451720479/450359962737049600000000000000000), (-39107870919893498374535041683/2814749767106560000000000000000000), (5609109628583784529859228591/11258999068426240000000000000000000), (134050503098271025229885657/1125899906842624000000000000000000), (-37990124448119240262527059/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial129.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial129.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial129.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 4498685586594236278121476698324821), (Int.negOfNat 768845007348527313934331498418613), (Int.negOfNat 82690687704134604245879619151330), (Int.ofNat 47907428960931983016421701838300), (Int.ofNat 1858218639109086397434994446128), (Int.negOfNat 1113329511998969497729085520532), (Int.ofNat 7675840801658181741826112159), (Int.ofNat 12883184546782765750733473077), (Int.negOfNat 443309724499770752195167814), (Int.negOfNat 82279378666592068579475878), (Int.ofNat 4907726099558452553457041), (Int.ofNat 289689901680153406596440), (Int.negOfNat 29812129325610428281311), (Int.negOfNat 360103755979737648765), (Int.ofNat 118838605050576866899), (Int.negOfNat 1614377769356172674), (Int.negOfNat 679741194665488059), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-4498685586594236278121476698324821/11258999068426240000000000000000000), (-768845007348527313934331498418613/11258999068426240000000000000000000), (-8269068770413460424587961915133/1125899906842624000000000000000000), (479074289609319830164217018383/112589990684262400000000000000000), (116138664944317899839687152883/703687441776640000000000000000000), (-278332377999742374432271380133/2814749767106560000000000000000000), (7675840801658181741826112159/11258999068426240000000000000000000), (12883184546782765750733473077/11258999068426240000000000000000000), (-221654862249885376097583907/5629499534213120000000000000000000), (-41139689333296034289737939/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial129.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial129.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial129.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 5987783783852329433724843775966168), (Int.negOfNat 547692415915393508710948583368733), (Int.ofNat 169673584810115807506212499389933), (Int.ofNat 25530211008608256132033322877804), (Int.negOfNat 5961089106853988591273728104149), (Int.negOfNat 258394400985730780162354104825), (Int.ofNat 102113958737040416907972756775), (Int.negOfNat 564049400399244948543018833), (Int.negOfNat 888850101615827292149764413), (Int.ofNat 29723501948879913453380719), (Int.ofNat 4197980561613080953675479), (Int.negOfNat 263797599258761911570003), (Int.negOfNat 8975208105141537088592), (Int.ofNat 1300488404446508152561), (Int.negOfNat 13170843880871927253), (Int.negOfNat 3809723690778340318), (Int.ofNat 124003836509741337), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-748472972981541179215605471995771/1407374883553280000000000000000000), (-547692415915393508710948583368733/11258999068426240000000000000000000), (169673584810115807506212499389933/11258999068426240000000000000000000), (6382552752152064033008330719451/2814749767106560000000000000000000), (-5961089106853988591273728104149/11258999068426240000000000000000000), (-10335776039429231206494164193/450359962737049600000000000000000), (4084558349481616676318910271/450359962737049600000000000000000), (-564049400399244948543018833/11258999068426240000000000000000000), (-888850101615827292149764413/11258999068426240000000000000000000), (29723501948879913453380719/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial129.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial129.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial129.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 6297624135065209252382602670387266), (Int.ofNat 244467906676861642150109156980771), (Int.ofNat 181830140481604487136519608978412), (Int.negOfNat 17852247373190209655244107751295), (Int.negOfNat 3407204282066846191244714812206), (Int.ofNat 606856321344191517281151632755), (Int.ofNat 24580494073836677005476714616), (Int.negOfNat 7964769568533023136614730297), (Int.ofNat 30604296720719573696728318), (Int.ofNat 52791843141705345880216948), (Int.negOfNat 1520050332155743280225332), (Int.negOfNat 176586128198577208121548), (Int.ofNat 10591693076416367827695), (Int.ofNat 90521896316118226855), (Int.negOfNat 40074325023934223375), (Int.ofNat 2306068003120314768), (Int.ofNat 433379158408430169), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-3148812067532604626191301335193633/5629499534213120000000000000000000), (244467906676861642150109156980771/11258999068426240000000000000000000), (45457535120401121784129902244603/2814749767106560000000000000000000), (-3570449474638041931048821550259/2251799813685248000000000000000000), (-1703602141033423095622357406103/5629499534213120000000000000000000), (121371264268838303456230326551/2251799813685248000000000000000000), (3072561759229584625684589327/1407374883553280000000000000000000), (-7964769568533023136614730297/11258999068426240000000000000000000), (15302148360359786848364159/5629499534213120000000000000000000), (13197960785426336470054237/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial129.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial129.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial129.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 5258694954388978080276164426125179), (Int.ofNat 698374167517943039931948787257953), (Int.ofNat 42315594109790548807830520383910), (Int.negOfNat 21053981685638065882425477741254), (Int.ofNat 2126638951402321224353478223983), (Int.ofNat 336511340309245786174355972155), (Int.negOfNat 55119165565150502170121117823), (Int.negOfNat 2000152284697515069028713534), (Int.ofNat 555943691226261845821873981), (Int.ofNat 1377641000974796727762739), (Int.negOfNat 2827015641544096174368877), (Int.ofNat 37809239362150251130945), (Int.ofNat 6278817309285570729665), (Int.negOfNat 172136328748719716917), (Int.ofNat 10098239557947253682), (Int.negOfNat 173251369934303132), (Int.negOfNat 90803831257156788), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-5258694954388978080276164426125179/11258999068426240000000000000000000), (698374167517943039931948787257953/11258999068426240000000000000000000), (4231559410979054880783052038391/1125899906842624000000000000000000), (-10526990842819032941212738870627/5629499534213120000000000000000000), (2126638951402321224353478223983/11258999068426240000000000000000000), (67302268061849157234871194431/2251799813685248000000000000000000), (-55119165565150502170121117823/11258999068426240000000000000000000), (-1000076142348757534514356767/5629499534213120000000000000000000), (555943691226261845821873981/11258999068426240000000000000000000), (1377641000974796727762739/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial129.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial129.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial129.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 3819964922390135766164935463027642), (Int.ofNat 699041727706352774254089148817065), (Int.negOfNat 19649258586361103367782458078824), (Int.ofNat 442927554860067033037739436375), (Int.ofNat 2217116200118705748264204650903), (Int.negOfNat 262180615211780897964569072714), (Int.negOfNat 28528799375546209256828575208), (Int.ofNat 4723306874628463132161514537), (Int.ofNat 166120617062279354859732573), (Int.negOfNat 37235787179948882846672386), (Int.negOfNat 613854180536542850818568), (Int.ofNat 151921775771226440753092), (Int.ofNat 2972454473241424915269), (Int.negOfNat 242977744333842866881), (Int.negOfNat 20780406507197826180), (Int.negOfNat 872573700854018105), (Int.negOfNat 198083790568900462), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-1909982461195067883082467731513821/5629499534213120000000000000000000), (139808345541270554850817829763413/2251799813685248000000000000000000), (-2456157323295137920972807259853/1407374883553280000000000000000000), (3543420438880536264301915491/90071992547409920000000000000000), (2217116200118705748264204650903/11258999068426240000000000000000000), (-131090307605890448982284536357/5629499534213120000000000000000000), (-3566099921943276157103571901/1407374883553280000000000000000000), (4723306874628463132161514537/11258999068426240000000000000000000), (166120617062279354859732573/11258999068426240000000000000000000), (-18617893589974441423336193/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial129.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial129.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial129.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 2471049106708370764065984138835604), (Int.ofNat 672454547447787604545377347787908), (Int.ofNat 11695262975585175144705593664253), (Int.ofNat 5867821149973048891961288974814), (Int.negOfNat 759538831822904321649847845628), (Int.negOfNat 208672503078857850979793238732), (Int.ofNat 31469975961318998232745951248), (Int.ofNat 2271398284915501427205447557), (Int.negOfNat 404629043133802948958930813), (Int.negOfNat 14984991059594248079226756), (Int.ofNat 2627903433765648829312428), (Int.ofNat 90434613122153250033392), (Int.negOfNat 9634362317539036402509), (Int.negOfNat 544295689038681816741), (Int.ofNat 17172830559408758310), (Int.ofNat 3305449599244836525), (Int.negOfNat 95570863082604838), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-617762276677092691016496034708901/2814749767106560000000000000000000), (168113636861946901136344336946977/2814749767106560000000000000000000), (11695262975585175144705593664253/11258999068426240000000000000000000), (2933910574986524445980644487407/5629499534213120000000000000000000), (-189884707955726080412461961407/2814749767106560000000000000000000), (-52168125769714462744948309683/2814749767106560000000000000000000), (1966873497582437389546621953/703687441776640000000000000000000), (2271398284915501427205447557/11258999068426240000000000000000000), (-404629043133802948958930813/11258999068426240000000000000000000), (-3746247764898562019806689/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial129.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial129.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial129.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.negOfNat 1049050139393160745837020635296637), (Int.ofNat 755275576961439736679109758945788), (Int.ofNat 20296576283375773575658093887814), (Int.negOfNat 3010907023429240376715313794673), (Int.negOfNat 797933519349205995089142961194), (Int.ofNat 171016615384309897407463386450), (Int.ofNat 17378887498837778400962779403), (Int.negOfNat 3652150933975337897628684724), (Int.negOfNat 175177319384477729804217741), (Int.ofNat 36226339823619514954758919), (Int.ofNat 1349019946020879699759517), (Int.negOfNat 207156264472546053668235), (Int.negOfNat 9262042293524104586765), (Int.ofNat 752160226319067375453), (Int.ofNat 51606773976714580888), (Int.negOfNat 1149939319593092492), (Int.ofNat 55975769899251568), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-1049050139393160745837020635296637/11258999068426240000000000000000000), (188818894240359934169777439736447/2814749767106560000000000000000000), (10148288141687886787829046943907/5629499534213120000000000000000000), (-3010907023429240376715313794673/11258999068426240000000000000000000), (-398966759674602997544571480597/5629499534213120000000000000000000), (3420332307686197948149267729/225179981368524800000000000000000), (17378887498837778400962779403/11258999068426240000000000000000000), (-913037733493834474407171181/2814749767106560000000000000000000), (-175177319384477729804217741/11258999068426240000000000000000000), (36226339823619514954758919/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial129.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial129.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial129.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 511925060951135311315238562485183), (Int.ofNat 790087512380722871637172482393866), (Int.negOfNat 1659021940494523073736552511992), (Int.negOfNat 1926276703134797907451286919547), (Int.ofNat 890757592314359495230310402762), (Int.ofNat 71442672114289946286720055648), (Int.negOfNat 27906274815176742301240267776), (Int.negOfNat 1170847667885005337942402657), (Int.ofNat 411641732501681040063680662), (Int.ofNat 12373974541998080030419638), (Int.negOfNat 3376483591607491281053248), (Int.negOfNat 109111968454312434246808), (Int.ofNat 17565086851414324776395), (Int.ofNat 749585019659703084295), (Int.negOfNat 63366503952639575445), (Int.negOfNat 3806692705814409742), (Int.ofNat 352999567757190911), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(511925060951135311315238562485183/11258999068426240000000000000000000), (395043756190361435818586241196933/5629499534213120000000000000000000), (-207377742561815384217069063999/1407374883553280000000000000000000), (-1926276703134797907451286919547/11258999068426240000000000000000000), (445378796157179747615155201381/5629499534213120000000000000000000), (2232583503571560821460001739/351843720888320000000000000000000), (-27252221499196037403554949/10995116277760000000000000000000), (-1170847667885005337942402657/11258999068426240000000000000000000), (205820866250840520031840331/5629499534213120000000000000000000), (6186987270999040015209819/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial129.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial129.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial129.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 2084764312946581396197968226327164), (Int.ofNat 789105194092645945997216493852063), (Int.ofNat 7146590415923222562872318061056), (Int.ofNat 3686670189028404451463523313387), (Int.ofNat 66339113672249557915961508878), (Int.negOfNat 180923067601239816340378522340), (Int.negOfNat 1689910827751634975106473688), (Int.ofNat 3874668940688689411569476187), (Int.ofNat 38098057913723862146628873), (Int.negOfNat 44580556191900963768100861), (Int.negOfNat 677934350569000084440329), (Int.ofNat 313320054657748926437107), (Int.ofNat 7421583559947279281592), (Int.negOfNat 1477920057226183492099), (Int.negOfNat 49312311350428395557), (Int.ofNat 4786920013269222092), (Int.negOfNat 89175775151836117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(521191078236645349049492056581791/2814749767106560000000000000000000), (789105194092645945997216493852063/11258999068426240000000000000000000), (13958184406100044068109996213/21990232555520000000000000000000), (3686670189028404451463523313387/11258999068426240000000000000000000), (33169556836124778957980754439/5629499534213120000000000000000000), (-9046153380061990817018926117/562949953421312000000000000000000), (-211238853468954371888309211/1407374883553280000000000000000000), (3874668940688689411569476187/11258999068426240000000000000000000), (38098057913723862146628873/11258999068426240000000000000000000), (-44580556191900963768100861/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial129.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial129.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial129.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 3716701008280766099489889094123026), (Int.ofNat 850928449404643807035973290233949), (Int.ofNat 18447213229222077668307192912481), (Int.negOfNat 1288306284292724358484974459697), (Int.negOfNat 891970905600411938250888235196), (Int.ofNat 55492528134087662140788663832), (Int.ofNat 29308821453676512399874293671), (Int.negOfNat 918701327252060006486986283), (Int.negOfNat 479796798397742319963636966), (Int.ofNat 5584946242212687500675272), (Int.ofNat 4550264334225244571575819), (Int.ofNat 12929406429284998118480), (Int.negOfNat 27649651748106619918959), (Int.negOfNat 397650104951732760245), (Int.ofNat 116090555462268027051), (Int.ofNat 3148293198320316516), (Int.negOfNat 599361604014248801), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1858350504140383049744944547061513/5629499534213120000000000000000000), (850928449404643807035973290233949/11258999068426240000000000000000000), (18447213229222077668307192912481/11258999068426240000000000000000000), (-1288306284292724358484974459697/11258999068426240000000000000000000), (-222992726400102984562722058799/2814749767106560000000000000000000), (6936566016760957767598582979/1407374883553280000000000000000000), (29308821453676512399874293671/11258999068426240000000000000000000), (-918701327252060006486986283/11258999068426240000000000000000000), (-239898399198871159981818483/5629499534213120000000000000000000), (698118280276585937584409/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial129.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial129.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial129.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 5471187309864523305273481050983457), (Int.ofNat 889913987587862338942264337296775), (Int.negOfNat 616938699399487667187977410410), (Int.negOfNat 2791907674495196824799775904478), (Int.ofNat 707569634058919428266716609949), (Int.ofNat 160603473191059264297582297748), (Int.negOfNat 19686328302321218724599555628), (Int.negOfNat 4045796540149747959588693799), (Int.ofNat 244813986789266125984523840), (Int.ofNat 53981739076873775913070382), (Int.negOfNat 1448193149776338648081840), (Int.negOfNat 430844984572690665132569), (Int.ofNat 2897236475735439340529), (Int.ofNat 2252725008732967290542), (Int.ofNat 14748638605576685866), (Int.negOfNat 7774696575253003342), (Int.ofNat 122375780404420666), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(5471187309864523305273481050983457/11258999068426240000000000000000000), (35596559503514493557690573491871/450359962737049600000000000000000), (-61693869939948766718797741041/1125899906842624000000000000000000), (-1395953837247598412399887952239/5629499534213120000000000000000000), (707569634058919428266716609949/11258999068426240000000000000000000), (40150868297764816074395574437/2814749767106560000000000000000000), (-4921582075580304681149888907/2814749767106560000000000000000000), (-4045796540149747959588693799/11258999068426240000000000000000000), (765043708716456643701637/35184372088832000000000000000000), (26990869538436887956535191/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial129.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial129.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial129.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 7240982883158673710261457540034003), (Int.ofNat 884204541365470342436019101770761), (Int.ofNat 5677262802130431266495343143580), (Int.ofNat 4566780215045322893365720334784), (Int.ofNat 454968042948593352197209015940), (Int.negOfNat 220368311694791684366297381987), (Int.negOfNat 23212634117525860408089868194), (Int.ofNat 4292653865061418211132208852), (Int.ofNat 498600515908974210351580622), (Int.negOfNat 40684764921585701854595815), (Int.negOfNat 5584918472593934121470510), (Int.ofNat 202289300106750947273663), (Int.ofNat 37364571719211904385290), (Int.negOfNat 506921902245458899793), (Int.negOfNat 167525350478381691039), (Int.negOfNat 277501331767737106), (Int.ofNat 845723640271306691), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(7240982883158673710261457540034003/11258999068426240000000000000000000), (884204541365470342436019101770761/11258999068426240000000000000000000), (283863140106521563324767157179/562949953421312000000000000000000), (71355940860083170208839380231/175921860444160000000000000000000), (22748402147429667609860450797/562949953421312000000000000000000), (-220368311694791684366297381987/11258999068426240000000000000000000), (-11606317058762930204044934097/5629499534213120000000000000000000), (1073163466265354552783052213/2814749767106560000000000000000000), (249300257954487105175790311/5629499534213120000000000000000000), (-8136952984317140370919163/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial129.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial129.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial129.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 9068028465308334977376674198732244), (Int.ofNat 956502136280984025843030557999336), (Int.ofNat 24331101605026297769864401689345), (Int.negOfNat 1316873411537921982144901940738), (Int.negOfNat 1607272516380382522989966445887), (Int.negOfNat 32585090495598140253226920151), (Int.ofNat 51587439253709783281209833034), (Int.ofNat 2939413106822493772274345131), (Int.negOfNat 727226149821184476884775555), (Int.negOfNat 57820728908841558999819670), (Int.ofNat 5170585520445624240964149), (Int.ofNat 528744508565594729008823), (Int.negOfNat 21456474793309389168506), (Int.negOfNat 2938663783395043232698), (Int.ofNat 53289770367600675904), (Int.ofNat 11134063960762985962), (Int.negOfNat 237696464409357845), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(2267007116327083744344168549683061/2814749767106560000000000000000000), (119562767035123003230378819749917/1407374883553280000000000000000000), (4866220321005259553972880337869/2251799813685248000000000000000000), (-658436705768960991072450970369/5629499534213120000000000000000000), (-1607272516380382522989966445887/11258999068426240000000000000000000), (-32585090495598140253226920151/11258999068426240000000000000000000), (25793719626854891640604916517/5629499534213120000000000000000000), (2939413106822493772274345131/11258999068426240000000000000000000), (-145445229964236895376955111/2251799813685248000000000000000000), (-5782072890884155899981967/1125899906842624000000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial129.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial129.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial129.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 11044531407532630739913927131104905), (Int.ofNat 994360034982561126609031480889035), (Int.negOfNat 11892278562550166032893199828352), (Int.negOfNat 7093892517163913510928851108845), (Int.ofNat 1025648748558796609800735033951), (Int.ofNat 445284604377866954842772160638), (Int.negOfNat 4221551940288590802239749186), (Int.negOfNat 10092510281463402467653414231), (Int.negOfNat 411414071790646852769302475), (Int.ofNat 97266635022390283634959180), (Int.ofNat 6242235355329650612212439), (Int.negOfNat 534548861749423715009343), (Int.negOfNat 45188238377883002669396), (Int.ofNat 1892236075455358658468), (Int.ofNat 207603753031290848664), (Int.negOfNat 4096924564679723322), (Int.negOfNat 987831660940955585), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(2208906281506526147982785426220981/2251799813685248000000000000000000), (198872006996512225321806296177807/2251799813685248000000000000000000), (-92908426269923172131978123659/87960930222080000000000000000000), (-1418778503432782702185770221769/2251799813685248000000000000000000), (1025648748558796609800735033951/11258999068426240000000000000000000), (222642302188933477421386080319/5629499534213120000000000000000000), (-2110775970144295401119874593/5629499534213120000000000000000000), (-10092510281463402467653414231/11258999068426240000000000000000000), (-16456562871625874110772099/450359962737049600000000000000000), (4863331751119514181747959/562949953421312000000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial129.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial129.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial129.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 12957978299236802731828721983818382), (Int.ofNat 924603522375117068800069482636707), (Int.negOfNat 2247505459759640469355678184577), (Int.ofNat 12449988870679460202617895804452), (Int.ofNat 2387173506485087748867420168527), (Int.negOfNat 410600155879436785999808200652), (Int.negOfNat 115273678613623587713952862234), (Int.negOfNat 355499298969463825744341412), (Int.ofNat 1511745498638622369495134302), (Int.ofNat 57639329215406690829930655), (Int.negOfNat 10523490659320794377445230), (Int.negOfNat 603123985646870603033863), (Int.ofNat 46837517117216404830090), (Int.ofNat 3454661098726383016743), (Int.negOfNat 143612779457517236639), (Int.negOfNat 13923028627410776044), (Int.ofNat 424071158749119471), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(6478989149618401365914360991909191/5629499534213120000000000000000000), (924603522375117068800069482636707/11258999068426240000000000000000000), (-2247505459759640469355678184577/11258999068426240000000000000000000), (3112497217669865050654473951113/2814749767106560000000000000000000), (2387173506485087748867420168527/11258999068426240000000000000000000), (-102650038969859196499952050163/2814749767106560000000000000000000), (-57636839306811793856976431117/5629499534213120000000000000000000), (-88874824742365956436085353/2814749767106560000000000000000000), (755872749319311184747567151/5629499534213120000000000000000000), (11527865843081338165986131/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial129.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial129.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial129.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 14915832509173955853931567615878372), (Int.ofNat 1087884566580695977527116294275475), (Int.ofNat 71832088906061312766141526699225), (Int.negOfNat 681541111602424464147104176927), (Int.negOfNat 6969126747726786678095616569448), (Int.negOfNat 1127277764660941497665203984905), (Int.ofNat 46909162700180304331696068262), (Int.ofNat 20328670831396752203305954989), (Int.ofNat 334709497000220309773598050), (Int.negOfNat 176458223261753733773519152), (Int.negOfNat 6882085433621411747220120), (Int.ofNat 955874823925047220182659), (Int.ofNat 51024915283969430651349), (Int.negOfNat 3592416704323272095052), (Int.negOfNat 236059892046743377274), (Int.ofNat 9871844032321454332), (Int.ofNat 1036752334440723666), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(3728958127293488963482891903969593/2814749767106560000000000000000000), (43515382663227839101084651771019/450359962737049600000000000000000), (2873283556242452510645661067969/450359962737049600000000000000000), (-681541111602424464147104176927/11258999068426240000000000000000000), (-871140843465848334761952071181/1407374883553280000000000000000000), (-225455552932188299533040796981/2251799813685248000000000000000000), (23454581350090152165848034131/5629499534213120000000000000000000), (20328670831396752203305954989/11258999068426240000000000000000000), (6694189940004406195471961/225179981368524800000000000000000), (-11028638953859608360844947/703687441776640000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial129.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial129.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial129.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 17231493434400015067949218955264504), (Int.ofNat 1071866707548477632257591144362039), (Int.negOfNat 165042242478214349534769921508228), (Int.negOfNat 83045775056786116094199768974761), (Int.negOfNat 10119108443483213507626907888033), (Int.ofNat 914001181182487816097473051179), (Int.ofNat 243504244836744795934445359468), (Int.negOfNat 470275489759845619000231507), (Int.negOfNat 2597298915828865755905955136), (Int.negOfNat 66058628855931671635206312), (Int.ofNat 16903781844746071786552839), (Int.ofNat 675221566558038317153980), (Int.negOfNat 75507209596469546649479), (Int.negOfNat 3772569712119912434035), (Int.ofNat 246888618428730171541), (Int.ofNat 14502929410517557254), (Int.negOfNat 670433195006177361), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(2153936679300001883493652369408063/1407374883553280000000000000000000), (1071866707548477632257591144362039/11258999068426240000000000000000000), (-41260560619553587383692480377057/2814749767106560000000000000000000), (-83045775056786116094199768974761/11258999068426240000000000000000000), (-10119108443483213507626907888033/11258999068426240000000000000000000), (914001181182487816097473051179/11258999068426240000000000000000000), (60876061209186198983611339867/2814749767106560000000000000000000), (-470275489759845619000231507/11258999068426240000000000000000000), (-40582795559826027436030549/175921860444160000000000000000000), (-8257328606991458954400789/1407374883553280000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial129.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial129.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial129.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 17932877684303745813202071867003410), (Int.negOfNat 791720512381855478435216390177583), (Int.negOfNat 779681022194747436554232877421903), (Int.negOfNat 93472000431379565346887246957595), (Int.ofNat 10569204362779446532750794074732), (Int.ofNat 2647455086735713812656496001570), (Int.negOfNat 36662475794282221567125260995), (Int.negOfNat 33946826385205135497127678487), (Int.negOfNat 548918682656692619784362287), (Int.ofNat 263832154480372320657168721), (Int.ofNat 8133293080829928713339021), (Int.negOfNat 1392094302055857152518587), (Int.negOfNat 55358781185175938562408), (Int.ofNat 5333154540031441556909), (Int.ofNat 245275774792298560093), (Int.negOfNat 15424618060582346602), (Int.negOfNat 1003552329188139117), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(1793287768430374581320207186700341/1125899906842624000000000000000000), (-791720512381855478435216390177583/11258999068426240000000000000000000), (-779681022194747436554232877421903/11258999068426240000000000000000000), (-18694400086275913069377449391519/2251799813685248000000000000000000), (2642301090694861633187698518683/2814749767106560000000000000000000), (264745508673571381265649600157/1125899906842624000000000000000000), (-7332495158856444313425052199/2251799813685248000000000000000000), (-33946826385205135497127678487/11258999068426240000000000000000000), (-548918682656692619784362287/11258999068426240000000000000000000), (263832154480372320657168721/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial129.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial129.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial129.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 12730070664434723992663613317644791), (Int.negOfNat 4504274347423658879929223291954880), (Int.negOfNat 906383216782713364460036745737826), (Int.ofNat 72599921075780562362943184102056), (Int.ofNat 25833527664770046464909700717759), (Int.negOfNat 337289407046027653038406905152), (Int.negOfNat 391313210087179055196585230326), (Int.negOfNat 5018749479462527717464016083), (Int.ofNat 3640031139282670552202589942), (Int.ofNat 93686985345457713316984532), (Int.negOfNat 22761666064398831562123718), (Int.negOfNat 756641421611001461261872), (Int.ofNat 101961905564203074322915), (Int.ofNat 3882519067576539315245), (Int.negOfNat 342548054862669823365), (Int.negOfNat 14602507523435209398), (Int.ofNat 916795231263235251), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(12730070664434723992663613317644791/11258999068426240000000000000000000), (-14075857335698933999778822787359/35184372088832000000000000000000), (-453191608391356682230018372868913/5629499534213120000000000000000000), (9074990134472570295367898012757/1407374883553280000000000000000000), (25833527664770046464909700717759/11258999068426240000000000000000000), (-5270146985094182078725107893/175921860444160000000000000000000), (-195656605043589527598292615163/5629499534213120000000000000000000), (-5018749479462527717464016083/11258999068426240000000000000000000), (1820015569641335276101294971/5629499534213120000000000000000000), (23421746336364428329246133/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial129.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial129.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial129.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 1054600608871857413522391870486493), (Int.negOfNat 6532478110661781713331360665985793), (Int.ofNat 31628548017011579735797387519508), (Int.ofNat 207013314388032894316472093621868), (Int.ofNat 1707252482856745429762291871606), (Int.negOfNat 3829709254682794451241209825078), (Int.negOfNat 72009530396100696252000447527), (Int.ofNat 43708684506509917175025745634), (Int.ofNat 1123664385703136076684262499), (Int.negOfNat 329168249884764373041536489), (Int.negOfNat 9934540952480794423634743), (Int.ofNat 1739861860724817518136265), (Int.ofNat 57570486218937761787045), (Int.negOfNat 6791547225468883747403), (Int.negOfNat 237748535522261347692), (Int.ofNat 19999705242141480002), (Int.ofNat 970352323935554568), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1054600608871857413522391870486493/11258999068426240000000000000000000), (-6532478110661781713331360665985793/11258999068426240000000000000000000), (7907137004252894933949346879877/2814749767106560000000000000000000), (51753328597008223579118023405467/2814749767106560000000000000000000), (853626241428372714881145935803/5629499534213120000000000000000000), (-1914854627341397225620604912539/5629499534213120000000000000000000), (-72009530396100696252000447527/11258999068426240000000000000000000), (21854342253254958587512872817/5629499534213120000000000000000000), (1123664385703136076684262499/11258999068426240000000000000000000), (-329168249884764373041536489/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial129.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial129.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial129.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 10321870768829121935707897927857348), (Int.negOfNat 4167431153055399682425559887406196), (Int.ofNat 1020829786353940573980674824642681), (Int.ofNat 80607557356017649623091282539002), (Int.negOfNat 28796083815437619965522346997614), (Int.negOfNat 1207740406636015865169745821196), (Int.ofNat 438690561839263103683533701421), (Int.ofNat 14582095315792660749246547503), (Int.negOfNat 4143802334585429865695549693), (Int.negOfNat 129402937333248188748000374), (Int.ofNat 26399239815490607624005398), (Int.ofNat 815621022835284448939398), (Int.negOfNat 120830362857611400849679), (Int.negOfNat 3728585371779959397699), (Int.ofNat 417889601723088940150), (Int.ofNat 12576901100322422785), (Int.negOfNat 1152090599102764958), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-2580467692207280483926974481964337/2814749767106560000000000000000000), (-1041857788263849920606389971851549/2814749767106560000000000000000000), (1020829786353940573980674824642681/11258999068426240000000000000000000), (40303778678008824811545641269501/5629499534213120000000000000000000), (-14398041907718809982761173498807/5629499534213120000000000000000000), (-301935101659003966292436455299/2814749767106560000000000000000000), (438690561839263103683533701421/11258999068426240000000000000000000), (14582095315792660749246547503/11258999068426240000000000000000000), (-4143802334585429865695549693/11258999068426240000000000000000000), (-64701468666624094374000187/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial129.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial129.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial129.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial129.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial129.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial129.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial129.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial129.reflect := by
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

end Bin129
end
end ErdosOverlap.OuterNumerics
