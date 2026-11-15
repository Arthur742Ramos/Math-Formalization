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

/-! # Exact integer weighted outer models for source bin 148

Generated proposals; the generator is not trusted by any theorem.
-/

namespace ErdosOverlap.OuterNumerics
open Numerics MeasureTheory Set
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Bin148

def weightDenominator : ℤ := (Int.ofNat 20000000000000000000)

def cosineIntegerTerms : List IntTrigTerm := [⟨(731972361809/125000000000), (Int.negOfNat 4967440748650992000)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 4904881896188747400)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 4348066629892609000)⟩, ⟨(15615577889447/1000000000000), (Int.negOfNat 2969762210609017600)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 1915697726413849800)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 1092615382299757200)⟩, ⟨(2859108040201/125000000000), (Int.negOfNat 645541287743426600)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 989725043002094300)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 342094187363846260)⟩]

theorem cosineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator cosineIntegerTerms) Outer180.polynomial148.cosineTerms = true := by
  decide +kernel

theorem cosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial148.cosineTerms :=
  trigTermListCheck_sound cosineIntegerTerms_checked

def sineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.ofNat 19339650959167994000)⟩, ⟨(314159265359/50000000000), (Int.ofNat 4524557512813867600)⟩, ⟨(9424777960769/1000000000000), (Int.ofNat 2952335246326801600)⟩, ⟨(12566370614359/1000000000000), (Int.ofNat 1859804715206452000)⟩, ⟨(15707963267949/1000000000000), (Int.ofNat 596547204148565680)⟩, ⟨(18849555921539/1000000000000), (Int.ofNat 102152780329574840)⟩, ⟨(21991148575129/1000000000000), (Int.ofNat 233263498517282200)⟩, ⟨(12566370614359/500000000000), (Int.negOfNat 209582139825227020)⟩, ⟨(7068583470577/250000000000), (Int.ofNat 6085778219275897)⟩]

theorem sineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator sineIntegerTerms) Outer180.polynomial148.sineTerms = true := by
  decide +kernel

theorem sineIntegerTerms_exact : decodeTerms weightDenominator sineIntegerTerms = Outer180.polynomial148.sineTerms :=
  trigTermListCheck_sound sineIntegerTerms_checked

def reflectedSineIntegerTerms : List IntTrigTerm := [⟨(314159265359/100000000000), (Int.negOfNat 19339650959167994000)⟩, ⟨(314159265359/50000000000), (Int.negOfNat 4524557512813867600)⟩, ⟨(9424777960769/1000000000000), (Int.negOfNat 2952335246326801600)⟩, ⟨(12566370614359/1000000000000), (Int.negOfNat 1859804715206452000)⟩, ⟨(15707963267949/1000000000000), (Int.negOfNat 596547204148565680)⟩, ⟨(18849555921539/1000000000000), (Int.negOfNat 102152780329574840)⟩, ⟨(21991148575129/1000000000000), (Int.negOfNat 233263498517282200)⟩, ⟨(12566370614359/500000000000), (Int.ofNat 209582139825227020)⟩, ⟨(7068583470577/250000000000), (Int.negOfNat 6085778219275897)⟩]

theorem reflectedSineIntegerTerms_checked : trigTermListCheck (decodeTerms weightDenominator reflectedSineIntegerTerms) Outer180.polynomial148.reflect.sineTerms = true := by
  decide +kernel

theorem reflectedSineIntegerTerms_exact : decodeTerms weightDenominator reflectedSineIntegerTerms = Outer180.polynomial148.reflect.sineTerms :=
  trigTermListCheck_sound reflectedSineIntegerTerms_checked

theorem reflectedCosineIntegerTerms_exact : decodeTerms weightDenominator cosineIntegerTerms = Outer180.polynomial148.reflect.cosineTerms :=
  cosineIntegerTerms_exact

def positiveCell00Integer : List ℤ := [(Int.negOfNat 17305922287423816757910747317678331), (Int.ofNat 9788092796890799050506994849275469), (Int.ofNat 1863722261690492352492320573098700), (Int.negOfNat 322754003129458248657229113076783), (Int.negOfNat 54584973502102207065381491590249), (Int.ofNat 6566444234223573084229904992343), (Int.ofNat 858322281237100281091160270253), (Int.negOfNat 81509922633326645027060554053), (Int.negOfNat 8415533464654061688577213968), (Int.ofNat 666937515939176654699053364), (Int.ofNat 55992647822983218596777153), (Int.negOfNat 3845501273552994005420318), (Int.negOfNat 268764766592930973327159), (Int.ofNat 16445941192847731046279), (Int.ofNat 973636328438384891915), (Int.negOfNat 53811295997916123965), (Int.negOfNat 2873263450330897238), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms sineIntegerTerms positiveCell00Integer = true := by
  decide +kernel

def positiveCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-17305922287423816757910747317678331/22517998136852480000000000000000000), (9788092796890799050506994849275469/22517998136852480000000000000000000), (18637222616904923524923205730987/225179981368524800000000000000000), (-322754003129458248657229113076783/22517998136852480000000000000000000), (-54584973502102207065381491590249/22517998136852480000000000000000000), (6566444234223573084229904992343/22517998136852480000000000000000000), (858322281237100281091160270253/22517998136852480000000000000000000), (-81509922633326645027060554053/22517998136852480000000000000000000), (-525970841540878855536075873/1407374883553280000000000000000000), (166734378984794163674763341/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell00Integer = Outer180.polynomial148.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell00Integer_checked
  exact hi.symm

theorem positiveCell00_exact : positiveCell00.coefficients = (Outer180.polynomial148.compiledCoefficients basis00).take 10 := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_error : Outer180.polynomial148.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis00).drop 10) ≤ positiveCell00.error := by
  rw [← positiveCell00_full_exact]
  decide +kernel

theorem positiveCell00_correct : positiveCell00.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell00 Outer180.polynomial148 basis00_correct
    (by decide +kernel) 10 positiveCell00_exact positiveCell00_error

def positiveCell01Integer : List ℤ := [(Int.ofNat 6522621927672726315778446286521177), (Int.ofNat 12269968477588596131774815373771318), (Int.negOfNat 717788769857423424596651281711543), (Int.negOfNat 415912422681082762063194289945487), (Int.ofNat 33582622008449817311351416750075), (Int.ofNat 7910670043652570237624784214900), (Int.negOfNat 657580518025297895158980017017), (Int.negOfNat 91350306373182638123277777719), (Int.ofNat 7276212074099437323441527099), (Int.ofNat 697929737439335659040577469), (Int.negOfNat 52543644201687415051668308), (Int.negOfNat 3765870572365199217165385), (Int.ofNat 269045371220301164701655), (Int.ofNat 15095049013164781812423), (Int.negOfNat 1032547505972013572152), (Int.negOfNat 46288930208164746157), (Int.ofNat 3199145327600894688), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms sineIntegerTerms positiveCell01Integer = true := by
  decide +kernel

def positiveCell01 : OuterCellModel := ⟨(3/32), (1/32), [(6522621927672726315778446286521177/22517998136852480000000000000000000), (6134984238794298065887407686885659/11258999068426240000000000000000000), (-717788769857423424596651281711543/22517998136852480000000000000000000), (-415912422681082762063194289945487/22517998136852480000000000000000000), (1343304880337992692454056670003/900719925474099200000000000000000), (79106700436525702376247842149/225179981368524800000000000000000), (-657580518025297895158980017017/22517998136852480000000000000000000), (-91350306373182638123277777719/22517998136852480000000000000000000), (7276212074099437323441527099/22517998136852480000000000000000000), (697929737439335659040577469/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell01Integer = Outer180.polynomial148.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell01Integer_checked
  exact hi.symm

theorem positiveCell01_exact : positiveCell01.coefficients = (Outer180.polynomial148.compiledCoefficients basis01).take 10 := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_error : Outer180.polynomial148.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis01).drop 10) ≤ positiveCell01.error := by
  rw [← positiveCell01_full_exact]
  decide +kernel

theorem positiveCell01_correct : positiveCell01.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell01 Outer180.polynomial148 basis01_correct
    (by decide +kernel) 10 positiveCell01_exact positiveCell01_error

def positiveCell02Integer : List ℤ := [(Int.ofNat 25602949563726007184060350991426828), (Int.ofNat 5956936153981812469206820432935005), (Int.negOfNat 1978069645224869270668800320477088), (Int.ofNat 28665088064543273301055636771389), (Int.ofNat 57793015860959294187165373831740), (Int.negOfNat 3490936099006302995174403198512), (Int.negOfNat 866420463959347485855753849516), (Int.ofNat 63211630105784331494661909673), (Int.ofNat 7937198188241158126846233652), (Int.negOfNat 611239201567538628667389887), (Int.negOfNat 49062531333451338468961618), (Int.ofNat 3864964632794141804304617), (Int.ofNat 218614391829717317605360), (Int.negOfNat 17510612493437151669620), (Int.negOfNat 736253782529237012915), (Int.ofNat 59933270424656261003), (Int.ofNat 1840895110020082561), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms sineIntegerTerms positiveCell02Integer = true := by
  decide +kernel

def positiveCell02 : OuterCellModel := ⟨(5/32), (1/32), [(6400737390931501796015087747856707/5629499534213120000000000000000000), (1191387230796362493841364086587001/4503599627370496000000000000000000), (-61814676413277164708400010014909/703687441776640000000000000000000), (28665088064543273301055636771389/22517998136852480000000000000000000), (2889650793047964709358268691587/1125899906842624000000000000000000), (-218183506187893937198400199907/1407374883553280000000000000000000), (-216605115989836871463938462379/5629499534213120000000000000000000), (63211630105784331494661909673/22517998136852480000000000000000000), (1984299547060289531711558413/5629499534213120000000000000000000), (-611239201567538628667389887/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell02Integer = Outer180.polynomial148.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell02Integer_checked
  exact hi.symm

theorem positiveCell02_exact : positiveCell02.coefficients = (Outer180.polynomial148.compiledCoefficients basis02).take 10 := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_error : Outer180.polynomial148.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis02).drop 10) ≤ positiveCell02.error := by
  rw [← positiveCell02_full_exact]
  decide +kernel

theorem positiveCell02_correct : positiveCell02.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell02 Outer180.polynomial148 basis02_correct
    (by decide +kernel) 10 positiveCell02_exact positiveCell02_error

def positiveCell03Integer : List ℤ := [(Int.ofNat 30601159858560831827971354196713061), (Int.negOfNat 172777567293694968926849715289346), (Int.negOfNat 852822056275855248847628449565556), (Int.ofNat 258509168691669447887980686766678), (Int.negOfNat 5452598999862950149528485491509), (Int.negOfNat 6520123744288162706702533774320), (Int.ofNat 397726117884757217470545722767), (Int.ofNat 78895966714865762105641294182), (Int.negOfNat 5872258936555739237437785252), (Int.negOfNat 583965486499058646414791936), (Int.ofNat 48148492844445243768912831), (Int.ofNat 2947882033840278306698327), (Int.negOfNat 264210689253521581150368), (Int.negOfNat 10848610073090803014814), (Int.ofNat 1055753390202680679728), (Int.ofNat 29326197665200576902), (Int.negOfNat 3180887992943066997), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms sineIntegerTerms positiveCell03Integer = true := by
  decide +kernel

def positiveCell03 : OuterCellModel := ⟨(7/32), (1/32), [(30601159858560831827971354196713061/22517998136852480000000000000000000), (-86388783646847484463424857644673/11258999068426240000000000000000000), (-213205514068963812211907112391389/5629499534213120000000000000000000), (129254584345834723943990343383339/11258999068426240000000000000000000), (-5452598999862950149528485491509/22517998136852480000000000000000000), (-81501546803602033833781672179/281474976710656000000000000000000), (397726117884757217470545722767/22517998136852480000000000000000000), (39447983357432881052820647091/11258999068426240000000000000000000), (-1468064734138934809359446313/5629499534213120000000000000000000), (-2281115181636947837557781/87960930222080000000000000000000)], (1/100000000)⟩

theorem positiveCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell03Integer = Outer180.polynomial148.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell03Integer_checked
  exact hi.symm

theorem positiveCell03_exact : positiveCell03.coefficients = (Outer180.polynomial148.compiledCoefficients basis03).take 10 := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_error : Outer180.polynomial148.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis03).drop 10) ≤ positiveCell03.error := by
  rw [← positiveCell03_full_exact]
  decide +kernel

theorem positiveCell03_correct : positiveCell03.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell03 Outer180.polynomial148 basis03_correct
    (by decide +kernel) 10 positiveCell03_exact positiveCell03_error

def positiveCell04Integer : List ℤ := [(Int.ofNat 28650309359594320691879082483072041), (Int.negOfNat 1073425896260856552517808466575712), (Int.ofNat 181637544477911660758684799669253), (Int.ofNat 49070831538680725343543731268554), (Int.negOfNat 32895552016849006644033296230866), (Int.ofNat 1518024798152945659964334454415), (Int.ofNat 640367859914577229186459578586), (Int.negOfNat 44756822245630887811204842248), (Int.negOfNat 6148018608799142638033530986), (Int.ofNat 510906535690199735419196202), (Int.ofNat 36540836470999135704504559), (Int.negOfNat 3509086028747853656043565), (Int.negOfNat 148851928183214529591679), (Int.ofNat 16667037733246788630895), (Int.ofNat 440024512646826391136), (Int.negOfNat 59589124224029961859), (Int.negOfNat 814612547928543781), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms sineIntegerTerms positiveCell04Integer = true := by
  decide +kernel

def positiveCell04 : OuterCellModel := ⟨(9/32), (1/32), [(28650309359594320691879082483072041/22517998136852480000000000000000000), (-33544559258151767266181514580491/703687441776640000000000000000000), (181637544477911660758684799669253/22517998136852480000000000000000000), (24535415769340362671771865634277/11258999068426240000000000000000000), (-16447776008424503322016648115433/11258999068426240000000000000000000), (303604959630589131992866890883/4503599627370496000000000000000000), (320183929957288614593229789293/11258999068426240000000000000000000), (-5594602780703860976400605281/2814749767106560000000000000000000), (-3074009304399571319016765493/11258999068426240000000000000000000), (255453267845099867709598101/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell04Integer = Outer180.polynomial148.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell04Integer_checked
  exact hi.symm

theorem positiveCell04_exact : positiveCell04.coefficients = (Outer180.polynomial148.compiledCoefficients basis04).take 10 := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_error : Outer180.polynomial148.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis04).drop 10) ≤ positiveCell04.error := by
  rw [← positiveCell04_full_exact]
  decide +kernel

theorem positiveCell04_correct : positiveCell04.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell04 Outer180.polynomial148 basis04_correct
    (by decide +kernel) 10 positiveCell04_exact positiveCell04_error

def positiveCell05Integer : List ℤ := [(Int.ofNat 27178794483014642242874772247984947), (Int.negOfNat 591315462544277653622490083412350), (Int.negOfNat 76725171852843697789895672786614), (Int.negOfNat 83846797705205262007567081573563), (Int.ofNat 3679458181308060293796710290713), (Int.ofNat 3900116924681243802799747800085), (Int.negOfNat 265535468995315733736047389743), (Int.negOfNat 54851371961101103211381351534), (Int.ofNat 4536152899356884078775790875), (Int.ofNat 407368556431717392668653892), (Int.negOfNat 40517677845465362515958055), (Int.negOfNat 1892359654455168351002409), (Int.ofNat 233886028076689147632704), (Int.ofNat 5901008176741732465442), (Int.negOfNat 964119313210172992069), (Int.negOfNat 12446533599637659667), (Int.ofNat 3162630658285239306), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms sineIntegerTerms positiveCell05Integer = true := by
  decide +kernel

def positiveCell05 : OuterCellModel := ⟨(11/32), (1/32), [(27178794483014642242874772247984947/22517998136852480000000000000000000), (-11826309250885553072449801668247/450359962737049600000000000000000), (-38362585926421848894947836393307/11258999068426240000000000000000000), (-83846797705205262007567081573563/22517998136852480000000000000000000), (3679458181308060293796710290713/22517998136852480000000000000000000), (780023384936248760559949560017/4503599627370496000000000000000000), (-265535468995315733736047389743/22517998136852480000000000000000000), (-27425685980550551605690675767/11258999068426240000000000000000000), (36289223194855072630206327/180143985094819840000000000000000), (101842139107929348167163473/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell05Integer = Outer180.polynomial148.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell05Integer_checked
  exact hi.symm

theorem positiveCell05_exact : positiveCell05.coefficients = (Outer180.polynomial148.compiledCoefficients basis05).take 10 := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_error : Outer180.polynomial148.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis05).drop 10) ≤ positiveCell05.error := by
  rw [← positiveCell05_full_exact]
  decide +kernel

theorem positiveCell05_correct : positiveCell05.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell05 Outer180.polynomial148 basis05_correct
    (by decide +kernel) 10 positiveCell05_exact positiveCell05_error

def positiveCell06Integer : List ℤ := [(Int.ofNat 25179473768268026809643635302367736), (Int.negOfNat 1544821149441604089017445377218345), (Int.negOfNat 270575968825583933872463960174216), (Int.ofNat 38034961276856584226045218384992), (Int.ofNat 17519423596260988967058110183954), (Int.negOfNat 1398404951395944808604734732460), (Int.negOfNat 401390988599547429145057339219), (Int.ofNat 33648753492176207877836082342), (Int.ofNat 3987377090649562172447652367), (Int.negOfNat 401574395675389801287202430), (Int.negOfNat 22037321767825072783768020), (Int.ofNat 2886695921323884592848648), (Int.ofNat 73413085996784293785465), (Int.negOfNat 14141234986929359919273), (Int.negOfNat 133361418365544482299), (Int.ofNat 51769724544821862709), (Int.negOfNat 211670014162994999), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms sineIntegerTerms positiveCell06Integer = true := by
  decide +kernel

def positiveCell06 : OuterCellModel := ⟨(13/32), (1/32), [(3147434221033503351205454412795967/2814749767106560000000000000000000), (-308964229888320817803489075443669/4503599627370496000000000000000000), (-33821996103197991734057995021777/2814749767106560000000000000000000), (1188592539901768257063913074531/703687441776640000000000000000000), (8759711798130494483529055091977/11258999068426240000000000000000000), (-69920247569797240430236736623/1125899906842624000000000000000000), (-401390988599547429145057339219/22517998136852480000000000000000000), (16824376746088103938918041171/11258999068426240000000000000000000), (3987377090649562172447652367/22517998136852480000000000000000000), (-40157439567538980128720243/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell06Integer = Outer180.polynomial148.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell06Integer_checked
  exact hi.symm

theorem positiveCell06_exact : positiveCell06.coefficients = (Outer180.polynomial148.compiledCoefficients basis06).take 10 := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_error : Outer180.polynomial148.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis06).drop 10) ≤ positiveCell06.error := by
  rw [← positiveCell06_full_exact]
  decide +kernel

theorem positiveCell06_correct : positiveCell06.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell06 Outer180.polynomial148 basis06_correct
    (by decide +kernel) 10 positiveCell06_exact positiveCell06_error

def positiveCell07Integer : List ℤ := [(Int.ofNat 21526785813036861710608687654698506), (Int.negOfNat 1780870179264533842490707203552373), (Int.ofNat 197630733786296303205219913098081), (Int.ofNat 81648972648753643791656314504149), (Int.negOfNat 8449840359821401620729335974196), (Int.negOfNat 2501388089820699925774905111186), (Int.ofNat 216309572900329824108818136979), (Int.ofNat 34035257025648353198956522261), (Int.negOfNat 3383956265111382281187559225), (Int.negOfNat 233011034582692920828070525), (Int.ofNat 30892053849468950193124199), (Int.ofNat 851665528741201621685123), (Int.negOfNat 183227652644439501590726), (Int.negOfNat 1182091963517290570963), (Int.ofNat 766903210686361656804), (Int.negOfNat 4642547735143272468), (Int.negOfNat 2802279136263565355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms sineIntegerTerms positiveCell07Integer = true := by
  decide +kernel

def positiveCell07 : OuterCellModel := ⟨(15/32), (1/32), [(10763392906518430855304343827349253/11258999068426240000000000000000000), (-1780870179264533842490707203552373/22517998136852480000000000000000000), (197630733786296303205219913098081/22517998136852480000000000000000000), (81648972648753643791656314504149/22517998136852480000000000000000000), (-2112460089955350405182333993549/5629499534213120000000000000000000), (-1250694044910349962887452555593/11258999068426240000000000000000000), (216309572900329824108818136979/22517998136852480000000000000000000), (34035257025648353198956522261/22517998136852480000000000000000000), (-135358250604455291247502369/900719925474099200000000000000000), (-9320441383307716833122821/900719925474099200000000000000000)], (1/100000000)⟩

theorem positiveCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell07Integer = Outer180.polynomial148.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell07Integer_checked
  exact hi.symm

theorem positiveCell07_exact : positiveCell07.coefficients = (Outer180.polynomial148.compiledCoefficients basis07).take 10 := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_error : Outer180.polynomial148.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis07).drop 10) ≤ positiveCell07.error := by
  rw [← positiveCell07_full_exact]
  decide +kernel

theorem positiveCell07_correct : positiveCell07.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell07 Outer180.polynomial148 basis07_correct
    (by decide +kernel) 10 positiveCell07_exact positiveCell07_error

def positiveCell08Integer : List ℤ := [(Int.ofNat 19210765667113494706961749286296363), (Int.negOfNat 428125026098479728512609644634071), (Int.ofNat 352633145249188937105712378343062), (Int.negOfNat 39162669059888763317925376656873), (Int.negOfNat 15256534839538974299335735932045), (Int.ofNat 1223611933923019125538568087283), (Int.ofNat 263071941062851435263191677379), (Int.negOfNat 23964174504168346866481965381), (Int.negOfNat 2256168280919343152649608425), (Int.ofNat 280923015078514952412372525), (Int.ofNat 9368223183288745737276999), (Int.negOfNat 2058247595249447445135683), (Int.negOfNat 7517659566754885202446), (Int.ofNat 10265065516425803417723), (Int.negOfNat 126235959899622873276), (Int.negOfNat 37917585098900312092), (Int.ofNat 883686832452135725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms sineIntegerTerms positiveCell08Integer = true := by
  decide +kernel

def positiveCell08 : OuterCellModel := ⟨(17/32), (1/32), [(19210765667113494706961749286296363/22517998136852480000000000000000000), (-428125026098479728512609644634071/22517998136852480000000000000000000), (176316572624594468552856189171531/11258999068426240000000000000000000), (-39162669059888763317925376656873/22517998136852480000000000000000000), (-3051306967907794859867147186409/4503599627370496000000000000000000), (1223611933923019125538568087283/22517998136852480000000000000000000), (263071941062851435263191677379/22517998136852480000000000000000000), (-23964174504168346866481965381/22517998136852480000000000000000000), (-90246731236773726105984337/900719925474099200000000000000000), (11236920603140598096494901/900719925474099200000000000000000)], (1/100000000)⟩

theorem positiveCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell08Integer = Outer180.polynomial148.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell08Integer_checked
  exact hi.symm

theorem positiveCell08_exact : positiveCell08.coefficients = (Outer180.polynomial148.compiledCoefficients basis08).take 10 := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_error : Outer180.polynomial148.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis08).drop 10) ≤ positiveCell08.error := by
  rw [← positiveCell08_full_exact]
  decide +kernel

theorem positiveCell08_correct : positiveCell08.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell08 Outer180.polynomial148 basis08_correct
    (by decide +kernel) 10 positiveCell08_exact positiveCell08_error

def positiveCell09Integer : List ℤ := [(Int.ofNat 19260138739140295622819740636625274), (Int.ofNat 160271278873357488766626846004671), (Int.negOfNat 106274953650566037258126697973429), (Int.negOfNat 86072752143435929939067689231400), (Int.ofNat 4701254138913567504879919144728), (Int.ofNat 1940135498015311168559911338220), (Int.negOfNat 133661760408568443277287583499), (Int.negOfNat 20657103494218282354127063982), (Int.ofNat 2082040281906177658335161167), (Int.ofNat 101433232019770231120873990), (Int.negOfNat 19374166755047212316240580), (Int.negOfNat 36713838187013049908808), (Int.ofNat 117219274050222674274465), (Int.negOfNat 2473236131278036201087), (Int.negOfNat 497892067722544920379), (Int.ofNat 16883585082306208531), (Int.ofNat 2105919205097321041), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms sineIntegerTerms positiveCell09Integer = true := by
  decide +kernel

def positiveCell09 : OuterCellModel := ⟨(19/32), (1/32), [(9630069369570147811409870318312637/11258999068426240000000000000000000), (160271278873357488766626846004671/22517998136852480000000000000000000), (-106274953650566037258126697973429/22517998136852480000000000000000000), (-430363760717179649695338446157/112589990684262400000000000000000), (587656767364195938109989893091/2814749767106560000000000000000000), (97006774900765558427995566911/1125899906842624000000000000000000), (-133661760408568443277287583499/22517998136852480000000000000000000), (-10328551747109141177063531991/11258999068426240000000000000000000), (2082040281906177658335161167/22517998136852480000000000000000000), (10143323201977023112087399/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell09Integer = Outer180.polynomial148.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell09Integer_checked
  exact hi.symm

theorem positiveCell09_exact : positiveCell09.coefficients = (Outer180.polynomial148.compiledCoefficients basis09).take 10 := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_error : Outer180.polynomial148.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis09).drop 10) ≤ positiveCell09.error := by
  rw [← positiveCell09_full_exact]
  decide +kernel

theorem positiveCell09_correct : positiveCell09.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell09 Outer180.polynomial148 basis09_correct
    (by decide +kernel) 10 positiveCell09_exact positiveCell09_error

def positiveCell10Integer : List ℤ := [(Int.ofNat 18593670879539740413270961252853197), (Int.negOfNat 1024699230478652518267128717858990), (Int.negOfNat 396649368299964159105195705506851), (Int.ofNat 178170472698088651901387190548), (Int.ofNat 12791334450883825760828910204645), (Int.negOfNat 408455869742140583827056954725), (Int.negOfNat 181089700426539078840797935583), (Int.ofNat 10984639982983946013830175174), (Int.ofNat 1120873314476731563513336155), (Int.negOfNat 140829250432543948328996452), (Int.negOfNat 649626359077189851472935), (Int.ofNat 1077464179569117758049449), (Int.negOfNat 37609307069378279184736), (Int.negOfNat 5483992019843257465802), (Int.ofNat 300142180098357455691), (Int.ofNat 19412146568377594107), (Int.negOfNat 1207523685158154294), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms sineIntegerTerms positiveCell10Integer = true := by
  decide +kernel

def positiveCell10 : OuterCellModel := ⟨(21/32), (1/32), [(18593670879539740413270961252853197/22517998136852480000000000000000000), (-102469923047865251826712871785899/2251799813685248000000000000000000), (-396649368299964159105195705506851/22517998136852480000000000000000000), (44542618174522162975346797637/5629499534213120000000000000000000), (2558266890176765152165782040929/4503599627370496000000000000000000), (-16338234789685623353082278189/900719925474099200000000000000000), (-181089700426539078840797935583/22517998136852480000000000000000000), (5492319991491973006915087587/11258999068426240000000000000000000), (224174662895346312702667231/4503599627370496000000000000000000), (-35207312608135987082249113/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell10Integer = Outer180.polynomial148.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell10Integer_checked
  exact hi.symm

theorem positiveCell10_exact : positiveCell10.coefficients = (Outer180.polynomial148.compiledCoefficients basis10).take 10 := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_error : Outer180.polynomial148.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis10).drop 10) ≤ positiveCell10.error := by
  rw [← positiveCell10_full_exact]
  decide +kernel

theorem positiveCell10_correct : positiveCell10.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell10 Outer180.polynomial148 basis10_correct
    (by decide +kernel) 10 positiveCell10_exact positiveCell10_error

def positiveCell11Integer : List ℤ := [(Int.ofNat 15140723552553084632323145852130326), (Int.negOfNat 2261529592587801719256153546536482), (Int.negOfNat 155965408710265935899051974749145), (Int.ofNat 64629109567152723061692470349120), (Int.ofNat 1635006707365930497909131789717), (Int.negOfNat 1419227837010733476971099217258), (Int.ofNat 14182673472859949238940626046), (Int.ofNat 12304725142502957235728929208), (Int.negOfNat 563421025871711265815779986), (Int.negOfNat 22336035868218522448780962), (Int.ofNat 6520039617532711454470319), (Int.negOfNat 439369681846981345863835), (Int.negOfNat 42641149196899192400319), (Int.ofNat 4503682910464132544425), (Int.ofNat 184456300329491650856), (Int.negOfNat 23448865651843291381), (Int.negOfNat 1079636643005782261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms sineIntegerTerms positiveCell11Integer = true := by
  decide +kernel

def positiveCell11 : OuterCellModel := ⟨(23/32), (1/32), [(7570361776276542316161572926065163/11258999068426240000000000000000000), (-1130764796293900859628076773268241/11258999068426240000000000000000000), (-31193081742053187179810394949829/4503599627370496000000000000000000), (201965967397352259567788969841/70368744177664000000000000000000), (1635006707365930497909131789717/22517998136852480000000000000000000), (-709613918505366738485549608629/11258999068426240000000000000000000), (7091336736429974619470313023/11258999068426240000000000000000000), (1538090642812869654466116151/2814749767106560000000000000000000), (-281710512935855632907889993/11258999068426240000000000000000000), (-11168017934109261224390481/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell11Integer = Outer180.polynomial148.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell11Integer_checked
  exact hi.symm

theorem positiveCell11_exact : positiveCell11.coefficients = (Outer180.polynomial148.compiledCoefficients basis11).take 10 := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_error : Outer180.polynomial148.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis11).drop 10) ≤ positiveCell11.error := by
  rw [← positiveCell11_full_exact]
  decide +kernel

theorem positiveCell11_correct : positiveCell11.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell11 Outer180.polynomial148 basis11_correct
    (by decide +kernel) 10 positiveCell11_exact positiveCell11_error

def positiveCell12Integer : List ℤ := [(Int.ofNat 10493913090890278519780814820883553), (Int.negOfNat 2163425099291394475216225992983652), (Int.ofNat 168131849047131205737637092898007), (Int.ofNat 29048392684424963860720944972176), (Int.negOfNat 8916640594260673349520292957721), (Int.negOfNat 476018134249303294609379804580), (Int.ofNat 122295271175490762791040768470), (Int.ofNat 3468111203090727720539603938), (Int.negOfNat 508568987678275968609209532), (Int.negOfNat 8070044255647011785679264), (Int.negOfNat 3468058734312643826284449), (Int.negOfNat 43889773124480546513607), (Int.ofNat 56316044795866280603312), (Int.ofNat 397927942426665275694), (Int.negOfNat 359557120422542362072), (Int.negOfNat 714015148100500302), (Int.ofNat 1189266350500326603), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms sineIntegerTerms positiveCell12Integer = true := by
  decide +kernel

def positiveCell12 : OuterCellModel := ⟨(25/32), (1/32), [(10493913090890278519780814820883553/22517998136852480000000000000000000), (-540856274822848618804056498245913/5629499534213120000000000000000000), (168131849047131205737637092898007/22517998136852480000000000000000000), (1815524542776560241295059060761/1407374883553280000000000000000000), (-8916640594260673349520292957721/22517998136852480000000000000000000), (-23800906712465164730468990229/1125899906842624000000000000000000), (12229527117549076279104076847/2251799813685248000000000000000000), (1734055601545363860269801969/11258999068426240000000000000000000), (-127142246919568992152302383/5629499534213120000000000000000000), (-252188882988969118302477/703687441776640000000000000000000)], (1/100000000)⟩

theorem positiveCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell12Integer = Outer180.polynomial148.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell12Integer_checked
  exact hi.symm

theorem positiveCell12_exact : positiveCell12.coefficients = (Outer180.polynomial148.compiledCoefficients basis12).take 10 := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_error : Outer180.polynomial148.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis12).drop 10) ≤ positiveCell12.error := by
  rw [← positiveCell12_full_exact]
  decide +kernel

theorem positiveCell12_correct : positiveCell12.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell12 Outer180.polynomial148 basis12_correct
    (by decide +kernel) 10 positiveCell12_exact positiveCell12_error

def positiveCell13Integer : List ℤ := [(Int.ofNat 6922211677096560984757689945730026), (Int.negOfNat 1441252789526133115950360676674566), (Int.ofNat 121036821984350060903983957184978), (Int.negOfNat 40819740854586170739162800170840), (Int.negOfNat 6011716443026767599730750330734), (Int.ofNat 1014952648098601216888686620835), (Int.ofNat 99312771320813445312769012564), (Int.negOfNat 8073679340193594379766119913), (Int.negOfNat 939421823062014312001452428), (Int.negOfNat 4911045123811509484216833), (Int.ofNat 6147951001593632972789262), (Int.ofNat 542389774028004120132823), (Int.negOfNat 31100223227850591171360), (Int.negOfNat 4684678063880321778140), (Int.ofNat 127252941716500481405), (Int.ofNat 23805632205408323837), (Int.ofNat 53354080914243481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms sineIntegerTerms positiveCell13Integer = true := by
  decide +kernel

def positiveCell13 : OuterCellModel := ⟨(27/32), (1/32), [(3461105838548280492378844972865013/11258999068426240000000000000000000), (-720626394763066557975180338337283/11258999068426240000000000000000000), (60518410992175030451991978592489/11258999068426240000000000000000000), (-1020493521364654268479070004271/562949953421312000000000000000000), (-3005858221513383799865375165367/11258999068426240000000000000000000), (202990529619720243377737324167/4503599627370496000000000000000000), (24828192830203361328192253141/5629499534213120000000000000000000), (-8073679340193594379766119913/22517998136852480000000000000000000), (-234855455765503578000363107/5629499534213120000000000000000000), (-4911045123811509484216833/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell13Integer = Outer180.polynomial148.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell13Integer_checked
  exact hi.symm

theorem positiveCell13_exact : positiveCell13.coefficients = (Outer180.polynomial148.compiledCoefficients basis13).take 10 := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_error : Outer180.polynomial148.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis13).drop 10) ≤ positiveCell13.error := by
  rw [← positiveCell13_full_exact]
  decide +kernel

theorem positiveCell13_correct : positiveCell13.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell13 Outer180.polynomial148 basis13_correct
    (by decide +kernel) 10 positiveCell13_exact positiveCell13_error

def positiveCell14Integer : List ℤ := [(Int.ofNat 4138673304123847596717626404237574), (Int.negOfNat 1543606752190383091754629506348493), (Int.negOfNat 170179813153994383003179150013365), (Int.negOfNat 38543825668851140989486003383346), (Int.ofNat 6864066351058322055483000376387), (Int.ofNat 1158869806445062115489843758720), (Int.negOfNat 96274346478710025693638151857), (Int.negOfNat 16258154673938078684625641601), (Int.ofNat 396832321110895912737944619), (Int.ofNat 143573397233985582020825931), (Int.ofNat 3027575793252518607620932), (Int.negOfNat 902448432079748076352375), (Int.negOfNat 47791819595418997100825), (Int.ofNat 4295057406442844799097), (Int.ofNat 304419750672464321248), (Int.negOfNat 16532671045319956443), (Int.negOfNat 1171009015842498912), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms sineIntegerTerms positiveCell14Integer = true := by
  decide +kernel

def positiveCell14 : OuterCellModel := ⟨(29/32), (1/32), [(2069336652061923798358813202118787/11258999068426240000000000000000000), (-1543606752190383091754629506348493/22517998136852480000000000000000000), (-34035962630798876600635830002673/4503599627370496000000000000000000), (-19271912834425570494743001691673/11258999068426240000000000000000000), (6864066351058322055483000376387/22517998136852480000000000000000000), (1810734072570409555452880873/35184372088832000000000000000000), (-96274346478710025693638151857/22517998136852480000000000000000000), (-16258154673938078684625641601/22517998136852480000000000000000000), (396832321110895912737944619/22517998136852480000000000000000000), (143573397233985582020825931/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell14Integer = Outer180.polynomial148.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell14Integer_checked
  exact hi.symm

theorem positiveCell14_exact : positiveCell14.coefficients = (Outer180.polynomial148.compiledCoefficients basis14).take 10 := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_error : Outer180.polynomial148.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis14).drop 10) ≤ positiveCell14.error := by
  rw [← positiveCell14_full_exact]
  decide +kernel

theorem positiveCell14_correct : positiveCell14.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell14 Outer180.polynomial148 basis14_correct
    (by decide +kernel) 10 positiveCell14_exact positiveCell14_error

def positiveCell15Integer : List ℤ := [(Int.ofNat 201232429749129960856817920944872), (Int.negOfNat 2399518962746006121693632530328850), (Int.negOfNat 176647184642512147002926673903526), (Int.ofNat 39702461321092979691521062932465), (Int.ofNat 9145708424247131862938398366382), (Int.negOfNat 900326957726075321739896149146), (Int.negOfNat 187828574951891087816909802027), (Int.ofNat 8269584915735118678223199293), (Int.ofNat 2175481015120391336453048752), (Int.negOfNat 16380577238017398187383044), (Int.negOfNat 16743794668388817164503167), (Int.negOfNat 293303733148982499366922), (Int.ofNat 93350425422962932702721), (Int.ofNat 3090016954535832184761), (Int.negOfNat 392160106362895232525), (Int.negOfNat 16944751891785942075), (Int.ofNat 966842702958019402), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms sineIntegerTerms positiveCell15Integer = true := by
  decide +kernel

def positiveCell15 : OuterCellModel := ⟨(31/32), (1/32), [(25154053718641245107102240118109/2814749767106560000000000000000000), (-47990379254920122433872650606577/450359962737049600000000000000000), (-88323592321256073501463336951763/11258999068426240000000000000000000), (7940492264218595938304212586493/4503599627370496000000000000000000), (4572854212123565931469199183191/11258999068426240000000000000000000), (-450163478863037660869948074573/11258999068426240000000000000000000), (-187828574951891087816909802027/22517998136852480000000000000000000), (8269584915735118678223199293/22517998136852480000000000000000000), (135967563445024458528315547/1407374883553280000000000000000000), (-4095144309504349546845761/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell15Integer = Outer180.polynomial148.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell15Integer_checked
  exact hi.symm

theorem positiveCell15_exact : positiveCell15.coefficients = (Outer180.polynomial148.compiledCoefficients basis15).take 10 := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_error : Outer180.polynomial148.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis15).drop 10) ≤ positiveCell15.error := by
  rw [← positiveCell15_full_exact]
  decide +kernel

theorem positiveCell15_correct : positiveCell15.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell15 Outer180.polynomial148 basis15_correct
    (by decide +kernel) 10 positiveCell15_exact positiveCell15_error

def positiveCell16Integer : List ℤ := [(Int.negOfNat 4879685002833361762219033944579106), (Int.negOfNat 2439296635102645870146058086395168), (Int.ofNat 173145208104252961005036624484117), (Int.ofNat 54985373279205057035073686283581), (Int.negOfNat 6666205140611282294950417219657), (Int.negOfNat 1651687827012687480435303446943), (Int.ofNat 105861687791631822017085232667), (Int.ofNat 25609109359020310225640707133), (Int.negOfNat 738331948495662431853124152), (Int.negOfNat 244489265928712916848684044), (Int.ofNat 1395395002586399443491607), (Int.ofNat 1617393783850675490887998), (Int.ofNat 15304001367103568891519), (Int.negOfNat 7889103043308869702559), (Int.negOfNat 147643292896502145435), (Int.ofNat 30137805671743224205), (Int.ofNat 474649084676254598), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms sineIntegerTerms positiveCell16Integer = true := by
  decide +kernel

def positiveCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-2439842501416680881109516972289553/11258999068426240000000000000000000), (-76228019846957683442064315199849/703687441776640000000000000000000), (173145208104252961005036624484117/22517998136852480000000000000000000), (54985373279205057035073686283581/22517998136852480000000000000000000), (-6666205140611282294950417219657/22517998136852480000000000000000000), (-1651687827012687480435303446943/22517998136852480000000000000000000), (105861687791631822017085232667/22517998136852480000000000000000000), (25609109359020310225640707133/22517998136852480000000000000000000), (-92291493561957803981640519/2814749767106560000000000000000000), (-61122316482178229212171011/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell16Integer = Outer180.polynomial148.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell16Integer_checked
  exact hi.symm

theorem positiveCell16_exact : positiveCell16.coefficients = (Outer180.polynomial148.compiledCoefficients basis16).take 10 := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_error : Outer180.polynomial148.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis16).drop 10) ≤ positiveCell16.error := by
  rw [← positiveCell16_full_exact]
  decide +kernel

theorem positiveCell16_correct : positiveCell16.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell16 Outer180.polynomial148 basis16_correct
    (by decide +kernel) 10 positiveCell16_exact positiveCell16_error

def positiveCell17Integer : List ℤ := [(Int.negOfNat 8775584086621420278746749481507043), (Int.negOfNat 1401840634758511549331187976279643), (Int.ofNat 251161293615833065097674587270081), (Int.negOfNat 35681162116243777730457693864517), (Int.negOfNat 11387485067371626243898082710726), (Int.ofNat 1004125970970996497226119713900), (Int.ofNat 245137288861932970697481838817), (Int.negOfNat 12023634991939513837756409121), (Int.negOfNat 2959568025695585544385671299), (Int.ofNat 76383114095236368222939331), (Int.ofNat 23567701865974259460747068), (Int.negOfNat 238374168756231299918455), (Int.negOfNat 134335631616329491891375), (Int.negOfNat 51787451492052855623), (Int.ofNat 573775358861828871712), (Int.ofNat 5328935206716757517), (Int.negOfNat 1638859521247160128), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms sineIntegerTerms positiveCell17Integer = true := by
  decide +kernel

def positiveCell17 : OuterCellModel := ⟨(35/32), (1/32), [(-8775584086621420278746749481507043/22517998136852480000000000000000000), (-1401840634758511549331187976279643/22517998136852480000000000000000000), (251161293615833065097674587270081/22517998136852480000000000000000000), (-35681162116243777730457693864517/22517998136852480000000000000000000), (-5693742533685813121949041355363/11258999068426240000000000000000000), (10041259709709964972261197139/225179981368524800000000000000000), (245137288861932970697481838817/22517998136852480000000000000000000), (-12023634991939513837756409121/22517998136852480000000000000000000), (-2959568025695585544385671299/22517998136852480000000000000000000), (76383114095236368222939331/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell17Integer = Outer180.polynomial148.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell17Integer_checked
  exact hi.symm

theorem positiveCell17_exact : positiveCell17.coefficients = (Outer180.polynomial148.compiledCoefficients basis17).take 10 := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_error : Outer180.polynomial148.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis17).drop 10) ≤ positiveCell17.error := by
  rw [← positiveCell17_full_exact]
  decide +kernel

theorem positiveCell17_correct : positiveCell17.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell17 Outer180.polynomial148 basis17_correct
    (by decide +kernel) 10 positiveCell17_exact positiveCell17_error

def positiveCell18Integer : List ℤ := [(Int.negOfNat 10996682884776393914408612835316773), (Int.negOfNat 1070498946924723473451847574325361), (Int.negOfNat 109837835180564993264433367890843), (Int.negOfNat 58682972668393970193573114658598), (Int.ofNat 7278878946302909457013852218423), (Int.ofNat 1933839682365465251662122667072), (Int.negOfNat 135192078594229669658301121044), (Int.negOfNat 30173941910756626734449574673), (Int.ofNat 1384111026644214005666981028), (Int.ofNat 293542796233645435066809247), (Int.negOfNat 8649115472699541744235062), (Int.negOfNat 1980495971050145112359137), (Int.ofNat 34531632502816403296200), (Int.ofNat 9798966430556017743940), (Int.negOfNat 88083124723885949845), (Int.negOfNat 36905321386226787843), (Int.ofNat 557719255634560079), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms sineIntegerTerms positiveCell18Integer = true := by
  decide +kernel

def positiveCell18 : OuterCellModel := ⟨(37/32), (1/32), [(-10996682884776393914408612835316773/22517998136852480000000000000000000), (-1070498946924723473451847574325361/22517998136852480000000000000000000), (-109837835180564993264433367890843/22517998136852480000000000000000000), (-29341486334196985096786557329299/11258999068426240000000000000000000), (7278878946302909457013852218423/22517998136852480000000000000000000), (30216245036960394557220666673/351843720888320000000000000000000), (-33798019648557417414575280261/5629499534213120000000000000000000), (-30173941910756626734449574673/22517998136852480000000000000000000), (346027756661053501416745257/5629499534213120000000000000000000), (293542796233645435066809247/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell18Integer = Outer180.polynomial148.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell18Integer_checked
  exact hi.symm

theorem positiveCell18_exact : positiveCell18.coefficients = (Outer180.polynomial148.compiledCoefficients basis18).take 10 := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_error : Outer180.polynomial148.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis18).drop 10) ≤ positiveCell18.error := by
  rw [← positiveCell18_full_exact]
  decide +kernel

theorem positiveCell18_correct : positiveCell18.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell18 Outer180.polynomial148 basis18_correct
    (by decide +kernel) 10 positiveCell18_exact positiveCell18_error

def positiveCell19Integer : List ℤ := [(Int.negOfNat 13880173592640063865260309879868309), (Int.negOfNat 1863861051860157508548096093958153), (Int.negOfNat 181576990658340639315523119208321), (Int.ofNat 42222039863512993138466439175248), (Int.ofNat 12598689383653257155372806532677), (Int.negOfNat 1132988027565066487589220401900), (Int.negOfNat 259650203775035371740256244947), (Int.ofNat 17336953710582545240019547018), (Int.ofNat 3128437672018310090656900172), (Int.negOfNat 158832288456051726662234184), (Int.negOfNat 25300685015948618290144911), (Int.ofNat 944775857461579758393193), (Int.ofNat 146781659203360241277448), (Int.negOfNat 3888428365519520118906), (Int.negOfNat 633730288412733285168), (Int.ofNat 10988256048503985138), (Int.ofNat 1620602186589332437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms sineIntegerTerms positiveCell19Integer = true := by
  decide +kernel

def positiveCell19 : OuterCellModel := ⟨(39/32), (1/32), [(-13880173592640063865260309879868309/22517998136852480000000000000000000), (-1863861051860157508548096093958153/22517998136852480000000000000000000), (-181576990658340639315523119208321/22517998136852480000000000000000000), (2638877491469562071154152448453/1407374883553280000000000000000000), (12598689383653257155372806532677/22517998136852480000000000000000000), (-11329880275650664875892204019/225179981368524800000000000000000), (-259650203775035371740256244947/22517998136852480000000000000000000), (8668476855291272620009773509/11258999068426240000000000000000000), (782109418004577522664225043/5629499534213120000000000000000000), (-19854036057006465832779273/2814749767106560000000000000000000)], (1/100000000)⟩

theorem positiveCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell19Integer = Outer180.polynomial148.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell19Integer_checked
  exact hi.symm

theorem positiveCell19_exact : positiveCell19.coefficients = (Outer180.polynomial148.compiledCoefficients basis19).take 10 := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_error : Outer180.polynomial148.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis19).drop 10) ≤ positiveCell19.error := by
  rw [← positiveCell19_full_exact]
  decide +kernel

theorem positiveCell19_correct : positiveCell19.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell19 Outer180.polynomial148 basis19_correct
    (by decide +kernel) 10 positiveCell19_exact positiveCell19_error

def positiveCell20Integer : List ℤ := [(Int.negOfNat 17844806265393577930011863557256496), (Int.negOfNat 1810349397450105345242968910706374), (Int.ofNat 237437614095301260951365432940429), (Int.ofNat 70275214644652966740235406190712), (Int.negOfNat 6875977920596901257391320677294), (Int.negOfNat 1874239808868319806969664106992), (Int.ofNat 163058094889291262760862677614), (Int.ofNat 28264564680584860459488650288), (Int.negOfNat 2141281000292611386828295534), (Int.negOfNat 277313212186165358273268802), (Int.ofNat 17239483672870239451033641), (Int.ofNat 1911674789848083127290845), (Int.negOfNat 92932022594587716336761), (Int.negOfNat 9663665842102784901335), (Int.ofNat 356451973555669563024), (Int.ofNat 37206716473343915299), (Int.negOfNat 1584001817726098859), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms sineIntegerTerms positiveCell20Integer = true := by
  decide +kernel

def positiveCell20 : OuterCellModel := ⟨(41/32), (1/32), [(-1115300391587098620625741472328531/1407374883553280000000000000000000), (-905174698725052672621484455353187/11258999068426240000000000000000000), (237437614095301260951365432940429/22517998136852480000000000000000000), (8784401830581620842529425773839/2814749767106560000000000000000000), (-3437988960298450628695660338647/11258999068426240000000000000000000), (-117139988054269987935604006687/1407374883553280000000000000000000), (81529047444645631380431338807/11258999068426240000000000000000000), (1766535292536553778718040643/1407374883553280000000000000000000), (-1070640500146305693414147767/11258999068426240000000000000000000), (-138656606093082679136634401/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell20Integer = Outer180.polynomial148.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell20Integer_checked
  exact hi.symm

theorem positiveCell20_exact : positiveCell20.coefficients = (Outer180.polynomial148.compiledCoefficients basis20).take 10 := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_error : Outer180.polynomial148.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis20).drop 10) ≤ positiveCell20.error := by
  rw [← positiveCell20_full_exact]
  decide +kernel

theorem positiveCell20_correct : positiveCell20.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell20 Outer180.polynomial148 basis20_correct
    (by decide +kernel) 10 positiveCell20_exact positiveCell20_error

def positiveCell21Integer : List ℤ := [(Int.negOfNat 20110159661801052002159809359658937), (Int.negOfNat 346021715472320400860439175590170), (Int.ofNat 397383712261887057775051874235980), (Int.negOfNat 22780182054654508941027791625402), (Int.negOfNat 11139580117580652221444153323604), (Int.ofNat 1121730161159281301582435098412), (Int.ofNat 211511084057095055291295144423), (Int.negOfNat 22492219317928245255405106306), (Int.negOfNat 2545909313475988137762369635), (Int.ofNat 246553147467620354996076268), (Int.ofNat 21162736957958775814134255), (Int.negOfNat 1702994517383128160072671), (Int.negOfNat 127112003626077879228664), (Int.ofNat 8087515148509736309198), (Int.ofNat 568771981638726969909), (Int.negOfNat 27222378826323475773), (Int.negOfNat 1602344851931504746), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms sineIntegerTerms positiveCell21Integer = true := by
  decide +kernel

def positiveCell21 : OuterCellModel := ⟨(43/32), (1/32), [(-20110159661801052002159809359658937/22517998136852480000000000000000000), (-34602171547232040086043917559017/2251799813685248000000000000000000), (19869185613094352888752593711799/1125899906842624000000000000000000), (-11390091027327254470513895812701/11258999068426240000000000000000000), (-2784895029395163055361038330901/5629499534213120000000000000000000), (280432540289820325395608774603/5629499534213120000000000000000000), (211511084057095055291295144423/22517998136852480000000000000000000), (-11246109658964122627702553153/11258999068426240000000000000000000), (-509181862695197627552473927/4503599627370496000000000000000000), (61638286866905088749019067/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell21Integer = Outer180.polynomial148.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell21Integer_checked
  exact hi.symm

theorem positiveCell21_exact : positiveCell21.coefficients = (Outer180.polynomial148.compiledCoefficients basis21).take 10 := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_error : Outer180.polynomial148.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis21).drop 10) ≤ positiveCell21.error := by
  rw [← positiveCell21_full_exact]
  decide +kernel

theorem positiveCell21_correct : positiveCell21.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell21 Outer180.polynomial148 basis21_correct
    (by decide +kernel) 10 positiveCell21_exact positiveCell21_error

def positiveCell22Integer : List ℤ := [(Int.negOfNat 19527097692373918680145404573287338), (Int.ofNat 732003993790341077615108529439339), (Int.ofNat 115501569326099483421461642431420), (Int.negOfNat 48776747879862554747230990353684), (Int.ofNat 4813084197658533734618853344320), (Int.ofNat 1237560542880819617401537431877), (Int.negOfNat 182298803031269198118520367621), (Int.negOfNat 18538847011348088650191895142), (Int.ofNat 2860309307056826203495555073), (Int.ofNat 189021225775892341908698750), (Int.negOfNat 25730114584475137370232700), (Int.negOfNat 1386124803710738227849408), (Int.ofNat 150744270231646970219335), (Int.ofNat 7418162936732768181633), (Int.negOfNat 623546927199315332341), (Int.negOfNat 30032858081879242749), (Int.ofNat 2610284379817637639), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms sineIntegerTerms positiveCell22Integer = true := by
  decide +kernel

def positiveCell22 : OuterCellModel := ⟨(45/32), (1/32), [(-9763548846186959340072702286643669/11258999068426240000000000000000000), (732003993790341077615108529439339/22517998136852480000000000000000000), (5775078466304974171073082121571/1125899906842624000000000000000000), (-12194186969965638686807747588421/5629499534213120000000000000000000), (15040888117682917920683916701/70368744177664000000000000000000), (1237560542880819617401537431877/22517998136852480000000000000000000), (-182298803031269198118520367621/22517998136852480000000000000000000), (-9269423505674044325095947571/11258999068426240000000000000000000), (2860309307056826203495555073/22517998136852480000000000000000000), (151216980620713873526959/18014398509481984000000000000000)], (1/100000000)⟩

theorem positiveCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell22Integer = Outer180.polynomial148.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell22Integer_checked
  exact hi.symm

theorem positiveCell22_exact : positiveCell22.coefficients = (Outer180.polynomial148.compiledCoefficients basis22).take 10 := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_error : Outer180.polynomial148.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis22).drop 10) ≤ positiveCell22.error := by
  rw [← positiveCell22_full_exact]
  decide +kernel

theorem positiveCell22_correct : positiveCell22.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell22 Outer180.polynomial148 basis22_correct
    (by decide +kernel) 10 positiveCell22_exact positiveCell22_error

def positiveCell23Integer : List ℤ := [(Int.negOfNat 17887925722996729530230901428614429), (Int.ofNat 821627192841415438457648810493194), (Int.negOfNat 13177512524996823256015686254880), (Int.ofNat 5387514721071643876869706977238), (Int.ofNat 4642313674837671204904651727767), (Int.negOfNat 1076260492741195560164613683214), (Int.negOfNat 91405124426832834906494166959), (Int.ofNat 26750717831743089866817034099), (Int.ofNat 1164000136655310881763212945), (Int.negOfNat 326533107801401079857939915), (Int.negOfNat 11134437083833981636527319), (Int.ofNat 2402882138304491356006797), (Int.ofNat 76407466811868754994006), (Int.negOfNat 11927833425708442805117), (Int.negOfNat 374760188615733672524), (Int.ofNat 43020377585617554708), (Int.ofNat 1241993329909830795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms sineIntegerTerms positiveCell23Integer = true := by
  decide +kernel

def positiveCell23 : OuterCellModel := ⟨(47/32), (1/32), [(-17887925722996729530230901428614429/22517998136852480000000000000000000), (410813596420707719228824405246597/11258999068426240000000000000000000), (-82359453281230145350098039093/140737488355328000000000000000000), (2693757360535821938434853488619/11258999068426240000000000000000000), (4642313674837671204904651727767/22517998136852480000000000000000000), (-538130246370597780082306841607/11258999068426240000000000000000000), (-91405124426832834906494166959/22517998136852480000000000000000000), (26750717831743089866817034099/22517998136852480000000000000000000), (232800027331062176352642589/4503599627370496000000000000000000), (-65306621560280215971587983/4503599627370496000000000000000000)], (1/100000000)⟩

theorem positiveCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell23Integer = Outer180.polynomial148.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell23Integer_checked
  exact hi.symm

theorem positiveCell23_exact : positiveCell23.coefficients = (Outer180.polynomial148.compiledCoefficients basis23).take 10 := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_error : Outer180.polynomial148.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis23).drop 10) ≤ positiveCell23.error := by
  rw [← positiveCell23_full_exact]
  decide +kernel

theorem positiveCell23_correct : positiveCell23.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell23 Outer180.polynomial148 basis23_correct
    (by decide +kernel) 10 positiveCell23_exact positiveCell23_error

def positiveCell24Integer : List ℤ := [(Int.negOfNat 16216745893606813978873283953966920), (Int.ofNat 890865927526207879060807349835555), (Int.ofNat 41025294694607565003701873543637), (Int.ofNat 97023616778443747592032711800), (Int.negOfNat 4170389576622570557983837678226), (Int.negOfNat 78047855685885892677757738563), (Int.ofNat 193883175824608744590246577741), (Int.ofNat 889986092574235253033160941), (Int.negOfNat 3465899339054494366741730895), (Int.negOfNat 31638683853153216288884165), (Int.ofNat 33107550673450526337788121), (Int.ofNat 448563727049558786960803), (Int.negOfNat 200198391165841346304234), (Int.negOfNat 3322052385054811749603), (Int.ofNat 845094949900891646396), (Int.ofNat 16180718635957692132), (Int.negOfNat 3282301198106778365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms sineIntegerTerms positiveCell24Integer = true := by
  decide +kernel

def positiveCell24 : OuterCellModel := ⟨(49/32), (1/32), [(-405418647340170349471832098849173/562949953421312000000000000000000), (178173185505241575812161469967111/4503599627370496000000000000000000), (41025294694607565003701873543637/22517998136852480000000000000000000), (485118083892218737960163559/112589990684262400000000000000000), (-2085194788311285278991918839113/11258999068426240000000000000000000), (-78047855685885892677757738563/22517998136852480000000000000000000), (193883175824608744590246577741/22517998136852480000000000000000000), (889986092574235253033160941/22517998136852480000000000000000000), (-693179867810898873348346179/4503599627370496000000000000000000), (-6327736770630643257776833/4503599627370496000000000000000000)], (1/100000000)⟩

theorem positiveCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell24Integer = Outer180.polynomial148.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell24Integer_checked
  exact hi.symm

theorem positiveCell24_exact : positiveCell24.coefficients = (Outer180.polynomial148.compiledCoefficients basis24).take 10 := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_error : Outer180.polynomial148.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis24).drop 10) ≤ positiveCell24.error := by
  rw [← positiveCell24_full_exact]
  decide +kernel

theorem positiveCell24_correct : positiveCell24.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell24 Outer180.polynomial148 basis24_correct
    (by decide +kernel) 10 positiveCell24_exact positiveCell24_error

def positiveCell25Integer : List ℤ := [(Int.negOfNat 14327707475424504664032097707280812), (Int.ofNat 950606967828627458792911713804163), (Int.negOfNat 23572098048971774234443636656718), (Int.negOfNat 10744683628376414704809252784792), (Int.ofNat 3360163514593126264165379583258), (Int.ofNat 966547228802119094213150354457), (Int.negOfNat 97125762277322225906885948661), (Int.negOfNat 30025588178732777051029884618), (Int.ofNat 960282743680543101343890793), (Int.ofNat 394074965173193367907560130), (Int.negOfNat 3824083065220032116599100), (Int.negOfNat 2970005235221811390897352), (Int.negOfNat 1089721093045369975265), (Int.ofNat 14909276107657160118047), (Int.ofNat 88054831918158463419), (Int.negOfNat 55261414932780490771), (Int.negOfNat 545633398743586481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms sineIntegerTerms positiveCell25Integer = true := by
  decide +kernel

def positiveCell25 : OuterCellModel := ⟨(51/32), (1/32), [(-3581926868856126166008024426820203/5629499534213120000000000000000000), (950606967828627458792911713804163/22517998136852480000000000000000000), (-11786049024485887117221818328359/11258999068426240000000000000000000), (-1343085453547051838101156598099/2814749767106560000000000000000000), (1680081757296563132082689791629/11258999068426240000000000000000000), (966547228802119094213150354457/22517998136852480000000000000000000), (-97125762277322225906885948661/22517998136852480000000000000000000), (-15012794089366388525514942309/11258999068426240000000000000000000), (960282743680543101343890793/22517998136852480000000000000000000), (39407496517319336790756013/2251799813685248000000000000000000)], (1/100000000)⟩

theorem positiveCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell25Integer = Outer180.polynomial148.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell25Integer_checked
  exact hi.symm

theorem positiveCell25_exact : positiveCell25.coefficients = (Outer180.polynomial148.compiledCoefficients basis25).take 10 := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_error : Outer180.polynomial148.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis25).drop 10) ≤ positiveCell25.error := by
  rw [← positiveCell25_full_exact]
  decide +kernel

theorem positiveCell25_correct : positiveCell25.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell25 Outer180.polynomial148 basis25_correct
    (by decide +kernel) 10 positiveCell25_exact positiveCell25_error

def positiveCell26Integer : List ℤ := [(Int.negOfNat 12531668879893769031412150772445427), (Int.ofNat 881970781287811866406521510560510), (Int.ofNat 29851452884578182019782209019365), (Int.ofNat 26103450776712979859875771409887), (Int.ofNat 1283758866451211410500616288903), (Int.negOfNat 1610381922354091667625337921075), (Int.negOfNat 198734396196425401103377826297), (Int.ofNat 24291216653620744027445535786), (Int.ofNat 4022369827574883165850865605), (Int.negOfNat 178809544957914314105648388), (Int.negOfNat 39048628387073492645860065), (Int.ofNat 772794751263443291896671), (Int.ofNat 235938703813385978555496), (Int.negOfNat 2017291949981234176758), (Int.negOfNat 996514326513771112931), (Int.ofNat 2324719894565025853), (Int.ofNat 3606138050812796934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms sineIntegerTerms positiveCell26Integer = true := by
  decide +kernel

def positiveCell26 : OuterCellModel := ⟨(53/32), (1/32), [(-12531668879893769031412150772445427/22517998136852480000000000000000000), (88197078128781186640652151056051/2251799813685248000000000000000000), (5970290576915636403956441803873/4503599627370496000000000000000000), (26103450776712979859875771409887/22517998136852480000000000000000000), (1283758866451211410500616288903/22517998136852480000000000000000000), (-64415276894163666705013516843/900719925474099200000000000000000), (-198734396196425401103377826297/22517998136852480000000000000000000), (12145608326810372013722767893/11258999068426240000000000000000000), (804473965514976633170173121/4503599627370496000000000000000000), (-44702386239478578526412097/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell26Integer = Outer180.polynomial148.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell26Integer_checked
  exact hi.symm

theorem positiveCell26_exact : positiveCell26.coefficients = (Outer180.polynomial148.compiledCoefficients basis26).take 10 := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_error : Outer180.polynomial148.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis26).drop 10) ≤ positiveCell26.error := by
  rw [← positiveCell26_full_exact]
  decide +kernel

theorem positiveCell26_correct : positiveCell26.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell26 Outer180.polynomial148 basis26_correct
    (by decide +kernel) 10 positiveCell26_exact positiveCell26_error

def positiveCell27Integer : List ℤ := [(Int.negOfNat 10479194997937778402743560150013234), (Int.ofNat 1203114477247492989601539837627936), (Int.ofNat 63050573012111202021055363859663), (Int.negOfNat 40531254086088603410489212908554), (Int.negOfNat 16622492787097479689071825952037), (Int.negOfNat 782962208644893238314621124459), (Int.ofNat 364683910528996789514949538657), (Int.ofNat 34836277439876535259516805232), (Int.negOfNat 3598861907075183249405559494), (Int.negOfNat 456238934965118764675129638), (Int.ofNat 21431734518989637177314081), (Int.ofNat 3369061345034153840589115), (Int.negOfNat 86848805564157081603641), (Int.negOfNat 16671016044074838461865), (Int.ofNat 253737944054467566184), (Int.ofNat 60535612926830720421), (Int.negOfNat 480649163347952299), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms sineIntegerTerms positiveCell27Integer = true := by
  decide +kernel

def positiveCell27 : OuterCellModel := ⟨(55/32), (1/32), [(-5239597498968889201371780075006617/11258999068426240000000000000000000), (37597327413984155925048119925873/703687441776640000000000000000000), (63050573012111202021055363859663/22517998136852480000000000000000000), (-20265627043044301705244606454277/11258999068426240000000000000000000), (-16622492787097479689071825952037/22517998136852480000000000000000000), (-782962208644893238314621124459/22517998136852480000000000000000000), (364683910528996789514949538657/22517998136852480000000000000000000), (2177267339992283453719800327/1407374883553280000000000000000000), (-1799430953537591624702779747/11258999068426240000000000000000000), (-228119467482559382337564819/11258999068426240000000000000000000)], (1/100000000)⟩

theorem positiveCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell27Integer = Outer180.polynomial148.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell27Integer_checked
  exact hi.symm

theorem positiveCell27_exact : positiveCell27.coefficients = (Outer180.polynomial148.compiledCoefficients basis27).take 10 := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_error : Outer180.polynomial148.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis27).drop 10) ≤ positiveCell27.error := by
  rw [← positiveCell27_full_exact]
  decide +kernel

theorem positiveCell27_correct : positiveCell27.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell27 Outer180.polynomial148 basis27_correct
    (by decide +kernel) 10 positiveCell27_exact positiveCell27_error

def positiveCell28Integer : List ℤ := [(Int.negOfNat 8409356188816728249003606484812145), (Int.ofNat 455419229521145288957383546277593), (Int.negOfNat 538997768806134200289652821118827), (Int.negOfNat 135416710862391498320569658918090), (Int.ofNat 1726462733298863020516133425573), (Int.ofNat 4246006832003616884835246642900), (Int.ofNat 256089711911848441227329228970), (Int.negOfNat 53907983567432778828430854338), (Int.negOfNat 4785924583617425917043123588), (Int.ofNat 403836219361769931802850544), (Int.ofNat 43671505603994777706718529), (Int.negOfNat 2059999782673671988649873), (Int.negOfNat 254527781320806644840992), (Int.ofNat 7719200126270604476986), (Int.ofNat 1052803706076898551112), (Int.negOfNat 21668392602585546258), (Int.negOfNat 3587880716154969243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms sineIntegerTerms positiveCell28Integer = true := by
  decide +kernel

def positiveCell28 : OuterCellModel := ⟨(57/32), (1/32), [(-1681871237763345649800721296962429/4503599627370496000000000000000000), (455419229521145288957383546277593/22517998136852480000000000000000000), (-538997768806134200289652821118827/22517998136852480000000000000000000), (-13541671086239149832056965891809/2251799813685248000000000000000000), (1726462733298863020516133425573/22517998136852480000000000000000000), (42460068320036168848352466429/225179981368524800000000000000000), (25608971191184844122732922897/2251799813685248000000000000000000), (-26953991783716389414215427169/11258999068426240000000000000000000), (-1196481145904356479260780897/5629499534213120000000000000000000), (25239763710110620737678159/1407374883553280000000000000000000)], (1/100000000)⟩

theorem positiveCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell28Integer = Outer180.polynomial148.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell28Integer_checked
  exact hi.symm

theorem positiveCell28_exact : positiveCell28.coefficients = (Outer180.polynomial148.compiledCoefficients basis28).take 10 := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_error : Outer180.polynomial148.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis28).drop 10) ≤ positiveCell28.error := by
  rw [← positiveCell28_full_exact]
  decide +kernel

theorem positiveCell28_correct : positiveCell28.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell28 Outer180.polynomial148 basis28_correct
    (by decide +kernel) 10 positiveCell28_exact positiveCell28_error

def positiveCell29Integer : List ℤ := [(Int.negOfNat 10565836244681349173989279271318981), (Int.negOfNat 2909402258446231308004693737120850), (Int.negOfNat 951433031080665307904659690714184), (Int.ofNat 53173893828060207324299587243974), (Int.ofNat 41197207220865617035898013453111), (Int.ofNat 1729832944658054017252658915202), (Int.negOfNat 659615240498084679626679218204), (Int.negOfNat 46477296533128205540740844887), (Int.ofNat 6101059112082369173005014348), (Int.ofNat 520434922378179121197440593), (Int.negOfNat 37928446039187749022770582), (Int.negOfNat 3568875191735299702853943), (Int.ofNat 171378097585453828765800), (Int.ofNat 16976374566215477810460), (Int.negOfNat 590831873743474217645), (Int.negOfNat 60246838192652326277), (Int.ofNat 1506931725439491079), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms sineIntegerTerms positiveCell29Integer = true := by
  decide +kernel

def positiveCell29 : OuterCellModel := ⟨(59/32), (1/32), [(-10565836244681349173989279271318981/22517998136852480000000000000000000), (-58188045168924626160093874742417/450359962737049600000000000000000), (-118929128885083163488082461339273/2814749767106560000000000000000000), (26586946914030103662149793621987/11258999068426240000000000000000000), (41197207220865617035898013453111/22517998136852480000000000000000000), (864916472329027008626329457601/11258999068426240000000000000000000), (-164903810124521169906669804551/5629499534213120000000000000000000), (-46477296533128205540740844887/22517998136852480000000000000000000), (1525264778020592293251253587/5629499534213120000000000000000000), (520434922378179121197440593/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell29Integer = Outer180.polynomial148.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell29Integer_checked
  exact hi.symm

theorem positiveCell29_exact : positiveCell29.coefficients = (Outer180.polynomial148.compiledCoefficients basis29).take 10 := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_error : Outer180.polynomial148.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis29).drop 10) ≤ positiveCell29.error := by
  rw [← positiveCell29_full_exact]
  decide +kernel

theorem positiveCell29_correct : positiveCell29.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell29 Outer180.polynomial148 basis29_correct
    (by decide +kernel) 10 positiveCell29_exact positiveCell29_error

def positiveCell30Integer : List ℤ := [(Int.negOfNat 19096853219329639572947146564939608), (Int.negOfNat 4760601137920680887471733251855452), (Int.ofNat 317997392613084739929111089965387), (Int.ofNat 333400502806718987402873948318582), (Int.ofNat 14203224208351274958401409405364), (Int.negOfNat 6696356517907497551260564063717), (Int.negOfNat 444176082590454242944909846343), (Int.ofNat 76689054890387479166834262961), (Int.ofNat 5831475582693880795739522981), (Int.negOfNat 581255870251088206495123731), (Int.negOfNat 46403725456883276870549092), (Int.ofNat 3145641252533923856264735), (Int.ofNat 252699281692692944383345), (Int.negOfNat 12777480432624642381097), (Int.negOfNat 1006894036440515599608), (Int.ofNat 39560620083749429603), (Int.ofNat 3569623381497141552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms sineIntegerTerms positiveCell30Integer = true := by
  decide +kernel

def positiveCell30 : OuterCellModel := ⟨(61/32), (1/32), [(-2387106652416204946618393320617451/2814749767106560000000000000000000), (-1190150284480170221867933312963863/5629499534213120000000000000000000), (317997392613084739929111089965387/22517998136852480000000000000000000), (166700251403359493701436974159291/11258999068426240000000000000000000), (3550806052087818739600352351341/5629499534213120000000000000000000), (-6696356517907497551260564063717/22517998136852480000000000000000000), (-444176082590454242944909846343/22517998136852480000000000000000000), (76689054890387479166834262961/22517998136852480000000000000000000), (5831475582693880795739522981/22517998136852480000000000000000000), (-581255870251088206495123731/22517998136852480000000000000000000)], (1/100000000)⟩

theorem positiveCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell30Integer = Outer180.polynomial148.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell30Integer_checked
  exact hi.symm

theorem positiveCell30_exact : positiveCell30.coefficients = (Outer180.polynomial148.compiledCoefficients basis30).take 10 := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_error : Outer180.polynomial148.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis30).drop 10) ≤ positiveCell30.error := by
  rw [← positiveCell30_full_exact]
  decide +kernel

theorem positiveCell30_correct : positiveCell30.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell30 Outer180.polynomial148 basis30_correct
    (by decide +kernel) 10 positiveCell30_exact positiveCell30_error

def positiveCell31Integer : List ℤ := [(Int.negOfNat 24683349698768924374094451143438192), (Int.ofNat 384499496973248539689229217115491), (Int.ofNat 2075842343924153589543936319400169), (Int.ofNat 157819076197391920271480789180153), (Int.negOfNat 54214689657532127478720157405996), (Int.negOfNat 4404564399867054000576033063454), (Int.ofNat 794069425484122929672531101004), (Int.ofNat 62994192882923519783902511987), (Int.negOfNat 7508062861540347630399988832), (Int.negOfNat 566569957785869284116191036), (Int.ofNat 49283976798270913958406007), (Int.ofNat 3497477701722820206500402), (Int.negOfNat 236827843249931658054281), (Int.negOfNat 15682046674589679415241), (Int.ofNat 866689843343608125845), (Int.ofNat 52740416591286517915), (Int.negOfNat 2527128509311753962), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem positiveCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms sineIntegerTerms positiveCell31Integer = true := by
  decide +kernel

def positiveCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1542709356173057773380903196464887/1407374883553280000000000000000000), (384499496973248539689229217115491/22517998136852480000000000000000000), (2075842343924153589543936319400169/22517998136852480000000000000000000), (157819076197391920271480789180153/22517998136852480000000000000000000), (-13553672414383031869680039351499/5629499534213120000000000000000000), (-2202282199933527000288016531727/11258999068426240000000000000000000), (198517356371030732418132775251/5629499534213120000000000000000000), (62994192882923519783902511987/22517998136852480000000000000000000), (-234626964423135863449999651/703687441776640000000000000000000), (-141642489446467321029047759/5629499534213120000000000000000000)], (1/100000000)⟩

theorem positiveCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) positiveCell31Integer = Outer180.polynomial148.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148 weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact cosineIntegerTerms_exact sineIntegerTerms_exact positiveCell31Integer_checked
  exact hi.symm

theorem positiveCell31_exact : positiveCell31.coefficients = (Outer180.polynomial148.compiledCoefficients basis31).take 10 := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_error : Outer180.polynomial148.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial148.compiledCoefficients basis31).drop 10) ≤ positiveCell31.error := by
  rw [← positiveCell31_full_exact]
  decide +kernel

theorem positiveCell31_correct : positiveCell31.Correct Outer180.polynomial148 :=
  OuterCellModel.correct_of_basis_truncated positiveCell31 Outer180.polynomial148 basis31_correct
    (by decide +kernel) 10 positiveCell31_exact positiveCell31_error

def positiveModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then positiveCell00 else positiveCell01) else (if j < 3 then positiveCell02 else positiveCell03)) else (if j < 6 then (if j < 5 then positiveCell04 else positiveCell05) else (if j < 7 then positiveCell06 else positiveCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then positiveCell08 else positiveCell09) else (if j < 11 then positiveCell10 else positiveCell11)) else (if j < 14 then (if j < 13 then positiveCell12 else positiveCell13) else (if j < 15 then positiveCell14 else positiveCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then positiveCell16 else positiveCell17) else (if j < 19 then positiveCell18 else positiveCell19)) else (if j < 22 then (if j < 21 then positiveCell20 else positiveCell21) else (if j < 23 then positiveCell22 else positiveCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then positiveCell24 else positiveCell25) else (if j < 27 then positiveCell26 else positiveCell27)) else (if j < 30 then (if j < 29 then positiveCell28 else positiveCell29) else (if j < 31 then positiveCell30 else positiveCell31)))))

theorem positiveModel_correct (j : ℕ) (hj : j < 32) : (positiveModel j).Correct Outer180.polynomial148 := by
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

def negativeCell00Integer : List ℤ := [(Int.negOfNat 27865738559391028322228146358565549), (Int.negOfNat 540707569595822916692247881726429), (Int.ofNat 2208242446440501713301638917799900), (Int.negOfNat 211284319976190808259321807762457), (Int.negOfNat 57165765642583047286092640809631), (Int.ofNat 5999253428865018564259672057697), (Int.ofNat 835083220543061821215776227907), (Int.negOfNat 83239196101526501032935461387), (Int.negOfNat 7850159315043456594045823832), (Int.ofNat 712816707033574543006127036), (Int.ofNat 51143758337176363780600007), (Int.negOfNat 4182279980523384837236202), (Int.negOfNat 243880006474383474833881), (Int.ofNat 17934856115982711053441), (Int.ofNat 886056081975910923845), (Int.negOfNat 58550288180977357315), (Int.negOfNat 2527128509311753962), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell00Integer_checked :
    integerCompileSumCheck intBasis00 cosineIntegerTerms reflectedSineIntegerTerms negativeCell00Integer = true := by
  decide +kernel

def negativeCell00 : OuterCellModel := ⟨(1/32), (1/32), [(-27865738559391028322228146358565549/22517998136852480000000000000000000), (-540707569595822916692247881726429/22517998136852480000000000000000000), (22082424464405017133016389177999/225179981368524800000000000000000), (-211284319976190808259321807762457/22517998136852480000000000000000000), (-57165765642583047286092640809631/22517998136852480000000000000000000), (5999253428865018564259672057697/22517998136852480000000000000000000), (835083220543061821215776227907/22517998136852480000000000000000000), (-83239196101526501032935461387/22517998136852480000000000000000000), (-981269914380432074255727979/2814749767106560000000000000000000), (178204176758393635751531759/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell00_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell00Integer = Outer180.polynomial148.reflect.compiledCoefficients basis00 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis00_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell00Integer_checked
  exact hi.symm

theorem negativeCell00_exact : negativeCell00.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis00).take 10 := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_error : Outer180.polynomial148.reflect.compiledError basis00 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis00).drop 10) ≤ negativeCell00.error := by
  rw [← negativeCell00_full_exact]
  decide +kernel

theorem negativeCell00_correct : negativeCell00.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell00 Outer180.polynomial148.reflect basis00_correct
    (by decide +kernel) 10 negativeCell00_exact negativeCell00_error

def negativeCell01Integer : List ℤ := [(Int.negOfNat 22485945616431883144253852223344577), (Int.ofNat 4524344529742324528950994724196202), (Int.ofNat 182656894323277659027196726955903), (Int.negOfNat 351289092521875306018818904681153), (Int.ofNat 24193788981436602463081969579565), (Int.ofNat 7218984202104445387887434888900), (Int.negOfNat 630426089636550854758478285943), (Int.negOfNat 83110346935116976207669824561), (Int.ofNat 7588756669436973277950694781), (Int.ofNat 626888474095989200036606331), (Int.negOfNat 56529088749466288718676492), (Int.negOfNat 3357690067298681962224535), (Int.ofNat 292159004261398133626945), (Int.ofNat 13472728399524312829297), (Int.negOfNat 1118572679220128401408), (Int.negOfNat 41497243946979709403), (Int.ofNat 3569623381497141552), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell01Integer_checked :
    integerCompileSumCheck intBasis01 cosineIntegerTerms reflectedSineIntegerTerms negativeCell01Integer = true := by
  decide +kernel

def negativeCell01 : OuterCellModel := ⟨(3/32), (1/32), [(-22485945616431883144253852223344577/22517998136852480000000000000000000), (2262172264871162264475497362098101/11258999068426240000000000000000000), (182656894323277659027196726955903/22517998136852480000000000000000000), (-351289092521875306018818904681153/22517998136852480000000000000000000), (4838757796287320492616393915913/4503599627370496000000000000000000), (72189842021044453878874348889/225179981368524800000000000000000), (-630426089636550854758478285943/22517998136852480000000000000000000), (-83110346935116976207669824561/22517998136852480000000000000000000), (7588756669436973277950694781/22517998136852480000000000000000000), (626888474095989200036606331/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell01_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell01Integer = Outer180.polynomial148.reflect.compiledCoefficients basis01 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis01_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell01Integer_checked
  exact hi.symm

theorem negativeCell01_exact : negativeCell01.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis01).take 10 := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_error : Outer180.polynomial148.reflect.compiledError basis01 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis01).drop 10) ≤ negativeCell01.error := by
  rw [← negativeCell01_full_exact]
  decide +kernel

theorem negativeCell01_correct : negativeCell01.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell01 Outer180.polynomial148.reflect basis01_correct
    (by decide +kernel) 10 negativeCell01_exact negativeCell01_error

def negativeCell02Integer : List ℤ := [(Int.negOfNat 14947618781929104141652714296933348), (Int.ofNat 2241843484503562727173829208708595), (Int.negOfNat 958296965639613336752414798765752), (Int.negOfNat 394333305409593234722016099709), (Int.ofNat 45453328089368351031459704414420), (Int.negOfNat 3186145219084946484420779087088), (Int.negOfNat 743040605430643185049029621204), (Int.ofNat 64929804254641249359108476287), (Int.ofNat 6896436867228901391654836548), (Int.negOfNat 653868943062187655636077993), (Int.negOfNat 42529676210310303960153782), (Int.ofNat 4194047022984581993120943), (Int.ofNat 189339238525652778687200), (Int.negOfNat 19033584997422251188860), (Int.negOfNat 641829635475204919045), (Int.ofNat 64765627206856312477), (Int.ofNat 1506931725439491079), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell02Integer_checked :
    integerCompileSumCheck intBasis02 cosineIntegerTerms reflectedSineIntegerTerms negativeCell02Integer = true := by
  decide +kernel

def negativeCell02 : OuterCellModel := ⟨(5/32), (1/32), [(-3736904695482276035413178574233337/5629499534213120000000000000000000), (448368696900712545434765841741719/4503599627370496000000000000000000), (-119787120704951667094051849845719/2814749767106560000000000000000000), (-394333305409593234722016099709/22517998136852480000000000000000000), (2272666404468417551572985220721/1125899906842624000000000000000000), (-199134076192809155276298692943/1407374883553280000000000000000000), (-185760151357660796262257405301/5629499534213120000000000000000000), (64929804254641249359108476287/22517998136852480000000000000000000), (1724109216807225347913709137/5629499534213120000000000000000000), (-653868943062187655636077993/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell02_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell02Integer = Outer180.polynomial148.reflect.compiledCoefficients basis02 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis02_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell02Integer_checked
  exact hi.symm

theorem negativeCell02_exact : negativeCell02.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis02).take 10 := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_error : Outer180.polynomial148.reflect.compiledError basis02 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis02).drop 10) ≤ negativeCell02.error := by
  rw [← negativeCell02_full_exact]
  decide +kernel

theorem negativeCell02_correct : negativeCell02.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell02 Outer180.polynomial148.reflect basis02_correct
    (by decide +kernel) 10 negativeCell02_exact negativeCell02_error

def negativeCell03Integer : List ℤ := [(Int.negOfNat 13712824966008624246190510734066661), (Int.negOfNat 504648230291696054325956237810254), (Int.negOfNat 250388500949528522451803662073884), (Int.ofNat 161643194468493845836768884074842), (Int.negOfNat 8100488704524975728684933022411), (Int.negOfNat 5083597950480510572493182852880), (Int.ofNat 424781758809821085436416871673), (Int.ofNat 64971690121633232939661433938), (Int.negOfNat 6343121906809008431257544988), (Int.negOfNat 485201837880937578249749144), (Int.ofNat 52564010374251805603818729), (Int.ofNat 2444089253725960139696673), (Int.negOfNat 289040734615883418810792), (Int.negOfNat 8985880424219788385786), (Int.ofNat 1150280440526155967712), (Int.ofNat 24250557753559252658), (Int.negOfNat 3587880716154969243), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell03Integer_checked :
    integerCompileSumCheck intBasis03 cosineIntegerTerms reflectedSineIntegerTerms negativeCell03Integer = true := by
  decide +kernel

def negativeCell03 : OuterCellModel := ⟨(7/32), (1/32), [(-13712824966008624246190510734066661/22517998136852480000000000000000000), (-252324115145848027162978118905127/11258999068426240000000000000000000), (-62597125237382130612950915518471/5629499534213120000000000000000000), (80821597234246922918384442037421/11258999068426240000000000000000000), (-8100488704524975728684933022411/22517998136852480000000000000000000), (-63544974381006382156164785661/281474976710656000000000000000000), (424781758809821085436416871673/22517998136852480000000000000000000), (32485845060816616469830716969/11258999068426240000000000000000000), (-1585780476702252107814386247/5629499534213120000000000000000000), (-60650229735117197281218643/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell03_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell03Integer = Outer180.polynomial148.reflect.compiledCoefficients basis03 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis03_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell03Integer_checked
  exact hi.symm

theorem negativeCell03_exact : negativeCell03.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis03).take 10 := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_error : Outer180.polynomial148.reflect.compiledError basis03 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis03).drop 10) ≤ negativeCell03.error := by
  rw [← negativeCell03_full_exact]
  decide +kernel

theorem negativeCell03_correct : negativeCell03.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell03 Outer180.polynomial148.reflect basis03_correct
    (by decide +kernel) 10 negativeCell03_exact negativeCell03_error

def negativeCell04Integer : List ℤ := [(Int.negOfNat 14689125089003989809707357832147161), (Int.negOfNat 129046009664413552373576241822208), (Int.ofNat 251030851077301204465084681302907), (Int.negOfNat 15254403606934642638038708187794), (Int.negOfNat 23547113992422998720174396057334), (Int.ofNat 2116625858817183457024299458585), (Int.ofNat 492502493331940557555068294414), (Int.negOfNat 50807099264223103675531255232), (Int.negOfNat 4818086346054867001794802294), (Int.ofNat 568855288474970488784978238), (Int.ofNat 28497532275746384874790281), (Int.negOfNat 3890617510694702226392315), (Int.negOfNat 114459101907875459373441), (Int.ofNat 18377569264640350276865), (Int.ofNat 331848439871422184784), (Int.negOfNat 65054401941034706621), (Int.negOfNat 480649163347952299), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell04Integer_checked :
    integerCompileSumCheck intBasis04 cosineIntegerTerms reflectedSineIntegerTerms negativeCell04Integer = true := by
  decide +kernel

def negativeCell04 : OuterCellModel := ⟨(9/32), (1/32), [(-14689125089003989809707357832147161/22517998136852480000000000000000000), (-252042987625807719479641097309/43980465111040000000000000000000), (251030851077301204465084681302907/22517998136852480000000000000000000), (-7627201803467321319019354093897/11258999068426240000000000000000000), (-11773556996211499360087198028667/11258999068426240000000000000000000), (423325171763436691404859891717/4503599627370496000000000000000000), (246251246665970278777534147207/11258999068426240000000000000000000), (-793860926003485994930175863/351843720888320000000000000000000), (-2409043173027433500897401147/11258999068426240000000000000000000), (284427644237485244392489119/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell04_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell04Integer = Outer180.polynomial148.reflect.compiledCoefficients basis04 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis04_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell04Integer_checked
  exact hi.symm

theorem negativeCell04_exact : negativeCell04.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis04).take 10 := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_error : Outer180.polynomial148.reflect.compiledError basis04 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis04).drop 10) ≤ negativeCell04.error := by
  rw [← negativeCell04_full_exact]
  decide +kernel

theorem negativeCell04_correct : negativeCell04.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell04 Outer180.polynomial148.reflect basis04_correct
    (by decide +kernel) 10 negativeCell04_exact negativeCell04_error

def negativeCell05Integer : List ℤ := [(Int.negOfNat 14350055156087120003676764819725667), (Int.ofNat 176123063872963039152797128246990), (Int.negOfNat 158036735877672262154343213341786), (Int.negOfNat 73927704354340967259284935751477), (Int.ofNat 10051723486776779636397790070807), (Int.ofNat 2856527608004738595381335852715), (Int.negOfNat 340561849154584708425490587897), (Int.negOfNat 40009364422235122748076856786), (Int.ofNat 5276317483335299470628481605), (Int.ofNat 292390414102375841134411388), (Int.negOfNat 46058123612500604003674265), (Int.negOfNat 1304819954594910061995871), (Int.ofNat 262871864105005051279296), (Int.ofNat 3766579186934393066958), (Int.negOfNat 1071397115892008598531), (Int.negOfNat 6843508908769012053), (Int.ofNat 3606138050812796934), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell05Integer_checked :
    integerCompileSumCheck intBasis05 cosineIntegerTerms reflectedSineIntegerTerms negativeCell05Integer = true := by
  decide +kernel

def negativeCell05 : OuterCellModel := ⟨(11/32), (1/32), [(-14350055156087120003676764819725667/22517998136852480000000000000000000), (17612306387296303915279712824699/2251799813685248000000000000000000), (-79018367938836131077171606670893/11258999068426240000000000000000000), (-73927704354340967259284935751477/22517998136852480000000000000000000), (10051723486776779636397790070807/22517998136852480000000000000000000), (571305521600947719076267170543/4503599627370496000000000000000000), (-340561849154584708425490587897/22517998136852480000000000000000000), (-20004682211117561374038428393/11258999068426240000000000000000000), (1055263496667059894125696321/4503599627370496000000000000000000), (73097603525593960283602847/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell05_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell05Integer = Outer180.polynomial148.reflect.compiledCoefficients basis05 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis05_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell05Integer_checked
  exact hi.symm

theorem negativeCell05_exact : negativeCell05.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis05).take 10 := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_error : Outer180.polynomial148.reflect.compiledError basis05 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis05).drop 10) ≤ negativeCell05.error := by
  rw [← negativeCell05_full_exact]
  decide +kernel

theorem negativeCell05_correct : negativeCell05.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell05 Outer180.polynomial148.reflect basis05_correct
    (by decide +kernel) 10 negativeCell05_exact negativeCell05_error

def negativeCell06Integer : List ℤ := [(Int.negOfNat 14994606609026890817487854398506576), (Int.negOfNat 870458402296630417497539787008615), (Int.negOfNat 230207394674215644197874148258144), (Int.ofNat 54146448266716462139006743325688), (Int.ofNat 13428520981007192065824191459286), (Int.negOfNat 2020945362950593177159750933940), (Int.negOfNat 271746604576654121307751502861), (Int.ofNat 42023691113331972291585052218), (Int.ofNat 2562674701381842102422522793), (Int.negOfNat 476231957131159666934542930), (Int.negOfNat 12943419673372866159253100), (Int.ofNat 3345066666927168629607152), (Int.ofNat 34247722163616125787135), (Int.negOfNat 16127929767520168619247), (Int.negOfNat 11358526394329232981), (Int.ofNat 57843580083754197171), (Int.negOfNat 545633398743586481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell06Integer_checked :
    integerCompileSumCheck intBasis06 cosineIntegerTerms reflectedSineIntegerTerms negativeCell06Integer = true := by
  decide +kernel

def negativeCell06 : OuterCellModel := ⟨(13/32), (1/32), [(-937162913064180676092990899906661/1407374883553280000000000000000000), (-174091680459326083499507957401723/4503599627370496000000000000000000), (-7193981083569238881183567133067/703687441776640000000000000000000), (6768306033339557767375842915711/2814749767106560000000000000000000), (6714260490503596032912095729643/11258999068426240000000000000000000), (-101047268147529658857987546697/1125899906842624000000000000000000), (-271746604576654121307751502861/22517998136852480000000000000000000), (21011845556665986145792526109/11258999068426240000000000000000000), (2562674701381842102422522793/22517998136852480000000000000000000), (-47623195713115966693454293/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell06_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell06Integer = Outer180.polynomial148.reflect.compiledCoefficients basis06 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis06_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell06Integer_checked
  exact hi.symm

theorem negativeCell06_exact : negativeCell06.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis06).take 10 := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_error : Outer180.polynomial148.reflect.compiledError basis06 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis06).drop 10) ≤ negativeCell06.error := by
  rw [← negativeCell06_full_exact]
  decide +kernel

theorem negativeCell06_correct : negativeCell06.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell06 Outer180.polynomial148.reflect basis06_correct
    (by decide +kernel) 10 negativeCell06_exact negativeCell06_error

def negativeCell07Integer : List ℤ := [(Int.negOfNat 17084602251974091279558637340641746), (Int.negOfNat 905343949902013701604699294877747), (Int.ofNat 220643610827290000003637006626999), (Int.ofNat 62764414188510953704225698162211), (Int.negOfNat 10403154603295776854619682117884), (Int.negOfNat 1571075166740157857763416001134), (Int.ofNat 288153031983293479496020199341), (Int.ofNat 18865693488955468609862773659), (Int.negOfNat 4275068675075594271269421895), (Int.negOfNat 107281340200346259390088235), (Int.ofNat 37566210043689252451533121), (Int.ofNat 193851559888359007060397), (Int.negOfNat 217210747378892750672034), (Int.ofNat 1223010061541296561803), (Int.ofNat 892219463906161788196), (Int.negOfNat 11016388334010279332), (Int.negOfNat 3282301198106778365), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell07Integer_checked :
    integerCompileSumCheck intBasis07 cosineIntegerTerms reflectedSineIntegerTerms negativeCell07Integer = true := by
  decide +kernel

def negativeCell07 : OuterCellModel := ⟨(15/32), (1/32), [(-8542301125987045639779318670320873/11258999068426240000000000000000000), (-905343949902013701604699294877747/22517998136852480000000000000000000), (220643610827290000003637006626999/22517998136852480000000000000000000), (62764414188510953704225698162211/22517998136852480000000000000000000), (-2600788650823944213654920529471/5629499534213120000000000000000000), (-785537583370078928881708000567/11258999068426240000000000000000000), (288153031983293479496020199341/22517998136852480000000000000000000), (18865693488955468609862773659/22517998136852480000000000000000000), (-855013735015118854253884379/4503599627370496000000000000000000), (-21456268040069251878017647/4503599627370496000000000000000000)], (1/100000000)⟩

theorem negativeCell07_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell07Integer = Outer180.polynomial148.reflect.compiledCoefficients basis07 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis07_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell07Integer_checked
  exact hi.symm

theorem negativeCell07_exact : negativeCell07.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis07).take 10 := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_error : Outer180.polynomial148.reflect.compiledError basis07 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis07).drop 10) ≤ negativeCell07.error := by
  rw [← negativeCell07_full_exact]
  decide +kernel

theorem negativeCell07_correct : negativeCell07.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell07 Outer180.polynomial148.reflect basis07_correct
    (by decide +kernel) 10 negativeCell07_exact negativeCell07_error

def negativeCell08Integer : List ℤ := [(Int.negOfNat 17707580017534349012667405677437123), (Int.ofNat 331158217190279954188359823363991), (Int.ofNat 295971625880761720254145422699938), (Int.negOfNat 34310492523770453703538446844847), (Int.negOfNat 8276097920174904940296480023915), (Int.ofNat 1627878286579883510911530668597), (Int.ofNat 118522721454969220545266531501), (Int.negOfNat 32907291421688187834525107099), (Int.negOfNat 703528127906888108126592055), (Int.ofNat 368625143172556168707396715), (Int.negOfNat 661024475675930003977919), (Int.negOfNat 2595001950513931909120397), (Int.ofNat 36101916021774707698806), (Int.ofNat 12553492586363350376317), (Int.negOfNat 262436004548377444124), (Int.negOfNat 44957001448847834508), (Int.ofNat 1241993329909830795), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell08Integer_checked :
    integerCompileSumCheck intBasis08 cosineIntegerTerms reflectedSineIntegerTerms negativeCell08Integer = true := by
  decide +kernel

def negativeCell08 : OuterCellModel := ⟨(17/32), (1/32), [(-17707580017534349012667405677437123/22517998136852480000000000000000000), (331158217190279954188359823363991/22517998136852480000000000000000000), (147985812940380860127072711349969/11258999068426240000000000000000000), (-34310492523770453703538446844847/22517998136852480000000000000000000), (-1655219584034980988059296004783/4503599627370496000000000000000000), (1627878286579883510911530668597/22517998136852480000000000000000000), (118522721454969220545266531501/22517998136852480000000000000000000), (-32907291421688187834525107099/22517998136852480000000000000000000), (-140705625581377621625318411/4503599627370496000000000000000000), (73725028634511233741479343/4503599627370496000000000000000000)], (1/100000000)⟩

theorem negativeCell08_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell08Integer = Outer180.polynomial148.reflect.compiledCoefficients basis08 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis08_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell08Integer_checked
  exact hi.symm

theorem negativeCell08_exact : negativeCell08.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis08).take 10 := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_error : Outer180.polynomial148.reflect.compiledError basis08 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis08).drop 10) ≤ negativeCell08.error := by
  rw [← negativeCell08_full_exact]
  decide +kernel

theorem negativeCell08_correct : negativeCell08.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell08 Outer180.polynomial148.reflect basis08_correct
    (by decide +kernel) 10 negativeCell08_exact negativeCell08_error

def negativeCell09Integer : List ℤ := [(Int.negOfNat 16212810274046650351637262863386074), (Int.ofNat 976825636189260823624821092200569), (Int.ofNat 28405860699996801876447736079509), (Int.negOfNat 34259881282305249789651409605600), (Int.ofNat 6488642216841245406888654330792), (Int.ofNat 639249598958316295664497827980), (Int.negOfNat 209255401480060639272460900821), (Int.negOfNat 3304067527402003782458317458), (Int.ofNat 3108234617368146161487576073), (Int.negOfNat 37106228045058684196493750), (Int.negOfNat 27146025830136426870777500), (Int.ofNat 687150760149909782379408), (Int.ofNat 156242731614982423606535), (Int.negOfNat 5138884941107309776633), (Int.negOfNat 639039918105157570741), (Int.ofNat 24222986492188403349), (Int.ofNat 2610284379817637639), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell09Integer_checked :
    integerCompileSumCheck intBasis09 cosineIntegerTerms reflectedSineIntegerTerms negativeCell09Integer = true := by
  decide +kernel

def negativeCell09 : OuterCellModel := ⟨(19/32), (1/32), [(-8106405137023325175818631431693037/11258999068426240000000000000000000), (976825636189260823624821092200569/22517998136852480000000000000000000), (28405860699996801876447736079509/22517998136852480000000000000000000), (-42824851602881562237064262007/28147497671065600000000000000000), (811080277105155675861081791349/2814749767106560000000000000000000), (31962479947915814783224891399/1125899906842624000000000000000000), (-209255401480060639272460900821/22517998136852480000000000000000000), (-1652033763701001891229158729/11258999068426240000000000000000000), (3108234617368146161487576073/22517998136852480000000000000000000), (-5936996487209389471439/3602879701896396800000000000000)], (1/100000000)⟩

theorem negativeCell09_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell09Integer = Outer180.polynomial148.reflect.compiledCoefficients basis09 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis09_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell09Integer_checked
  exact hi.symm

theorem negativeCell09_exact : negativeCell09.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis09).take 10 := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_error : Outer180.polynomial148.reflect.compiledError basis09 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis09).drop 10) ≤ negativeCell09.error := by
  rw [← negativeCell09_full_exact]
  decide +kernel

theorem negativeCell09_correct : negativeCell09.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell09 Outer180.polynomial148.reflect basis09_correct
    (by decide +kernel) 10 negativeCell09_exact negativeCell09_error

def negativeCell10Integer : List ℤ := [(Int.negOfNat 14308404705112759781247727271837157), (Int.ofNat 899419354648648604824250879494070), (Int.negOfNat 17612552519172652792081165090309), (Int.ofNat 12886303996139255565479480753252), (Int.ofNat 2413810462333807324274321504755), (Int.negOfNat 1016682188495817066251918195195), (Int.negOfNat 5682778640811112461194672377), (Int.ofNat 21816108923245564302224054906), (Int.negOfNat 610922517501672660708099835), (Int.negOfNat 243636098615143254253011468), (Int.ofNat 10297239178611492444702855), (Int.ofNat 1693481756251086866351071), (Int.negOfNat 85273035694800031919264), (Int.negOfNat 8061563844168472049398), (Int.ofNat 451929008557166755309), (Int.ofNat 27222378826323475773), (Int.negOfNat 1602344851931504746), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell10Integer_checked :
    integerCompileSumCheck intBasis10 cosineIntegerTerms reflectedSineIntegerTerms negativeCell10Integer = true := by
  decide +kernel

def negativeCell10 : OuterCellModel := ⟨(21/32), (1/32), [(-14308404705112759781247727271837157/22517998136852480000000000000000000), (89941935464864860482425087949407/2251799813685248000000000000000000), (-17612552519172652792081165090309/22517998136852480000000000000000000), (3221575999034813891369870188313/5629499534213120000000000000000000), (482762092466761464854864300951/4503599627370496000000000000000000), (-203336437699163413250383639039/4503599627370496000000000000000000), (-5682778640811112461194672377/22517998136852480000000000000000000), (10908054461622782151112027453/11258999068426240000000000000000000), (-122184503500334532141619967/4503599627370496000000000000000000), (-60909024653785813563252867/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell10_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell10Integer = Outer180.polynomial148.reflect.compiledCoefficients basis10 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis10_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell10Integer_checked
  exact hi.symm

theorem negativeCell10_exact : negativeCell10.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis10).take 10 := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_error : Outer180.polynomial148.reflect.compiledError basis10 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis10).drop 10) ≤ negativeCell10.error := by
  rw [← negativeCell10_full_exact]
  decide +kernel

theorem negativeCell10_correct : negativeCell10.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell10 Outer180.polynomial148.reflect basis10_correct
    (by decide +kernel) 10 negativeCell10_exact negativeCell10_error

def negativeCell11Integer : List ℤ := [(Int.negOfNat 12468677404799093566951719745185726), (Int.ofNat 987077083272952457175905634331282), (Int.ofNat 47540707798955269762280869788105), (Int.ofNat 650827659772164837900009830680), (Int.negOfNat 3455344649721025343976044630997), (Int.ofNat 105154323252844673398598584658), (Int.ofNat 120820413293036744903737571874), (Int.negOfNat 7028878612482355968980735488), (Int.negOfNat 1811478162550886771051694334), (Int.ofNat 127586061148487720183243002), (Int.ofNat 15509577042995455990396841), (Int.negOfNat 1218333714108739896490445), (Int.negOfNat 86492082286535098432161), (Int.ofNat 7396137242488235370935), (Int.ofNat 339022358786597044824), (Int.negOfNat 31396844883653075899), (Int.negOfNat 1584001817726098859), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell11Integer_checked :
    integerCompileSumCheck intBasis11 cosineIntegerTerms reflectedSineIntegerTerms negativeCell11Integer = true := by
  decide +kernel

def negativeCell11 : OuterCellModel := ⟨(23/32), (1/32), [(-6234338702399546783475859872592863/11258999068426240000000000000000000), (493538541636476228587952817165641/11258999068426240000000000000000000), (9508141559791053952456173957621/4503599627370496000000000000000000), (16270691494304120947500245767/562949953421312000000000000000000), (-3455344649721025343976044630997/22517998136852480000000000000000000), (52577161626422336699299292329/11258999068426240000000000000000000), (60410206646518372451868785937/11258999068426240000000000000000000), (-13728278540004601501915499/43980465111040000000000000000000), (-905739081275443385525847167/11258999068426240000000000000000000), (63793030574243860091621501/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell11_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell11Integer = Outer180.polynomial148.reflect.compiledCoefficients basis11 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis11_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell11Integer_checked
  exact hi.symm

theorem negativeCell11_exact : negativeCell11.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis11).take 10 := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_error : Outer180.polynomial148.reflect.compiledError basis11 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis11).drop 10) ≤ negativeCell11.error := by
  rw [← negativeCell11_full_exact]
  decide +kernel

theorem negativeCell11_correct : negativeCell11.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell11 Outer180.polynomial148.reflect basis11_correct
    (by decide +kernel) 10 negativeCell11_exact negativeCell11_error

def negativeCell12Integer : List ℤ := [(Int.negOfNat 10344626868711826113539011555398033), (Int.ofNat 1101442734701437221300494769663412), (Int.negOfNat 1315214999967399166434393401087), (Int.negOfNat 9771548477075384346882329065616), (Int.ofNat 1511898268924734475985108773161), (Int.ofNat 493205017607441030289385616780), (Int.negOfNat 63945859681605803907242106110), (Int.negOfNat 10469524331481634959886706618), (Int.ofNat 1325720732004072932907102572), (Int.ofNat 113055160368596353983367784), (Int.negOfNat 15026009127808475993031511), (Int.negOfNat 738531232610930959464593), (Int.ofNat 106942213728845980959048), (Int.ofNat 3222358047964884787306), (Int.negOfNat 522051645633120483368), (Int.negOfNat 9051632185273705338), (Int.ofNat 1620602186589332437), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell12Integer_checked :
    integerCompileSumCheck intBasis12 cosineIntegerTerms reflectedSineIntegerTerms negativeCell12Integer = true := by
  decide +kernel

def negativeCell12 : OuterCellModel := ⟨(25/32), (1/32), [(-10344626868711826113539011555398033/22517998136852480000000000000000000), (275360683675359305325123692415853/5629499534213120000000000000000000), (-1315214999967399166434393401087/22517998136852480000000000000000000), (-610721779817211521680145566601/1407374883553280000000000000000000), (1511898268924734475985108773161/22517998136852480000000000000000000), (24660250880372051514469280839/1125899906842624000000000000000000), (-6394585968160580390724210611/2251799813685248000000000000000000), (-5234762165740817479943353309/11258999068426240000000000000000000), (331430183001018233226775643/5629499534213120000000000000000000), (14131895046074544247920973/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell12_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell12Integer = Outer180.polynomial148.reflect.compiledCoefficients basis12 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis12_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell12Integer_checked
  exact hi.symm

theorem negativeCell12_exact : negativeCell12.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis12).take 10 := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_error : Outer180.polynomial148.reflect.compiledError basis12 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis12).drop 10) ≤ negativeCell12.error := by
  rw [← negativeCell12_full_exact]
  decide +kernel

theorem negativeCell12_correct : negativeCell12.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell12 Outer180.polynomial148.reflect basis12_correct
    (by decide +kernel) 10 negativeCell12_exact negativeCell12_error

def negativeCell13Integer : List ℤ := [(Int.negOfNat 8190253523153025842892797847559906), (Int.ofNat 1051327990351301128881646292134566), (Int.negOfNat 3874777610591219740490381271698), (Int.ofNat 8691637105672957280736991461120), (Int.ofNat 1397410714155193030954433159854), (Int.negOfNat 463397914923548343660236695235), (Int.negOfNat 40852315498956107085281263044), (Int.ofNat 11526200197409517963327347473), (Int.ofNat 558164328236806832373114628), (Int.negOfNat 158860378421188960691343047), (Int.negOfNat 4056086834992886018124662), (Int.ofNat 1349888394262266243928337), (Int.ofNat 16927965915931805267600), (Int.negOfNat 7724971925867915273940), (Int.negOfNat 39021986855385528245), (Int.ofNat 32386532372022801643), (Int.ofNat 557719255634560079), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell13Integer_checked :
    integerCompileSumCheck intBasis13 cosineIntegerTerms reflectedSineIntegerTerms negativeCell13Integer = true := by
  decide +kernel

def negativeCell13 : OuterCellModel := ⟨(27/32), (1/32), [(-4095126761576512921446398923779953/11258999068426240000000000000000000), (525663995175650564440823146067283/11258999068426240000000000000000000), (-1937388805295609870245190635849/11258999068426240000000000000000000), (6790341488806997875575774579/17592186044416000000000000000000), (698705357077596515477216579927/11258999068426240000000000000000000), (-92679582984709668732047339047/4503599627370496000000000000000000), (-10213078874739026771320315761/5629499534213120000000000000000000), (11526200197409517963327347473/22517998136852480000000000000000000), (139541082059201708093278657/5629499534213120000000000000000000), (-158860378421188960691343047/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell13_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell13Integer = Outer180.polynomial148.reflect.compiledCoefficients basis13 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis13_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell13Integer_checked
  exact hi.symm

theorem negativeCell13_exact : negativeCell13.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis13).take 10 := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_error : Outer180.polynomial148.reflect.compiledError basis13 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis13).drop 10) ≤ negativeCell13.error := by
  rw [← negativeCell13_full_exact]
  decide +kernel

theorem negativeCell13_correct : negativeCell13.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell13 Outer180.polynomial148.reflect basis13_correct
    (by decide +kernel) 10 negativeCell13_exact negativeCell13_error

def negativeCell14Integer : List ℤ := [(Int.negOfNat 6027112741286310214647147747416854), (Int.ofNat 1145293920057780200062106161956173), (Int.ofNat 42941531530379772598834254858285), (Int.ofNat 1393897566762305858602949737026), (Int.negOfNat 2473880954741595826729047626667), (Int.negOfNat 49196699966586056858074817520), (Int.ofNat 81957489999533952802919822817), (Int.ofNat 429104744715026348368153321), (Int.negOfNat 1415863044622958938938058099), (Int.ofNat 5600639468938094167337469), (Int.ofNat 14656622697425676941942668), (Int.negOfNat 141715950205520294579945), (Int.negOfNat 99579322870122908855375), (Int.ofNat 1294454430398149060623), (Int.ofNat 475007541837084601912), (Int.negOfNat 7911100357690463917), (Int.negOfNat 1638859521247160128), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell14Integer_checked :
    integerCompileSumCheck intBasis14 cosineIntegerTerms reflectedSineIntegerTerms negativeCell14Integer = true := by
  decide +kernel

def negativeCell14 : OuterCellModel := ⟨(29/32), (1/32), [(-3013556370643155107323573873708427/11258999068426240000000000000000000), (1145293920057780200062106161956173/22517998136852480000000000000000000), (8588306306075954519766850971657/4503599627370496000000000000000000), (696948783381152929301474868513/11258999068426240000000000000000000), (-2473880954741595826729047626667/22517998136852480000000000000000000), (-614958749582325710725935219/281474976710656000000000000000000), (81957489999533952802919822817/22517998136852480000000000000000000), (429104744715026348368153321/22517998136852480000000000000000000), (-1415863044622958938938058099/22517998136852480000000000000000000), (5600639468938094167337469/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell14_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell14Integer = Outer180.polynomial148.reflect.compiledCoefficients basis14 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis14_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell14Integer_checked
  exact hi.symm

theorem negativeCell14_exact : negativeCell14.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis14).take 10 := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_error : Outer180.polynomial148.reflect.compiledError basis14 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis14).drop 10) ≤ negativeCell14.error := by
  rw [← negativeCell14_full_exact]
  decide +kernel

theorem negativeCell14_correct : negativeCell14.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell14 Outer180.polynomial148.reflect basis14_correct
    (by decide +kernel) 10 negativeCell14_exact negativeCell14_error

def negativeCell15Integer : List ℤ := [(Int.negOfNat 3589809044501974095151805144216632), (Int.ofNat 1265249146832247948385818010431530), (Int.ofNat 5601273705174822542999114016766), (Int.negOfNat 9310002180774340575534022321145), (Int.ofNat 687876201199095741541533542138), (Int.ofNat 452106382406003109520292937586), (Int.negOfNat 24966512044408255111845495333), (Int.negOfNat 10289390870748317736580627533), (Int.ofNat 481305242997755827397227048), (Int.ofNat 133123814080315469296880644), (Int.negOfNat 5597940665453608883642393), (Int.negOfNat 1094313566099770503693598), (Int.ofNat 42494964709496397696319), (Int.ofNat 6167961678788313467359), (Int.negOfNat 221492943927360893235), (Int.negOfNat 25619016657539238005), (Int.ofNat 474649084676254598), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell15Integer_checked :
    integerCompileSumCheck intBasis15 cosineIntegerTerms reflectedSineIntegerTerms negativeCell15Integer = true := by
  decide +kernel

def negativeCell15 : OuterCellModel := ⟨(31/32), (1/32), [(-448726130562746761893975643027079/2814749767106560000000000000000000), (126524914683224794838581801043153/2251799813685248000000000000000000), (2800636852587411271499557008383/11258999068426240000000000000000000), (-1862000436154868115106804464229/4503599627370496000000000000000000), (343938100599547870770766771069/11258999068426240000000000000000000), (226053191203001554760146468793/11258999068426240000000000000000000), (-24966512044408255111845495333/22517998136852480000000000000000000), (-10289390870748317736580627533/22517998136852480000000000000000000), (60163155374719478424653381/2814749767106560000000000000000000), (33280953520078867324220161/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell15_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell15Integer = Outer180.polynomial148.reflect.compiledCoefficients basis15 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis15_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell15Integer_checked
  exact hi.symm

theorem negativeCell15_exact : negativeCell15.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis15).take 10 := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_error : Outer180.polynomial148.reflect.compiledError basis15 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis15).drop 10) ≤ negativeCell15.error := by
  rw [← negativeCell15_full_exact]
  decide +kernel

theorem negativeCell15_correct : negativeCell15.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell15 Outer180.polynomial148.reflect basis15_correct
    (by decide +kernel) 10 negativeCell15_exact negativeCell15_error

def negativeCell16Integer : List ℤ := [(Int.negOfNat 1088643528575954929981896573136894), (Int.ofNat 1225471474475976962714949374014688), (Int.negOfNat 9103250243247318752183545325877), (Int.ofNat 5972909777332246158769376291339), (Int.ofNat 1791627082439963704432771879097), (Int.negOfNat 299254486880644240336059918777), (Int.negOfNat 57000375115851010687979074027), (Int.ofNat 7050133572536873810836880307), (Int.ofNat 955843823626973077202697552), (Int.negOfNat 94984874610380049364420356), (Int.negOfNat 9750459000348808837369167), (Int.ofNat 816383950899887486561322), (Int.ofNat 66159462080570103897921), (Int.negOfNat 4811158319056388419961), (Int.negOfNat 318310455332036484725), (Int.ofNat 21463540905989928275), (Int.ofNat 966842702958019402), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell16Integer_checked :
    integerCompileSumCheck intBasis16 cosineIntegerTerms reflectedSineIntegerTerms negativeCell16Integer = true := by
  decide +kernel

def negativeCell16 : OuterCellModel := ⟨(33/32), (1/32), [(-544321764287977464990948286568447/11258999068426240000000000000000000), (38295983577374280084842167937959/703687441776640000000000000000000), (-9103250243247318752183545325877/22517998136852480000000000000000000), (5972909777332246158769376291339/22517998136852480000000000000000000), (1791627082439963704432771879097/22517998136852480000000000000000000), (-299254486880644240336059918777/22517998136852480000000000000000000), (-57000375115851010687979074027/22517998136852480000000000000000000), (7050133572536873810836880307/22517998136852480000000000000000000), (59740238976685817325168597/1407374883553280000000000000000000), (-23746218652595012341105089/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell16_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell16Integer = Outer180.polynomial148.reflect.compiledCoefficients basis16 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis16_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell16Integer_checked
  exact hi.symm

theorem negativeCell16_exact : negativeCell16.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis16).take 10 := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_error : Outer180.polynomial148.reflect.compiledError basis16 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis16).drop 10) ≤ negativeCell16.error := by
  rw [← negativeCell16_full_exact]
  decide +kernel

theorem negativeCell16_correct : negativeCell16.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell16 Outer180.polynomial148.reflect basis16_correct
    (by decide +kernel) 10 negativeCell16_exact negativeCell16_error

def negativeCell17Integer : List ℤ := [(Int.ofNat 1390201958796376403831712977758923), (Int.ofNat 1287060037490574303785870696913083), (Int.ofNat 38039948931583267698906773082679), (Int.ofNat 4256561119365565774262850459677), (Int.negOfNat 2049537761569512484701589866674), (Int.negOfNat 203940535440494732278523823020), (Int.ofNat 66905452383688992200923864143), (Int.ofNat 4663624426713591195237385801), (Int.negOfNat 1146872659961730692709668581), (Int.negOfNat 61589643669811119630549131), (Int.ofNat 11938654961801101126425332), (Int.ofNat 522358313117996481853975), (Int.negOfNat 82548128341625580136825), (Int.negOfNat 3052390427536748594097), (Int.ofNat 403187567697208591048), (Int.ofNat 13950505894346250043), (Int.negOfNat 1171009015842498912), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell17Integer_checked :
    integerCompileSumCheck intBasis17 cosineIntegerTerms reflectedSineIntegerTerms negativeCell17Integer = true := by
  decide +kernel

def negativeCell17 : OuterCellModel := ⟨(35/32), (1/32), [(1390201958796376403831712977758923/22517998136852480000000000000000000), (1287060037490574303785870696913083/22517998136852480000000000000000000), (38039948931583267698906773082679/22517998136852480000000000000000000), (4256561119365565774262850459677/22517998136852480000000000000000000), (-1024768880784756242350794933337/11258999068426240000000000000000000), (-10197026772024736613926191151/1125899906842624000000000000000000), (66905452383688992200923864143/22517998136852480000000000000000000), (4663624426713591195237385801/22517998136852480000000000000000000), (-1146872659961730692709668581/22517998136852480000000000000000000), (-61589643669811119630549131/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell17_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell17Integer = Outer180.polynomial148.reflect.compiledCoefficients basis17 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis17_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell17Integer_checked
  exact hi.symm

theorem negativeCell17_exact : negativeCell17.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis17).take 10 := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_error : Outer180.polynomial148.reflect.compiledError basis17 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis17).drop 10) ≤ negativeCell17.error := by
  rw [← negativeCell17_full_exact]
  decide +kernel

theorem negativeCell17_correct : negativeCell17.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell17 Outer180.polynomial148.reflect basis17_correct
    (by decide +kernel) 10 negativeCell17_exact negativeCell17_error

def negativeCell18Integer : List ℤ := [(Int.ofNat 4115782315483181928522749550615493), (Int.ofNat 1422081832954124193370561375608161), (Int.ofNat 15073764414478920652162387198163), (Int.negOfNat 9171594708134754055457962564762), (Int.negOfNat 130248210879032312337154310663), (Int.ofNat 455489119342465190997459891128), (Int.ofNat 4973008225539882739749154564), (Int.negOfNat 10574062373153514391356107287), (Int.negOfNat 113475124654607138707586028), (Int.ofNat 139593462936267983859683033), (Int.ofNat 1554922363886977246678862), (Int.negOfNat 1172997350815882988563623), (Int.negOfNat 13496556640965993142760), (Int.ofNat 6758672568568424248140), (Int.ofNat 78191803848000059805), (Int.negOfNat 28324421219612310037), (Int.ofNat 53354080914243481), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell18Integer_checked :
    integerCompileSumCheck intBasis18 cosineIntegerTerms reflectedSineIntegerTerms negativeCell18Integer = true := by
  decide +kernel

def negativeCell18 : OuterCellModel := ⟨(37/32), (1/32), [(4115782315483181928522749550615493/22517998136852480000000000000000000), (1422081832954124193370561375608161/22517998136852480000000000000000000), (15073764414478920652162387198163/22517998136852480000000000000000000), (-4585797354067377027728981282381/11258999068426240000000000000000000), (-130248210879032312337154310663/22517998136852480000000000000000000), (56936139917808148874682486391/2814749767106560000000000000000000), (1243252056384970684937288641/5629499534213120000000000000000000), (-10574062373153514391356107287/22517998136852480000000000000000000), (-28368781163651784676896507/5629499534213120000000000000000000), (139593462936267983859683033/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell18_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell18Integer = Outer180.polynomial148.reflect.compiledCoefficients basis18 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis18_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell18Integer_checked
  exact hi.symm

theorem negativeCell18_exact : negativeCell18.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis18).take 10 := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_error : Outer180.polynomial148.reflect.compiledError basis18 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis18).drop 10) ≤ negativeCell18.error := by
  rw [← negativeCell18_full_exact]
  decide +kernel

theorem negativeCell18_correct : negativeCell18.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell18 Outer180.polynomial148.reflect basis18_correct
    (by decide +kernel) 10 negativeCell18_exact negativeCell18_error

def negativeCell19Integer : List ℤ := [(Int.ofNat 6958366366975147982922440246280309), (Int.ofNat 1401006782134375021820771990004913), (Int.negOfNat 12129926611227746707489243979719), (Int.ofNat 3402098701988444606195116111472), (Int.ofNat 2170150520464854617017395164843), (Int.negOfNat 163764875708274799973070870180), (Int.negOfNat 73409072917926633485534818573), (Int.ofNat 3399318176010182559593236462), (Int.ofNat 1294147952335961189140588068), (Int.negOfNat 37707083831808360893187136), (Int.negOfNat 13742734622452786123397849), (Int.ofNat 250134397975129345442207), (Int.ofNat 96155490270380540921712), (Int.negOfNat 1063998259981300607294), (Int.negOfNat 471235763202155163872), (Int.ofNat 2650639011330780102), (Int.ofNat 1189266350500326603), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell19Integer_checked :
    integerCompileSumCheck intBasis19 cosineIntegerTerms reflectedSineIntegerTerms negativeCell19Integer = true := by
  decide +kernel

def negativeCell19 : OuterCellModel := ⟨(39/32), (1/32), [(6958366366975147982922440246280309/22517998136852480000000000000000000), (1401006782134375021820771990004913/22517998136852480000000000000000000), (-12129926611227746707489243979719/22517998136852480000000000000000000), (212631168874277787887194756967/1407374883553280000000000000000000), (2170150520464854617017395164843/22517998136852480000000000000000000), (-8188243785413739998653543509/1125899906842624000000000000000000), (-73409072917926633485534818573/22517998136852480000000000000000000), (1699659088005091279796618231/11258999068426240000000000000000000), (323536988083990297285147017/5629499534213120000000000000000000), (-589173184872005638956049/351843720888320000000000000000000)], (1/100000000)⟩

theorem negativeCell19_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell19Integer = Outer180.polynomial148.reflect.compiledCoefficients basis19 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis19_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell19Integer_checked
  exact hi.symm

theorem negativeCell19_exact : negativeCell19.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis19).take 10 := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_error : Outer180.polynomial148.reflect.compiledError basis19 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis19).drop 10) ≤ negativeCell19.error := by
  rw [← negativeCell19_full_exact]
  decide +kernel

theorem negativeCell19_correct : negativeCell19.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell19 Outer180.polynomial148.reflect basis19_correct
    (by decide +kernel) 10 negativeCell19_exact negativeCell19_error

def negativeCell20Integer : List ℤ := [(Int.ofNat 9764594691974914923070382844394936), (Int.ofNat 1438257278411999748483234666594734), (Int.ofNat 33931497585895127279243677463891), (Int.ofNat 6296932737232780312486313293968), (Int.negOfNat 1785626563513430894484320765226), (Int.negOfNat 349857648603878984927788293408), (Int.ofNat 56420355069114467096065731786), (Int.ofNat 8930960925599547254778985592), (Int.negOfNat 893223863613435881592381186), (Int.negOfNat 127391115169459115641244838), (Int.ofNat 8249946247407494915107119), (Int.ofNat 1132710757586324576664235), (Int.negOfNat 49081089504951810304919), (Int.negOfNat 6771211510078682074825), (Int.ofNat 201885915098564169056), (Int.ofNat 29258737241534130781), (Int.negOfNat 1079636643005782261), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell20Integer_checked :
    integerCompileSumCheck intBasis20 cosineIntegerTerms reflectedSineIntegerTerms negativeCell20Integer = true := by
  decide +kernel

def negativeCell20 : OuterCellModel := ⟨(41/32), (1/32), [(1220574336496864365383797855549367/2814749767106560000000000000000000), (719128639205999874241617333297367/11258999068426240000000000000000000), (33931497585895127279243677463891/22517998136852480000000000000000000), (393558296077048769530394580873/1407374883553280000000000000000000), (-892813281756715447242160382613/11258999068426240000000000000000000), (-10933051518871218278993384169/703687441776640000000000000000000), (28210177534557233548032865893/11258999068426240000000000000000000), (1116370115699943406847373199/2814749767106560000000000000000000), (-446611931806717940796190593/11258999068426240000000000000000000), (-63695557584729557820622419/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell20_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell20Integer = Outer180.polynomial148.reflect.compiledCoefficients basis20 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis20_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell20Integer_checked
  exact hi.symm

theorem negativeCell20_exact : negativeCell20.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis20).take 10 := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_error : Outer180.polynomial148.reflect.compiledError basis20 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis20).drop 10) ≤ negativeCell20.error := by
  rw [← negativeCell20_full_exact]
  decide +kernel

theorem negativeCell20_correct : negativeCell20.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell20 Outer180.polynomial148.reflect basis20_correct
    (by decide +kernel) 10 negativeCell20_exact negativeCell20_error

def negativeCell21Integer : List ℤ := [(Int.ofNat 12791915922869426769707317662025657), (Int.ofNat 1578096869655110252168108061328690), (Int.ofNat 18346896480705057367265943586380), (Int.negOfNat 10072048531234749958869636690718), (Int.negOfNat 762056129020551297672895391836), (Int.ofNat 513503842405078757886716631388), (Int.ofNat 36104162271367088911691881217), (Int.negOfNat 11660750377666626967011226574), (Int.negOfNat 814113481497583913540933645), (Int.ofNat 143746299285021049072061252), (Int.ofNat 10215871420270093517958465), (Int.negOfNat 1086976940701159051771049), (Int.negOfNat 79448275000656126494136), (Int.ofNat 5509943324184521725602), (Int.ofNat 416985153179917670291), (Int.negOfNat 19412146568377594107), (Int.negOfNat 1207523685158154294), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell21Integer_checked :
    integerCompileSumCheck intBasis21 cosineIntegerTerms reflectedSineIntegerTerms negativeCell21Integer = true := by
  decide +kernel

def negativeCell21 : OuterCellModel := ⟨(43/32), (1/32), [(12791915922869426769707317662025657/22517998136852480000000000000000000), (157809686965511025216810806132869/2251799813685248000000000000000000), (917344824035252868363297179319/1125899906842624000000000000000000), (-5036024265617374979434818345359/11258999068426240000000000000000000), (-190514032255137824418223847959/5629499534213120000000000000000000), (128375960601269689471679157847/5629499534213120000000000000000000), (36104162271367088911691881217/22517998136852480000000000000000000), (-5830375188833313483505613287/11258999068426240000000000000000000), (-162822696299516782708186729/4503599627370496000000000000000000), (35936574821255262268015313/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell21_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell21Integer = Outer180.polynomial148.reflect.compiledCoefficients basis21 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis21_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell21Integer_checked
  exact hi.symm

theorem negativeCell21_exact : negativeCell21.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis21).take 10 := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_error : Outer180.polynomial148.reflect.compiledError basis21 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis21).drop 10) ≤ negativeCell21.error := by
  rw [← negativeCell21_full_exact]
  decide +kernel

theorem negativeCell21_correct : negativeCell21.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell21 Outer180.polynomial148.reflect basis21_correct
    (by decide +kernel) 10 negativeCell21_exact negativeCell21_error

def negativeCell22Integer : List ℤ := [(Int.ofNat 15945851320829594329346714879150298), (Int.ofNat 1548558351104774501279237784368741), (Int.negOfNat 19179245024827187350843270923980), (Int.ofNat 3036122981293953484078580063244), (Int.ofNat 3025696119730176576367247808160), (Int.negOfNat 63325356176821450048956388557), (Int.negOfNat 106705161959777002123347050299), (Int.negOfNat 1185811044531810078523148618), (Int.ofNat 1834114971594857700343140167), (Int.ofNat 50481765711063426591331010), (Int.negOfNat 17958255509385922815695780), (Int.negOfNat 662260205373815395561192), (Int.ofNat 111720812666887220887265), (Int.ofNat 4752514126903494606087), (Int.negOfNat 482399076816702681979), (Int.negOfNat 22693456671997047931), (Int.ofNat 2105919205097321041), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell22Integer_checked :
    integerCompileSumCheck intBasis22 cosineIntegerTerms reflectedSineIntegerTerms negativeCell22Integer = true := by
  decide +kernel

def negativeCell22 : OuterCellModel := ⟨(45/32), (1/32), [(7972925660414797164673357439575149/11258999068426240000000000000000000), (1548558351104774501279237784368741/22517998136852480000000000000000000), (-958962251241359367542163546199/1125899906842624000000000000000000), (759030745323488371019645015811/5629499534213120000000000000000000), (18910600748313603602295298801/140737488355328000000000000000000), (-63325356176821450048956388557/22517998136852480000000000000000000), (-106705161959777002123347050299/22517998136852480000000000000000000), (-592905522265905039261574309/11258999068426240000000000000000000), (1834114971594857700343140167/22517998136852480000000000000000000), (5048176571106342659133101/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell22_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell22Integer = Outer180.polynomial148.reflect.compiledCoefficients basis22 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis22_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell22Integer_checked
  exact hi.symm

theorem negativeCell22_exact : negativeCell22.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis22).take 10 := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_error : Outer180.polynomial148.reflect.compiledError basis22 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis22).drop 10) ≤ negativeCell22.error := by
  rw [← negativeCell22_full_exact]
  decide +kernel

theorem negativeCell22_correct : negativeCell22.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell22 Outer180.polynomial148.reflect basis22_correct
    (by decide +kernel) 10 negativeCell22_exact negativeCell22_error

def negativeCell23Integer : List ℤ := [(Int.ofNat 19030419961663518182396970162687749), (Int.ofNat 1580910436127610997157889015901166), (Int.ofNat 43484006843235297984610259475520), (Int.ofNat 10239691257203852141799212610322), (Int.negOfNat 2338123244532634212850978664527), (Int.negOfNat 671994140084271640517828439746), (Int.ofNat 53144095181049379811430978919), (Int.ofNat 17807600914223248898773892381), (Int.negOfNat 388640016357144162759803425), (Int.negOfNat 238830979707359863562915725), (Int.negOfNat 1105189424869305895272401), (Int.ofNat 1866127783040006892022083), (Int.ofNat 32787891223339162092754), (Int.negOfNat 9639406355770895846523), (Int.negOfNat 238560143966979101676), (Int.ofNat 35980961235670032292), (Int.ofNat 883686832452135725), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell23Integer_checked :
    integerCompileSumCheck intBasis23 cosineIntegerTerms reflectedSineIntegerTerms negativeCell23Integer = true := by
  decide +kernel

def negativeCell23 : OuterCellModel := ⟨(47/32), (1/32), [(19030419961663518182396970162687749/22517998136852480000000000000000000), (790455218063805498578944507950583/11258999068426240000000000000000000), (135887521385110306201907060861/70368744177664000000000000000000), (5119845628601926070899606305161/11258999068426240000000000000000000), (-2338123244532634212850978664527/22517998136852480000000000000000000), (-335997070042135820258914219873/11258999068426240000000000000000000), (53144095181049379811430978919/22517998136852480000000000000000000), (17807600914223248898773892381/22517998136852480000000000000000000), (-15545600654285766510392137/900719925474099200000000000000000), (-9553239188294394542516629/900719925474099200000000000000000)], (1/100000000)⟩

theorem negativeCell23_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell23Integer = Outer180.polynomial148.reflect.compiledCoefficients basis23 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis23_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell23Integer_checked
  exact hi.symm

theorem negativeCell23_exact : negativeCell23.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis23).take 10 := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_error : Outer180.polynomial148.reflect.compiledError basis23 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis23).drop 10) ≤ negativeCell23.error := by
  rw [← negativeCell23_full_exact]
  decide +kernel

theorem negativeCell23_correct : negativeCell23.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell23 Outer180.polynomial148.reflect basis23_correct
    (by decide +kernel) 10 negativeCell23_exact negativeCell23_error

def negativeCell24Integer : List ℤ := [(Int.ofNat 22394642171410663322112744619518960), (Int.ofNat 1766392156885379994884758613016885), (Int.ofNat 18012417653409340329801645783683), (Int.negOfNat 18787534843477893876893479662200), (Int.negOfNat 2217075333144343920897466116654), (Int.ofNat 852265067395973202446505395763), (Int.ofNat 122039716741645089203044515379), (Int.negOfNat 14279577444118649336060587661), (Int.negOfNat 2574786929090282376659868225), (Int.ofNat 94091010529193445149098125), (Int.ofNat 26433394479230224079379199), (Int.negOfNat 209250241803283827663923), (Int.negOfNat 166215296431388097222926), (Int.negOfNat 916950359996224616837), (Int.ofNat 719778696681091515004), (Int.ofNat 9806878037090685268), (Int.negOfNat 2802279136263565355), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell24Integer_checked :
    integerCompileSumCheck intBasis24 cosineIntegerTerms reflectedSineIntegerTerms negativeCell24Integer = true := by
  decide +kernel

def negativeCell24 : OuterCellModel := ⟨(49/32), (1/32), [(279933027142633291526409307743987/281474976710656000000000000000000), (353278431377075998976951722603377/4503599627370496000000000000000000), (18012417653409340329801645783683/22517998136852480000000000000000000), (-93937674217389469384467398311/112589990684262400000000000000000), (-1108537666572171960448733058327/11258999068426240000000000000000000), (852265067395973202446505395763/22517998136852480000000000000000000), (122039716741645089203044515379/22517998136852480000000000000000000), (-14279577444118649336060587661/22517998136852480000000000000000000), (-102991477163611295066394729/900719925474099200000000000000000), (150545616846709512238557/36028797018963968000000000000000)], (1/100000000)⟩

theorem negativeCell24_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell24Integer = Outer180.polynomial148.reflect.compiledCoefficients basis24 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis24_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell24Integer_checked
  exact hi.symm

theorem negativeCell24_exact : negativeCell24.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis24).take 10 := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_error : Outer180.polynomial148.reflect.compiledError basis24 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis24).drop 10) ≤ negativeCell24.error := by
  rw [← negativeCell24_full_exact]
  decide +kernel

theorem negativeCell24_correct : negativeCell24.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell24 Outer180.polynomial148.reflect basis24_correct
    (by decide +kernel) 10 negativeCell24_exact negativeCell24_error

def negativeCell25Integer : List ℤ := [(Int.ofNat 25846372901869387368635857237281652), (Int.ofNat 1624969714969473322129477158338197), (Int.negOfNat 63940672200465836093241602656682), (Int.ofNat 5366803361504911408356257689552), (Int.ofNat 7451066129854319603274908077342), (Int.ofNat 344006817247206885823652341143), (Int.negOfNat 226770146300215533744191785019), (Int.negOfNat 21650650557577012637280914742), (Int.ofNat 2384985132948263171369020367), (Int.ofNat 319417403717423502260219630), (Int.negOfNat 12917985159672238741114020), (Int.negOfNat 2511634489618527354138848), (Int.ofNat 38075642740122798023065), (Int.ofNat 12922581327066351418073), (Int.negOfNat 33948060053056785899), (Int.negOfNat 49187559393848156309), (Int.negOfNat 211670014162994999), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell25Integer_checked :
    integerCompileSumCheck intBasis25 cosineIntegerTerms reflectedSineIntegerTerms negativeCell25Integer = true := by
  decide +kernel

def negativeCell25 : OuterCellModel := ⟨(51/32), (1/32), [(6461593225467346842158964309320413/5629499534213120000000000000000000), (1624969714969473322129477158338197/22517998136852480000000000000000000), (-31970336100232918046620801328341/11258999068426240000000000000000000), (335425210094056963022266105597/1407374883553280000000000000000000), (3725533064927159801637454038671/11258999068426240000000000000000000), (344006817247206885823652341143/22517998136852480000000000000000000), (-226770146300215533744191785019/22517998136852480000000000000000000), (-10825325278788506318640457371/11258999068426240000000000000000000), (2384985132948263171369020367/22517998136852480000000000000000000), (31941740371742350226021963/2251799813685248000000000000000000)], (1/100000000)⟩

theorem negativeCell25_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell25Integer = Outer180.polynomial148.reflect.compiledCoefficients basis25 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis25_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell25Integer_checked
  exact hi.symm

theorem negativeCell25_exact : negativeCell25.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis25).take 10 := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_error : Outer180.polynomial148.reflect.compiledError basis25 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis25).drop 10) ≤ negativeCell25.error := by
  rw [← negativeCell25_full_exact]
  decide +kernel

theorem negativeCell25_correct : negativeCell25.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell25 Outer180.polynomial148.reflect basis25_correct
    (by decide +kernel) 10 negativeCell25_exact negativeCell25_error

def negativeCell26Integer : List ℤ := [(Int.ofNat 28997180759198516770457403583053187), (Int.ofNat 1649409307700946275939984686971450), (Int.ofNat 111163016909611887653829363233235), (Int.ofNat 36022544127639726721463266841353), (Int.negOfNat 5088506439021749994200852564623), (Int.negOfNat 2653971239031482566320434886885), (Int.negOfNat 123708016037156426413934628143), (Int.ofNat 39133224192486724490750030534), (Int.ofNat 3282205243596467773998174875), (Int.negOfNat 293787687287255865639890892), (Int.negOfNat 33508182620038251158143855), (Int.ofNat 1360334451123701580903209), (Int.ofNat 206952867785070074908904), (Int.negOfNat 4151720939788573575242), (Int.negOfNat 889236523831935506469), (Int.ofNat 7927744585433673467), (Int.ofNat 3162630658285239306), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell26Integer_checked :
    integerCompileSumCheck intBasis26 cosineIntegerTerms reflectedSineIntegerTerms negativeCell26Integer = true := by
  decide +kernel

def negativeCell26 : OuterCellModel := ⟨(53/32), (1/32), [(28997180759198516770457403583053187/22517998136852480000000000000000000), (32988186154018925518799693739429/450359962737049600000000000000000), (22232603381922377530765872646647/4503599627370496000000000000000000), (36022544127639726721463266841353/22517998136852480000000000000000000), (-5088506439021749994200852564623/22517998136852480000000000000000000), (-530794247806296513264086977377/4503599627370496000000000000000000), (-123708016037156426413934628143/22517998136852480000000000000000000), (19566612096243362245375015267/11258999068426240000000000000000000), (26257641948771742191985399/180143985094819840000000000000000), (-73446921821813966409972723/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell26_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell26Integer = Outer180.polynomial148.reflect.compiledCoefficients basis26 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis26_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell26Integer_checked
  exact hi.symm

theorem negativeCell26_exact : negativeCell26.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis26).take 10 := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_error : Outer180.polynomial148.reflect.compiledError basis26 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis26).drop 10) ≤ negativeCell26.error := by
  rw [← negativeCell26_full_exact]
  decide +kernel

theorem negativeCell26_correct : negativeCell26.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell26 Outer180.polynomial148.reflect basis26_correct
    (by decide +kernel) 10 negativeCell26_exact negativeCell26_error

def negativeCell27Integer : List ℤ := [(Int.ofNat 32860239450644208458288596415241354), (Int.ofNat 2147494363841387249730808843379424), (Int.negOfNat 6342733586742900482289674012943), (Int.negOfNat 104856489231686670834328096241286), (Int.negOfNat 25970930811532141838535023557403), (Int.negOfNat 184361147981050262421429470741), (Int.ofNat 512549277111645632702779374623), (Int.ofNat 28786000421284319395190392248), (Int.negOfNat 4928794169819458885644288186), (Int.negOfNat 398290182180348011309347602), (Int.ofNat 29475038714242388007028359), (Int.ofNat 2987529863087305270240365), (Int.negOfNat 121241631839496151821879), (Int.negOfNat 14960484512681276815895), (Int.ofNat 361914016829871772536), (Int.ofNat 55070335209825975659), (Int.negOfNat 814612547928543781), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell27Integer_checked :
    integerCompileSumCheck intBasis27 cosineIntegerTerms reflectedSineIntegerTerms negativeCell27Integer = true := by
  decide +kernel

def negativeCell27 : OuterCellModel := ⟨(55/32), (1/32), [(16430119725322104229144298207620677/11258999068426240000000000000000000), (67109198870043351554087776355607/703687441776640000000000000000000), (-6342733586742900482289674012943/22517998136852480000000000000000000), (-52428244615843335417164048120643/11258999068426240000000000000000000), (-25970930811532141838535023557403/22517998136852480000000000000000000), (-184361147981050262421429470741/22517998136852480000000000000000000), (512549277111645632702779374623/22517998136852480000000000000000000), (3598250052660539924398799031/2814749767106560000000000000000000), (-2464397084909729442822144093/11258999068426240000000000000000000), (-199145091090174005654673801/11258999068426240000000000000000000)], (1/100000000)⟩

theorem negativeCell27_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell27Integer = Outer180.polynomial148.reflect.compiledCoefficients basis27 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis27_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell27Integer_checked
  exact hi.symm

theorem negativeCell27_exact : negativeCell27.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis27).take 10 := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_error : Outer180.polynomial148.reflect.compiledError basis27 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis27).drop 10) ≤ negativeCell27.error := by
  rw [← negativeCell27_full_exact]
  decide +kernel

theorem negativeCell27_correct : negativeCell27.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell27 Outer180.polynomial148.reflect basis27_correct
    (by decide +kernel) 10 negativeCell27_exact negativeCell27_error

def negativeCell28Integer : List ℤ := [(Int.ofNat 35904628635733312939629884295702625), (Int.ofNat 123548566522502458468629289978887), (Int.negOfNat 1141431324132077318410307707524373), (Int.negOfNat 232282685085628323884578213439110), (Int.ofNat 4374352437953650827020097419787), (Int.ofNat 5682532625812154710321282582780), (Int.ofNat 229034070986772401705019528270), (Int.negOfNat 67832260160665307994410714582), (Int.negOfNat 4315061613364156723223363852), (Int.ofNat 502599867979890999967893336), (Int.ofNat 39255988074188215871812631), (Int.negOfNat 2563792562787990155651527), (Int.negOfNat 229697735958444807180568), (Int.ofNat 9581929775141619106014), (Int.ofNat 958276655753423263128), (Int.negOfNat 26744032514226870502), (Int.negOfNat 3180887992943066997), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell28Integer_checked :
    integerCompileSumCheck intBasis28 cosineIntegerTerms reflectedSineIntegerTerms negativeCell28Integer = true := by
  decide +kernel

def negativeCell28 : OuterCellModel := ⟨(57/32), (1/32), [(287237029085866503517039074365621/180143985094819840000000000000000), (123548566522502458468629289978887/22517998136852480000000000000000000), (-1141431324132077318410307707524373/22517998136852480000000000000000000), (-23228268508562832388457821343911/2251799813685248000000000000000000), (4374352437953650827020097419787/22517998136852480000000000000000000), (284126631290607735516064129139/1125899906842624000000000000000000), (22903407098677240170501952827/2251799813685248000000000000000000), (-33916130080332653997205357291/11258999068426240000000000000000000), (-1078765403341039180805840963/5629499534213120000000000000000000), (62824983497486374995986667/2814749767106560000000000000000000)], (1/100000000)⟩

theorem negativeCell28_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell28Integer = Outer180.polynomial148.reflect.compiledCoefficients basis28 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis28_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell28Integer_checked
  exact hi.symm

theorem negativeCell28_exact : negativeCell28.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis28).take 10 := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_error : Outer180.polynomial148.reflect.compiledError basis28 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis28).drop 10) ≤ negativeCell28.error := by
  rw [← negativeCell28_full_exact]
  decide +kernel

theorem negativeCell28_correct : negativeCell28.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell28 Outer180.polynomial148.reflect basis28_correct
    (by decide +kernel) 10 negativeCell28_exact negativeCell28_error

def negativeCell29Integer : List ℤ := [(Int.ofNat 29984732100953977331158438839933061), (Int.negOfNat 6624494927924427780642614366688950), (Int.negOfNat 1971205710665940430724459727261816), (Int.ofNat 24114472458054468807441790224346), (Int.ofNat 53536894992464688650826859376009), (Int.ofNat 2034623824580224513452706831118), (Int.negOfNat 782995099026788980433403446516), (Int.negOfNat 44759122384271287676294278273), (Int.ofNat 7141820433094625908196411452), (Int.ofNat 477805180883530094228752487), (Int.negOfNat 44461301162328783531578418), (Int.negOfNat 3239792801544859514037617), (Int.ofNat 200653250889518367683960), (Int.ofNat 15453402062230378291220), (Int.negOfNat 685256020797506311515), (Int.negOfNat 55414481410452274803), (Int.ofNat 1840895110020082561), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell29Integer_checked :
    integerCompileSumCheck intBasis29 cosineIntegerTerms reflectedSineIntegerTerms negativeCell29Integer = true := by
  decide +kernel

def negativeCell29 : OuterCellModel := ⟨(59/32), (1/32), [(29984732100953977331158438839933061/22517998136852480000000000000000000), (-132489898558488555612852287333779/450359962737049600000000000000000), (-246400713833242553840557465907727/2814749767106560000000000000000000), (12057236229027234403720895112173/11258999068426240000000000000000000), (53536894992464688650826859376009/22517998136852480000000000000000000), (1017311912290112256726353415559/11258999068426240000000000000000000), (-195748774756697245108350861629/5629499534213120000000000000000000), (-44759122384271287676294278273/22517998136852480000000000000000000), (1785455108273656477049102863/5629499534213120000000000000000000), (477805180883530094228752487/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell29_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell29Integer = Outer180.polynomial148.reflect.compiledCoefficients basis29 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis29_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell29Integer_checked
  exact hi.symm

theorem negativeCell29_exact : negativeCell29.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis29).take 10 := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_error : Outer180.polynomial148.reflect.compiledError basis29 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis29).drop 10) ≤ negativeCell29.error := by
  rw [← negativeCell29_full_exact]
  decide +kernel

theorem negativeCell29_correct : negativeCell29.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell29 Outer180.polynomial148.reflect basis29_correct
    (by decide +kernel) 10 negativeCell29_exact negativeCell29_error

def negativeCell30Integer : List ℤ := [(Int.ofNat 9911714324754970209798643817763368), (Int.negOfNat 12506225085767265576430581374847988), (Int.negOfNat 582448271567665971017459721896387), (Int.ofNat 398023832965948819479557984860618), (Int.ofNat 23592057235373967107271851110956), (Int.negOfNat 7388042359456495920718159856363), (Int.negOfNat 471330510979201283345411577417), (Int.ofNat 84929014328453141082442216119), (Int.ofNat 5518930987356344841230355299), (Int.negOfNat 652297133594434665499094869), (Int.negOfNat 42418280909104403203540908), (Int.ofNat 3553821757600441111205585), (Int.ofNat 229585648651595975458055), (Int.negOfNat 14399801046265111364223), (Int.negOfNat 920868863192400770352), (Int.ofNat 44352306344934466357), (Int.ofNat 3199145327600894688), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell30Integer_checked :
    integerCompileSumCheck intBasis30 cosineIntegerTerms reflectedSineIntegerTerms negativeCell30Integer = true := by
  decide +kernel

def negativeCell30 : OuterCellModel := ⟨(61/32), (1/32), [(1238964290594371276224830477220421/2814749767106560000000000000000000), (-3126556271441816394107645343711997/5629499534213120000000000000000000), (-582448271567665971017459721896387/22517998136852480000000000000000000), (199011916482974409739778992430309/11258999068426240000000000000000000), (5898014308843491776817962777739/5629499534213120000000000000000000), (-7388042359456495920718159856363/22517998136852480000000000000000000), (-471330510979201283345411577417/22517998136852480000000000000000000), (84929014328453141082442216119/22517998136852480000000000000000000), (5518930987356344841230355299/22517998136852480000000000000000000), (-652297133594434665499094869/22517998136852480000000000000000000)], (1/100000000)⟩

theorem negativeCell30_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell30Integer = Outer180.polynomial148.reflect.compiledCoefficients basis30 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis30_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell30Integer_checked
  exact hi.symm

theorem negativeCell30_exact : negativeCell30.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis30).take 10 := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_error : Outer180.polynomial148.reflect.compiledError basis30 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis30).drop 10) ≤ negativeCell30.error := by
  rw [← negativeCell30_full_exact]
  decide +kernel

theorem negativeCell30_correct : negativeCell30.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell30 Outer180.polynomial148.reflect basis30_correct
    (by decide +kernel) 10 negativeCell30_exact negativeCell30_error

def negativeCell31Integer : List ℤ := [(Int.negOfNat 14123533426822490694186855114207928), (Int.negOfNat 9944300869513674586003999737483331), (Int.ofNat 1731322159174255301151768467758751), (Int.ofNat 269288759350687607714661126046647), (Int.negOfNat 51633897517058673178844229764164), (Int.negOfNat 4971755205226901204546162918786), (Int.ofNat 817308486178149217991476591556), (Int.ofNat 61264919414723663778027604653), (Int.negOfNat 8073437011150952724931378968), (Int.negOfNat 520690766691471395809117364), (Int.ofNat 54132866284077768774583153), (Int.ofNat 3160698994752429374684518), (Int.negOfNat 261712603368479156547559), (Int.negOfNat 14193131751454699408079), (Int.ofNat 954270089806082093915), (Int.ofNat 48001424408225284565), (Int.negOfNat 2873263450330897238), (Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 0)]

theorem negativeCell31Integer_checked :
    integerCompileSumCheck intBasis31 cosineIntegerTerms reflectedSineIntegerTerms negativeCell31Integer = true := by
  decide +kernel

def negativeCell31 : OuterCellModel := ⟨(63/32), (1/32), [(-1765441678352811336773356889275991/2814749767106560000000000000000000), (-9944300869513674586003999737483331/22517998136852480000000000000000000), (1731322159174255301151768467758751/22517998136852480000000000000000000), (269288759350687607714661126046647/22517998136852480000000000000000000), (-12908474379264668294711057441041/5629499534213120000000000000000000), (-2485877602613450602273081459393/11258999068426240000000000000000000), (204327121544537304497869147889/5629499534213120000000000000000000), (61264919414723663778027604653/22517998136852480000000000000000000), (-1009179626393869090616422371/2814749767106560000000000000000000), (-130172691672867848952279341/5629499534213120000000000000000000)], (1/100000000)⟩

theorem negativeCell31_full_exact : decodeCoefficients (weightDenominator * (Int.ofNat 1125899906842624)) negativeCell31Integer = Outer180.polynomial148.reflect.compiledCoefficients basis31 := by
  have hi := Numerics.OuterFourierPolynomial.compiledCoefficients_eq_integer Outer180.polynomial148.reflect weightDenominator (Int.ofNat 1125899906842624)
    intBasis31_exact reflectedCosineIntegerTerms_exact reflectedSineIntegerTerms_exact negativeCell31Integer_checked
  exact hi.symm

theorem negativeCell31_exact : negativeCell31.coefficients = (Outer180.polynomial148.reflect.compiledCoefficients basis31).take 10 := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_error : Outer180.polynomial148.reflect.compiledError basis31 + coefficientAbsSum ((Outer180.polynomial148.reflect.compiledCoefficients basis31).drop 10) ≤ negativeCell31.error := by
  rw [← negativeCell31_full_exact]
  decide +kernel

theorem negativeCell31_correct : negativeCell31.Correct Outer180.polynomial148.reflect :=
  OuterCellModel.correct_of_basis_truncated negativeCell31 Outer180.polynomial148.reflect basis31_correct
    (by decide +kernel) 10 negativeCell31_exact negativeCell31_error

def negativeModel (j : ℕ) : OuterCellModel := (if j < 16 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then negativeCell00 else negativeCell01) else (if j < 3 then negativeCell02 else negativeCell03)) else (if j < 6 then (if j < 5 then negativeCell04 else negativeCell05) else (if j < 7 then negativeCell06 else negativeCell07))) else (if j < 12 then (if j < 10 then (if j < 9 then negativeCell08 else negativeCell09) else (if j < 11 then negativeCell10 else negativeCell11)) else (if j < 14 then (if j < 13 then negativeCell12 else negativeCell13) else (if j < 15 then negativeCell14 else negativeCell15)))) else (if j < 24 then (if j < 20 then (if j < 18 then (if j < 17 then negativeCell16 else negativeCell17) else (if j < 19 then negativeCell18 else negativeCell19)) else (if j < 22 then (if j < 21 then negativeCell20 else negativeCell21) else (if j < 23 then negativeCell22 else negativeCell23))) else (if j < 28 then (if j < 26 then (if j < 25 then negativeCell24 else negativeCell25) else (if j < 27 then negativeCell26 else negativeCell27)) else (if j < 30 then (if j < 29 then negativeCell28 else negativeCell29) else (if j < 31 then negativeCell30 else negativeCell31)))))

theorem negativeModel_correct (j : ℕ) (hj : j < 32) : (negativeModel j).Correct Outer180.polynomial148.reflect := by
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

end Bin148
end
end ErdosOverlap.OuterNumerics
