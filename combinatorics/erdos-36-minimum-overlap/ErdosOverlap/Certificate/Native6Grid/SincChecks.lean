module

public import ErdosOverlap.Certificate.Native6Grid.SincCheck00
public import ErdosOverlap.Certificate.Native6Grid.SincCheck01
public import ErdosOverlap.Certificate.Native6Grid.SincCheck02
public import ErdosOverlap.Certificate.Native6Grid.SincCheck03
public import ErdosOverlap.Certificate.Native6Grid.SincCheck04
public import ErdosOverlap.Certificate.Native6Grid.SincCheck05
public import ErdosOverlap.Certificate.Native6Grid.SincCheck06
public import ErdosOverlap.Certificate.Native6Grid.SincCheck07
public import ErdosOverlap.Certificate.Native6Grid.SincCheck08
public import ErdosOverlap.Certificate.Native6Grid.SincCheck09
public import ErdosOverlap.Certificate.Native6Grid.SincCheck10
public import ErdosOverlap.Certificate.Native6Normalization

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def checkedLowerAtZero : ℚ := 99999999999999/100000000000000

theorem lowerAtZero_checked : (checkedLowerAtZero : ℝ) ≤ Native6.lowerAtZero := by
  rw [Native6.lowerAtZero_decomposition]
  unfold Native6Trig.terms
  simp only [cosineLower_append]
  have h00 := sincLower00_le
  have h01 := sincLower01_le
  have h02 := sincLower02_le
  have h03 := sincLower03_le
  have h04 := sincLower04_le
  have h05 := sincLower05_le
  have h06 := sincLower06_le
  have h07 := sincLower07_le
  have h08 := sincLower08_le
  have h09 := sincLower09_le
  have h10 := sincLower10_le
  norm_num [checkedLowerAtZero, Native6.rationalPartExact, sincLower00, sincLower01, sincLower02, sincLower03, sincLower04, sincLower05, sincLower06, sincLower07, sincLower08, sincLower09, sincLower10] at *
  linarith

end
end ErdosOverlap.Native6Grid
