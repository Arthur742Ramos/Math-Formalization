/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck00
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck01
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck02
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck03
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck04
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck05
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck06
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck07
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck08
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck09
public import ErdosOverlap.Certificate.Native6Grid.RemainderCheck10

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem cosineRemainderSum_append (xs ys : List CosineTerm) (radius : ℚ) (n : ℕ) :
    cosineRemainderSum (xs ++ ys) radius n =
      cosineRemainderSum xs radius n + cosineRemainderSum ys radius n := by
  induction xs with
  | nil => simp only [List.nil_append, cosineRemainderSum, zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, cosineRemainderSum, ih]
    ring

theorem remainder_bound :
    cosineRemainderSum Native6Trig.terms taylorGridRadius 20 ≤
      (1 / 10000000000000 : ℚ) := by
  unfold Native6Trig.terms
  simp only [cosineRemainderSum_append]
  linarith [remainder00_bound, remainder01_bound, remainder02_bound, remainder03_bound, remainder04_bound, remainder05_bound, remainder06_bound, remainder07_bound, remainder08_bound, remainder09_bound, remainder10_bound]

theorem remainder_checked : taylorRemainderCheck Native6Trig.terms = true := by
  exact decide_eq_true_eq.mpr remainder_bound

end
end ErdosOverlap.Native6Grid
