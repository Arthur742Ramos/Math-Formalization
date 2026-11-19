/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierTrigData

namespace ErdosOverlap.FrontierTrig
open Numerics
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem cosineSum_append (xs ys : List CosineTerm) (t : ℝ) :
    cosineSum (xs ++ ys) t = cosineSum xs t + cosineSum ys t := by
  induction xs with
  | nil => simp [cosineSum]
  | cons x xs ih => simp only [List.cons_append, cosineSum, ih]; ring

def correctionChunk00 : List CosineTerm := [⟨(2970005434023 / 500000000000 : ℚ), (-15418636573637 / 200000000000000000 : ℚ)⟩, ⟨(8459639015983 / 1000000000000 : ℚ), (-31069822843763 / 500000000000000000 : ℚ)⟩, ⟨(160226331108947 / 1000000000000 : ℚ), (12119033929 / 200000000000000000 : ℚ)⟩, ⟨(21135657945867 / 125000000000 : ℚ), (35170983009 / 500000000000000000 : ℚ)⟩, ⟨(87960901795701 / 500000000000 : ℚ), (116657171437 / 1000000000000000000 : ℚ)⟩, ⟨(93682778410277 / 500000000000 : ℚ), (111065511071 / 1000000000000000000 : ℚ)⟩, ⟨(46998614391117 / 250000000000 : ℚ), (13366998003 / 200000000000000000 : ℚ)⟩, ⟨(194779094310759 / 1000000000000 : ℚ), (92242690011 / 100000000000000000 : ℚ)⟩, ⟨(7916833728451 / 40000000000 : ℚ), (36391239277 / 40000000000000000 : ℚ)⟩, ⟨(100502912049667 / 500000000000 : ℚ), (1497869706351 / 1000000000000000000 : ℚ)⟩, ⟨(8089457376783 / 40000000000 : ℚ), (1552330564997 / 500000000000000000 : ℚ)⟩, ⟨(204024202751173 / 1000000000000 : ℚ), (-13091388207 / 125000000000000000 : ℚ)⟩, ⟨(102241612327817 / 500000000000 : ℚ), (1832795638627 / 250000000000000000 : ℚ)⟩, ⟨(103503515767183 / 500000000000 : ℚ), (3031759894427 / 500000000000000000 : ℚ)⟩, ⟨(41922913488559 / 200000000000 : ℚ), (2092409714289 / 1000000000000000000 : ℚ)⟩, ⟨(1648331946407 / 7812500000 : ℚ), (-37905902019 / 200000000000000000 : ℚ)⟩, ⟨(43397433142779 / 200000000000 : ℚ), (56543537161 / 500000000000000000 : ℚ)⟩]

theorem chunk00_sum_identity (t : ℝ) :
    cosineSum chunk00 t =
      cosineSum Native6Trig.chunk00 t + cosineSum correctionChunk00 t := by
  simp only [chunk00, Native6Trig.chunk00, correctionChunk00,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk00_lower_identity :
    Native6.cosineLower chunk00 =
      Native6.cosineLower Native6Trig.chunk00 + Native6.cosineLower correctionChunk00 := by
  simp only [chunk00, Native6Trig.chunk00, correctionChunk00,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk01 : List CosineTerm := [⟨(16337164543921 / 40000000000 : ℚ), (-32356888921 / 1000000000000000000 : ℚ)⟩, ⟨(410458642678853 / 1000000000000 : ℚ), (-66518170911 / 1000000000000000000 : ℚ)⟩, ⟨(415583992501423 / 1000000000000 : ℚ), (20003817941 / 250000000000000000 : ℚ)⟩, ⟨(104459281932979 / 250000000000 : ℚ), (4440185067 / 500000000000000000 : ℚ)⟩]

theorem chunk01_sum_identity (t : ℝ) :
    cosineSum chunk01 t =
      cosineSum Native6Trig.chunk01 t + cosineSum correctionChunk01 t := by
  simp only [chunk01, Native6Trig.chunk01, correctionChunk01,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk01_lower_identity :
    Native6.cosineLower chunk01 =
      Native6.cosineLower Native6Trig.chunk01 + Native6.cosineLower correctionChunk01 := by
  simp only [chunk01, Native6Trig.chunk01, correctionChunk01,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk02 : List CosineTerm := [⟨(424679134771653 / 1000000000000 : ℚ), (-46255842009 / 1000000000000000000 : ℚ)⟩, ⟨(426883052594511 / 1000000000000 : ℚ), (-30284942437 / 500000000000000000 : ℚ)⟩, ⟨(570532927802181 / 1000000000000 : ℚ), (11955595697 / 1000000000000000000 : ℚ)⟩, ⟨(619685848969153 / 1000000000000 : ℚ), (1026768921 / 15625000000000000 : ℚ)⟩, ⟨(622203596359213 / 1000000000000 : ℚ), (3641396603 / 25000000000000000 : ℚ)⟩, ⟨(156287114378611 / 250000000000 : ℚ), (111466393153 / 1000000000000000000 : ℚ)⟩, ⟨(628296578646467 / 1000000000000 : ℚ), (93887693811 / 500000000000000000 : ℚ)⟩, ⟨(315065646859221 / 500000000000 : ℚ), (23128069809 / 500000000000000000 : ℚ)⟩, ⟨(631147832759033 / 1000000000000 : ℚ), (3085825189 / 31250000000000000 : ℚ)⟩]

theorem chunk02_sum_identity (t : ℝ) :
    cosineSum chunk02 t =
      cosineSum Native6Trig.chunk02 t + cosineSum correctionChunk02 t := by
  simp only [chunk02, Native6Trig.chunk02, correctionChunk02,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk02_lower_identity :
    Native6.cosineLower chunk02 =
      Native6.cosineLower Native6Trig.chunk02 + Native6.cosineLower correctionChunk02 := by
  simp only [chunk02, Native6Trig.chunk02, correctionChunk02,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk03 : List CosineTerm := [⟨(5148716680513 / 7812500000 : ℚ), (543437801 / 500000000000000000 : ℚ)⟩]

theorem chunk03_sum_identity (t : ℝ) :
    cosineSum chunk03 t =
      cosineSum Native6Trig.chunk03 t + cosineSum correctionChunk03 t := by
  simp only [chunk03, Native6Trig.chunk03, correctionChunk03,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk03_lower_identity :
    Native6.cosineLower chunk03 =
      Native6.cosineLower Native6Trig.chunk03 + Native6.cosineLower correctionChunk03 := by
  simp only [chunk03, Native6Trig.chunk03, correctionChunk03,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk04 : List CosineTerm := [⟨(65050208610379 / 62500000000 : ℚ), (-1063840651 / 500000000000000000 : ℚ)⟩]

theorem chunk04_sum_identity (t : ℝ) :
    cosineSum chunk04 t =
      cosineSum Native6Trig.chunk04 t + cosineSum correctionChunk04 t := by
  simp only [chunk04, Native6Trig.chunk04, correctionChunk04,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk04_lower_identity :
    Native6.cosineLower chunk04 =
      Native6.cosineLower Native6Trig.chunk04 + Native6.cosineLower correctionChunk04 := by
  simp only [chunk04, Native6Trig.chunk04, correctionChunk04,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk05 : List CosineTerm := []

theorem chunk05_sum_identity (t : ℝ) :
    cosineSum chunk05 t =
      cosineSum Native6Trig.chunk05 t + cosineSum correctionChunk05 t := by
  simp only [chunk05, Native6Trig.chunk05, correctionChunk05,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk05_lower_identity :
    Native6.cosineLower chunk05 =
      Native6.cosineLower Native6Trig.chunk05 + Native6.cosineLower correctionChunk05 := by
  simp only [chunk05, Native6Trig.chunk05, correctionChunk05,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk06 : List CosineTerm := []

theorem chunk06_sum_identity (t : ℝ) :
    cosineSum chunk06 t =
      cosineSum Native6Trig.chunk06 t + cosineSum correctionChunk06 t := by
  simp only [chunk06, Native6Trig.chunk06, correctionChunk06,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk06_lower_identity :
    Native6.cosineLower chunk06 =
      Native6.cosineLower Native6Trig.chunk06 + Native6.cosineLower correctionChunk06 := by
  simp only [chunk06, Native6Trig.chunk06, correctionChunk06,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk07 : List CosineTerm := []

theorem chunk07_sum_identity (t : ℝ) :
    cosineSum chunk07 t =
      cosineSum Native6Trig.chunk07 t + cosineSum correctionChunk07 t := by
  simp only [chunk07, Native6Trig.chunk07, correctionChunk07,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk07_lower_identity :
    Native6.cosineLower chunk07 =
      Native6.cosineLower Native6Trig.chunk07 + Native6.cosineLower correctionChunk07 := by
  simp only [chunk07, Native6Trig.chunk07, correctionChunk07,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk08 : List CosineTerm := []

theorem chunk08_sum_identity (t : ℝ) :
    cosineSum chunk08 t =
      cosineSum Native6Trig.chunk08 t + cosineSum correctionChunk08 t := by
  simp only [chunk08, Native6Trig.chunk08, correctionChunk08,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk08_lower_identity :
    Native6.cosineLower chunk08 =
      Native6.cosineLower Native6Trig.chunk08 + Native6.cosineLower correctionChunk08 := by
  simp only [chunk08, Native6Trig.chunk08, correctionChunk08,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk09 : List CosineTerm := []

theorem chunk09_sum_identity (t : ℝ) :
    cosineSum chunk09 t =
      cosineSum Native6Trig.chunk09 t + cosineSum correctionChunk09 t := by
  simp only [chunk09, Native6Trig.chunk09, correctionChunk09,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk09_lower_identity :
    Native6.cosineLower chunk09 =
      Native6.cosineLower Native6Trig.chunk09 + Native6.cosineLower correctionChunk09 := by
  simp only [chunk09, Native6Trig.chunk09, correctionChunk09,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

def correctionChunk10 : List CosineTerm := []

theorem chunk10_sum_identity (t : ℝ) :
    cosineSum chunk10 t =
      cosineSum Native6Trig.chunk10 t + cosineSum correctionChunk10 t := by
  simp only [chunk10, Native6Trig.chunk10, correctionChunk10,
    cosineSum, CosineTerm.value]
  push_cast
  ring

theorem chunk10_lower_identity :
    Native6.cosineLower chunk10 =
      Native6.cosineLower Native6Trig.chunk10 + Native6.cosineLower correctionChunk10 := by
  simp only [chunk10, Native6Trig.chunk10, correctionChunk10,
    Native6.cosineLower, CosineTerm.value]
  push_cast
  ring

theorem correctionTerms_split : correctionTerms =
  correctionChunk00 ++
  correctionChunk01 ++
  correctionChunk02 ++
  correctionChunk03 ++
  correctionChunk04 ++
  correctionChunk05 ++
  correctionChunk06 ++
  correctionChunk07 ++
  correctionChunk08 ++
  correctionChunk09 ++
  correctionChunk10 := by
  rfl

theorem sum_eq_old_add_corrections (t : ℝ) :
    cosineSum terms t = cosineSum Native6Trig.terms t +
      cosineSum correctionTerms t := by
  rw [correctionTerms_split]
  unfold terms Native6Trig.terms
  simp only [cosineSum_append]
  rw [chunk00_sum_identity, chunk01_sum_identity, chunk02_sum_identity, chunk03_sum_identity, chunk04_sum_identity, chunk05_sum_identity, chunk06_sum_identity, chunk07_sum_identity, chunk08_sum_identity, chunk09_sum_identity, chunk10_sum_identity]
  ring

theorem lower_eq_old_add_corrections :
    Native6.cosineLower terms = Native6.cosineLower Native6Trig.terms +
      Native6.cosineLower correctionTerms := by
  rw [correctionTerms_split]
  unfold terms Native6Trig.terms
  simp only [Numerics.cosineLower_append]
  rw [chunk00_lower_identity, chunk01_lower_identity, chunk02_lower_identity, chunk03_lower_identity, chunk04_lower_identity, chunk05_lower_identity, chunk06_lower_identity, chunk07_lower_identity, chunk08_lower_identity, chunk09_lower_identity, chunk10_lower_identity]
  ring

end
end ErdosOverlap.FrontierTrig
