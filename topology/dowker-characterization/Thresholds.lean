/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-! # Positive reciprocal thresholds converging to zero -/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Dowker

def threshold (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem threshold_pos (n : ℕ) : 0 < threshold n := by
  unfold threshold
  positivity

theorem threshold_le_one (n : ℕ) : threshold n ≤ 1 := by
  unfold threshold
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  simp

theorem threshold_antitone : Antitone threshold := by
  intro n m hnm
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem exists_threshold_lt {a : ℝ} (ha : 0 < a) : ∃ n, threshold n < a := by
  exact exists_nat_one_div_lt ha

theorem threshold_tendsto : Tendsto threshold atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans (threshold_pos n)
  · intro a ha
    obtain ⟨n, hn⟩ := exists_threshold_lt ha
    exact eventually_atTop.mpr ⟨n, fun m hm => (threshold_antitone hm).trans_lt hn⟩

def intervalThreshold (n : ℕ) : unitInterval :=
  ⟨threshold n, (threshold_pos n).le, threshold_le_one n⟩

theorem intervalThreshold_ne_zero (n : ℕ) : intervalThreshold n ≠ 0 := by
  intro h
  have he := congrArg (fun t : unitInterval => (t : ℝ)) h
  exact (ne_of_gt (threshold_pos n)) he

theorem intervalThreshold_tendsto : Tendsto intervalThreshold atTop (𝓝 0) :=
  tendsto_subtype_rng.mpr threshold_tendsto

end Dowker
