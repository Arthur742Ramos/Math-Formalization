/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Exact quadratic certificates and interval chains

This module proves the real algebra needed to turn exact rational endpoint tests
into a continuous interval cover. It makes no assumptions about numerical
integration, overlap functions, or the meaning of any imported certificate.
-/

@[expose] public section

namespace ErdosOverlap.Certificate

/-- A quadratic return with rational coefficients and a rational interval. -/
structure Row where
  lo : ℚ
  hi : ℚ
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq, Repr

/-- The real-valued return represented by a row. -/
noncomputable def Row.eval (r : Row) (x : ℝ) : ℝ :=
  ((r.a : ℝ) + (r.b : ℝ) * x + (r.c : ℝ) * x ^ 2) / (r.d : ℝ)

/-- Exact rational conditions sufficient to exceed a fixed height on the row's
entire interval. These conditions are decidable in the Lean kernel. -/
def Row.Valid (r : Row) (height : ℚ) : Prop :=
  r.lo ≤ r.hi ∧ 0 < r.d ∧ r.c ≤ 0 ∧
    height * r.d < r.a + r.b * r.lo + r.c * r.lo ^ 2 ∧
    height * r.d < r.a + r.b * r.hi + r.c * r.hi ^ 2

instance (r : Row) (height : ℚ) : Decidable (r.Valid height) :=
  inferInstanceAs (Decidable (r.lo ≤ r.hi ∧ 0 < r.d ∧ r.c ≤ 0 ∧
    height * r.d < r.a + r.b * r.lo + r.c * r.lo ^ 2 ∧
    height * r.d < r.a + r.b * r.hi + r.c * r.hi ^ 2))

/-- A concave quadratic takes no smaller value in an interval than the smaller
of its two endpoint values. -/
theorem quadratic_ge_min (a b c lo hi x : ℝ) (hc : c ≤ 0)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    min (a + b * lo + c * lo ^ 2) (a + b * hi + c * hi ^ 2) ≤
      a + b * x + c * x ^ 2 := by
  by_cases heq : lo = hi
  · have hx : x = lo := by linarith
    subst x
    exact min_le_left _ _
  · have hw : 0 < hi - lo :=
      sub_pos.mpr (lt_of_le_of_ne (hlo.trans hhi) heq)
    let z := min (a + b * lo + c * lo ^ 2) (a + b * hi + c * hi ^ 2)
    have hl : 0 ≤ a + b * lo + c * lo ^ 2 - z :=
      sub_nonneg.mpr (min_le_left _ _)
    have hh : 0 ≤ a + b * hi + c * hi ^ 2 - z :=
      sub_nonneg.mpr (min_le_right _ _)
    have hsum : 0 ≤ (hi - x) * (a + b * lo + c * lo ^ 2 - z) +
        (x - lo) * (a + b * hi + c * hi ^ 2 - z) :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr hhi) hl)
        (mul_nonneg (sub_nonneg.mpr hlo) hh)
    have hcor : c * (hi - lo) * (x - lo) * (hi - x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hc hw.le) (sub_nonneg.mpr hlo))
        (sub_nonneg.mpr hhi)
    have hid : (hi - lo) * (a + b * x + c * x ^ 2 - z) =
        (hi - x) * (a + b * lo + c * lo ^ 2 - z) +
          (x - lo) * (a + b * hi + c * hi ^ 2 - z) -
          c * (hi - lo) * (x - lo) * (hi - x) := by ring
    have hprod : 0 ≤ (hi - lo) * (a + b * x + c * x ^ 2 - z) := by
      rw [hid]
      exact sub_nonneg.mpr (hcor.trans hsum)
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hw).mp hprod)

/-- Every valid row exceeds its threshold at every real point of its interval. -/
theorem Row.eval_gt (r : Row) (height : ℚ) (h : r.Valid height)
    (x : ℝ) (hlo : (r.lo : ℝ) ≤ x) (hhi : x ≤ (r.hi : ℝ)) :
    (height : ℝ) < r.eval x := by
  rcases h with ⟨_, hd, hc, hl, hh⟩
  have hd' : (0 : ℝ) < (r.d : ℝ) := by exact_mod_cast hd
  have hc' : (r.c : ℝ) ≤ 0 := by exact_mod_cast hc
  have hl' : (height : ℝ) * (r.d : ℝ) <
      (r.a : ℝ) + (r.b : ℝ) * (r.lo : ℝ) + (r.c : ℝ) * (r.lo : ℝ) ^ 2 := by
    have hcast := (Rat.cast_lt (K := ℝ)).2 hl
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_pow] using hcast
  have hh' : (height : ℝ) * (r.d : ℝ) <
      (r.a : ℝ) + (r.b : ℝ) * (r.hi : ℝ) + (r.c : ℝ) * (r.hi : ℝ) ^ 2 := by
    have hcast := (Rat.cast_lt (K := ℝ)).2 hh
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_pow] using hcast
  unfold Row.eval
  apply (lt_div_iff₀ hd').2
  exact (lt_min hl' hh').trans_le
    (quadratic_ge_min _ _ _ _ _ _ hc' hlo hhi)

/-- A finite chain of closed rational intervals. Consecutive intervals may
overlap; the definition and its theorem do not assume a sampled real grid. -/
inductive CoverChain : ℚ → ℚ → List Row → Prop
  | single (r : Row) : CoverChain r.lo r.hi [r]
  | cons (r : Row) {lo hi : ℚ} {rows : List Row}
      (join : lo ≤ r.hi) (tail : CoverChain lo hi rows) :
      CoverChain r.lo hi (r :: rows)

/-- A rational interval chain covers every real point between its endpoints. -/
theorem CoverChain.covers {lo hi : ℚ} {rows : List Row}
    (h : CoverChain lo hi rows) (x : ℝ)
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    ∃ r ∈ rows, (r.lo : ℝ) ≤ x ∧ x ≤ (r.hi : ℝ) := by
  induction h with
  | single r => exact ⟨r, List.mem_singleton_self _, hxlo, hxhi⟩
  | @cons r lo hi rows hj ht ih =>
    by_cases hr : x ≤ (r.hi : ℝ)
    · exact ⟨r, List.mem_cons_self, hxlo, hr⟩
    · have hj' : (lo : ℝ) ≤ (r.hi : ℝ) := by exact_mod_cast hj
      have hxl : (lo : ℝ) ≤ x := le_trans hj' (le_of_not_ge hr)
      rcases ih hxl hxhi with ⟨s, hs, hsl, hsh⟩
      exact ⟨s, List.mem_cons_of_mem _ hs, hsl, hsh⟩

/-- Selection of a strictly separating return from a finite valid chain. -/
theorem exists_separating_row {lo hi height : ℚ} {rows : List Row}
    (hchain : CoverChain lo hi rows)
    (hvalid : ∀ r ∈ rows, r.Valid height)
    (x : ℝ) (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    ∃ r ∈ rows, (r.lo : ℝ) ≤ x ∧ x ≤ (r.hi : ℝ) ∧ (height : ℝ) < r.eval x := by
  rcases hchain.covers x hxlo hxhi with ⟨r, hr, hl, hh⟩
  exact ⟨r, hr, hl, hh, r.eval_gt height (hvalid r hr) x hl hh⟩

end ErdosOverlap.Certificate
