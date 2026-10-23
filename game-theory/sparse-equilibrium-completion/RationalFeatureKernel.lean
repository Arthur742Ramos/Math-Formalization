/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Actual rational kernel discovery by finitely many calls
of the existing total Fourier–Motzkin solver. No polynomial complexity claim.
Classical arguments below are proofs, not a runtime kernel oracle. This module
proves the intended exact conditional completeness specification; the separate
cardinality/linear-dependence theorem and full compressor are not assumed. -/
module
public import RationalFeatureDeletion
public import RationalLinearSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Feature equations, mass, zero coordinates outside positive input support,
and one normalization equation. This is finite, genuinely enumerable row data. -/
abbrev RationalFeatureEquation (d m : ℕ) := Fin d ⊕ (Unit ⊕ (Fin m ⊕ Unit))

def rationalFeatureEquationCoefficient {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (p : Fin m) :
    RationalFeatureEquation d m → Fin m → ℚ :=
  Sum.elim A (Sum.elim (fun _ _ => 1)
    (Sum.elim (fun i j => if 0 < q i then 0 else if j = i then 1 else 0)
      (fun _ j => if j = p then 1 else 0)))

def rationalFeatureEquationRight {d m : ℕ} : RationalFeatureEquation d m → ℚ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun _ => 0) (fun _ => 1)))

/-- Each equality is encoded as its two opposite rational inequalities. No
existential feasibility decision is taken in this construction. -/
def rationalFeatureKernelSystem {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (p : Fin m) :
    RationalLinearSystem (RationalFeatureEquation d m × Bool) m where
  coefficient := fun r i => if r.2 then rationalFeatureEquationCoefficient A q p r.1 i
    else -rationalFeatureEquationCoefficient A q p r.1 i
  rightSide := fun r => if r.2 then rationalFeatureEquationRight r.1
    else -rationalFeatureEquationRight r.1

/-- Data needed by the deletion step, except nonzeroness is supplied separately. -/
def RationalFeatureDirection {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q w : Fin m → ℚ) : Prop :=
  (∀ a, ∑ i, A a i * w i = 0) ∧ (∑ i, w i = 0) ∧
    ∀ i, w i ≠ 0 → 0 < q i

theorem rational_feature_system_equations {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (p : Fin m) (w : Fin m → ℚ) :
    (rationalFeatureKernelSystem A q p).Satisfies w ↔
      ∀ r, (∑ i, rationalFeatureEquationCoefficient A q p r i * w i) =
        rationalFeatureEquationRight r := by
  constructor
  · intro h r
    have hp := h (r, true)
    have hn := h (r, false)
    simp only [rationalFeatureKernelSystem, Bool.false_eq_true, ↓reduceIte,
      neg_mul, Finset.sum_neg_distrib] at hp hn
    exact le_antisymm hp (by linarith)
  · intro h r
    rcases r with ⟨r, b⟩
    cases b <;> simp only [rationalFeatureKernelSystem, Bool.false_eq_true,
      ↓reduceIte, neg_mul, Finset.sum_neg_distrib, h r, le_refl]

theorem rational_feature_system_iff {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (p : Fin m) (w : Fin m → ℚ) :
    (rationalFeatureKernelSystem A q p).Satisfies w ↔
      RationalFeatureDirection A q w ∧ w p = 1 := by
  rw [rational_feature_system_equations]
  constructor
  · intro h
    have ha : ∀ a, ∑ i, A a i * w i = 0 := by
      intro a
      simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight]
        using h (.inl a)
    have hm : ∑ i, w i = 0 := by
      simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight]
        using h (.inr (.inl ()))
    have hs : ∀ i, w i ≠ 0 → 0 < q i := by
      intro i hi
      by_contra hqi
      have hz := h (.inr (.inr (.inl i)))
      have hw : w i = 0 := by
        simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight, hqi]
          using hz
      exact hi hw
    have hp : w p = 1 := by
      simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight]
        using h (.inr (.inr (.inr ())))
    exact ⟨⟨ha, hm, hs⟩, hp⟩
  · rintro ⟨⟨ha, hm, hs⟩, hp⟩ r
    rcases r with a | u | i | u
    · simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight] using ha a
    · simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight] using hm
    · by_cases hi : 0 < q i
      · simp [rationalFeatureEquationCoefficient, rationalFeatureEquationRight, hi]
      · have hw : w i = 0 := by
          by_contra hn
          exact hi (hs i hn)
        simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight, hi] using hw
    · simpa [rationalFeatureEquationCoefficient, rationalFeatureEquationRight] using hp

/-- The continuation is a Unit thunk. A successful pivot does not run any later
pivot's LP call. List.rec can construct tail closures; administrative costs are
not counted or bounded here. Public Option.orElse avoids a generated matcher. -/
def rationalFeatureKernelSearch {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (ps : List (Fin m)) :
    Option (Fin m → ℚ) :=
  (List.rec (motive := fun _ => Unit → Option (Fin m → ℚ))
    (fun _ => none)
    (fun p _ tail _ => (rationalLPSolve m (rationalFeatureKernelSystem A q p)).orElse tail)
    ps) ()

def rationalFeatureKernel {d m : ℕ} (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) :
    Option (Fin m → ℚ) := rationalFeatureKernelSearch A q (List.finRange m)

theorem rational_feature_search_sound {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (ps : List (Fin m))
    (w : Fin m → ℚ) (h : rationalFeatureKernelSearch A q ps = some w) :
    ∃ p ∈ ps, RationalFeatureDirection A q w ∧ w p = 1 := by
  induction ps with
  | nil => simp [rationalFeatureKernelSearch] at h
  | cons p ps ih =>
    cases he : rationalLPSolve m (rationalFeatureKernelSystem A q p) with
    | none =>
      have ht : rationalFeatureKernelSearch A q ps = some w := by
        simpa only [rationalFeatureKernelSearch, he, Option.orElse_none] using h
      obtain ⟨p', hp', hd⟩ := ih ht
      exact ⟨p', List.mem_cons_of_mem p hp', hd⟩
    | some v =>
      have hv : v = w := Option.some.inj (by
        simpa only [rationalFeatureKernelSearch, he, Option.orElse_some] using h)
      subst v
      exact ⟨p, (by simp), (rational_feature_system_iff A q p w).mp
        (rational_lp_solve_sound m _ w he)⟩

theorem rational_feature_search_complete {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (ps : List (Fin m))
    (p : Fin m) (hp : p ∈ ps) (w : Fin m → ℚ)
    (hw : RationalFeatureDirection A q w) (hn : w p = 1) :
    ∃ v, rationalFeatureKernelSearch A q ps = some v := by
  induction ps with
  | nil => simp at hp
  | cons a ps ih =>
    cases he : rationalLPSolve m (rationalFeatureKernelSystem A q a) with
    | some v =>
      exact ⟨v, by simp only [rationalFeatureKernelSearch, he,
        Option.orElse_some]⟩
    | none =>
      have hpa : p ≠ a := by
        intro hpa
        subst a
        obtain ⟨v, hv⟩ := rational_lp_solve_complete m
          (rationalFeatureKernelSystem A q p)
          ⟨w, (rational_feature_system_iff A q p w).mpr ⟨hw, hn⟩⟩
        rw [he] at hv
        cases hv
      have hpt : p ∈ ps := (List.mem_cons.mp hp).resolve_left hpa
      obtain ⟨v, hv⟩ := ih hpt
      exact ⟨v, by simpa only [rationalFeatureKernelSearch, he,
        Option.orElse_none] using hv⟩

/-- Normalizing an existing nonzero rational direction is proof-only algebra.
Runtime kernel discovery still uses the actual finite LP search above. -/
theorem rational_feature_direction_normalize {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ) (p : Fin m)
    (hw : RationalFeatureDirection A q w) (hp : w p ≠ 0) :
    RationalFeatureDirection A q (fun i => w i / w p) ∧ w p / w p = 1 := by
  rcases hw with ⟨ha, hm, hs⟩
  refine ⟨⟨?_, ?_, ?_⟩, div_self hp⟩
  · intro a
    change (∑ i, A a i * (w i / w p)) = 0
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, ha a, zero_div]
  · rw [← Finset.sum_div, hm, zero_div]
  · intro i hi
    exact hs i (fun hz => hi (by change w i / w p = 0; rw [hz, zero_div]))

theorem rational_feature_kernel_sound {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ)
    (h : rationalFeatureKernel A q = some w) :
    RationalFeatureDirection A q w ∧ ∃ i, w i ≠ 0 := by
  obtain ⟨p, _, hd, hp⟩ := rational_feature_search_sound A q (List.finRange m) w h
  exact ⟨hd, p, by rw [hp]; exact one_ne_zero⟩

/-- Completeness is not postulated: the LP solver is complete, and finite search
normalizes and tries any nonzero coordinate of any existing direction. The
separate dimension-count theorem must supply such a direction when applicable. -/
theorem rational_feature_kernel_complete {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ)
    (hw : RationalFeatureDirection A q w) (hn : ∃ p, w p ≠ 0) :
    ∃ v, rationalFeatureKernel A q = some v := by
  obtain ⟨p, hp⟩ := hn
  obtain ⟨hd, he⟩ := rational_feature_direction_normalize A q w p hw hp
  exact rational_feature_search_complete A q (List.finRange m) p
    (by simp only [List.mem_finRange]) (fun i => w i / w p) hd he

theorem rational_feature_kernel_none_iff {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) :
    rationalFeatureKernel A q = none ↔
      ¬ ∃ w, RationalFeatureDirection A q w ∧ ∃ i, w i ≠ 0 := by
  constructor
  · intro hnone ⟨w, hw, hn⟩
    obtain ⟨v, hv⟩ := rational_feature_kernel_complete A q w hw hn
    rw [hnone] at hv
    cases hv
  · intro hn
    cases he : rationalFeatureKernel A q with
    | none => rfl
    | some w => exact False.elim (hn ⟨w, rational_feature_kernel_sound A q w he⟩)

/-- End-to-end single deletion, using an ACTUALLY COMPUTED kernel direction.
No compatibility witness is accepted as program input. -/
def rationalFeatureKernelDelete {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) : Option (Fin m → ℚ) :=
  (rationalFeatureKernel A q).map (rationalFeatureDelete q)

theorem rational_feature_kernel_deletion_witness {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ)
    (hq : ∀ i, 0 ≤ q i) (h : rationalFeatureKernel A q = some w) :
    rationalFeatureKernelDelete A q = some (rationalFeatureDelete q w) ∧
    (∀ i, 0 ≤ rationalFeatureDelete q w i) ∧
    (∑ i, rationalFeatureDelete q w i) = ∑ i, q i ∧
    (∀ a, (∑ i, rationalFeatureDelete q w i * A a i) = ∑ i, q i * A a i) ∧
    (∀ i, q i = 0 → rationalFeatureDelete q w i = 0) ∧
    (rationalWeightSupport (rationalFeatureDelete q w)).card <
      (rationalWeightSupport q).card := by
  obtain ⟨⟨ha, hm, hs⟩, hn⟩ := rational_feature_kernel_sound A q w h
  refine ⟨by simp only [rationalFeatureKernelDelete, h, Option.map_some], ?_⟩
  exact rational_feature_delete_contract A q w hq hm
    (fun a => by simpa only [mul_comm] using ha a) hs hn

end SparseCompletion
