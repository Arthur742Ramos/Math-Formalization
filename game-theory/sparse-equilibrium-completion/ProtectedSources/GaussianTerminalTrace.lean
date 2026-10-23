/- AI-assisted Gaussian global-height continuation; Apache-2.0.
Exact check status is recorded in source-bound receipts outside this source.
The original uncompiled v1 draft is preserved in source-global-height-v1.
Frozen Gaussian kernel APIs are unchanged. No bit-cost or general LP claim.
-/
module
public import ProtectedSources.GaussianActualMinors
@[expose] public section
open scoped BigOperators Matrix
namespace SparseCompletion.Gaussian

def columnStepEquiv (ι : Type*) (n : ℕ) :
    ((ι ⊕ Unit) ⊕ Fin n) ≃ ι ⊕ Fin (n+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr 0))
    (fun j => Sum.inr j.succ)
  invFun := Sum.elim (fun i => Sum.inl (Sum.inl i))
    (Fin.cases (Sum.inl (Sum.inr ())) Sum.inr)
  left_inv x := by
    rcases x with (i | u) | j
    · rfl
    · cases u
      rfl
    · simp
  right_inv x := by
    rcases x with i | j
    · rfl
    · refine Fin.cases rfl (fun _ => by simp) j

theorem minorStage_dimensions {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) : k+n = N := by
  induction h with
  | initial => simp
  | step previous p hp ih => omega

/-- The actual selected and remaining labels partition the entire original
input, exactly once, even for empty prefix or empty remaining dimensions. -/
theorem minorStage_columns_bijective {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) : Function.Bijective (Sum.elim Q σ) := by
  induction h with
  | initial =>
    constructor
    · intro x y hxy
      rcases x with x | x
      · exact PEmpty.elim x
      · rcases y with y | y
        · exact PEmpty.elim y
        · exact congrArg Sum.inr hxy
    · intro j
      exact ⟨Sum.inr j, rfl⟩
  | @step k n P Q σ B previous p hp ih =>
    have he : Sum.elim (appendMap Q (σ 0)) (fun j => σ j.succ) =
        (Sum.elim Q σ) ∘ columnStepEquiv (PrefixIndex k) n := by
      funext x
      rcases x with (x | u) | j <;> rfl
    rw [he]
    exact ih.comp (columnStepEquiv (PrefixIndex k) n).bijective

theorem minorStage_remaining_val {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) : ∀ j, (σ j).val = k+j.val := by
  induction h with
  | initial => intro j; simp
  | @step k n P Q σ B previous p hp ih =>
    intro j
    change (σ j.succ).val = k+1+j.val
    have hh := ih j.succ
    simp only [Fin.val_succ] at hh
    omega

theorem minorStage_selected_zero {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) : ∀ s j, entry B (P s) j = 0 := by
  induction h with
  | initial => intro s; exact PEmpty.elim s
  | @step k n P Q σ B previous p hp ih =>
    intro s j
    rcases s with s | u
    · simpa only [entry_tableOfFn, appendMap, Sum.elim_inl] using
        residual_preserves_zero_row (entry B) p (P s) (ih s) j
    · have hp0 := firstNonzero_some r (fun i => entry B i 0) p hp
      simpa only [entry_tableOfFn, appendMap, Sum.elim_inr] using
        residual_pivot_row_zero (entry B) p hp0 j

theorem minorStage_rows_injective {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) : Function.Injective P := by
  induction h with
  | initial => intro s; exact PEmpty.elim s
  | @step k n P Q σ B previous p hp ih =>
    have hp0 := firstNonzero_some r (fun i => entry B i 0) p hp
    have hne : ∀ s, P s ≠ p := by
      intro s hs
      apply hp0
      simpa only [hs] using minorStage_selected_zero previous s 0
    intro x y hxy
    rcases x with x | u <;> rcases y with y | v
    · exact congrArg Sum.inl (ih hxy)
    · exact False.elim (hne x hxy)
    · exact False.elim (hne y hxy.symm)
    · exact congrArg Sum.inr (Subsingleton.elim u v)

theorem minorStage_pivots_le_rows {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) : k ≤ r := by
  simpa only [prefixIndex_card, Fintype.card_fin] using
    Fintype.card_le_of_injective P (minorStage_rows_injective h)

/-- Success of the actual recursive call extends any actual previous stage to
its real zero-first-column terminal stage. The output's unit coordinate tracks
the exact number of newly executed pivots, rather than a surrogate cost count. -/
theorem kernel_terminal_trace {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (hstage : MinorStage A k n P Q σ B) (w : QVec n)
    (hkernel : kernel r n B = some w) :
    ∃ f : Fin n, w.get f = 1 ∧ (∀ j, f < j → w.get j = 0) ∧
      ∃ (k' m : ℕ) (P' : PrefixIndex k' → Fin r) (Q' : PrefixIndex k' → Fin N)
        (σ' : Fin (m+1) → Fin N) (C : QTable r (m+1)),
        MinorStage A k' (m+1) P' Q' σ' C ∧
        firstNonzero r (fun i => entry C i 0) = none ∧ k' = k+f.val := by
  induction n generalizing k with
  | zero => simp [kernel] at hkernel
  | succ n ih =>
    cases hp : firstNonzero r (fun i => entry B i 0) with
    | none =>
      have hw : List.Vector.ofFn (Fin.cons 1 (fun _ : Fin n => 0)) = w := by
        simpa only [kernel, hp, Option.some.injEq] using hkernel
      subst w
      refine ⟨0, by simp, ?_, k, n, P, Q, σ, B, hstage, hp, by simp⟩
      intro j
      refine Fin.cases (by simp) (fun _ _ => by simp) j
    | some p =>
      cases hc : kernel r n (tableOfFn (residual (entry B) p)) with
      | none => simp [kernel, hp, hc] at hkernel
      | some u =>
        have hw : List.Vector.ofFn (lift (entry B) p u.get) = w := by
          simpa only [kernel, hp, hc, Option.map_some, Option.some.injEq] using hkernel
        subst w
        obtain ⟨f, hf, hz, k', m, P', Q', σ', C, hs, hstop, hk'⟩ :=
          ih (MinorStage.step hstage p hp) u hc
        refine ⟨f.succ, by simpa using hf, ?_, k', m, P', Q', σ', C,
          hs, hstop, ?_⟩
        · intro j
          refine Fin.cases (by simp) ?_ j
          intro j hj
          exact by simpa using hz j (by simpa using hj)
        · simp only [Fin.val_succ]
          omega

/-- Every real returned vector therefore has a real terminal trace, an actual
unit free column, zeros on every later column, and a computed prefix length
bounded by the number of rows. Zero-column failure cannot fake this witness. -/
theorem kernel_terminal_data {r N : ℕ} (A : QTable r N) (w : QVec N)
    (hkernel : kernel r N A = some w) :
    ∃ (k n : ℕ) (P : PrefixIndex k → Fin r) (Q : PrefixIndex k → Fin N)
      (σ : Fin (n+1) → Fin N) (B : QTable r (n+1)),
      MinorStage A k (n+1) P Q σ B ∧
      firstNonzero r (fun i => entry B i 0) = none ∧
      k < N ∧ k ≤ r ∧ w.get (σ 0) = 1 ∧
      ∀ j : Fin n, w.get (σ j.succ) = 0 := by
  obtain ⟨f, hf, hz, k, n, P, Q, σ, B, hs, hstop, hk⟩ :=
    kernel_terminal_trace (MinorStage.initial (A := A)) w hkernel
  have hkf : k = f.val := by simpa using hk
  have hσ : σ 0 = f := by
    apply Fin.ext
    have hval := minorStage_remaining_val hs 0
    simpa only [Fin.val_zero, add_zero, hkf] using hval
  refine ⟨k, n, P, Q, σ, B, hs, hstop, ?_, minorStage_pivots_le_rows hs, ?_, ?_⟩
  · simpa only [hkf] using f.isLt
  · simpa only [hσ] using hf
  · intro j
    apply hz
    change f.val < (σ j.succ).val
    rw [minorStage_remaining_val hs, ← hkf]
    simp

/-- Selected ORIGINAL rows of the actual returned relation solve the prefix
square system with the negative ORIGINAL free column. The actual column
bijection earns the sum split; no unknown outside-support residual is dropped. -/
theorem terminal_prefix_equation {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin (n+1) → Fin N} {B : QTable r (n+1)}
    (hs : MinorStage A k (n+1) P Q σ B) (v : Fin N → ℚ)
    (hv : IsKernel A v) (hf : v (σ 0) = 1)
    (hz : ∀ j : Fin n, v (σ j.succ) = 0) :
    selectedBlock (entry A) P Q *ᵥ (fun t => v (Q t)) =
      fun s => -entry A (P s) (σ 0) := by
  classical
  funext s
  change (∑ t, entry A (P s) (Q t) * v (Q t)) = -entry A (P s) (σ 0)
  have he := (minorStage_columns_bijective hs).sum_comp
    (fun j => entry A (P s) j * v j)
  rw [Fintype.sum_sum_type, Fin.sum_univ_succ] at he
  simp only [Sum.elim_inl, Sum.elim_inr, hf, mul_one, hz,
    mul_zero, Finset.sum_const_zero, add_zero] at he
  have hzero : (∑ j, entry A (P s) j * v j) = 0 := hv (P s)
  linarith

end SparseCompletion.Gaussian
