/- AI-assisted original-input and transient-value continuation; Apache-2.0.
Exact compilation/audit status is recorded in source-bound receipts.
The uncompiled original draft remains in source-input-bits-v1.
These are value/encoding bounds, not primitive or total running-time claims.
-/
module
public import GaussianOutputBits
@[expose] public section
namespace SparseCompletion.Gaussian

inductive ReturnedCall {r N : ℕ} (A : QTable r N) (w : QVec N) :
    (k n : ℕ) → (PrefixIndex k → Fin r) → (PrefixIndex k → Fin N) →
      (Fin n → Fin N) → QTable r n → QVec n → Prop
  | initial (hroot : kernel r N A = some w) :
      ReturnedCall A w 0 N PEmpty.elim PEmpty.elim id A w
  | step {k n : ℕ} {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
      {σ : Fin (n+1) → Fin N} {B : QTable r (n+1)} {v : QVec (n+1)}
      (previous : ReturnedCall A w k (n+1) P Q σ B v) (p : Fin r)
      (pivot : firstNonzero r (fun i => entry B i 0) = some p)
      (u : QVec n) (child : kernel r n (tableOfFn (residual (entry B) p)) = some u) :
      ReturnedCall A w (k+1) n (appendMap P p) (appendMap Q (σ 0))
        (fun j => σ j.succ) (tableOfFn (residual (entry B) p)) u

theorem returnedCall_kernel {r N k n : ℕ} {A : QTable r N} {w : QVec N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n} {v : QVec n}
    (h : ReturnedCall A w k n P Q σ B v) : kernel r n B = some v := by
  cases h with
  | initial hroot => exact hroot
  | step previous p pivot u child => exact child

theorem returnedCall_stage {r N k n : ℕ} {A : QTable r N} {w : QVec N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n} {v : QVec n}
    (h : ReturnedCall A w k n P Q σ B v) : MinorStage A k n P Q σ B := by
  induction h with
  | initial => exact MinorStage.initial
  | step previous p pivot u child ih => exact MinorStage.step ih p pivot

/-- Every inner stored output coefficient is literally an original stored
output coefficient. This is earned from the actual Option.map/lift program. -/
theorem returnedCall_tail {r N k n : ℕ} {A : QTable r N} {w : QVec N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n} {v : QVec n}
    (h : ReturnedCall A w k n P Q σ B v) : ∀ j, v.get j = w.get (σ j) := by
  induction h with
  | initial => intro j; rfl
  | @step k n P Q σ B v previous p hp u hu ih =>
    have hv : List.Vector.ofFn (lift (entry B) p u.get) = v := by
      simpa only [kernel, hp, hu, Option.map_some, Option.some.injEq] using
        returnedCall_kernel previous
    intro j
    calc
      u.get j = v.get j.succ := by rw [← hv]; simp
      _ = w.get (σ j.succ) := ih j.succ

/-- Consequently every actual recursive stored output, including intermediate
back-substitution returns, has the root's earned polynomial binary digit bound.
No bound on an inner output is a trace constructor field or theorem premise. -/
theorem returnedCall_output_bits {r N k n : ℕ} {A : QTable r N} {w : QVec N}
    (Bbits : ℕ)
    (hnum : ∀ i j, (entry A i j).num.natAbs ≤ 2^Bbits)
    (hden : ∀ i j, (entry A i j).den ≤ 2^Bbits)
    (hroot : kernel r N A = some w)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {C : QTable r n} {v : QVec n}
    (h : ReturnedCall A w k n P Q σ C v) :
    ∀ j, Nat.size (v.get j).num.natAbs ≤ kernelOutputBitBound r N Bbits ∧
      Nat.size (v.get j).den ≤ kernelOutputBitBound r N Bbits := by
  intro j
  rw [returnedCall_tail h j]
  exact kernel_output_bits_from_original_input A Bbits hnum hden w hroot (σ j)

end SparseCompletion.Gaussian
