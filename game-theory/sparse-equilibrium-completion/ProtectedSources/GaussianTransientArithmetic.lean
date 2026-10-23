/- AI-assisted original-input and transient-value continuation; Apache-2.0.
Exact compilation/audit status is recorded in source-bound receipts.
The uncompiled original draft remains in source-input-bits-v1.
These are value/encoding bounds, not primitive or total running-time claims.
-/
module
public import ProtectedSources.GaussianRecursiveReturns
public import ProtectedSources.GaussianTransientStage
@[expose] public section
open scoped BigOperators
namespace SparseCompletion.Gaussian

theorem rational_mul_height (q s : ℚ) (Nq Dq Ns Ds : ℕ)
    (hqN : q.num.natAbs ≤ Nq) (hqD : q.den ≤ Dq)
    (hsN : s.num.natAbs ≤ Ns) (hsD : s.den ≤ Ds) :
    (q*s).num.natAbs ≤ Nq*Ns ∧ (q*s).den ≤ Dq*Ds := by
  have hd : (q.den : ℤ) * (s.den : ℤ) ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr q.den_ne_zero) (Int.natCast_ne_zero.mpr s.den_ne_zero)
  have he : q*s = ((q.num * s.num : ℤ) : ℚ) /
      (((q.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den s]
    push_cast
    rw [div_mul_div_comm]
  rw [he]
  constructor
  · apply (quotient_num_height _ _ hd).trans
    simpa only [Int.natAbs_mul] using Nat.mul_le_mul hqN hsN
  · apply (quotient_den_height _ _ hd).trans
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hqD hsD

theorem rational_add_height (q s : ℚ) (Nq Dq Ns Ds : ℕ)
    (hqN : q.num.natAbs ≤ Nq) (hqD : q.den ≤ Dq)
    (hsN : s.num.natAbs ≤ Ns) (hsD : s.den ≤ Ds) :
    (q+s).num.natAbs ≤ Nq*Ds+Ns*Dq ∧ (q+s).den ≤ Dq*Ds := by
  have hd : (q.den : ℤ) * (s.den : ℤ) ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr q.den_ne_zero) (Int.natCast_ne_zero.mpr s.den_ne_zero)
  have he : q+s = ((q.num * (s.den : ℤ) + s.num * (q.den : ℤ) : ℤ) : ℚ) /
      (((q.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den s]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr q.den_ne_zero, Nat.cast_ne_zero.mpr s.den_ne_zero]
  rw [he]
  constructor
  · apply (quotient_num_height _ _ hd).trans
    apply (Int.natAbs_add_le _ _).trans
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      Nat.add_le_add (Nat.mul_le_mul hqN hsD) (Nat.mul_le_mul hsN hqD)
  · apply (quotient_den_height _ _ hd).trans
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hqD hsD

/-- Every subset sum, so in particular every finite enumeration prefix, has
an explicit magnitude bound. This is a value statement; identifying compiler
accumulators with these prefixes remains part of the cost-semantics bridge. -/
theorem rational_finset_sum_height {ι : Type*} [DecidableEq ι]
    (f : ι → ℚ) (s : Finset ι) (M : ℕ)
    (h : ∀ i ∈ s, (f i).num.natAbs ≤ M ∧ (f i).den ≤ M) :
    (∑ i ∈ s, f i).num.natAbs ≤ s.card * M^s.card ∧
      (∑ i ∈ s, f i).den ≤ M^s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := h a (Finset.mem_insert_self a s)
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hadd := rational_add_height (f a) (∑ i ∈ s, f i) M M
      (s.card*M^s.card) (M^s.card) hfa.1 hfa.2 hs.1 hs.2
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    constructor
    · apply hadd.1.trans_eq
      rw [pow_succ]
      ring
    · apply hadd.2.trans_eq
      rw [pow_succ]
      ring

/-- Value bound for a real lift's actual summands and every finite partial sum.
Both coefficient and child-vector bounds are earned from real program traces,
original input bits and actual parent/child success equations.

No height bound for a child return, primitive event count, primitive cost or
cached lift sum is supplied. Repeated evaluation of this mathematical sum is
allowed; its sharing and total execution cost are separate obligations. -/
theorem actual_lift_partial_sum_height {r N k n : ℕ}
    (A : QTable r N) (w : QVec N) (Bbits : ℕ)
    (hnum : ∀ i j, (entry A i j).num.natAbs ≤ 2^Bbits)
    (hden : ∀ i j, (entry A i j).den ≤ 2^Bbits)
    (hroot : kernel r N A = some w)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin (n+1) → Fin N} {C : QTable r (n+1)} {v : QVec (n+1)}
    (hcall : ReturnedCall A w k (n+1) P Q σ C v) (p : Fin r)
    (hp : firstNonzero r (fun i => entry C i 0) = some p)
    (u : QVec n) (hchild : kernel r n (tableOfFn (residual (entry C) p)) = some u) :
    let M := (k+1).factorial * (2^(clearedInputExponent r N Bbits))^(k+1)
    let D := (2^Bbits)^(r*N) * (k.factorial * (2^(clearedInputExponent r N Bbits))^k)
    let L := (M*D) * 2^(kernelOutputBitBound r N Bbits)
    ∀ s : Finset (Fin n),
      (∑ j ∈ s, (entry C p j.succ / entry C p 0) * u.get j).num.natAbs ≤ s.card*L^s.card ∧
      (∑ j ∈ s, (entry C p j.succ / entry C p 0) * u.get j).den ≤ L^s.card := by
  dsimp only
  intro s
  apply rational_finset_sum_height
  intro j _
  have hpiv := minorStage_actual_pivot_division_height A Bbits hnum hden
    (returnedCall_stage hcall) p hp j
  have htail := returnedCall_output_bits Bbits hnum hden hroot
    (ReturnedCall.step hcall p hp u hchild) j
  have hun : (u.get j).num.natAbs ≤ 2^(kernelOutputBitBound r N Bbits) :=
    (Nat.size_le.mp htail.1).le
  have hud : (u.get j).den ≤ 2^(kernelOutputBitBound r N Bbits) :=
    (Nat.size_le.mp htail.2).le
  have hmul := rational_mul_height _ _ _ _ _ _ hpiv.1 hpiv.2 hun hud
  simpa only [Nat.mul_comm] using hmul

end SparseCompletion.Gaussian
