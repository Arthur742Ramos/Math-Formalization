/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.LeafIntegrationAE
public import ErdosOverlap.Numerics.FixedBox

/-!
# Exact assembly of a list of local integral claims

Each amount uses the common integer scale. The chain check verifies every
adjacent endpoint and both outer endpoints. Local error terms telescope to
the error rate times the total interval length. The empty chain is allowed
exactly when its two endpoints agree.
-/

namespace ErdosOverlap.Numerics

open MeasureTheory

public section

structure IntegralClaim where
  left : ℚ
  right : ℚ
  amount : ℤ
  deriving DecidableEq, Repr

namespace IntegralClaim

@[expose] def chainCheck (lo hi : ℚ) : List IntegralClaim → Bool
  | [] => decide (lo = hi)
  | c :: cs => decide (lo = c.left) && chainCheck c.right hi cs

@[expose] def total (cs : List IntegralClaim) : ℤ :=
  (cs.map fun c => c.amount).sum

theorem total_cons (c : IntegralClaim) (cs : List IntegralClaim) :
    total (c :: cs) = c.amount + total cs := by
  simp only [total, List.map_cons, List.sum_cons]

theorem total_append (cs ds : List IntegralClaim) :
    total (cs ++ ds) = total cs + total ds := by
  simp only [total, List.map_append, List.sum_append]

theorem chainCheck_append {cs ds : List IntegralClaim} {lo mid hi : ℚ}
    (hc : chainCheck lo mid cs = true) (hd : chainCheck mid hi ds = true) :
    chainCheck lo hi (cs ++ ds) = true := by
  induction cs generalizing lo with
  | nil =>
    have he : lo = mid := of_decide_eq_true hc
    simpa only [List.nil_append, he] using hd
  | cons c cs ih =>
    change decide (lo = c.left) && chainCheck c.right mid cs = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    change decide (lo = c.left) && chainCheck c.right hi (cs ++ ds) = true
    exact Bool.and_eq_true_iff.mpr ⟨hs.1, ih hs.2⟩

theorem chain_integrable {f : ℝ → ℝ} {cs : List IntegralClaim} {lo hi : ℚ}
    (hc : chainCheck lo hi cs = true)
    (hf : ∀ c ∈ cs, IntervalIntegrable f volume (c.left : ℝ) (c.right : ℝ)) :
    IntervalIntegrable f volume (lo : ℝ) (hi : ℝ) := by
  induction cs generalizing lo with
  | nil =>
    have he : lo = hi := of_decide_eq_true hc
    rw [he]
  | cons c cs ih =>
    change decide (lo = c.left) && chainCheck c.right hi cs = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have he : lo = c.left := of_decide_eq_true hs.1
    rw [he]
    exact (hf c List.mem_cons_self).trans
      (ih hs.2 (fun d hd => hf d (List.mem_cons_of_mem c hd)))

theorem lower_bound {f : ℝ → ℝ} {cs : List IntegralClaim} {lo hi : ℚ} {error : ℝ}
    (hc : chainCheck lo hi cs = true)
    (hf : ∀ c ∈ cs, IntervalIntegrable f volume (c.left : ℝ) (c.right : ℝ))
    (hb : ∀ c ∈ cs, (c.amount : ℝ) / (fixedScale : ℝ) -
      error * ((c.right : ℝ) - (c.left : ℝ)) ≤
      ∫ t in (c.left : ℝ)..(c.right : ℝ), f t) :
    (total cs : ℝ) / (fixedScale : ℝ) - error * ((hi : ℝ) - (lo : ℝ)) ≤
      ∫ t in (lo : ℝ)..(hi : ℝ), f t := by
  induction cs generalizing lo with
  | nil =>
    have he : lo = hi := of_decide_eq_true hc
    simp only [total, List.map_nil, List.sum_nil, Int.cast_zero, zero_div, he,
      sub_self, mul_zero, intervalIntegral.integral_same, le_refl]
  | cons c cs ih =>
    change decide (lo = c.left) && chainCheck c.right hi cs = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have he : lo = c.left := of_decide_eq_true hs.1
    rw [he]
    have hfTail : ∀ d ∈ cs, IntervalIntegrable f volume (d.left : ℝ) (d.right : ℝ) :=
      fun d hd => hf d (List.mem_cons_of_mem c hd)
    have hbTail := ih hs.2 hfTail (fun d hd => hb d (List.mem_cons_of_mem c hd))
    calc
      _ = ((c.amount : ℝ) / (fixedScale : ℝ) -
          error * ((c.right : ℝ) - (c.left : ℝ))) +
          ((total cs : ℝ) / (fixedScale : ℝ) -
          error * ((hi : ℝ) - (c.right : ℝ))) := by
        rw [total_cons, Int.cast_add]
        ring
      _ ≤ (∫ t in (c.left : ℝ)..(c.right : ℝ), f t) +
          (∫ t in (c.right : ℝ)..(hi : ℝ), f t) :=
        add_le_add (hb c List.mem_cons_self) hbTail
      _ = _ := intervalIntegral.integral_add_adjacent_intervals
        (hf c List.mem_cons_self) (chain_integrable hs.2 hfTail)

theorem upper_bound {f : ℝ → ℝ} {cs : List IntegralClaim} {lo hi : ℚ} {error : ℝ}
    (hc : chainCheck lo hi cs = true)
    (hf : ∀ c ∈ cs, IntervalIntegrable f volume (c.left : ℝ) (c.right : ℝ))
    (hb : ∀ c ∈ cs, (∫ t in (c.left : ℝ)..(c.right : ℝ), f t) ≤
      (c.amount : ℝ) / (fixedScale : ℝ) + error * ((c.right : ℝ) - (c.left : ℝ))) :
    (∫ t in (lo : ℝ)..(hi : ℝ), f t) ≤
      (total cs : ℝ) / (fixedScale : ℝ) + error * ((hi : ℝ) - (lo : ℝ)) := by
  induction cs generalizing lo with
  | nil =>
    have he : lo = hi := of_decide_eq_true hc
    simp only [total, List.map_nil, List.sum_nil, Int.cast_zero, zero_div, he,
      sub_self, mul_zero, zero_add, intervalIntegral.integral_same, le_refl]
  | cons c cs ih =>
    change decide (lo = c.left) && chainCheck c.right hi cs = true at hc
    have hs := Bool.and_eq_true_iff.mp hc
    have he : lo = c.left := of_decide_eq_true hs.1
    rw [he]
    have hfTail : ∀ d ∈ cs, IntervalIntegrable f volume (d.left : ℝ) (d.right : ℝ) :=
      fun d hd => hf d (List.mem_cons_of_mem c hd)
    have hbTail := ih hs.2 hfTail (fun d hd => hb d (List.mem_cons_of_mem c hd))
    calc
      _ = (∫ t in (c.left : ℝ)..(c.right : ℝ), f t) +
          (∫ t in (c.right : ℝ)..(hi : ℝ), f t) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hf c List.mem_cons_self) (chain_integrable hs.2 hfTail)).symm
      _ ≤ ((c.amount : ℝ) / (fixedScale : ℝ) +
          error * ((c.right : ℝ) - (c.left : ℝ))) +
          ((total cs : ℝ) / (fixedScale : ℝ) +
          error * ((hi : ℝ) - (c.right : ℝ))) :=
        add_le_add (hb c List.mem_cons_self) hbTail
      _ = _ := by
        rw [total_cons, Int.cast_add]
        ring

theorem lower_bound_rat {f : ℝ → ℝ} {cs : List IntegralClaim} {lo hi error : ℚ}
    (hc : chainCheck lo hi cs = true)
    (hf : ∀ c ∈ cs, IntervalIntegrable f volume (c.left : ℝ) (c.right : ℝ))
    (hb : ∀ c ∈ cs, (((c.amount : ℚ) / (fixedScale : ℚ) -
      error * (c.right - c.left) : ℚ) : ℝ) ≤
      ∫ t in (c.left : ℝ)..(c.right : ℝ), f t) :
    ((((total cs : ℚ) / (fixedScale : ℚ) - error * (hi - lo) : ℚ) : ℝ)) ≤
      ∫ t in (lo : ℝ)..(hi : ℝ), f t := by
  push_cast at hb ⊢
  exact lower_bound hc hf hb

theorem upper_bound_rat {f : ℝ → ℝ} {cs : List IntegralClaim} {lo hi error : ℚ}
    (hc : chainCheck lo hi cs = true)
    (hf : ∀ c ∈ cs, IntervalIntegrable f volume (c.left : ℝ) (c.right : ℝ))
    (hb : ∀ c ∈ cs, (∫ t in (c.left : ℝ)..(c.right : ℝ), f t) ≤
      (((c.amount : ℚ) / (fixedScale : ℚ) + error * (c.right - c.left) : ℚ) : ℝ)) :
    (∫ t in (lo : ℝ)..(hi : ℝ), f t) ≤
      ((((total cs : ℚ) / (fixedScale : ℚ) + error * (hi - lo) : ℚ) : ℝ)) := by
  push_cast at hb ⊢
  exact upper_bound hc hf hb

end IntegralClaim
end
end ErdosOverlap.Numerics
