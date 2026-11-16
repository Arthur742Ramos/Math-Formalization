/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.IntegralClaim

/-!
# Balanced gluing of already proved integral certificates

Only four rational/integer equalities are checked at a join. Both local
analytic proofs are reused by theorem application, so a balanced assembly
does not revisit a large list of original leaves.
-/

namespace ErdosOverlap.Numerics.IntegralClaim

open MeasureTheory

public section

structure LowerCertificate (f : ℝ → ℝ) (error : ℚ) (c : IntegralClaim) : Prop where
  integrable : IntervalIntegrable f volume (c.left : ℝ) (c.right : ℝ)
  bound : (((c.amount : ℚ) / (fixedScale : ℚ) - error * (c.right - c.left) : ℚ) : ℝ) ≤
    ∫ t in (c.left : ℝ)..(c.right : ℝ), f t

structure UpperCertificate (f : ℝ → ℝ) (error : ℚ) (c : IntegralClaim) : Prop where
  integrable : IntervalIntegrable f volume (c.left : ℝ) (c.right : ℝ)
  bound : (∫ t in (c.left : ℝ)..(c.right : ℝ), f t) ≤
    (((c.amount : ℚ) / (fixedScale : ℚ) + error * (c.right - c.left) : ℚ) : ℝ)

@[expose] def joinCheck (a b c : IntegralClaim) : Bool :=
  decide (a.right = b.left ∧ c.left = a.left ∧ c.right = b.right ∧
    c.amount = a.amount + b.amount)

private theorem forall_pair {P : IntegralClaim → Prop} {a b : IntegralClaim}
    (ha : P a) (hb : P b) : ∀ d ∈ [a, b], P d := by
  intro d hd
  rcases List.mem_cons.mp hd with hd | hd
  · subst d
    exact ha
  · have he : d = b := List.mem_singleton.mp hd
    subst d
    exact hb

theorem LowerCertificate.glue {f : ℝ → ℝ} {error : ℚ} {a b c : IntegralClaim}
    (ha : LowerCertificate f error a) (hb : LowerCertificate f error b)
    (hc : joinCheck a b c = true) : LowerCertificate f error c := by
  have hs : a.right = b.left ∧ c.left = a.left ∧ c.right = b.right ∧
      c.amount = a.amount + b.amount := of_decide_eq_true hc
  have hchain : chainCheck a.left b.right [a, b] = true := by
    simp [chainCheck, hs.1]
  have hi := forall_pair
    (P := fun d => IntervalIntegrable f volume (d.left : ℝ) (d.right : ℝ))
    ha.integrable hb.integrable
  have hlocal := forall_pair
    (P := fun d => (((d.amount : ℚ) / (fixedScale : ℚ) -
      error * (d.right - d.left) : ℚ) : ℝ) ≤
      ∫ t in (d.left : ℝ)..(d.right : ℝ), f t) ha.bound hb.bound
  refine ⟨?_, ?_⟩
  · simpa only [hs.2.1, hs.2.2.1] using chain_integrable hchain hi
  · have h := lower_bound_rat hchain hi hlocal
    simpa only [total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, hs.2.1, hs.2.2.1, hs.2.2.2] using h

theorem UpperCertificate.glue {f : ℝ → ℝ} {error : ℚ} {a b c : IntegralClaim}
    (ha : UpperCertificate f error a) (hb : UpperCertificate f error b)
    (hc : joinCheck a b c = true) : UpperCertificate f error c := by
  have hs : a.right = b.left ∧ c.left = a.left ∧ c.right = b.right ∧
      c.amount = a.amount + b.amount := of_decide_eq_true hc
  have hchain : chainCheck a.left b.right [a, b] = true := by
    simp [chainCheck, hs.1]
  have hi := forall_pair
    (P := fun d => IntervalIntegrable f volume (d.left : ℝ) (d.right : ℝ))
    ha.integrable hb.integrable
  have hlocal := forall_pair
    (P := fun d => (∫ t in (d.left : ℝ)..(d.right : ℝ), f t) ≤
      (((d.amount : ℚ) / (fixedScale : ℚ) + error * (d.right - d.left) : ℚ) : ℝ))
    ha.bound hb.bound
  refine ⟨?_, ?_⟩
  · simpa only [hs.2.1, hs.2.2.1] using chain_integrable hchain hi
  · have h := upper_bound_rat hchain hi hlocal
    simpa only [total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, hs.2.1, hs.2.2.1, hs.2.2.2] using h

end
end ErdosOverlap.Numerics.IntegralClaim
