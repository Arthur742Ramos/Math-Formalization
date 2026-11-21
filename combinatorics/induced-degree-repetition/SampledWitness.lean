module

public import RetainedRows
public import SampleSelection
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V : Type}

/-- Assemble the parity core, the exceptional-row bounds and the group edits
on a single realization of the original product sample. -/
theorem sampled_witness {g n s r : ℕ} (G : SimpleGraph V) (p θ η v κ count : ℝ) (T : Finset V)
    (len : Fin n → ℕ) (pool : Fin g → (i : Fin n) → Fin (len i) → Finset V)
    (ref : ∀ j i, ↥(tupleSpace (List.ofFn (pool j i)))) (ys : Fin g → Fin s → T) (m : ℕ)
    (length : ∑ i, len i=m)
    (dis : ∀ a b : (z : Fin g × Fin n) × Fin (len z.2), a ≠ b →
      Disjoint (pool a.1.1 a.1.2 a.2) (pool b.1.1 b.1.2 b.2)) (away : ∀ j i k, Disjoint (pool j i k) T)
    (inj : Function.Injective (fun z : Fin g × Fin s => ys z.1 z.2))
    (mom : fourthMoment (fun i j : Fin g × Fin s => centered G p (ys i.1 i.2) (ys j.1 j.2)) univ ≤ κ^2)
    (few : ((univ.filter (fun z : Fin g × Fin s => ∃ j, v < |(∑ i, (tupleDegree (adj G) (ys z.1 z.2) (ref j i):ℝ))-p*m|)).card:ℝ) ≤ count)
    (edits : ∀ j, Adjustable G θ (fun i => List.ofFn (pool j i)) (fun _ => exteriorList j (fun k t => (ys k t:V)))
      (fun i => (ref j i).val) (fun t => (ys j t).val))
    (θp : 0 < θ) (ep : 0 ≤ η) (vp : 0 < v) (kp : 0 ≤ κ) (p₀ : 2*θ ≤ p) (p₁ : p ≤ 1-2*θ)
    (margin : 2+((g:ℝ)+2)*v ≤ θ*m) (nh : 4*r ≤ g*s) (tail : g*m < r)
    (exc : (2*r:ℕ)*κ/v^2+count+(g*m:ℕ) ≤ η*r) :
    ∃ S : Finset V, ∃ d : ℕ, r ≤ S.card ∧ S.card < 2*r ∧ (1-η)*S.card ≤ ((degreeClass G S d).card:ℝ) := by
  classical
  let x : Fin g × Fin s ↪ V := ⟨fun z => ys z.1 z.2,fun _ _ h => inj (Subtype.ext h)⟩
  let W := univ.map x
  let ref' := fun j i => (ref j i).val
  let total := fun y => ∑ j, contribution G (ref' j) y
  have hw : W.card=g*s := by simp [W,Fintype.card_prod]
  obtain ⟨E,eW,lo,hi,e,small,par⟩ := parity_core G W r (g*m) (hw.symm ▸ nh) tail total
  let other := univ.filter (fun z : Fin g × Fin s => ∃ j, v < |(∑ i, (tupleDegree (adj G) (ys z.1 z.2) (ref j i):ℝ))-p*m|)
  obtain ⟨good,goodE,loss,base,out⟩ := retained_errors G p v κ vp kp x E eW mom other
  obtain ⟨d,parD,near⟩ := nearby_parity (p*(E.card+g*m)) (mul_nonneg (by linarith) (by positivity)) e small
  have label (y) (hy : y ∈ good) : ∃ j k, (ys j k:V)=y := by
    obtain ⟨⟨j,k⟩,_,eq⟩ := mem_map.mp (eW (goodE hy))
    exact ⟨j,k,eq⟩
  obtain ⟨S,hs⟩ := good_witness G η p θ v len pool T E good (fun j k => (ys j k:V))
    ref' (fun j _ => exteriorList j (fun k t => (ys k t:V))) m d length
    (fun y hy => by obtain ⟨z,_,rfl⟩ := mem_map.mp (eW hy); exact (ys z.1 z.2).2) goodE label dis away edits
    (fun j _ k t ne => exterior_mem j k t ne (fun j k => (ys j k:V))) lo hi (by
      have es : E.card ≤ 2*r := by omega
      have a := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr es) kp) (sq_nonneg v)
      have b := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr lo : (r:ℝ) ≤ (E.card+g*m:ℕ)) ep
      change (other.card:ℝ) ≤ count at few
      push_cast [Nat.cast_sub (card_le_card goodE)] at exc a b ⊢
      linarith) θp p₀ p₁ margin near (fun y hy => (par _ (goodE hy)).trans parD.symm) base (by
      intro y hy j
      obtain ⟨k,t,rfl⟩ := label y hy
      have no := out (k,t) hy
      apply le_of_not_gt
      intro h
      apply no
      apply mem_filter.mpr
      exact ⟨mem_univ _,j,by simpa [contribution,ref',Nat.cast_sum] using h⟩)
  exact ⟨S,d,hs⟩

end InducedDegreeRepetition.Sampling
