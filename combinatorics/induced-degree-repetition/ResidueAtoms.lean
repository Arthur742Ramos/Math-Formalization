module

public import RemainingStatements
public import PoolLaw
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Residues

open Finset Duality OpenProblems
open scoped Classical
variable {V P : Type*} {q : ℕ} [NeZero q]

theorem tuple_len {sets : List (Finset V)} {p : List V} (hp : p ∈ tupleSpace sets) :
    p.length = sets.length := by
  induction sets generalizing p with
  | nil => simpa [tupleSpace] using congrArg List.length (mem_singleton.mp hp)
  | cons X t ih =>
    obtain ⟨⟨x,p⟩,h,rfl⟩ := mem_map.mp hp
    simpa using ih (mem_product.mp h).2

omit [NeZero q] in
theorem sum_adj {n : ℕ} (G : SimpleGraph V) (ys : Fin n → V) (p : List V) (j : Fin n) :
    vectorSum (fun x i => adjMod q G x (ys i)) p j = (tupleDegree (adj G) (ys j) p : ZMod q) := by
  induction p with
  | nil => simp [vectorSum,tupleDegree]
  | cons x p ih =>
    by_cases h : G.Adj x (ys j)
    · have h' := h.symm
      simpa [vectorSum,tupleDegree,adj,adjMod,h,h',List.countP_cons,add_comm] using ih
    · have h' : ¬G.Adj (ys j) x := fun m => h (m.symm)
      simpa [vectorSum,tupleDegree,adj,adjMod,h,h',List.countP_cons] using ih

theorem large_integer_fiber (Q : Finset P) (f : P → ℕ) (L : ℕ) (small : ∀ p ∈ Q, f p ≤ L) :
    ∃ t, Q.card ≤ (L+1)*(Q.filter (fun p => f p = t)).card := by
  classical
  let g t := (Q.filter fun p => f p=t).card
  obtain ⟨t,_,h⟩ := (range (L+1)).exists_max_image g (by simp)
  refine ⟨t,?_⟩
  have all : Q.filter (fun p => f p ∈ range (L+1)) = Q := filter_eq_self.mpr fun p hp =>
    mem_range.mpr (Nat.lt_succ_of_le (small p hp))
  calc
    _ = ∑ j ∈ range (L+1), g j := by
      have e := sum_card_fiberwise_eq_card_filter Q (range (L+1)) f
      rw [all] at e
      exact e.symm
    _ ≤ _ := by simpa using sum_le_sum (s := range (L+1)) fun j hj => h j hj

omit [NeZero q] in
theorem separated_atoms (Q : Finset P) (f : P → ℕ) (L : ℕ) (small : ∀ p ∈ Q, f p ≤ L)
    (ξ : ℝ) (hp : 0 < ξ) (h1 : ξ ≤ 1) (qpos : 0 < Q.card)
    (notHeavy : ∀ t : ZMod q, ((Q.filter (fun p => (f p : ZMod q) = t)).card:ℝ) ≤ (1-ξ)*Q.card) :
    ∃ k l, ¬ Nat.ModEq q k l ∧ ξ/(L+1)*Q.card ≤ ((Q.filter fun p => f p = k).card:ℝ) ∧
      ξ/(L+1)*Q.card ≤ ((Q.filter fun p => f p = l).card:ℝ) := by
  classical
  obtain ⟨k,hk⟩ := large_integer_fiber Q f L small
  let O := Q.filter fun p => (f p : ZMod q) ≠ (k:ZMod q)
  have hp' := notHeavy (k:ZMod q)
  have tot : ((Q.filter (fun p => (f p : ZMod q) = (k:ZMod q))).card:ℝ)+O.card = Q.card := by
    exact_mod_cast card_filter_add_card_filter_not (s := Q) (fun p => (f p : ZMod q) = (k:ZMod q))
  have outside : ξ*Q.card ≤ O.card := by linarith
  obtain ⟨l,hl⟩ := large_integer_fiber O f L fun p m => small p (mem_filter.mp m).1
  have positive : 0 < O.card := by exact_mod_cast (mul_pos hp (show (0:ℝ) < Q.card by exact_mod_cast qpos)).trans_le outside
  have witness : (O.filter fun p => f p = l).Nonempty := card_pos.mp (by
    by_contra! h
    have e := Nat.eq_zero_of_le_zero h
    rw [e,Nat.mul_zero] at hl
    omega)
  obtain ⟨p,hw⟩ := witness
  have neq := (mem_filter.mp (mem_filter.mp hw).1).2
  rw [(mem_filter.mp hw).2] at neq
  have lp : 0 < (L:ℝ)+1 := by positivity
  refine ⟨k,l,fun h => neq ((ZMod.natCast_eq_natCast_iff ..).mpr h.symm),?_,?_⟩
  · rw [div_mul_eq_mul_div,div_le_iff₀ lp]
    have h : (Q.card:ℝ) ≤ ((L:ℝ)+1)*(Q.filter (fun p => f p=k)).card := by exact_mod_cast hk
    nlinarith only [h,mul_le_of_le_one_left (Nat.cast_nonneg Q.card : (0:ℝ)≤Q.card) h1]
  · rw [div_mul_eq_mul_div,div_le_iff₀ lp]
    have le : (O.filter (fun p => f p=l)).card ≤ (Q.filter (fun p => f p=l)).card :=
      card_le_card (filter_subset_filter _ (filter_subset ..))
    have h : (O.card:ℝ) ≤ ((L:ℝ)+1)*(Q.filter (fun p => f p=l)).card := by
      exact_mod_cast hl.trans (Nat.mul_le_mul_left (L+1) le)
    nlinarith only [outside,h]

end InducedDegreeRepetition.Residues
