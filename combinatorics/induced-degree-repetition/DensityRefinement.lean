module

public import SelfPair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

public section
namespace InducedDegreeRepetition

open Finset OpenProblems
open scoped Classical

/-- Apply the self-pair theorem inside an arbitrary subset of the ambient graph. -/
theorem self_pair_in_subset (t : ℕ) (ht : 0 < t) :
    ∃ D N₀ : ℕ, 0 < D ∧ ∀ {V : Type} (G : SimpleGraph V) (W : Finset V),
      N₀ ≤ W.card → ∃ (U : Finset V) (p : ℝ), U ⊆ W ∧ U.Nonempty ∧
        W.card ≤ D * U.card ∧ 0 ≤ p ∧ p ≤ 1 ∧ CutDiscrepancy G U p ((4/t)*(U.card : ℝ)^2) := by
  classical
  obtain ⟨D,n,hD,h⟩ := large_self_pair t ht
  refine ⟨D,n,hD,?_⟩
  intro V G W hW
  let F := G.induce (W : Set V)
  obtain ⟨T,p,hT,hsize,hp,hp',disc⟩ := h F (by simpa using hW)
  let e : W ↪ V := Function.Embedding.subtype _
  refine ⟨T.map e,p,?_,hT.map,by simpa using hsize,hp,hp',?_⟩
  · intro x hx
    obtain ⟨v,_,rfl⟩ := mem_map.mp hx
    exact v.property
  intro X hX Y hY
  rw [map_eq_image] at hX hY
  obtain ⟨A,hA,rfl⟩ := subset_image_iff.mp hX
  obtain ⟨B,hB,rfl⟩ := subset_image_iff.mp hY
  rw [← map_eq_image, ← map_eq_image]
  have same (x y : W) : centered F p x y = centered G p (e x) (e y) := by
    by_cases ha : G.Adj x.val y.val <;> simp [centered,F,e,ha]
  simp only [sum_map, card_map]
  have result := disc A hA B hB
  simp only [same] at result
  convert result using 1

private theorem rect_counts {V : Type*} (G : SimpleGraph V) (p : ℝ) (X Y : Finset V) :
    (∑ x ∈ X, ∑ y ∈ Y, centered G p x y) =
      (∑ x ∈ X, ((Y.filter fun y => adj G x y = true).card : ℝ)) - p*(X.card*Y.card) := by
  classical
  simp [centered, adj, sum_sub_distrib, mul_comm, mul_left_comm]

/-- A two-sided cut in a self-pair forces its center away from the endpoints. -/
private theorem center_interior {V : Type*} (G : SimpleGraph V)
    (W U : Finset V) (hUW : U ⊆ W) (p d s τ : ℝ) (hτ : 0 < τ)
    (hU : 4 ≤ U.card) (hs : 4*s ≤ U.card)
    (cuts : CutBounds G W s τ) (disc : CutDiscrepancy G U p d)
    (small : 32*d ≤ τ*(U.card : ℝ)^2) : τ/2 ≤ p ∧ p ≤ 1-τ/2 := by
  classical
  obtain ⟨X,hX,hcard⟩ := exists_subset_card_eq (s := U) (n := U.card/2) (by omega)
  let Y := U \ X
  have hY : Y ⊆ U := sdiff_subset
  have hd : Disjoint X Y := disjoint_sdiff
  have hycard : Y.card + X.card = U.card := card_sdiff_add_card_eq_card hX
  have xlarge : (U.card : ℝ) ≤ 4*X.card := by exact_mod_cast (show U.card ≤ 4*X.card by omega)
  have ylarge : (U.card : ℝ) ≤ 4*Y.card := by exact_mod_cast (show U.card ≤ 4*Y.card by omega)
  have uPos : (0:ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  have xy : 0 < (X.card : ℝ)*Y.card := mul_pos (by linarith) (by linarith)
  have hprod := mul_le_mul xlarge ylarge (Nat.cast_nonneg U.card) (by positivity)
  have err : d ≤ τ/2 * ((X.card : ℝ)*Y.card) := by nlinarith [mul_le_mul_of_nonneg_left hprod hτ.le]
  have both (b) := cuts X (hX.trans hUW) Y (hY.trans hUW) hd (by linarith) (by linarith) b
  have discrepancy := abs_le.mp (disc X hX Y hY)
  rw [rect_counts] at discrepancy
  have split : (∑ x ∈ X, ((Y.filter fun y => adj G x y = true).card : ℝ)) +
      (∑ x ∈ X, ((Y.filter fun y => adj G x y = false).card : ℝ)) = X.card * Y.card := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _ ∈ X, (Y.card : ℝ) := sum_congr rfl fun x _ => by
        have e : (Y.filter fun y => adj G x y = false) = Y.filter fun y => ¬ adj G x y = true := by
          ext; simp
        rw [e, ← Nat.cast_add, card_filter_add_card_filter_not]
      _ = _ := by simp
  constructor <;> apply le_of_mul_le_mul_right (a := (X.card : ℝ)*Y.card) _ xy
  · nlinarith [both true,discrepancy.2]
  · nlinarith [both false,discrepancy.1]

/-- Finite refinement step in Lemma 3. The size loss D and host threshold depend only
on the error tolerances. The inherited cutoff can be any s ≤ |W|/(4D). -/
theorem refine_two_sided_cuts (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ D n : ℕ, 0 < D ∧ ∀ {V : Type} (G : SimpleGraph V) (W : Finset V)
      (s : ℝ), n ≤ W.card → 4*(D:ℝ)*s ≤ W.card → CutBounds G W s τ →
      ∃ (B : Finset V) (p : ℝ), B ⊆ W ∧ W.card ≤ D*B.card ∧ τ/2 ≤ p ∧ p ≤ 1-τ/2 ∧
        CutBounds G B s τ ∧ (∀ x ∈ B, |(degreeOn G B x : ℝ)-p*B.card| ≤ ε*B.card) ∧
        SpectralBound G B p ε := by
  classical
  let a := min (ε/6) (1/4)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have haε : 6*a ≤ ε := by linarith [min_le_left (ε/6) (1/4)]
  have ha1 : a ≤ 1/4 := min_le_right _ _
  obtain ⟨t,ht⟩ := exists_nat_ge (max (4/a^2) (128/τ))
  have htA : 4/a^2 ≤ (t:ℝ) := (le_max_left ..).trans ht
  have htB : 128/τ ≤ (t:ℝ) := (le_max_right ..).trans ht
  have tp : 0 < (t:ℝ) := (show 0 < 128/τ by positivity).trans_le htB
  have epsA : 4/(t:ℝ) ≤ a^2 := (div_le_iff₀ tp).mpr (by
    rw [mul_comm]; exact (div_le_iff₀ (sq_pos_of_pos ha)).mp htA)
  have epsB : 32*(4/(t:ℝ)) ≤ τ := by
    rw [← mul_div_assoc, div_le_iff₀ tp,mul_comm τ]
    convert (div_le_iff₀ hτ).mp htB using 1; norm_num
  obtain ⟨D,n,hD,self⟩ := self_pair_in_subset t (by exact_mod_cast tp)
  refine ⟨2*D,max n (4*D),by positivity,?_⟩
  intro V G W s hn hs cuts
  obtain ⟨U,p,hu,hne,hsize,hp,hp',disc⟩ := self G W ((le_max_left ..).trans hn)
  have dpos : 0 < (D:ℝ) := by exact_mod_cast hD
  have sz : (W.card : ℝ) ≤ D*U.card := by exact_mod_cast hsize
  have h4 : 4 ≤ U.card := by
    have hh : 4*D ≤ D*U.card := ((le_max_right ..).trans hn).trans hsize
    rwa [Nat.mul_comm 4, Nat.mul_le_mul_left_iff hD] at hh
  have scale : 4*s ≤ U.card := by
    by_cases hh : s ≤ 0
    · linarith [show (0:ℝ) ≤ U.card by positivity]
    push_cast at hs
    apply le_of_mul_le_mul_right (a := (D:ℝ)) _ dpos
    nlinarith [mul_nonneg dpos.le (le_of_not_ge hh)]
  have interior := center_interior G W U hu p _ s τ hτ h4 scale cuts disc (by
    nlinarith [mul_le_mul_of_nonneg_right epsB (sq_nonneg (U.card:ℝ))])
  obtain ⟨B,hBU,half,deg,spec⟩ := prune_self_pair G U hne p a hp hp' ha ha1 (fun X hX Y hY =>
    (disc X hX Y hY).trans (mul_le_mul_of_nonneg_right epsA (sq_nonneg _)))
  refine ⟨B,p,hBU.trans hu,?_,interior.1,interior.2,?_,?_,?_⟩
  · have h' : U.card ≤ 2*B.card := by exact_mod_cast half
    exact hsize.trans ((Nat.mul_le_mul_left _ h').trans_eq (by ac_rfl))
  · exact fun X hX Y hY => cuts X (hX.trans (hBU.trans hu)) Y (hY.trans (hBU.trans hu))
  · exact fun x hx => (deg x hx).trans (mul_le_mul_of_nonneg_right haε (Nat.cast_nonneg _))
  · intro v
    apply (spec v).trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith : 4*a ≤ ε) (Nat.cast_nonneg _)

end InducedDegreeRepetition
