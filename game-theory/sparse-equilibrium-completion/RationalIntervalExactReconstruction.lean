/- AI-assisted formalization under the repository Apache-2.0 license.
Exact candidate reconstruction uses the actual rational
residual LP at epsilon, without an eta-grid or extra reconstruction slack.
Failure does not classify the whole physical class: another V may work. -/
module
public import RationalIntervalExactGuards
public import RationalIntervalRecovery
public import RationalResidualSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion


/-- The singleton-cut cap also holds at zero payoff bound. -/
theorem supported_score_cap_of_nonnegative {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i)
    (hc : Cuts M r q v) : ∀ i, q i ≠ 0 → v i ≤ M*r := by
  classical
  intro i hi
  have hqi : 0 < q i := lt_of_le_of_ne (hq i) hi.symm
  have hcut := hc {i}
  simp only [Finset.sum_singleton,mass] at hcut
  have hsq := mul_nonneg hM (sq_nonneg (q i))
  by_contra hv
  have hprod := mul_pos hqi (sub_pos.mpr (lt_of_not_ge hv))
  nlinarith

def rationalIntervalExactReconstruction {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) :
    Option ((Fin m → Fin k → ℚ) × (Fin m → Fin m → ℚ)) :=
  if rationalIntervalExactCheck lo hi V coreLo coreHi K p q M r ε then
    (rationalResidualCompletion q (rationalScore (rationalIntervalRecover lo V q) p) M ε).map
      (Prod.mk (rationalIntervalRecover lo V q))
  else none

theorem rational_interval_exact_reconstruction_origin {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ)
    (out : (Fin m → Fin k → ℚ) × (Fin m → Fin m → ℚ))
    (ho : rationalIntervalExactReconstruction lo hi V coreLo coreHi K p q M r ε = some out) :
    rationalIntervalExactCheck lo hi V coreLo coreHi K p q M r ε = true ∧
      out.1 = rationalIntervalRecover lo V q ∧
      rationalResidualCompletion q (rationalScore (rationalIntervalRecover lo V q) p) M ε = some out.2 := by
  unfold rationalIntervalExactReconstruction at ho
  split at ho
  · rename_i hc
    obtain ⟨B,hB,he⟩ := Option.map_eq_some_iff.mp ho
    subst out
    exact ⟨hc,rfl,hB⟩
  · cases ho

theorem rational_interval_exact_residual_exists {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) (hM : 0 ≤ M)
    (hc : rationalIntervalExactCheck lo hi V coreLo coreHi K p q M r ε = true) :
    ∃ B, ResidualRealConditions q (rationalScore (rationalIntervalRecover lo V q) p) M ε B := by
  have hs := (rational_interval_exact_check_iff lo hi V coreLo coreHi K p q M r ε hM).mp hc
  rcases hs with ⟨hq,hr,hV,_,_,_,hg,hcuts⟩
  have hguard : RationalIntervalExactGuards lo hi V coreLo coreHi K p q M r ε := by
    have hh := hc
    unfold rationalIntervalExactCheck at hh
    rw [Bool.and_eq_true] at hh
    exact of_decide_eq_true hh.1
  have hVq := hguard.2.2.1
  have hprod := rational_interval_recovered_product lo hi V q hVq
  let D := rationalIntervalRecover lo V q
  have hprodR : ∀ i a, (q i : ℝ)*(D i a : ℝ) = (V i a : ℝ) := by
    intro i a
    exact_mod_cast hprod i a
  have hH : ∀ i, (q i : ℝ)*score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i =
      intervalMomentScore (fun a => (p a : ℝ)) (fun i a => (V i a : ℝ)) i := by
    intro i
    unfold score intervalMomentScore
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = (p a : ℝ)*((q i : ℝ)*(D i a : ℝ)) := by ring
      _ = _ := by rw [hprodR i a]
  have hcut := (perspective_cuts_iff (fun i => (q i : ℝ))
    (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)))
    (intervalMomentScore (fun a => (p a : ℝ)) (fun i a => (V i a : ℝ)))
    (M : ℝ) (r : ℝ) (ε : ℝ) hH).mpr hcuts
  have hMr : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hgD : ∀ i, score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i ≤
      (ε : ℝ)+(M : ℝ)*(r : ℝ) := by
    intro i
    by_cases hz : q i=0
    · simpa only [score,D,rationalIntervalRecover,hz,ite_true] using hg i
    · have hn : (q i : ℝ) ≠ 0 := by exact_mod_cast hz
      have hh := supported_score_cap_of_nonnegative (fun i => (q i : ℝ))
        (fun i => score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i-(ε : ℝ))
        (M : ℝ) (r : ℝ) hMr hq hcut i hn
      linarith
  obtain ⟨B,hB,hb,hrows⟩ :=
    (weighted_completion_iff (fun i => (q i : ℝ))
      (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)))
      (M : ℝ) (r : ℝ) (ε : ℝ) hMr hq hr).mpr ⟨hgD,hcut⟩
  refine ⟨B,hB,hb,?_⟩
  intro i
  simpa only [response,rational_score_real] using hrows i

theorem rational_interval_exact_reconstruction_complete {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) (hM : 0 ≤ M)
    (hc : rationalIntervalExactCheck lo hi V coreLo coreHi K p q M r ε = true) :
    ∃ out, rationalIntervalExactReconstruction lo hi V coreLo coreHi K p q M r ε = some out := by
  obtain ⟨B,hB⟩ := rational_residual_completion_complete q
    (rationalScore (rationalIntervalRecover lo V q) p) M ε
    (rational_interval_exact_residual_exists lo hi V coreLo coreHi K p q M r ε hM hc)
  refine ⟨(rationalIntervalRecover lo V q,B),?_⟩
  simp only [rationalIntervalExactReconstruction,hc,ite_true,hB,Option.map_some]

theorem rational_interval_exact_reconstruction_none_iff {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) (hM : 0 ≤ M) :
    rationalIntervalExactReconstruction lo hi V coreLo coreHi K p q M r ε = none ↔
      rationalIntervalExactCheck lo hi V coreLo coreHi K p q M r ε ≠ true := by
  constructor
  · intro hn hc
    obtain ⟨out,ho⟩ := rational_interval_exact_reconstruction_complete
      lo hi V coreLo coreHi K p q M r ε hM hc
    rw [hn] at ho
    cases ho
  · intro hc
    unfold rationalIntervalExactReconstruction
    split
    · rename_i hh
      exact (hc hh).elim
    · rfl

theorem rational_interval_exact_reconstruction_sound {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (out : (Fin m → Fin k → ℚ) × (Fin m → Fin m → ℚ))
    (ho : rationalIntervalExactReconstruction lo hi V coreLo coreHi K p q M r ε = some out) :
    (∀ i a, q i*out.1 i a=V i a) ∧
      (∀ i a, lo i a ≤ out.1 i a ∧ out.1 i a ≤ hi i a) ∧
      ResidualRatConditions q (rationalScore out.1 p) M ε out.2 ∧
      ∀ a, rationalAnchorResponse K out.1 p q a ≤ ε := by
  obtain ⟨hc,hD,hB⟩ := rational_interval_exact_reconstruction_origin lo hi V coreLo coreHi K p q M r ε out ho
  have hg : RationalIntervalExactGuards lo hi V coreLo coreHi K p q M r ε := by
    have hh := hc
    unfold rationalIntervalExactCheck at hh
    rw [Bool.and_eq_true] at hh
    exact of_decide_eq_true hh.1
  rcases hg with ⟨hq,_,hV,ha,_,_,_⟩
  have hprod := rational_interval_recovered_product lo hi V q hV
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hD] using hprod
  · simpa only [hD] using rational_interval_recovered_bounds lo hi V q hq hlu hV
  · rw [hD]
    exact rational_residual_completion_rat_sound _ _ _ _ out.2 hB
  · intro a
    unfold rationalAnchorResponse
    have he : (∑ i, out.1 i a*q i) = ∑ i, V i a := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm,hD,hprod i a]
    rw [he]
    exact ha a

theorem rational_interval_exact_reconstruction_full_rows {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (out : (Fin m → Fin k → ℚ) × (Fin m → Fin m → ℚ))
    (ho : rationalIntervalExactReconstruction lo hi V coreLo coreHi K p q M r ε = some out) :
    ∀ a, response (blockMatrix (fun a b => (K a b : ℝ))
      (fun i a => (out.1 i a : ℝ)) (fun i j => (out.2 i j : ℝ)))
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ (ε : ℝ) := by
  obtain ⟨_,_,hB,ha⟩ := rational_interval_exact_reconstruction_sound
    lo hi V coreLo coreHi K p q M r ε hlu out ho
  have hBR := (residual_rat_real_iff q (rationalScore out.1 p) M ε out.2).mp hB
  apply (block_response_bounds_iff _ _ _ _ _ _).mpr
  constructor
  · intro a
    have hh : (rationalAnchorResponse K out.1 p q a : ℝ) ≤ (ε : ℝ) := by
      exact_mod_cast ha a
    rw [rational_anchor_response_real] at hh
    exact hh
  · intro i
    simpa only [response,← rational_score_real] using hBR.2.2 i


/-- Every returned rational table gives this normalized bounded original game. -/
theorem rational_interval_exact_reconstruction_normalized_game {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ)
    (hp : ∀ a, 0 ≤ p a) (hpmass : (∑ a, p a)+r=1)
    (hclo : ∀ a b, -M ≤ coreLo a b) (hchi : ∀ a b, coreHi a b ≤ M)
    (hlo : ∀ i a, -M ≤ lo i a) (hhi : ∀ i a, hi i a ≤ M)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (out : (Fin m → Fin k → ℚ) × (Fin m → Fin m → ℚ))
    (ho : rationalIntervalExactReconstruction lo hi V coreLo coreHi K p q M r ε = some out) :
    (∀ i a, q i*out.1 i a=V i a) ∧
      (∀ i a, lo i a ≤ out.1 i a ∧ out.1 i a ≤ hi i a) ∧
      (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a) ∧
      (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
      IsSkew (blockMatrix (fun a b => (K a b : ℝ))
        (fun i a => (out.1 i a : ℝ)) (fun i j => (out.2 i j : ℝ))) ∧
      (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ))
        (fun i a => (out.1 i a : ℝ)) (fun i j => (out.2 i j : ℝ)) a b ∧
        blockMatrix (fun a b => (K a b : ℝ))
          (fun i a => (out.1 i a : ℝ)) (fun i j => (out.2 i j : ℝ)) a b ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun a b => (K a b : ℝ))
        (fun i a => (out.1 i a : ℝ)) (fun i j => (out.2 i j : ℝ)))
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ (ε : ℝ) := by
  obtain ⟨hc,_,_⟩ := rational_interval_exact_reconstruction_origin
    lo hi V coreLo coreHi K p q M r ε out ho
  have hg : RationalIntervalExactGuards lo hi V coreLo coreHi K p q M r ε := by
    have hh := hc
    unfold rationalIntervalExactCheck at hh
    rw [Bool.and_eq_true] at hh
    exact of_decide_eq_true hh.1
  rcases hg with ⟨hq,hr,_,_,hK,hC,_⟩
  obtain ⟨hprod,hD,hB,_⟩ := rational_interval_exact_reconstruction_sound
    lo hi V coreLo coreHi K p q M r ε hlu out ho
  have hBR := (residual_rat_real_iff q (rationalScore out.1 p) M ε out.2).mp hB
  have hpR : ∀ a, (0 : ℝ) ≤ (p a : ℝ) := by intro a; exact_mod_cast hp a
  have hqR : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := by intro i; exact_mod_cast hq i
  have hKR : IsSkew (fun a b => (K a b : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hKb : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    have hh : -M ≤ K a b ∧ K a b ≤ M :=
      ⟨(hclo a b).trans (hC a b).1,(hC a b).2.trans (hchi a b)⟩
    exact_mod_cast hh
  have hDb : ∀ i a, -(M : ℝ) ≤ (out.1 i a : ℝ) ∧ (out.1 i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    have hh : -M ≤ out.1 i a ∧ out.1 i a ≤ M :=
      ⟨(hlo i a).trans (hD i a).1,(hD i a).2.trans (hhi i a)⟩
    exact_mod_cast hh
  refine ⟨hprod,hD,blockWeights_nonneg _ _ hpR hqR,?_,
    blockMatrix_skew _ _ _ hKR hBR.1,
    blockMatrix_bounds _ _ _ _ hKb hDb hBR.2.1,
    rational_interval_exact_reconstruction_full_rows lo hi V coreLo coreHi K p q M r ε hlu out ho⟩
  rw [blockWeights_mass]
  have hh : (∑ a, p a)+(∑ i, q i)=1 := by rw [hr]; exact hpmass
  exact_mod_cast hh

end SparseCompletion
