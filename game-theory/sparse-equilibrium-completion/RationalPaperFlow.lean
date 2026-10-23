/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY draft. The output binds the actual FM-compressed rational qprime
and the actual demand-network completion table. No polynomial runtime claim.
The earlier15 mathematical proofs remain unchanged. -/
module
public import RationalPaperWitness
public import RationalDemandNetwork
public import RationalResidualSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Proof-only bridge from an earned Real completion to the exact rational
global guards and all demand cuts consumed by the executed flow program. The
completion is never a runtime parameter of that program. -/
theorem rational_paper_demand_guards_and_cuts {m : ℕ}
    (q t : Fin m → ℚ) (M r ε : ℚ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (h : ∃ B : Fin m → Fin m → ℝ, ResidualRealConditions q t M ε B) :
    (∀ i, t i ≤ ε+M*r) ∧
      ∀ S : Finset (Fin m), (∑ i ∈ S, q i*(t i-ε)) ≤
        ∑ i ∈ S, ∑ j ∈ Sᶜ, M*q i*q j := by
  obtain ⟨B, hsk, hb, hresp⟩ := h
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hqR : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := fun i => by exact_mod_cast hq i
  have hmR : ∑ i, (q i : ℝ)=(r : ℝ) := by exact_mod_cast hm
  have hc := (weighted_completion_iff (fun i => (q i : ℝ)) (fun i => (t i : ℝ))
    (M : ℝ) (r : ℝ) (ε : ℝ) hMR hqR hmR).mp ⟨B, hsk, hb, hresp⟩
  refine ⟨fun i => by exact_mod_cast hc.1 i, ?_⟩
  intro S
  have hscalar : (∑ i ∈ S, q i*(t i-ε)) ≤
      M*(∑ i ∈ S, q i)*(r-∑ i ∈ S, q i) := by
    have hh := hc.2 S
    change (∑ i ∈ S, (q i : ℝ)*((t i : ℝ)-(ε : ℝ))) ≤
      (M : ℝ)*(∑ i ∈ S, (q i : ℝ))*((r : ℝ)-∑ i ∈ S, (q i : ℝ)) at hh
    exact_mod_cast hh
  have hcomp : (∑ j ∈ Sᶜ, q j)=r-∑ i ∈ S, q i := by
    have hs := Finset.sum_add_sum_compl S q
    rw [hm] at hs
    linarith
  have hcapacity : (∑ i ∈ S, ∑ j ∈ Sᶜ, M*q i*q j) =
      M*(∑ i ∈ S, q i)*(r-∑ i ∈ S, q i) := by
    calc
      _ = (∑ i ∈ S, M*q i)*(∑ j ∈ Sᶜ, q j) := by
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
      _ = M*(∑ i ∈ S, q i)*(∑ j ∈ Sᶜ, q j) := by
        congr 1
        exact (Finset.mul_sum S q M).symm
      _ = _ := by rw [hcomp]
  rw [hcapacity]
  exact hscalar

theorem rational_paper_demand_reconstruction {m : ℕ}
    (q t : Fin m → ℚ) (M r ε : ℚ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (h : ∃ B : Fin m → Fin m → ℝ, ResidualRealConditions q t M ε B) :
    ResidualRatConditions q t M ε
      (rationalFlowTableEntry (rationalDemandCompletionTable q t M ε)) := by
  obtain ⟨hg, hc⟩ := rational_paper_demand_guards_and_cuts q t M r ε hM hq hm h
  exact rational_demand_completion_table_sound q t M r ε hM hq hm hg hc

def rationalPaperGeneralFlow {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : (Fin m → ℚ) × RationalFlowTable m :=
  let q' := rationalPaperGeneral D E p q M r ρ η
  (q', rationalDemandCompletionTable q' (rationalScore D p) M (ρ+η))

def rationalPaperExactFlow {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r η : ℚ) : (Fin m → ℚ) × RationalFlowTable m :=
  let q' := rationalPaperExact D E p q M r η
  (q', rationalDemandCompletionTable q' (rationalScore D p) M η)

/-- Replaces the proof-only Real completion by the matrix actually returned
from the materialized demand network, at the same single rho+eta threshold. -/
theorem rational_paper_general_flow_witness {k d m : ℕ}
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B)
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)) :
    let out := rationalPaperGeneralFlow D E p q M r ρ η
    let q' := out.1
    let B' := rationalFlowTableEntry out.2
    (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧ (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤
        min (rationalWeightSupport q).card (k+d+1+gridSize (M : ℝ) (r : ℝ) (η : ℝ)) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      ResidualRatConditions q' (rationalScore D p) M (ρ+η) B' ∧
      ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) (fun i j => (B' i j : ℝ)))
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  obtain ⟨Bc, hn, hmass, hz, hc, ha, he, hsk, hbound, hresp⟩ :=
    rational_paper_general_witness K D E B p q M r ρ η hM hη hq hm hB hb hrows
  let q' := rationalPaperGeneral D E p q M r ρ η
  have hreal : ResidualRealConditions q' (rationalScore D p) M (ρ+η) Bc := by
    refine ⟨hsk, hbound, ?_⟩
    intro i
    have hi := hresp (.inr i)
    rw [block_response_residual] at hi
    simpa only [response, ←rational_score_real, Rat.cast_add] using hi
  have hrat := rational_paper_demand_reconstruction q' (rationalScore D p) M r (ρ+η)
    (le_of_lt hM) hn hmass ⟨Bc, hreal⟩
  have hrreal := (residual_rat_real_iff _ _ _ _ _).mp hrat
  refine ⟨hn, hmass, hz, hc, ha, he, hrat, ?_⟩
  apply (block_response_bounds_iff _ _ _ _ _ _).mpr
  constructor
  · intro a
    exact ((block_response_bounds_iff _ _ _ _ _ _).mp hresp).1 a
  · intro i
    have hi := hrreal.2.2 i
    simpa only [response, ←rational_score_real, Rat.cast_add, rationalPaperGeneralFlow, q'] using hi

/-- Exact positive residual mass: the computed pair has the sharp k+d+H
bound already earned by the H-1 feature construction. -/
theorem rational_paper_exact_flow_witness {k d m : ℕ}
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r η : ℚ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B)
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ 0) :
    let out := rationalPaperExactFlow D E p q M r η
    let q' := out.1
    let B' := rationalFlowTableEntry out.2
    (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧ (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤
        min (rationalWeightSupport q).card (k+d+gridSize (M : ℝ) (r : ℝ) (η : ℝ)) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      ResidualRatConditions q' (rationalScore D p) M η B' ∧
      ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) (fun i j => (B' i j : ℝ)))
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (η : ℝ) := by
  obtain ⟨Bc, hn, hmass, hz, hc, ha, he, hsk, hbound, hresp⟩ :=
    rational_paper_exact_witness K D E B p q M r η hM hr hη hp hq hm hK hB hb hrows
  let q' := rationalPaperExact D E p q M r η
  have hreal : ResidualRealConditions q' (rationalScore D p) M η Bc := by
    refine ⟨hsk, hbound, ?_⟩
    intro i
    have hi := hresp (.inr i)
    rw [block_response_residual] at hi
    simpa only [response, ←rational_score_real] using hi
  have hrat := rational_paper_demand_reconstruction q' (rationalScore D p) M r η
    (le_of_lt hM) hn hmass ⟨Bc, hreal⟩
  have hrreal := (residual_rat_real_iff _ _ _ _ _).mp hrat
  refine ⟨hn, hmass, hz, hc, ha, he, hrat, ?_⟩
  apply (block_response_bounds_iff _ _ _ _ _ _).mpr
  constructor
  · intro a
    exact ((block_response_bounds_iff _ _ _ _ _ _).mp hresp).1 a
  · intro i
    have hi := hrreal.2.2 i
    simpa only [response, ←rational_score_real, rationalPaperExactFlow, q'] using hi

/-- Zero residual mass still invokes the concrete table program. Its guards
are earned from the original game's global rows, including every zero label. -/
theorem rational_paper_exact_zero_flow_witness {k d m : ℕ}
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=0)
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B)
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ 0) :
    let out := rationalPaperExactFlow D E p q M 0 η
    let q' := out.1
    let B' := rationalFlowTableEntry out.2
    q'=q ∧ (rationalWeightSupport q').card=0 ∧
      ResidualRatConditions q' (rationalScore D p) M η B' ∧
      ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) (fun i j => (B' i j : ℝ)))
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (η : ℝ) := by
  obtain ⟨hout, hc, Bc, hsk, hbound, hresp⟩ :=
    rational_paper_exact_zero_mass_witness K D E B p q M η hη hq hm hB hb hrows
  let q' := rationalPaperExact D E p q M 0 η
  have hn : ∀ i, 0 ≤ q' i := by simpa only [q', hout] using hq
  have hmass : ∑ i, q' i=0 := by simpa only [q', hout] using hm
  have hreal : ResidualRealConditions q' (rationalScore D p) M η Bc := by
    refine ⟨hsk, hbound, ?_⟩
    intro i
    have hi := hresp (.inr i)
    rw [block_response_residual] at hi
    simpa only [response, ←rational_score_real] using hi
  have hrat := rational_paper_demand_reconstruction q' (rationalScore D p) M 0 η
    (le_of_lt hM) hn hmass ⟨Bc, hreal⟩
  have hrreal := (residual_rat_real_iff _ _ _ _ _).mp hrat
  refine ⟨hout, hc, hrat, ?_⟩
  apply (block_response_bounds_iff _ _ _ _ _ _).mpr
  constructor
  · intro a
    exact ((block_response_bounds_iff _ _ _ _ _ _).mp hresp).1 a
  · intro i
    have hi := hrreal.2.2 i
    simpa only [response, ←rational_score_real, rationalPaperExactFlow, q'] using hi

/-- Entirely rational supplied-witness interface: both weights and residual
completion are the actual returned pair, cast to the normalized Real game. -/
theorem rational_paper_normalized_general_flow {k d m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hnorm : (∑ a, p a)+r=1) (hK : ∀ a b, K a b= -K b a)
    (hB : ∀ i j, B i j= -B j i)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hrows : ∀ a, response (blockMatrix (fun a b => (K a b : ℝ))
      (fun i a => (D i a : ℝ)) (fun i j => (B i j : ℝ)))
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)) :
    let out := rationalPaperGeneralFlow D E p q M r ρ η
    let q' := out.1
    let B' := rationalFlowTableEntry out.2
    (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) a) ∧
      (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) a)=1 ∧
      (∀ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) (.inl a)=(p a : ℝ)) ∧
      (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤ k+d+1+gridSize (M : ℝ) (r : ℝ) (η : ℝ) ∧
      (Finset.univ.filter fun a => blockWeights (fun a => (p a : ℝ))
        (fun i => (q' i : ℝ)) a ≠ 0).card ≤ (2 : ℕ)*k+d+1+gridSize (M : ℝ) (r : ℝ) (η : ℝ) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      IsSkew (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B' i j : ℝ))) ∧
      (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
          (fun i j => (B' i j : ℝ)) a b ∧
        blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
          (fun i j => (B' i j : ℝ)) a b ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B' i j : ℝ)))
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  classical
  have hKR : IsSkew (fun a b => (K a b : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hBR : IsSkew (fun i j => (B i j : ℝ)) := by
    intro i j
    change (B i j : ℝ)= -(B j i : ℝ)
    exact_mod_cast hB i j
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  have hBbR : ∀ i j, -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ) := by
    intro i j
    exact_mod_cast hBb i j
  obtain ⟨hn, hmass, hz, hc, ha, he, hrat, hresp⟩ :=
    rational_paper_general_flow_witness (fun a b => (K a b : ℝ)) D E
      (fun i j => (B i j : ℝ)) p q M r ρ η hM hη hq hm hBR hBbR hrows
  let out := rationalPaperGeneralFlow D E p q M r ρ η
  let q' := out.1
  let B' := rationalFlowTableEntry out.2
  have hreal := (residual_rat_real_iff _ _ _ _ _).mp hrat
  have hq'R : ∀ i, (0 : ℝ) ≤ (q' i : ℝ) := fun i => by exact_mod_cast hn i
  have hmR : ∑ i, (q' i : ℝ)=(r : ℝ) := by exact_mod_cast hmass
  have hs : (Finset.univ.filter fun i => (q' i : ℝ) ≠ 0).card =
      (rationalWeightSupport q').card := by
    congr 1
    ext i
    simp [rationalWeightSupport]
  have hcard : (rationalWeightSupport q').card ≤ k+d+1+gridSize (M : ℝ) (r : ℝ) (η : ℝ) :=
    le_trans hc (min_le_right _ _)
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a) hq'R,
    ?_, fun _ => rfl, hz, hcard, ?_, ha, he,
    blockMatrix_skew _ _ _ hKR hreal.1, blockMatrix_bounds _ _ _ _ hKbR hDbR hreal.2.1, hresp⟩
  · rw [blockWeights_mass, hmR]
    exact_mod_cast hnorm
  · rw [block_support_card, hs]
    have hanchor : (Finset.univ.filter fun a => (p a : ℝ) ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    omega


/-- Entirely rational supplied-witness interface: both weights and residual
completion are the actual returned pair, cast to the normalized Real game. -/
theorem rational_paper_normalized_exact_flow {k d m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r η : ℚ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hnorm : (∑ a, p a)+r=1) (hK : ∀ a b, K a b= -K b a)
    (hB : ∀ i j, B i j= -B j i)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hrows : ∀ a, response (blockMatrix (fun a b => (K a b : ℝ))
      (fun i a => (D i a : ℝ)) (fun i j => (B i j : ℝ)))
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ 0) :
    let out := rationalPaperExactFlow D E p q M r η
    let q' := out.1
    let B' := rationalFlowTableEntry out.2
    (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) a) ∧
      (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) a)=1 ∧
      (∀ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) (.inl a)=(p a : ℝ)) ∧
      (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤ k+d+gridSize (M : ℝ) (r : ℝ) (η : ℝ) ∧
      (Finset.univ.filter fun a => blockWeights (fun a => (p a : ℝ))
        (fun i => (q' i : ℝ)) a ≠ 0).card ≤ (2 : ℕ)*k+d+gridSize (M : ℝ) (r : ℝ) (η : ℝ) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      IsSkew (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B' i j : ℝ))) ∧
      (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
          (fun i j => (B' i j : ℝ)) a b ∧
        blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
          (fun i j => (B' i j : ℝ)) a b ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B' i j : ℝ)))
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (η : ℝ) := by
  classical
  have hKR : IsSkew (fun a b => (K a b : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hBR : IsSkew (fun i j => (B i j : ℝ)) := by
    intro i j
    change (B i j : ℝ)= -(B j i : ℝ)
    exact_mod_cast hB i j
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  have hBbR : ∀ i j, -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ) := by
    intro i j
    exact_mod_cast hBb i j
  obtain ⟨hn, hmass, hz, hc, ha, he, hrat, hresp⟩ :=
    rational_paper_exact_flow_witness (fun a b => (K a b : ℝ)) D E
      (fun i j => (B i j : ℝ)) p q M r η hM hr hη hp hq hm hKR hBR hBbR hrows
  let out := rationalPaperExactFlow D E p q M r η
  let q' := out.1
  let B' := rationalFlowTableEntry out.2
  have hreal := (residual_rat_real_iff _ _ _ _ _).mp hrat
  have hq'R : ∀ i, (0 : ℝ) ≤ (q' i : ℝ) := fun i => by exact_mod_cast hn i
  have hmR : ∑ i, (q' i : ℝ)=(r : ℝ) := by exact_mod_cast hmass
  have hs : (Finset.univ.filter fun i => (q' i : ℝ) ≠ 0).card =
      (rationalWeightSupport q').card := by
    congr 1
    ext i
    simp [rationalWeightSupport]
  have hcard : (rationalWeightSupport q').card ≤ k+d+gridSize (M : ℝ) (r : ℝ) (η : ℝ) :=
    le_trans hc (min_le_right _ _)
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a) hq'R,
    ?_, fun _ => rfl, hz, hcard, ?_, ha, he,
    blockMatrix_skew _ _ _ hKR hreal.1, blockMatrix_bounds _ _ _ _ hKbR hDbR hreal.2.1, hresp⟩
  · rw [blockWeights_mass, hmR]
    exact_mod_cast hnorm
  · rw [block_support_card, hs]
    have hanchor : (Finset.univ.filter fun a => (p a : ℝ) ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    omega

/-- Normalized zero-mass exact branch. General and exact executed pairs agree
because both compressors return the same original zero vector, and therefore
invoke the identical rational completion table at threshold eta. -/
theorem rational_paper_normalized_zero_flow {k d m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M η : ℚ)
    (hM : 0 < M) (hη : 0 < η)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=0)
    (hnorm : (∑ a, p a)+0=1) (hK : ∀ a b, K a b= -K b a)
    (hB : ∀ i j, B i j= -B j i)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hrows : ∀ a, response (blockMatrix (fun a b => (K a b : ℝ))
      (fun i a => (D i a : ℝ)) (fun i j => (B i j : ℝ)))
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ 0) :
    let out := rationalPaperExactFlow D E p q M 0 η
    let q' := out.1
    let B' := rationalFlowTableEntry out.2
    q'=q ∧ (rationalWeightSupport q').card=0 ∧
      (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) a) ∧
      (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) a)=1 ∧
      (∀ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ)) (.inl a)=(p a : ℝ)) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      IsSkew (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B' i j : ℝ))) ∧
      (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
          (fun i j => (B' i j : ℝ)) a b ∧
        blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
          (fun i j => (B' i j : ℝ)) a b ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B' i j : ℝ)))
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (η : ℝ) := by
  have hg := (rational_paper_compress_zero_mass D E q
    (fun i => rationalScore D p i-0) M η (rationalCanonicalGridSize M 0 η) hq hm).1
  obtain ⟨he, _, hc⟩ := rational_paper_compress_zero_mass D E q (rationalScore D p)
    M η (rationalCanonicalGridSize M 0 η-1) hq hm
  have hout : rationalPaperGeneralFlow D E p q M 0 0 η = rationalPaperExactFlow D E p q M 0 η := by
    simp only [rationalPaperGeneralFlow, rationalPaperExactFlow,
      rationalPaperGeneral, rationalPaperExact, hg, he, zero_add]
  have hgen := rational_paper_normalized_general_flow K D E B p q M 0 0 η
    hM hη hp hq hm hnorm hK hB hKb hDb hBb (by simpa only [Rat.cast_zero] using hrows)
  rw [hout] at hgen
  obtain ⟨hn, hmass, hanchor, _, _, _, ha, hE, hsk, hbound, hresp⟩ := hgen
  refine ⟨he, hc, hn, hmass, hanchor, ha, hE, hsk, hbound, ?_⟩
  simpa only [Rat.cast_zero, zero_add] using hresp

end SparseCompletion
