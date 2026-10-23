/- AI-assisted formalization under the repository Apache-2.0 license.
Separate source draft. Actual materialized Gaussian qprime and graph-bounded
demand-network Bprime. No total runtime or coefficient-height theorem. -/
module
public import ProtectedSources.RationalGaussianPaperWitness
public import ProtectedSources.RationalPaperGraphFlow
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalGaussianPaperGeneralVector {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : Gaussian.QVec m :=
  rationalGaussianPaperCompress D E q (fun i => rationalScore D p i-ρ) M r η
    (rationalCanonicalGridSize M r η)

def rationalGaussianPaperExactVector {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r η : ℚ) : Gaussian.QVec m :=
  rationalGaussianPaperCompress D E q (rationalScore D p) M r η
    (rationalCanonicalGridSize M r η-1)

def rationalGaussianPaperGeneralFlow {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : Gaussian.QVec m × RationalFlowTable m :=
  let q' := rationalGaussianPaperGeneralVector D E p q M r ρ η
  (q', rationalDemandGraphCompletionTable q'.get (rationalScore D p) M (ρ+η))

def rationalGaussianPaperExactFlow {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r η : ℚ) : Gaussian.QVec m × RationalFlowTable m :=
  let q' := rationalGaussianPaperExactVector D E p q M r η
  (q', rationalDemandGraphCompletionTable q'.get (rationalScore D p) M η)

/-- Literal normalized compatible-game obligations for the returned data.
This is a proposition about the executed pair, not a field accepted by it. -/
def RationalGaussianPaperGame {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (out : Gaussian.QVec m × RationalFlowTable m) (M ε : ℚ) : Prop :=
  let q := out.1.get
  let B := rationalFlowTableEntry out.2
  (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a) ∧
    (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
    (∀ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) (.inl a)=(p a : ℝ)) ∧
    IsSkew (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B i j : ℝ)) a b ∧
      blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
        (fun i j => (B i j : ℝ)) a b ≤ (M : ℝ)) ∧
    ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ)))
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ (ε : ℝ)

theorem rational_gaussian_pair_game {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (out : Gaussian.QVec m × RationalFlowTable m) (M r ε : ℚ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ out.1.get i) (hm : ∑ i, out.1.get i=r)
    (hnorm : (∑ a, p a)+r=1) (hK : ∀ a b, K a b= -K b a)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hB : ResidualRatConditions out.1.get (rationalScore D p) M ε (rationalFlowTableEntry out.2))
    (ha : ∀ a, anchorResponse (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun a => (p a : ℝ)) (fun i => (out.1.get i : ℝ)) a ≤ (ε : ℝ)) :
    RationalGaussianPaperGame K D p out M ε := by
  have hKR : IsSkew (fun a b => (K a b : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  have hreal := (residual_rat_real_iff _ _ _ _ _).mp hB
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a)
    (fun i => by exact_mod_cast hq i), ?_, fun _ => rfl,
    blockMatrix_skew _ _ _ hKR hreal.1,
    blockMatrix_bounds _ _ _ _ hKbR hDbR hreal.2.1, ?_⟩
  · rw [blockWeights_mass]
    have hmR : ∑ i, (out.1.get i : ℝ)=(r : ℝ) := by exact_mod_cast hm
    rw [hmR]
    exact_mod_cast hnorm
  · apply (block_response_bounds_iff _ _ _ _ _ _).mpr
    refine ⟨ha, ?_⟩
    intro i
    have hi := hreal.2.2 i
    simpa only [response, ←rational_score_real] using hi

/-- Actual Gaussian-vector/graph-table output on the original rational game;
canonical sharp support, all original labels/moments, and one additive eta. -/
theorem rational_gaussian_paper_general_algorithm {k d m : ℕ}
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
    let out := rationalGaussianPaperGeneralFlow D E p q M r ρ η
    let q' := out.1.get
    let B' := rationalFlowTableEntry out.2
    (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧ (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤ min (rationalWeightSupport q).card (k+d+1+gridSize (M : ℝ) (r : ℝ) (η : ℝ)) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      ResidualRatConditions q' (rationalScore D p) M (ρ+η) B' ∧
      RationalGaussianPaperGame K D p out M (ρ+η) := by
  have hBR : IsSkew (fun i j => (B i j : ℝ)) := by
    intro i j
    change (B i j : ℝ)= -(B j i : ℝ)
    exact_mod_cast hB i j
  have hBbR : ∀ i j, -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ) := by
    intro i j
    exact_mod_cast hBb i j
  obtain ⟨Bc, hn, hmass, hz, hc, ha, he, hsk, hbound, hresp⟩ :=
    rational_gaussian_paper_general_witness (fun a b => (K a b : ℝ)) D E
      (fun i j => (B i j : ℝ)) p q M r ρ η hM hη hq hm hBR hBbR hrows
  let qv := rationalGaussianPaperGeneralVector D E p q M r ρ η
  have hreal : ResidualRealConditions qv.get (rationalScore D p) M (ρ+η) Bc := by
    refine ⟨hsk, hbound, ?_⟩
    intro i
    have hi := hresp (.inr i)
    rw [block_response_residual] at hi
    simpa only [response, ←rational_score_real, Rat.cast_add, qv, rationalGaussianPaperGeneralVector, rationalGaussianPaperGeneral, rationalGaussianPaperWeights] using hi
  have hrat := rational_paper_graph_demand_reconstruction qv.get (rationalScore D p)
    M r (ρ+η) (le_of_lt hM) hn hmass ⟨Bc, hreal⟩
  refine ⟨hn, hmass, hz, hc, ha, he, hrat, ?_⟩
  apply rational_gaussian_pair_game K D p (rationalGaussianPaperGeneralFlow D E p q M r ρ η)
    M r (ρ+η) hp hn hmass hnorm hK hKb hDb hrat
  intro a
  have hh := ((block_response_bounds_iff _ _ _ _ _ _).mp hresp).1 a
  simpa only [Rat.cast_add, rationalGaussianPaperGeneralFlow, rationalGaussianPaperGeneralVector,
    rationalGaussianPaperGeneral, rationalGaussianPaperWeights] using hh


/-- Actual Gaussian-vector/graph-table output on the original rational game;
canonical sharp support, all original labels/moments, and one additive eta. -/
theorem rational_gaussian_paper_exact_algorithm {k d m : ℕ}
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
    let out := rationalGaussianPaperExactFlow D E p q M r η
    let q' := out.1.get
    let B' := rationalFlowTableEntry out.2
    (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧ (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤ min (rationalWeightSupport q).card (k+d+gridSize (M : ℝ) (r : ℝ) (η : ℝ)) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      ResidualRatConditions q' (rationalScore D p) M η B' ∧
      RationalGaussianPaperGame K D p out M η := by
  have hKR : IsSkew (fun a b => (K a b : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hBR : IsSkew (fun i j => (B i j : ℝ)) := by
    intro i j
    change (B i j : ℝ)= -(B j i : ℝ)
    exact_mod_cast hB i j
  have hBbR : ∀ i j, -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ) := by
    intro i j
    exact_mod_cast hBb i j
  obtain ⟨Bc, hn, hmass, hz, hc, ha, he, hsk, hbound, hresp⟩ :=
    rational_gaussian_paper_exact_witness (fun a b => (K a b : ℝ)) D E
      (fun i j => (B i j : ℝ)) p q M r η hM hr hη hp hq hm hKR hBR hBbR hrows
  let qv := rationalGaussianPaperExactVector D E p q M r η
  have hreal : ResidualRealConditions qv.get (rationalScore D p) M η Bc := by
    refine ⟨hsk, hbound, ?_⟩
    intro i
    have hi := hresp (.inr i)
    rw [block_response_residual] at hi
    simpa only [response, ←rational_score_real, qv, rationalGaussianPaperExactVector, rationalGaussianPaperExact, rationalGaussianPaperWeights] using hi
  have hrat := rational_paper_graph_demand_reconstruction qv.get (rationalScore D p)
    M r η (le_of_lt hM) hn hmass ⟨Bc, hreal⟩
  refine ⟨hn, hmass, hz, hc, ha, he, hrat, ?_⟩
  apply rational_gaussian_pair_game K D p (rationalGaussianPaperExactFlow D E p q M r η)
    M r η hp hn hmass hnorm hK hKb hDb hrat
  intro a
  have hh := ((block_response_bounds_iff _ _ _ _ _ _).mp hresp).1 a
  simpa only [rationalGaussianPaperExactFlow, rationalGaussianPaperExactVector,
    rationalGaussianPaperExact, rationalGaussianPaperWeights] using hh

/-- Zero residual mass returns the original zero vector and runs the actual
Gaussian-vector/graph-table program, retaining every original row guard. -/
theorem rational_gaussian_paper_zero_algorithm {k d m : ℕ}
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
    let out := rationalGaussianPaperExactFlow D E p q M 0 η
    out.1.get=q ∧ (rationalWeightSupport out.1.get).card=0 ∧
      ResidualRatConditions out.1.get (rationalScore D p) M η (rationalFlowTableEntry out.2) ∧
      RationalGaussianPaperGame K D p out M η := by
  have hBR : IsSkew (fun i j => (B i j : ℝ)) := by
    intro i j
    change (B i j : ℝ)= -(B j i : ℝ)
    exact_mod_cast hB i j
  have hBbR : ∀ i j, -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ) := by
    intro i j
    exact_mod_cast hBb i j
  obtain ⟨hout, hc, Bc, hsk, hbound, hresp⟩ :=
    rational_gaussian_paper_exact_zero_mass_witness (fun a b => (K a b : ℝ)) D E
      (fun i j => (B i j : ℝ)) p q M η hη hq hm hBR hBbR hrows
  let qv := rationalGaussianPaperExactVector D E p q M 0 η
  have hqv : qv.get=q := hout
  have hn : ∀ i, 0 ≤ qv.get i := by rw [hqv]; exact hq
  have hmass : ∑ i, qv.get i=0 := by rw [hqv]; exact hm
  have hreal : ResidualRealConditions qv.get (rationalScore D p) M η Bc := by
    refine ⟨hsk, hbound, ?_⟩
    intro i
    have hi := hresp (.inr i)
    rw [block_response_residual] at hi
    simpa only [response, ←rational_score_real, qv, rationalGaussianPaperExactVector,
      rationalGaussianPaperExact, rationalGaussianPaperWeights] using hi
  have hrat := rational_paper_graph_demand_reconstruction qv.get (rationalScore D p)
    M 0 η (le_of_lt hM) hn hmass ⟨Bc, hreal⟩
  refine ⟨hqv, hc, hrat, ?_⟩
  apply rational_gaussian_pair_game K D p (rationalGaussianPaperExactFlow D E p q M 0 η)
    M 0 η hp hn hmass hnorm hK hKb hDb hrat
  intro a
  have hh := ((block_response_bounds_iff _ _ _ _ _ _).mp hresp).1 a
  simpa only [rationalGaussianPaperExactFlow, rationalGaussianPaperExactVector,
    rationalGaussianPaperExact, rationalGaussianPaperWeights] using hh

end SparseCompletion
