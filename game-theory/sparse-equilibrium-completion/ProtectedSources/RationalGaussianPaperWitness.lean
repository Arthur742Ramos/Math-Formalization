/- AI-assisted formalization under the repository Apache-2.0 license.
Separate source draft. Rational weights are the coordinates of the executed Gaussian vector;
the Real bounded completion uses the existing proved sufficiency theorem.
No polynomial runtime or executable completion matrix is claimed here. -/
module
public import ProtectedSources.RationalGaussianPaperCuts
public import ProtectedSources.AllMassWitness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalGaussianPaperGeneral {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : Fin m → ℚ :=
  rationalGaussianPaperWeights D E q (fun i => rationalScore D p i-ρ) M r η
    (rationalCanonicalGridSize M r η)

def rationalGaussianPaperExact {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r η : ℚ) : Fin m → ℚ :=
  rationalGaussianPaperWeights D E q (rationalScore D p) M r η
    (rationalCanonicalGridSize M r η-1)

/-- The supplied original witness justifies all cuts and global guards. The
returned game uses exactly the rational vector computed from that same input,
on the original labels, with one eta slack and d preserved extra moments. -/
theorem rational_gaussian_paper_general_witness {k d m : ℕ}
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B)
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)) :
    let q' := rationalGaussianPaperGeneral D E p q M r ρ η
    ∃ B' : Fin m → Fin m → ℝ,
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧ (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤
        min (rationalWeightSupport q).card (k+d+1+gridSize (M : ℝ) (r : ℝ) (η : ℝ)) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      IsSkew B' ∧ (∀ i j, -(M : ℝ) ≤ B' i j ∧ B' i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B')
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  let H := rationalCanonicalGridSize M r η
  let v : Fin m → ℚ := fun i => rationalScore D p i-ρ
  let q' := rationalGaussianPaperWeights D E q v M r η H
  have hr : 0 ≤ r := by rw [←hm]; exact Finset.sum_nonneg (fun i _ => hq i)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have hqR : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := fun i => by exact_mod_cast hq i
  have hmR : ∑ i, (q i : ℝ)=(r : ℝ) := by exact_mod_cast hm
  have hres := ((block_response_bounds_iff _ _ _ _ _ _).mp hrows).2
  have hcuts := completion_cuts_necessary _ _ B _ _ _ hqR hmR hB
    (fun i j => (hb i j).1) hres
  have hv : ∀ i, (v i : ℝ)=score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i-(ρ : ℝ) := by
    intro i
    simp only [v, Rat.cast_sub, rational_score_real]
  have hcutsV : Cuts (M : ℝ) (r : ℝ) (fun i => (q i : ℝ)) (fun i => (v i : ℝ)) := by
    simpa only [hv] using hcuts
  obtain ⟨hn, hmass, hz, hc, ha, he, _⟩ :=
    rational_gaussian_paper_compress_contract D E q v M r η H hq
  have hq'R : ∀ i, (0 : ℝ) ≤ (q' i : ℝ) := fun i => by exact_mod_cast hn i
  have hm'R : ∑ i, (q' i : ℝ)=(r : ℝ) := by exact_mod_cast hmass.trans hm
  have hc' := rational_gaussian_paper_compress_cuts D E q v M r η H hM hr hη
    (rational_canonical_grid_size_bound M r η hη) hq hm hcutsV
  have hshift : (fun i => (v i : ℝ)-(η : ℝ)) =
      (fun i => score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i-((ρ : ℝ)+(η : ℝ))) := by
    funext i
    rw [hv]
    ring
  rw [hshift] at hc'
  have hguard : ∀ i, score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i ≤
      (ρ : ℝ)+(η : ℝ)+(M : ℝ)*(r : ℝ) := by
    intro i
    have hg := response_guard _ _ B _ _ _ hqR hmR (fun i j => (hb i j).1) hres i
    linarith
  obtain ⟨B', hsk, hbound, hresp⟩ := completion_of_cuts_and_guards
    (fun i => (q' i : ℝ)) (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)))
    (M : ℝ) (r : ℝ) ((ρ : ℝ)+(η : ℝ)) (le_of_lt hMR) hq'R hm'R hc' hguard
  refine ⟨B', hn, hmass.trans hm, hz, ?_, ha, he, hsk, hbound, ?_⟩
  · have hcanonical := rational_canonical_grid_size_real M r η (le_of_lt hM) hr hη
    simpa only [rationalGaussianPaperGeneral, H, v, hcanonical, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc
  · apply (block_response_bounds_iff _ _ _ _ _ _).mpr
    refine ⟨?_, hresp⟩
    have hanchor := anchor_response_of_moments k K (fun i a => (D i a : ℝ))
      (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) (fun i => (q' i : ℝ))
      (fun a => by exact_mod_cast ha a)
    intro a
    change anchorResponse K (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))
      (fun i => (q' i : ℝ)) a ≤ _
    rw [hanchor]
    have hh := ((block_response_bounds_iff _ _ _ _ _ _).mp hrows).1 a
    linarith

/-- Exact-equilibrium specialization earns the endpoint identity from the
original game. No bottom-hinge premise is passed to the compressor or wrapper. -/
theorem rational_gaussian_paper_exact_witness {k d m : ℕ}
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r η : ℚ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B)
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ 0) :
    let q' := rationalGaussianPaperExact D E p q M r η
    ∃ B' : Fin m → Fin m → ℝ,
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧ (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤
        min (rationalWeightSupport q).card (k+d+gridSize (M : ℝ) (r : ℝ) (η : ℝ)) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      IsSkew B' ∧ (∀ i j, -(M : ℝ) ≤ B' i j ∧ B' i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B')
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (η : ℝ) := by
  let H := rationalCanonicalGridSize M r η
  let q' := rationalGaussianPaperWeights D E q (rationalScore D p) M r η (H-1)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have hpR : ∀ a, (0 : ℝ) ≤ (p a : ℝ) := fun a => by exact_mod_cast hp a
  have hqR : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := fun i => by exact_mod_cast hq i
  have hmR : ∑ i, (q i : ℝ)=(r : ℝ) := by exact_mod_cast hm
  have hres := ((block_response_bounds_iff _ _ _ _ _ _).mp hrows).2
  have hcuts0 := completion_cuts_necessary _ _ B _ _ _ hqR hmR hB
    (fun i j => (hb i j).1) hres
  have hcuts : Cuts (M : ℝ) (r : ℝ) (fun i => (q i : ℝ))
      (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))) := by
    simpa only [sub_zero] using hcuts0
  have hmean := exact_score_mean_zero K (fun i a => (D i a : ℝ)) B
    (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) hpR hqR hK hB hrows
  have hlow : ∀ i, q i ≠ 0 → -(M : ℝ)*(r : ℝ) ≤
      score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i := by
    intro i hi
    have hiR : (q i : ℝ) ≠ 0 := by exact_mod_cast hi
    simpa only [neg_mul] using (abs_le.mp (exact_score_bounds K
      (fun i a => (D i a : ℝ)) B (fun a => (p a : ℝ)) (fun i => (q i : ℝ))
      (M : ℝ) (r : ℝ) hpR hqR hmR hK hB hb hrows i hiR)).1
  have hH := rational_canonical_grid_size_bound M r η hη
  have hHpos : 0 < H := by
    by_contra h
    have hzero : H=0 := by omega
    change M*r ≤ η*(H : ℚ)^2 at hH
    simp only [hzero, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hH
    nlinarith [mul_pos hM hr]
  obtain ⟨hn, hmass, hz, hc, ha, he, _⟩ :=
    rational_gaussian_paper_compress_contract D E q (rationalScore D p) M r η (H-1) hq
  have hq'R : ∀ i, (0 : ℝ) ≤ (q' i : ℝ) := fun i => by exact_mod_cast hn i
  have hm'R : ∑ i, (q' i : ℝ)=(r : ℝ) := by exact_mod_cast hmass.trans hm
  have hc' := (rational_gaussian_paper_exact_compress_cuts D E p q M r η H hM hr hη
    hH hq hm hcuts hmean hlow).2
  have hguard : ∀ i, score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i ≤
      (η : ℝ)+(M : ℝ)*(r : ℝ) := by
    intro i
    have hg := response_guard _ _ B _ _ _ hqR hmR (fun i j => (hb i j).1) hres i
    linarith
  obtain ⟨B', hsk, hbound, hresp⟩ := completion_of_cuts_and_guards
    (fun i => (q' i : ℝ)) (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)))
    (M : ℝ) (r : ℝ) (η : ℝ) (le_of_lt hMR) hq'R hm'R hc' hguard
  refine ⟨B', hn, hmass.trans hm, hz, ?_, ha, he, hsk, hbound, ?_⟩
  · have hcanonical := rational_canonical_grid_size_real M r η (le_of_lt hM) (le_of_lt hr) hη
    have hdim : k+d+(H-1)+1=k+d+H := by omega
    rw [hdim] at hc
    simpa only [rationalGaussianPaperExact, H, hcanonical] using hc
  · apply (block_response_bounds_iff _ _ _ _ _ _).mpr
    refine ⟨?_, hresp⟩
    have hanchor := anchor_response_of_moments k K (fun i a => (D i a : ℝ))
      (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) (fun i => (q' i : ℝ))
      (fun a => by exact_mod_cast ha a)
    intro a
    change anchorResponse K (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))
      (fun i => (q' i : ℝ)) a ≤ _
    rw [hanchor]
    have hh := ((block_response_bounds_iff _ _ _ _ _ _).mp hrows).1 a
    linarith

/-- Zero residual mass is handled independently of the positive-mass endpoint
argument: every executed output is identically zero, for any number of hinges. -/
theorem rational_gaussian_paper_compress_zero_mass {k d m : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (q v : Fin m → ℚ) (M η : ℚ) (L : ℕ)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=0) :
    rationalGaussianPaperWeights D E q v M 0 η L = q ∧
      q=(fun _ => 0) ∧
      (rationalWeightSupport (rationalGaussianPaperWeights D E q v M 0 η L)).card=0 := by
  have hmR : ∑ i, (q i : ℝ)=0 := by exact_mod_cast hm
  have hzeroR := nonnegative_mass_zero (fun i => (q i : ℝ))
    (fun i => by exact_mod_cast hq i) hmR
  have hzero : q=fun _ => 0 := by
    funext i
    exact_mod_cast congrFun hzeroR i
  obtain ⟨_, _, hz, _, _, _, _⟩ :=
    rational_gaussian_paper_compress_contract D E q v M 0 η L hq
  have hout : rationalGaussianPaperWeights D E q v M 0 η L=q := by
    funext i
    have hqi : q i=0 := congrFun hzero i
    rw [hz i hqi, hqi]
  refine ⟨hout, hzero, ?_⟩
  rw [hout, hzero]
  simp [rationalWeightSupport]


/-- In the zero-residual-mass branch the same exact program retains the
original zero vector, so the supplied bounded completion itself is a witness. -/
theorem rational_gaussian_paper_exact_zero_mass_witness {k d m : ℕ}
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (B : Fin m → Fin m → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M η : ℚ)
    (hη : 0 < η) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=0)
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B)
      (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ 0) :
    let q' := rationalGaussianPaperExact D E p q M 0 η
    q'=q ∧ (rationalWeightSupport q').card=0 ∧
      ∃ B' : Fin m → Fin m → ℝ,
        IsSkew B' ∧ (∀ i j, -(M : ℝ) ≤ B' i j ∧ B' i j ≤ (M : ℝ)) ∧
        ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B')
          (blockWeights (fun a => (p a : ℝ)) (fun i => (q' i : ℝ))) a ≤ (η : ℝ) := by
  obtain ⟨hout, _, hc⟩ := rational_gaussian_paper_compress_zero_mass D E q (rationalScore D p)
    M η (rationalCanonicalGridSize M 0 η-1) hq hm
  refine ⟨hout, hc, B, hB, hb, ?_⟩
  change ∀ a, response (blockMatrix K (fun i a => (D i a : ℝ)) B)
    (blockWeights (fun a => (p a : ℝ))
      (fun i => (rationalGaussianPaperWeights D E q (rationalScore D p) M 0 η
        (rationalCanonicalGridSize M 0 η-1) i : ℝ))) a ≤ (η : ℝ)
  rw [hout]
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  exact fun a => le_trans (hrows a) (le_of_lt hηR)


end SparseCompletion
