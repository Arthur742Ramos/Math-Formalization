/- AI-assisted formalization under the repository Apache-2.0 license.
Separate source draft. These theorems analyze the actual Gaussian vector output. -/
module
public import ProtectedSources.RationalGaussianPaperFeatures
public import ProtectedSources.GameSparseWitness
public import ProtectedSources.RationalGap
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_gaussian_paper_real_contract {k d m : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (q v : Fin m → ℚ) (M r η : ℚ) (L : ℕ) (hq : ∀ i, 0 ≤ q i)
    (hm : ∑ i, q i=r) :
    let q' := rationalGaussianPaperWeights D E q v M r η L
    (∀ i, (0 : ℝ) ≤ (q' i : ℝ)) ∧ (∑ i, (q' i : ℝ))=(r : ℝ) ∧
      (∀ i, (q i : ℝ)=0 → (q' i : ℝ)=0) ∧
      (Finset.univ.filter fun i => (q' i : ℝ) ≠ 0).card ≤ k+d+L+1 ∧
      (∀ a, (∑ i, (q' i : ℝ)*(D i a : ℝ)) = ∑ i, (q i : ℝ)*(D i a : ℝ)) ∧
      (∀ a, (∑ i, q' i*E a i) = ∑ i, q i*E a i) ∧
      ∀ l : Fin L,
        call (fun i => (q' i : ℝ)) (fun i => (v i : ℝ))
            ((M : ℝ)*(r : ℝ)-gridNode (M : ℝ) (r : ℝ) (η : ℝ) (l.val+1)) =
          call (fun i => (q i : ℝ)) (fun i => (v i : ℝ))
            ((M : ℝ)*(r : ℝ)-gridNode (M : ℝ) (r : ℝ) (η : ℝ) (l.val+1)) := by
  obtain ⟨hn, hs, hz, hc, ha, he, hh⟩ :=
    rational_gaussian_paper_compress_contract D E q v M r η L hq
  refine ⟨fun i => by exact_mod_cast hn i, ?_, ?_, ?_, ?_, he, ?_⟩
  · exact_mod_cast hs.trans hm
  · intro i hi
    have hqi : q i=0 := by exact_mod_cast hi
    exact_mod_cast hz i hqi
  · have hsupport : (Finset.univ.filter fun i =>
        ((rationalGaussianPaperWeights D E q v M r η L) i : ℝ) ≠ 0) =
        rationalWeightSupport (rationalGaussianPaperWeights D E q v M r η L) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, rationalWeightSupport,
        Rat.cast_ne_zero]
    rw [hsupport]
    exact le_trans hc (min_le_right _ _)
  · intro a
    exact_mod_cast ha a
  · intro l
    have h := congrArg (fun z : ℚ => (z : ℝ)) (hh l)
    simpa only [rational_call_real, Rat.cast_sub, Rat.cast_mul, rational_grid_node_real] using h

theorem rational_gaussian_paper_compress_cuts {k d m : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (q v : Fin m → ℚ) (M r η : ℚ) (H : ℕ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hH : M*r ≤ η*(H : ℚ)^2) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hcuts : Cuts (M : ℝ) (r : ℝ) (fun i => (q i : ℝ)) (fun i => (v i : ℝ))) :
    let q' := rationalGaussianPaperWeights D E q v M r η H
    Cuts (M : ℝ) (r : ℝ) (fun i => (q' i : ℝ)) (fun i => (v i : ℝ)-(η : ℝ)) := by
  obtain ⟨hn, hmass, hz, _, _, _, hh⟩ := rational_gaussian_paper_real_contract D E q v M r η H hq hm
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hrR : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have hHR : (M : ℝ)*(r : ℝ) ≤ (η : ℝ)*(H : ℝ)^2 := by exact_mod_cast hH
  apply call_bound_implies_cuts _ _ _ _ hMR hn hmass
  apply finite_grid_implication _ _ _ _ _ H hMR hrR hηR hHR hn
  · intro i hi
    exact supported_score_cap _ _ _ _ hMR (fun i => by exact_mod_cast hq i)
      hcuts i (fun hzero => hi (hz i hzero))
  · intro l hl hlH
    let j : Fin H := ⟨l-1, by omega⟩
    have hj : j.val+1=l := by dsimp [j]; omega
    have he := hh j
    rw [hj] at he
    rw [he]
    exact cuts_imply_call_bound _ _ _ _ hMR hcuts _

theorem rational_gaussian_paper_exact_compress_cuts {k d m : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r η : ℚ) (H : ℕ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hH : M*r ≤ η*(H : ℚ)^2) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hcuts : Cuts (M : ℝ) (r : ℝ) (fun i => (q i : ℝ))
      (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))))
    (hmean : ∑ i, (q i : ℝ)*score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i=0)
    (hlow : ∀ i, q i ≠ 0 → -(M : ℝ)*(r : ℝ) ≤
      score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i) :
    let q' := rationalGaussianPaperWeights D E q (rationalScore D p) M r η (H-1)
    (Finset.univ.filter fun i => (q' i : ℝ) ≠ 0).card ≤ k+d+H ∧
      Cuts (M : ℝ) (r : ℝ) (fun i => (q' i : ℝ))
        (fun i => score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i-(η : ℝ)) := by
  obtain ⟨hn, hmass, hz, hc, ha, _, hh⟩ :=
    rational_gaussian_paper_real_contract D E q (rationalScore D p) M r η (H-1) hq hm
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have hHR : (M : ℝ)*(r : ℝ) ≤ (η : ℝ)*(H : ℝ)^2 := by exact_mod_cast hH
  have hHpos : 0 < H := by
    by_contra h
    have hzero : H=0 := by omega
    simp only [hzero, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hHR
    nlinarith [mul_pos hMR hrR]
  refine ⟨by omega, ?_⟩
  apply call_bound_implies_cuts _ _ _ _ hMR hn hmass
  apply finite_grid_implication _ _ _ _ _ H hMR (le_of_lt hrR) hηR hHR hn
  · intro i hi
    exact supported_score_cap _ _ _ _ hMR (fun i => by exact_mod_cast hq i)
      hcuts i (fun hzero => hi (hz i hzero))
  · intro l hl hlH
    by_cases hlast : l=H
    · subst l
      have hnode : gridNode (M : ℝ) (r : ℝ) (η : ℝ) H=2*(M : ℝ)*(r : ℝ) :=
        min_eq_right (by nlinarith)
      rw [hnode]
      have harg : (M : ℝ)*(r : ℝ)-2*(M : ℝ)*(r : ℝ)=-(M : ℝ)*(r : ℝ) := by ring
      rw [harg]
      have hmean' : (∑ i,
          (rationalGaussianPaperWeights D E q (rationalScore D p) M r η (H-1) i : ℝ)*
            score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i)=0 :=
        (linear_score_moment_preserved k _ (fun a => (p a : ℝ))
          (fun i => (q i : ℝ)) _
          (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))) (fun _ => rfl) ha).trans hmean
      rw [bottom_call_of_zero_mean _ _ _ _ hmass hmean' (fun i hi =>
        hlow i (fun hzero => hi (hz i (by exact_mod_cast hzero))))]
      have he : envelope (M : ℝ) (r : ℝ) (-(M : ℝ)*(r : ℝ)) = (M : ℝ)*(r : ℝ)^2 := by
        unfold envelope
        field_simp
        ring
      rw [he]
    · let j : Fin (H-1) := ⟨l-1, by omega⟩
      have hj : j.val+1=l := by dsimp [j]; omega
      have he := hh j
      simp only [rational_score_real] at he
      rw [hj] at he
      rw [he]
      exact cuts_imply_call_bound _ _ _ _ hMR hcuts _

end SparseCompletion
