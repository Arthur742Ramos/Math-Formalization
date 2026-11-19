module

public import BoundedEdgeRegularSubgraphs.DensityIncrement
import BoundedEdgeRegularSubgraphs.DegreeDeletion
import BoundedEdgeRegularSubgraphs.OrderUpper
import BoundedEdgeRegularSubgraphs.TrimDegrees
import Mathlib.Tactic

/-!
# Iterating density increments until the variance is small
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

theorem arrayDensity_mem_Icc (q : Edge α → Set.Icc (0 : ℝ) 1)
    (hn : 2 ≤ Fintype.card α) : arrayDensity q ∈ Set.Icc 0 1 := by
  have hn' : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hden : 0 < (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  change 0 ≤ (2 * ∑ e, (q e : ℝ)) / _ ∧ (2 * ∑ e, (q e : ℝ)) / _ ≤ 1
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ ↦ (q e).property.1)) hden.le
  · apply (div_le_one hden).2
    rw [← card_edge_twice]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun e _ ↦ (q e).property.2)

omit [Fintype α] in
private def flattenVertices (S : Finset α) (T : Finset ↥S) : Finset α :=
  T.map (Function.Embedding.subtype (· ∈ S))

omit [Fintype α] in
private def flattenVerticesIso (S : Finset α) (T : Finset ↥S) : ↥T ≃o ↥(flattenVertices S T) where
  toEquiv :=
    { toFun := fun v ↦ ⟨v.val.val, Finset.mem_map.mpr ⟨v.val, v.property, rfl⟩⟩
      invFun := fun v ↦
        ⟨⟨v.val, by
          obtain ⟨z, _, hz⟩ := Finset.mem_map.mp v.property
          exact hz ▸ z.property⟩, by
          obtain ⟨z, hz, h⟩ := Finset.mem_map.mp v.property
          exact (Subtype.ext h : z = ⟨v.val, _⟩) ▸ hz⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl }
  map_rel_iff' := Iff.rfl

omit [Fintype α] in
private theorem induce_nested_reindex {β : Type*} (q : Edge α → β)
    (S : Finset α) (T : Finset ↥S) :
    induce T (induce S q) =
      induce (flattenVertices S T) q ∘ edgeEquiv (flattenVerticesIso S T) := by
  funext a
  have he :
      inducedEdge S (inducedEdge T a) =
        inducedEdge (flattenVertices S T) (edgeEquiv (flattenVerticesIso S T) a) := Subtype.ext rfl
  change q (inducedEdge S (inducedEdge T a)) =
    q (inducedEdge (flattenVertices S T) (edgeEquiv (flattenVerticesIso S T) a))
  rw [he]

omit [Fintype α] in
private theorem arrayDensity_nested (q : Edge α → Set.Icc (0 : ℝ) 1)
    (S : Finset α) (T : Finset ↥S) :
    arrayDensity (induce T (induce S q)) = arrayDensity (induce (flattenVertices S T) q) := by
  let e := flattenVerticesIso S T
  have hQ := induce_nested_reindex q S T
  rw [hQ, arrayDensity, arrayDensity, Fintype.card_congr e.toEquiv]
  let q' (a : Edge ↥(flattenVertices S T)) := (q (inducedEdge (flattenVertices S T) a) : ℝ)
  have hsum := (edgeEquiv e).sum_comp q'
  change (2 * ∑ a, q' (edgeEquiv e a)) / _ = (2 * ∑ a, q' a) / _
  rw [hsum]

/-- The extraction stage of Lemma 5.2. Each unsuccessful step raises the
density by more than half the variance threshold and keeps a quarter of the vertices. -/
theorem exists_subdomain_variation_le (q : Edge α → Set.Icc (0 : ℝ) 1)
    {τ M₀ : ℝ} (hM : 32 ≤ M₀)
    (hExp : 16 * Real.exp (-M₀ / 8) ≤ τ) (J : ℕ)
    (hJ : 2 ≤ (J : ℝ) * τ) (hn : (4 : ℝ) ^ J * M₀ ≤ Fintype.card α) :
    ∃ S : Finset α, (Fintype.card α : ℝ) ≤ (4 : ℝ) ^ J * S.card ∧
      M₀ ≤ (S.card : ℝ) ∧ normalizedDegreeVariation (induce S q) ≤ τ := by
  classical
  let n : ℝ := Fintype.card α
  let good := ∃ S : Finset α, n ≤ (4 : ℝ) ^ J * S.card ∧
    M₀ ≤ (S.card : ℝ) ∧ normalizedDegreeVariation (induce S q) ≤ τ
  have hJ₀ : J ≠ 0 := by rintro rfl; norm_num at hJ
  have hsize (i : ℕ) (hi : i ≤ J) (S : Finset α) (hs : n ≤ (4 : ℝ) ^ i * S.card) :
      M₀ ≤ (S.card : ℝ) := by
    apply le_of_mul_le_mul_left _ (by positivity : 0 < (4 : ℝ) ^ i)
    calc
      _ ≤ (4 : ℝ) ^ J * M₀ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (by linarith)
      _ ≤ _ := hn.trans hs
  have hiter (i : ℕ) (hi : i ≤ J) : good ∨
      ∃ S : Finset α, n ≤ (4 : ℝ) ^ i * S.card ∧
        (i : ℝ) * τ / 2 ≤ arrayDensity (induce S q) ∧
        (i = 0 ∨ (i : ℝ) * τ / 2 < arrayDensity (induce S q)) := by
    induction i with
    | zero =>
      right
      have hs : n ≤ (4 : ℝ) ^ 0 * (Finset.univ : Finset α).card := by simp [n]
      have hh := hsize 0 hi Finset.univ hs
      have hn' : 2 ≤ Fintype.card ↥(Finset.univ : Finset α) := by
        rw [Fintype.card_coe]
        have h := (show (2 : ℝ) ≤ M₀ by linarith).trans hh
        exact_mod_cast h
      refine ⟨Finset.univ, hs, ?_, Or.inl rfl⟩
      simpa only [Nat.cast_zero, zero_mul, zero_div] using
        (arrayDensity_mem_Icc (induce Finset.univ q) hn').1
    | succ i ih =>
      rcases ih (by omega) with hg | ⟨S, hS, hp, _⟩
      · exact Or.inl hg
      have hM' := hsize i (by omega) S hS
      rcases le_or_gt (normalizedDegreeVariation (induce S q)) τ with hv | hv
      · left
        refine ⟨S, hS.trans ?_, hM', hv⟩
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega : i ≤ J))
          (Nat.cast_nonneg _)
      have h32 : 32 ≤ Fintype.card ↥S := by
        rw [Fintype.card_coe]
        exact_mod_cast hM.trans hM'
      have hth :
          16 * Real.exp (-(Fintype.card ↥S : ℝ) / 8) < normalizedDegreeVariation (induce S q) := by
        have hsub : (-(Fintype.card ↥S : ℝ)) / 8 ≤ -M₀ / 8 := by
          rw [Fintype.card_coe]
          linarith only [hM']
        exact ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsub) (by norm_num)).trans hExp).trans_lt hv
      obtain ⟨T, hT, hinc⟩ := exists_density_increment (induce S q) h32 hth
      let U := flattenVertices S T
      have hcard : S.card ≤ 4 * U.card := by
        simpa only [U, flattenVertices, Finset.card_map, Fintype.card_coe] using hT
      have hcard' : (S.card : ℝ) ≤ 4 * U.card := by exact_mod_cast hcard
      have hnext : n ≤ (4 : ℝ) ^ (i + 1) * U.card := by
        rw [pow_succ, mul_assoc]
        exact hS.trans (mul_le_mul_of_nonneg_left hcard' (by positivity))
      have hp' : ((i + 1 : ℕ) : ℝ) * τ / 2 < arrayDensity (induce U q) := by
        rw [arrayDensity_nested] at hinc
        push_cast
        linarith only [hinc, hv, hp]
      exact Or.inr ⟨U, hnext, hp'.le, Or.inr hp'⟩
  rcases hiter J le_rfl with h | ⟨S, hS, _, hbad⟩
  · exact h
  have h32 : 2 ≤ Fintype.card ↥S := by
    rw [Fintype.card_coe]
    have hh := (show (2 : ℝ) ≤ M₀ by linarith).trans (hsize J le_rfl S hS)
    exact_mod_cast hh
  have htop := (arrayDensity_mem_Icc (induce S q) h32).2
  have hbad' := hbad.resolve_left hJ₀
  linarith only [hJ, htop, hbad']

/-- Lemma 5.2. Iteration and trimming give a large induced domain with both
the uniform and the mean-square bounds on expected degrees. -/
theorem exists_nearBalanced_subdomain (q : Edge α → Set.Icc (0 : ℝ) 1) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 16)
    (hn : (4 : ℝ) ^ (⌈2 / η ^ 2⌉₊ : ℕ) *
      max 32 (8 * Real.log (16 / η ^ 2)) ≤ Fintype.card α) :
    ∃ U : Finset α, (Fintype.card α : ℝ) / (4 : ℝ) ^ (⌈2 / η ^ 2⌉₊ : ℕ) / 2 ≤ (U.card : ℝ) ∧
      let d := degreeSum (fun e ↦ (q (inducedEdge U e) : ℝ))
      (∀ i, |d i - vertexMean d| ≤ 3 * Real.sqrt η * ((U.card : ℝ) - 1)) ∧
        (∑ i, (d i - vertexMean d) ^ 2) / (U.card : ℝ) ≤
          6 * η ^ 2 * ((U.card : ℝ) - 1) ^ 2 := by
  classical
  let J : ℕ := ⌈2 / η ^ 2⌉₊
  let M₀ := max 32 (8 * Real.log (16 / η ^ 2))
  have hη₂ : 0 < η ^ 2 := sq_pos_of_pos hη
  have hJ : 2 ≤ (J : ℝ) * η ^ 2 := (div_le_iff₀ hη₂).1 (Nat.le_ceil _)
  have hM : 32 ≤ M₀ := le_max_left _ _
  have hExp : 16 * Real.exp (-M₀ / 8) ≤ η ^ 2 := by
    have h := le_max_right (32 : ℝ) (8 * Real.log (16 / η ^ 2))
    have h₁ : -M₀ / 8 ≤ -Real.log (16 / η ^ 2) := by dsimp only [M₀]; linarith only [h]
    calc
      _ ≤ 16 * Real.exp (-Real.log (16 / η ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₁) (by norm_num)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  obtain ⟨S, hS, hS₀, hV⟩ := exists_subdomain_variation_le q hM hExp J hJ hn
  let d := degreeSum (fun e ↦ (q (inducedEdge S e) : ℝ))
  let c := vertexMean d
  have h32 : 32 ≤ Fintype.card ↥S := by
    rw [Fintype.card_coe]
    exact_mod_cast hM.trans hS₀
  have hvar : (∑ i, (d i - c) ^ 2) ≤ η ^ 2 * (Fintype.card ↥S : ℝ) ^ 3 := by
    have hpos : 0 < (Fintype.card ↥S : ℝ) := Nat.cast_pos.mpr (by omega)
    exact (div_le_iff₀ (pow_pos hpos 3)).1 hV
  obtain ⟨T, hT, hbounds⟩ := exists_trimmed_degree_bounds d c hη hη' h32 hvar
  let U := flattenVertices S T
  let e := flattenVerticesIso S T
  let qS := induce S q
  let y := degreeSum (fun a ↦ (qS (inducedEdge T a) : ℝ))
  let z := degreeSum (fun a ↦ (q (inducedEdge U a) : ℝ))
  obtain ⟨hmax, hms⟩ := hbounds y (fun i ↦ degreeSum_induce_loss qS T i)
  have hcard : U.card = T.card := Finset.card_map _
  have hrow (i : ↥T) : y i = z (e i) := by
    have h := degreeSum_reindex e (fun a ↦ (q (inducedEdge U a) : ℝ)) i
    have hp := induce_nested_reindex (fun a ↦ (q a : ℝ)) S T
    change degreeSum (induce T (induce S (fun a ↦ (q a : ℝ)))) i = _
    rw [hp]
    exact h
  have hmean : vertexMean y = vertexMean z := by
    unfold vertexMean
    simp_rw [hrow]
    have hsum : (∑ i : ↥T, z (e i)) = ∑ i : ↥U, z i := e.toEquiv.sum_comp z
    rw [hsum, Fintype.card_coe, Fintype.card_coe, hcard]
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [Fintype.card_coe, ← hcard] at hT
    have hT' : (S.card : ℝ) ≤ 2 * U.card := by
      linarith only [hT, Nat.cast_nonneg (α := ℝ) S.card]
    have ht' := mul_le_mul_of_nonneg_left hT' (show 0 ≤ (4 : ℝ) ^ J by positivity)
    change (Fintype.card α : ℝ) / (4 : ℝ) ^ J / 2 ≤ _
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ J)).2
    linarith only [hS, ht']
  · intro i
    have hh := hmax (e.symm i)
    rw [hrow, hmean, e.apply_symm_apply, ← hcard] at hh
    exact hh
  · have hh : (∑ i : ↥T, (y i - vertexMean y) ^ 2) =
        (∑ i : ↥U, (z i - vertexMean z) ^ 2) := by
      simp_rw [hrow, hmean]
      exact e.toEquiv.sum_comp (fun i ↦ (z i - vertexMean z) ^ 2)
    rw [hh, ← hcard] at hms
    exact hms

end BoundedEdgeRegularSubgraphs
