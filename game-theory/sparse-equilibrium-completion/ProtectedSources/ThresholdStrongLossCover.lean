/- AI-assisted source-only draft under repository Apache-2.0.
Exact-source verification is recorded in separate receipts. The strict threshold is the paper's d_ij > beta,
and beta is transported from its stated nonnegative loss domain. -/
module
public import ProtectedSources.ArbitraryWeakCover
public import ProtectedSources.IntervalLossOrder
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Strong-loss edges use the original intervalLoss, with a strict threshold. -/
def intervalStrongLossEdge {ν : Type*} (lo hi : ν → ν → ℝ) (M β : ℝ)
    (a b : ν) : Prop := a ≠ b ∧ β < intervalLoss M (lo a b) (hi a b)

def intervalStrongLossVertexCover {ν : Type*} (C : Set ν)
    (lo hi : ν → ν → ℝ) (M β : ℝ) : Prop :=
  ∀ a b, intervalStrongLossEdge lo hi M β a b → a ∈ C ∨ b ∈ C

/-- Unordered-pair form used literally in the paper's observation graph. -/
def orderedStrongLossVertexCover {ν : Type*} [LinearOrder ν] (C : Set ν)
    (lo hi : ν → ν → ℝ) (M β : ℝ) : Prop :=
  ∀ a b, a < b → β < intervalLoss M (lo a b) (hi a b) → a ∈ C ∨ b ∈ C

theorem strong_loss_cover_ordered_bridge {ν : Type*} [LinearOrder ν]
    (C : Set ν) (lo hi : ν → ν → ℝ) (M β : ℝ)
    (hrev : ∀ a b, a ≠ b → lo a b = -hi b a ∧ hi a b = -lo b a) :
    orderedStrongLossVertexCover C lo hi M β ↔
      intervalStrongLossVertexCover C lo hi M β := by
  constructor
  · intro h a b hab
    rcases lt_or_gt_of_ne hab.1 with hlt | hgt
    · exact h a b hlt hab.2
    · have hs : intervalLoss M (lo b a) (hi b a) = intervalLoss M (lo a b) (hi a b) := by
        rw [(hrev b a hab.1.symm).1, (hrev b a hab.1.symm).2, interval_loss_reverse]
      exact (h b a hgt (by rw [hs]; exact hab.2)).symm
  · intro h a b hab hβ
    exact h a b ⟨ne_of_lt hab, hβ⟩

/-- The inserted zero in residualLossValues handles empty labels and the
absence of uncovered pairs. Its comparison requires the earned beta≥0. -/
theorem strong_loss_cover_residual_bound {ν : Type*} [Fintype ν]
    (C : Set ν) [DecidablePred (· ∈ C)] (lo hi : ν → ν → ℝ) (M β : ℝ)
    (hβ : 0 ≤ β) (hcover : intervalStrongLossVertexCover C lo hi M β) :
    residualLossBound (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
      (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M ≤ β := by
  apply (residual_loss_bound_le_iff _ _ M β).mpr
  refine ⟨hβ, ?_⟩
  intro i j hij
  by_contra h
  have he : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  have hstrong : β < intervalLoss M (lo i.val j.val) (hi i.val j.val) := lt_of_not_ge h
  rcases hcover i.val j.val ⟨he, hstrong⟩ with hiC | hjC
  · exact i.property hiC
  · exact j.property hjC

theorem ordered_strong_loss_cover_residual_bound {ν : Type*} [Fintype ν] [LinearOrder ν]
    (C : Set ν) [DecidablePred (· ∈ C)] (lo hi : ν → ν → ℝ) (M β : ℝ)
    (hβ : 0 ≤ β)
    (hrev : ∀ a b, a ≠ b → lo a b = -hi b a ∧ hi a b = -lo b a)
    (hcover : orderedStrongLossVertexCover C lo hi M β) :
    residualLossBound (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
      (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M ≤ β :=
  strong_loss_cover_residual_bound C lo hi M β hβ
    ((strong_loss_cover_ordered_bridge C lo hi M β hrev).mp hcover)

/-- The source beta_C earns its entire [0,2M] domain from the actual
nonempty bounded interval endpoints, including no residual pairs. -/
theorem residual_loss_source_domain {ν : Type*} [Fintype ν]
    (C : Set ν) [DecidablePred (· ∈ C)] (lo hi : ν → ν → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hlo : ∀ a b, a ≠ b → -M ≤ lo a b)
    (hhi : ∀ a b, a ≠ b → hi a b ≤ M)
    (hlu : ∀ a b, a ≠ b → lo a b ≤ hi a b) :
    residualLossBound (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
      (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M ∈ Set.Icc 0 ((2 : ℕ) * M) := by
  refine ⟨residual_loss_bound_nonnegative _ _ M, ?_⟩
  apply residual_loss_bound_le _ _ M hM
  · intro i j hij
    exact hlo i.val j.val (fun he => hij (Subtype.ext he))
  · intro i j hij
    exact hhi i.val j.val (fun he => hij (Subtype.ext he))
  · intro i j hij
    exact hlu i.val j.val (fun he => hij (Subtype.ext he))

/-- beta_C itself is a threshold for which C covers every stronger edge;
this uses the computed finite loss maximum, not an assumed loss-bound field. -/
theorem residual_loss_bound_gives_strong_cover {ν : Type*} [Fintype ν]
    (C : Set ν) [DecidablePred (· ∈ C)] (lo hi : ν → ν → ℝ) (M : ℝ) :
    intervalStrongLossVertexCover C lo hi M
      (residualLossBound (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
        (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M) := by
  intro a b hab
  by_cases ha : a ∈ C
  · exact Or.inl ha
  · by_cases hb : b ∈ C
    · exact Or.inr hb
    · let i : (Cᶜ : Set ν) := ⟨a, ha⟩
      let j : (Cᶜ : Set ν) := ⟨b, hb⟩
      have hij : i ≠ j := fun he => hab.1 (congrArg Subtype.val he)
      have hbound := residual_loss_le_bound
        (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
        (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M i j hij
      exact False.elim (not_lt_of_ge hbound hab.2)

/-- This scalar statement includes r=0 literally; no positive residual mass
or nonempty residual type is introduced to transport the beta*r error. -/
theorem strong_loss_cover_error_bound {ν : Type*} [Fintype ν] [LinearOrder ν]
    (C : Set ν) [DecidablePred (· ∈ C)] (lo hi : ν → ν → ℝ) (x : ν → ℝ) (M β : ℝ)
    (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i)
    (hrev : ∀ a b, a ≠ b → lo a b = -hi b a ∧ hi a b = -lo b a)
    (hcover : orderedStrongLossVertexCover C lo hi M β) :
    residualLossBound (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
      (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M * (∑ i : (Cᶜ : Set ν), x i) ≤
      β * (∑ i : (Cᶜ : Set ν), x i) := by
  exact mul_le_mul_of_nonneg_right
    (ordered_strong_loss_cover_residual_bound C lo hi M β hβ hrev hcover)
    (Finset.sum_nonneg fun i _ => hx i.val)

/-- Paper-facing strict-threshold corollary, preserving all original witness, support, incident-entry, anchor-response and extra-moment guarantees. Only the nonnegative endpoint of beta’s source domain is needed. -/
theorem threshold_vertex_subset_weak_sparse {ν : Type*} [Fintype ν] [LinearOrder ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M ρ η β : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hlo : ∀ a b, a ≠ b → -M ≤ lo a b) (hhi : ∀ a b, a ≠ b → hi a b ≤ M)
    (hlu : ∀ a b, a ≠ b → lo a b ≤ hi a b)
    (hrev : ∀ a b, a ≠ b → lo a b= -hi b a ∧ hi a b= -lo b a)
    (hβ : β ∈ Set.Icc 0 ((2 : ℕ) * M))
    (hcover : orderedStrongLossVertexCover C lo hi M β) (hresp : ∀ i, response A x i ≤ ρ) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ ρ+η+β*r) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  have herr := strong_loss_cover_error_bound C lo hi x M β hβ.1 hn hrev hcover
  obtain ⟨A', x', hxn, hxm, hsk, hbb, hInt, hrows, hC, hS, hres, htotal, hentries, hanchors, hF⟩ :=
    arbitrary_vertex_subset_weak_sparse C d F A lo hi x M ρ η hM hη hA hb hn hm hI hlo hhi hlu hrev hresp
  refine ⟨A', x', hxn, hxm, hsk, hbb, hInt, ?_, hC, hS, hres, htotal, hentries, hanchors, hF⟩
  intro i
  exact le_trans (hrows i) (by linarith)


/-- Paper-facing strict-threshold corollary, preserving all original witness, support, incident-entry, anchor-response and extra-moment guarantees. Only the nonnegative endpoint of beta’s source domain is needed. -/
theorem threshold_vertex_subset_weak_exact {ν : Type*} [Fintype ν] [LinearOrder ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M η β : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hlo : ∀ a b, a ≠ b → -M ≤ lo a b) (hhi : ∀ a b, a ≠ b → hi a b ≤ M)
    (hlu : ∀ a b, a ≠ b → lo a b ≤ hi a b)
    (hrev : ∀ a b, a ≠ b → lo a b= -hi b a ∧ hi a b= -lo b a)
    (hβ : β ∈ Set.Icc 0 ((2 : ℕ) * M))
    (hcover : orderedStrongLossVertexCover C lo hi M β) (hresp : ∀ i, response A x i ≤ 0) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ η+β*r) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  have herr := strong_loss_cover_error_bound C lo hi x M β hβ.1 hn hrev hcover
  obtain ⟨A', x', hxn, hxm, hsk, hbb, hInt, hrows, hC, hS, hres, htotal, hentries, hanchors, hF⟩ :=
    arbitrary_vertex_subset_weak_exact C d F A lo hi x M η hM hη hA hb hn hm hI hlo hhi hlu hrev hresp
  refine ⟨A', x', hxn, hxm, hsk, hbb, hInt, ?_, hC, hS, hres, htotal, hentries, hanchors, hF⟩
  intro i
  exact le_trans (hrows i) (by linarith)

end
end SparseCompletion
