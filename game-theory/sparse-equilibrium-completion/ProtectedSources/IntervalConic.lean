/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.IntervalPerspective
public import ProtectedSources.SparseWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def perspectiveCuts {ι : Type*} [Fintype ι] (q H : ι → ℝ) (M r ε : ℝ) : Prop :=
  ∀ S : Finset ι, M*(mass S q)^2-M*r*mass S q+(∑ i ∈ S, (H i-ε*q i)) ≤ 0

theorem perspective_cuts_iff {ι : Type*} [Fintype ι] (q t H : ι → ℝ) (M r ε : ℝ)
    (hH : ∀ i, q i*t i=H i) :
    Cuts M r q (fun i => t i-ε) ↔ perspectiveCuts q H M r ε := by
  have he : ∀ S : Finset ι, (∑ i ∈ S, q i*(t i-ε))=∑ i ∈ S, (H i-ε*q i) := by
    intro S
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_sub,hH i,mul_comm (q i) ε]
  constructor <;> intro h S
  · have hc := h S
    rw [he] at hc
    nlinarith
  · have hc := h S
    rw [he]
    nlinarith

theorem anchor_response_of_perspective {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (hV : ∀ i h, q i*D i h=V i h) (h : α) :
    anchorResponse K D p q h=(∑ a, K h a*p a)-∑ i, V i h := by
  unfold anchorResponse
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, hV i h]

theorem score_lower_from_intervals {ι α : Type*} [Fintype α]
    (lo D : ι → α → ℝ) (p : α → ℝ) (hp : ∀ h, 0 ≤ p h)
    (hD : ∀ i h, lo i h ≤ D i h) (i : ι) : score lo p i ≤ score D p i := by
  unfold score
  exact Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hD i h) (hp h)

theorem interval_perspective_completion_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hr : ∑ i, q i=r) (hlu : ∀ i h, lo i h ≤ hi i h) :
    (∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧ IsSkew B ∧
      (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ V : ι → α → ℝ,
      (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
      (∀ h, (∑ a, K h a*p a)-(∑ i, V i h) ≤ ε) ∧
      (∀ i, score lo p i ≤ ε+M*r) ∧ perspectiveCuts q (intervalMomentScore p V) M r ε := by
  classical
  constructor
  · rintro ⟨D,B,hD,hB,hb,hrows⟩
    let V := fun i h => q i*D i h
    have hV : ∀ i h, q i*D i h=V i h := fun _ _ => rfl
    have hh := (block_response_bounds_iff K D B p q ε).mp hrows
    have hc := (weighted_completion_iff q (score D p) M r ε (le_of_lt hM) hq hr).mp
      ⟨B,hB,hb,hh.2⟩
    refine ⟨V,?_,?_,?_,?_⟩
    · intro i h
      exact ⟨by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).1) (hq i)],
        by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).2) (hq i)]⟩
    · intro h
      rw [←anchor_response_of_perspective K D V p q hV h]
      exact hh.1 h
    · intro i
      exact le_trans (score_lower_from_intervals lo D p hp (fun i h => (hD i h).1) i) (hc.1 i)
    · apply (perspective_cuts_iff q (score D p) (intervalMomentScore p V) M r ε ?_).mp hc.2
      intro i
      unfold score intervalMomentScore
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by dsimp only [V]; ring
  · rintro ⟨V,hV,ha,hg,hcuts⟩
    let D := intervalCrossRecover lo V q
    obtain ⟨hD,hprod⟩ := interval_recovered_cross_bounds lo hi V q hq hlu
      (fun i h => (hV i h).1) (fun i h => (hV i h).2)
    have hc : Cuts M r q (fun i => score D p i-ε) :=
      (perspective_cuts_iff q (score D p) (intervalMomentScore p V) M r ε
        (fun i => interval_recovered_score_moment lo V p q hprod i)).mpr hcuts
    have hguard : ∀ i, score D p i ≤ ε+M*r := by
      intro i
      by_cases hz : q i=0
      · have he : score D p i=score lo p i := by
          simp only [D,score,intervalCrossRecover,perspectiveRecover,hz,ite_true]
        rw [he]
        exact hg i
      · have ht := supported_score_cap q (fun i => score D p i-ε) M r hM hq hc i hz
        linarith
    obtain ⟨B,hB,hb,hrows⟩ :=
      (weighted_completion_iff q (score D p) M r ε (le_of_lt hM) hq hr).mpr ⟨hguard,hc⟩
    refine ⟨D,B,hD,hB,hb,?_⟩
    apply (block_response_bounds_iff K D B p q ε).mpr
    refine ⟨?_,hrows⟩
    intro h
    rw [anchor_response_of_perspective K D V p q hprod h]
    exact ha h

theorem normalized_interval_perspective_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hr : ∑ i, q i=r) (hpmass : (∑ h, p h)+r=1) (hK : IsSkew K)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) :
    (∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
      (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
      IsSkew (blockMatrix K D B) ∧
      (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ V : ι → α → ℝ,
      (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
      (∀ h, (∑ a, K h a*p a)-(∑ i, V i h) ≤ ε) ∧
      (∀ i, score lo p i ≤ ε+M*r) ∧ perspectiveCuts q (intervalMomentScore p V) M r ε := by
  constructor
  · rintro ⟨D,B,hD,_,_,hsk,hb,hrows⟩
    apply (interval_perspective_completion_iff K lo hi p q M r ε hM hp hq hr hlu).mp
    refine ⟨D,B,hD,?_,?_,hrows⟩
    · intro i j
      exact hsk (.inr i) (.inr j)
    · intro i j
      exact hb (.inr i) (.inr j)
  · intro h
    obtain ⟨D,B,hD,hB,hb,hrows⟩ :=
      (interval_perspective_completion_iff K lo hi p q M r ε hM hp hq hr hlu).mpr h
    have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun i h =>
      ⟨le_trans (hlo i h) (hD i h).1,le_trans (hD i h).2 (hhi i h)⟩
    refine ⟨D,B,hD,blockWeights_nonneg p q hp hq,?_,blockMatrix_skew K D B hK hB,
      blockMatrix_bounds K D B M hKb hDb hb,hrows⟩
    rw [blockWeights_mass,hr]
    exact hpmass

end
end SparseCompletion
