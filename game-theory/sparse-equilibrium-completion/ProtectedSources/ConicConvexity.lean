/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.ConicCompletion

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def prefixQuadratic {m : ℕ} (t : Fin m → ℝ) (M r ε : ℝ) (l : ℕ) (q : Fin m → ℝ) : ℝ :=
  M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
    ∑ i ∈ scorePrefix m l, q i*(t i-ε)

theorem finite_linear_mix {ι : Type*} (s : Finset ι) (q q' f : ι → ℝ) (a b : ℝ) :
    (∑ i ∈ s, (a*q i+b*q' i)*f i)=a*(∑ i ∈ s, q i*f i)+b*(∑ i ∈ s, q' i*f i) := by
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,←Finset.mul_sum]

theorem finite_mass_mix {ι : Type*} (s : Finset ι) (q q' : ι → ℝ) (a b : ℝ) :
    mass s (a • q+b • q')=a*mass s q+b*mass s q' := by
  unfold mass
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_one] using finite_linear_mix s q q' (fun _ => 1) a b

theorem prefix_quadratic_mix {m : ℕ} (t q q' : Fin m → ℝ) (M r ε a b : ℝ)
    (l : ℕ) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    prefixQuadratic t M r ε l (a • q+b • q') ≤
      a*prefixQuadratic t M r ε l q+b*prefixQuadratic t M r ε l q' := by
  unfold prefixQuadratic
  rw [finite_mass_mix]
  have he := finite_linear_mix (scorePrefix m l) q q' (fun i => t i-ε) a b
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [he]
  have hid : M*(a*mass (scorePrefix m l) q+b*mass (scorePrefix m l) q')^2-
      M*r*(a*mass (scorePrefix m l) q+b*mass (scorePrefix m l) q')+
      (a*(∑ i ∈ scorePrefix m l, q i*(t i-ε))+b*(∑ i ∈ scorePrefix m l, q' i*(t i-ε))) =
      a*(M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
        ∑ i ∈ scorePrefix m l, q i*(t i-ε))+
      b*(M*(mass (scorePrefix m l) q')^2-M*r*mass (scorePrefix m l) q'+
        ∑ i ∈ scorePrefix m l, q' i*(t i-ε))-
      M*a*b*(mass (scorePrefix m l) q-mass (scorePrefix m l) q')^2 := by
    have hb' : b=1-a := by linarith
    rw [hb']
    ring
  rw [hid]
  exact sub_le_self _ (by positivity)

theorem prefix_system_convex {m : ℕ} (t : Fin m → ℝ) (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {q : Fin m → ℝ | ∀ l : ℕ, l ≤ m → prefixQuadratic t M r ε l q ≤ 0} := by
  intro q hq q' hq' a b ha hb hab l hl
  have hm := prefix_quadratic_mix t q q' M r ε a b l hM ha hb hab
  have h1 := mul_nonpos_of_nonneg_of_nonpos ha (hq l hl)
  have h2 := mul_nonpos_of_nonneg_of_nonpos hb (hq' l hl)
  exact le_trans hm (by linarith)


theorem anchor_response_mix {m k : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ) (q q' : Fin m → ℝ)
    (a b : ℝ) (hab : a+b=1) (h : Fin k) :
    anchorResponse K D p (a • q+b • q') h=
      a*anchorResponse K D p q h+b*anchorResponse K D p q' h := by
  have hs := finite_linear_mix Finset.univ q q' (fun i => D i h) a b
  have hs' : (∑ i, D i h*(a • q+b • q') i)=
      a*(∑ i, D i h*q i)+b*(∑ i, D i h*q' i) := by
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hs
  unfold anchorResponse
  rw [hs']
  have hb : b=1-a := by linarith
  rw [hb]
  ring

def knownAnchorConicFeasible {m k : ℕ} (R : Set (Fin m → ℝ))
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ)
    (M r ε : ℝ) : Set (Fin m → ℝ) :=
  {q | q ∈ R ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
    (∀ h, anchorResponse K D p q h ≤ ε) ∧ (∀ i, score D p i ≤ ε+M*r) ∧
    ∀ l : ℕ, l ≤ m → prefixQuadratic (score D p) M r ε l q ≤ 0}

theorem known_anchor_conic_system_convex {m k : ℕ} (R : Set (Fin m → ℝ))
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ)
    (M r ε : ℝ) (hM : 0 ≤ M) (hR : Convex ℝ R) :
    Convex ℝ (knownAnchorConicFeasible R K D p M r ε) := by
  intro q hq q' hq' a b ha hb hab
  rcases hq with ⟨hqR,hqn,hqm,hqa,hqg,hqp⟩
  rcases hq' with ⟨hqR',hqn',hqm',hqa',_,hqp'⟩
  refine ⟨hR hqR hqR' ha hb hab,?_,?_,?_,hqg,?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hqn i)) (mul_nonneg hb (hqn' i))
  · have hm := finite_mass_mix Finset.univ q q' a b
    unfold mass at hm
    rw [hm,hqm,hqm',←add_mul,hab,one_mul]
  · intro h
    rw [anchor_response_mix K D p q q' a b hab h]
    have h0 := mul_le_mul_of_nonneg_left (hqa h) ha
    have h1 := mul_le_mul_of_nonneg_left (hqa' h) hb
    calc
      _ ≤ a*ε+b*ε := add_le_add h0 h1
      _ = ε := by rw [←add_mul,hab,one_mul]
  · exact prefix_system_convex (score D p) M r ε hM hqp hqp' ha hb hab

theorem known_anchor_conic_system_iff {m k : ℕ} (R : Set (Fin m → ℝ))
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ)
    (q : Fin m → ℝ) (M r ε : ℝ) (hM : 0 < M) (ht : Antitone (score D p)) :
    q ∈ knownAnchorConicFeasible R K D p M r ε ↔
      q ∈ R ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
      ∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
        ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε := by
  constructor
  · rintro ⟨hqR,hq,hm,ha,hg,hp⟩
    refine ⟨hqR,hq,hm,?_⟩
    apply (known_anchor_prefix_characterization K D p q M r ε hM hq hm ht).mpr
    refine ⟨ha,hg,?_⟩
    intro l hl
    exact (quadratic_rotated_cone M r _ _ hM).mp (hp l hl)
  · rintro ⟨hqR,hq,hm,hB⟩
    obtain ⟨ha,hg,hp⟩ := (known_anchor_prefix_characterization K D p q M r ε hM hq hm ht).mp hB
    refine ⟨hqR,hq,hm,ha,hg,?_⟩
    intro l hl
    exact (quadratic_rotated_cone M r _ _ hM).mpr (hp l hl)


theorem linear_repertoire_convex {m : ℕ} {β : Type*} (F : Fin m → β → ℝ) (c : β → ℝ) :
    Convex ℝ {q : Fin m → ℝ | ∀ j, (∑ i, q i*F i j) ≤ c j} := by
  intro q hq q' hq' a b ha hb hab j
  have hs := finite_linear_mix Finset.univ q q' (fun i => F i j) a b
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [hs]
  calc
    _ ≤ a*c j+b*c j := add_le_add
      (mul_le_mul_of_nonneg_left (hq j) ha) (mul_le_mul_of_nonneg_left (hq' j) hb)
    _ = c j := by rw [←add_mul,hab,one_mul]

end
end SparseCompletion
