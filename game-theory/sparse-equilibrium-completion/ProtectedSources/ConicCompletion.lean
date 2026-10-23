/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.ScorePrefixes
public import ProtectedSources.GameModel

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def rotatedLorentz (u v w : ℝ) : Prop := 0 ≤ u ∧ 0 ≤ v ∧ w^2 ≤ (2 : ℕ)*u*v

theorem prefix_cut_quadratic {m : ℕ} (q t : Fin m → ℝ) (M r ε : ℝ) (l : ℕ) :
    (∑ i ∈ scorePrefix m l, q i*(t i-ε)) ≤
      M*mass (scorePrefix m l) q*(r-mass (scorePrefix m l) q) ↔
    M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
      (∑ i ∈ scorePrefix m l, q i*(t i-ε)) ≤ 0 := by
  constructor <;> intro h <;> nlinarith

theorem quadratic_rotated_cone (M r Q a : ℝ) (hM : 0 < M) :
    M*Q^2-M*r*Q+a ≤ 0 ↔ rotatedLorentz (r*Q-a/M) (1/(2 : ℕ)) Q := by
  have hscale : M*(r*Q-a/M-Q^2)= -(M*Q^2-M*r*Q+a) := by
    field_simp
    ring
  unfold rotatedLorentz
  norm_num only [Nat.cast_ofNat]
  constructor
  · intro h
    have hh : 0 ≤ r*Q-a/M-Q^2 := nonneg_of_mul_nonneg_right (by linarith) hM
    refine ⟨?_,by norm_num,?_⟩ <;> nlinarith [sq_nonneg Q]
  · rintro ⟨_,_,h⟩
    have hh : 0 ≤ M*(r*Q-a/M-Q^2) := mul_nonneg (le_of_lt hM) (by nlinarith)
    linarith

theorem weighted_completion_prefix_quadratic_iff {m : ℕ} (q t : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (ht : Antitone t) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ε) ↔
    (∀ i, t i ≤ ε+M*r) ∧ ∀ l : ℕ, l ≤ m →
      M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
        (∑ i ∈ scorePrefix m l, q i*(t i-ε)) ≤ 0 := by
  rw [weighted_completion_iff q t M r ε (le_of_lt hM) hq hr]
  have hs : Antitone (fun i => t i-ε) := fun _ _ hij => sub_le_sub_right (ht hij) ε
  rw [cuts_iff_score_prefixes q (fun i => t i-ε) M r hM hq hr hs]
  constructor
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (prefix_cut_quadratic q t M r ε l).mp (hp l hl)⟩
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (prefix_cut_quadratic q t M r ε l).mpr (hp l hl)⟩

theorem weighted_completion_rotated_cones_iff {m : ℕ} (q t : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (ht : Antitone t) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ε) ↔
    (∀ i, t i ≤ ε+M*r) ∧ ∀ l : ℕ, l ≤ m →
      rotatedLorentz (r*mass (scorePrefix m l) q-
        (∑ i ∈ scorePrefix m l, q i*(t i-ε))/M) (1/(2 : ℕ)) (mass (scorePrefix m l) q) := by
  rw [weighted_completion_prefix_quadratic_iff q t M r ε hM hq hr ht]
  constructor
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (quadratic_rotated_cone M r _ _ hM).mp (hp l hl)⟩
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (quadratic_rotated_cone M r _ _ hM).mpr (hp l hl)⟩

theorem known_anchor_prefix_characterization {m k : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ) (q : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (ht : Antitone (score D p)) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    (∀ h, anchorResponse K D p q h ≤ ε) ∧ (∀ i, score D p i ≤ ε+M*r) ∧
      ∀ l : ℕ, l ≤ m →
        rotatedLorentz (r*mass (scorePrefix m l) q-
          (∑ i ∈ scorePrefix m l, q i*(score D p i-ε))/M) (1/(2 : ℕ)) (mass (scorePrefix m l) q) := by
  constructor
  · rintro ⟨B,hB,hb,hrows⟩
    have hh := (block_response_bounds_iff K D B p q ε).mp hrows
    have hc := (weighted_completion_rotated_cones_iff q (score D p) M r ε hM hq hr ht).mp
      ⟨B,hB,hb,hh.2⟩
    exact ⟨hh.1,hc⟩
  · rintro ⟨ha,hg,hp⟩
    obtain ⟨B,hB,hb,hrows⟩ :=
      (weighted_completion_rotated_cones_iff q (score D p) M r ε hM hq hr ht).mpr ⟨hg,hp⟩
    exact ⟨B,hB,hb,(block_response_bounds_iff K D B p q ε).mpr ⟨ha,hrows⟩⟩

theorem normalized_known_anchor_conic_iff {m k : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ) (q : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hr : ∑ i, q i=r) (hpmass : (∑ h, p h)+r=1)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M) (ht : Antitone (score D p)) :
    (∃ B, (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
      IsSkew (blockMatrix K D B) ∧
      (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    (∀ h, anchorResponse K D p q h ≤ ε) ∧ (∀ i, score D p i ≤ ε+M*r) ∧
      ∀ l : ℕ, l ≤ m →
        rotatedLorentz (r*mass (scorePrefix m l) q-
          (∑ i ∈ scorePrefix m l, q i*(score D p i-ε))/M) (1/(2 : ℕ)) (mass (scorePrefix m l) q) := by
  constructor
  · rintro ⟨B,_,_,hsk,hb,hrows⟩
    apply (known_anchor_prefix_characterization K D p q M r ε hM hq hr ht).mp
    refine ⟨B,?_,?_,hrows⟩
    · intro i j
      exact hsk (.inr i) (.inr j)
    · intro i j
      exact hb (.inr i) (.inr j)
  · intro h
    obtain ⟨B,hB,hb,hrows⟩ :=
      (known_anchor_prefix_characterization K D p q M r ε hM hq hr ht).mpr h
    refine ⟨B,blockWeights_nonneg p q hp hq,?_,blockMatrix_skew K D B hK hB,
      blockMatrix_bounds K D B M hKb hDb hb,hrows⟩
    rw [blockWeights_mass,hr]
    exact hpmass

end
end SparseCompletion
