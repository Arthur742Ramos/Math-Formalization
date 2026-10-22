/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GameModel
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
structure RationalCertificate (k m : ℕ) where
  support : Finset (Fin m)
  anchors : Fin k → ℚ
  weights : support → ℚ
  residual : support → support → ℚ

namespace RationalCertificate

def q {k m : ℕ} (c : RationalCertificate k m) (i : Fin m) : ℚ :=
  if h : i ∈ c.support then c.weights ⟨i,h⟩ else 0

def b {k m : ℕ} (c : RationalCertificate k m) (i j : Fin m) : ℚ :=
  if hi : i ∈ c.support then
    if hj : j ∈ c.support then c.residual ⟨i,hi⟩ ⟨j,hj⟩ else 0
  else 0

def Rows {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) : Prop :=
  (∀ h, (∑ h', K h h'*c.anchors h')-∑ i, D i h*c.q i ≤ σ) ∧
  (∀ i ∈ c.support, (∑ h, D i h*c.anchors h)+(∑ j ∈ c.support, c.b i j*c.q j) ≤ σ) ∧
  (∀ i, i ∉ c.support → (∑ h, D i h*c.anchors h)-M*(∑ j, c.q j) ≤ σ)

def Conditions {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) : Prop :=
  0 ≤ M ∧
  (∀ h, 0 ≤ c.anchors h) ∧ (∀ i, 0 ≤ c.q i) ∧
  (∑ h, c.anchors h)+(∑ i, c.q i)=1 ∧
  (∀ h h', K h h' = -K h' h) ∧
  (∀ h h', -M ≤ K h h' ∧ K h h' ≤ M) ∧
  (∀ i h, -M ≤ D i h ∧ D i h ≤ M) ∧
  (∀ i ∈ c.support, ∀ j ∈ c.support, c.b i j = -c.b j i) ∧
  (∀ i ∈ c.support, ∀ j ∈ c.support, -M ≤ c.b i j ∧ c.b i j ≤ M) ∧
  c.Rows K D M σ

instance {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) :
    Decidable (c.Conditions K D M σ) := by
  unfold RationalCertificate.Conditions RationalCertificate.Rows
  infer_instance

/-- Computable finite rational checker, including every omitted row. -/
def check {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) : Bool :=
  decide (c.Conditions K D M σ)

theorem check_iff {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) :
    c.check K D M σ=true ↔ c.Conditions K D M σ := by
  exact decide_eq_true_iff

theorem q_on {k m : ℕ} (c : RationalCertificate k m) (i : c.support) :
    c.q i=c.weights i := by simp [q]

theorem b_on {k m : ℕ} (c : RationalCertificate k m) (i j : c.support) :
    c.b i j=c.residual i j := by simp [b]

theorem reject_omitted_violation {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ)
    (i : Fin m) (hi : i ∉ c.support)
    (hv : σ < (∑ h, D i h*c.anchors h)-M*(∑ j, c.q j)) :
    c.check K D M σ=false := by
  cases he : c.check K D M σ
  · rfl
  · have hc := (c.check_iff K D M σ).mp he
    exact False.elim (not_le_of_gt hv (hc.2.2.2.2.2.2.2.2.2.2.2 i hi))

noncomputable section

def realQ {k m : ℕ} (c : RationalCertificate k m) : Fin m → ℝ :=
  fun i => (c.q i : ℝ)

def realB {k m : ℕ} (c : RationalCertificate k m) (M : ℚ) : Fin m → Fin m → ℝ :=
  compactCompletion c.support (M : ℝ) (fun i j => (c.b i j : ℝ))

theorem realQ_off {k m : ℕ} (c : RationalCertificate k m)
    (i : Fin m) (hi : i ∉ c.support) : c.realQ i=0 := by
  simp [realQ,q,hi]

theorem support_card_le {k m : ℕ} (c : RationalCertificate k m) :
    (Finset.univ.filter fun i => c.realQ i ≠ 0).card ≤ c.support.card := by
  classical
  apply Finset.card_le_card
  intro i hi
  by_contra hs
  exact (Finset.mem_filter.mp hi).2 (c.realQ_off i hs)

theorem realB_stored {k m : ℕ} (c : RationalCertificate k m)
    (M : ℚ) (i j : c.support) : c.realB M i j=(c.residual i j : ℝ) := by
  simp [realB,compactCompletion,b]

theorem realB_omitted {k m : ℕ} (c : RationalCertificate k m)
    (M : ℚ) (i j : Fin m) (hi : i ∉ c.support) :
    c.realB M i j=if j ∈ c.support then -(M : ℝ) else 0 := by
  simp [realB,compactCompletion,hi]

theorem rows_iff {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) :
    (∀ a, response (blockMatrix (fun h h' => (K h h' : ℝ))
      (fun i h => (D i h : ℝ)) (c.realB M))
      (blockWeights (fun h => (c.anchors h : ℝ)) c.realQ) a ≤ (σ : ℝ)) ↔
      c.Rows K D M σ := by
  rw [realB,compact_block_certificate_iff c.support _ _ _ _ c.realQ (M : ℝ)
    (∑ i, c.realQ i) (σ : ℝ) c.realQ_off rfl]
  simp only [anchorResponse,score,realQ,Rows]
  norm_cast
end
end RationalCertificate
end SparseCompletion
