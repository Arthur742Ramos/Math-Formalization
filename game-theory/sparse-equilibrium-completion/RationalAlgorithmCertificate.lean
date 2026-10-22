/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Actual finite rational certificate output; the container may include zero weights. -/
module
public import RationalLogRounds
public import RationalCertificateSoundness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def fullRationalCertificate {k m : ℕ} (p : Fin k → ℚ) (q : Fin m → ℚ)
    (B : Fin m → Fin m → ℚ) : RationalCertificate k m where
  support := Finset.univ
  anchors := p
  weights := fun i => q i
  residual := fun i j => B i j

theorem full_rational_certificate_q {k m : ℕ} (p : Fin k → ℚ) (q : Fin m → ℚ)
    (B : Fin m → Fin m → ℚ) (i : Fin m) : (fullRationalCertificate p q B).q i=q i := by
  simp [fullRationalCertificate,RationalCertificate.q]

theorem full_rational_certificate_b {k m : ℕ} (p : Fin k → ℚ) (q : Fin m → ℚ)
    (B : Fin m → Fin m → ℚ) (i j : Fin m) : (fullRationalCertificate p q B).b i j=B i j := by
  simp [fullRationalCertificate,RationalCertificate.b]

theorem rational_gap_algorithm_certificate {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ρ : ℚ) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapAlgorithm d.K d.D d.p d.M d.r ρ d.η d.R=some (q,B)) :
    (fullRationalCertificate d.p q B).check d.K d.D d.M (ρ+d.η)=true := by
  have hs := rational_gap_algorithm_sound d.K d.D d.p d.M d.r ρ d.η d.R q B h
  apply (RationalCertificate.check_iff _ _ _ _ _).mpr
  refine ⟨le_of_lt d.positiveBound,d.anchorNonneg,?_,?_,d.anchorSkew,d.anchorBounds,
    d.crossBounds,?_,?_,?_⟩
  · intro i
    rw [full_rational_certificate_q]
    exact hs.2.1.1 i
  · simp_rw [full_rational_certificate_q]
    rw [hs.2.1.2.1]
    exact d.normalized
  · intro i _ j _
    simpa only [full_rational_certificate_b] using hs.2.2.1 i j
  · intro i _ j _
    simpa only [full_rational_certificate_b] using hs.2.2.2.1 i j
  · refine ⟨?_,?_,?_⟩
    · intro a
      change (∑ b, d.K a b*d.p b)-(∑ i, d.D i a*(fullRationalCertificate d.p q B).q i) ≤ ρ+d.η
      simp_rw [full_rational_certificate_q]
      have ha := hs.2.1.2.2.2.1 a
      unfold rationalAnchorResponse at ha
      linarith [d.positiveSlack]
    · intro i _
      change (∑ a, d.D i a*d.p a)+(∑ j, (fullRationalCertificate d.p q B).b i j*
        (fullRationalCertificate d.p q B).q j) ≤ ρ+d.η
      simp_rw [full_rational_certificate_b,full_rational_certificate_q]
      simpa only [rationalScore] using hs.2.2.2.2 i
    · intro i hi
      exact False.elim (hi (Finset.mem_univ i))

def checkRationalGapOutput {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (σ : ℚ) (c : RationalCertificate k m) : Bool :=
  c.check d.K d.D d.M σ && decide (d.R.Satisfies c.q) && decide (c.anchors=d.p)

theorem rational_gap_algorithm_checked_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ρ : ℚ) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapAlgorithm d.K d.D d.p d.M d.r ρ d.η d.R=some (q,B)) :
    checkRationalGapOutput d (ρ+d.η) (fullRationalCertificate d.p q B)=true := by
  have hc := rational_gap_algorithm_certificate d ρ q B h
  have hs := (rational_gap_algorithm_sound d.K d.D d.p d.M d.r ρ d.η d.R q B h).1
  have he : (fullRationalCertificate d.p q B).q=q := by
    funext i
    exact full_rational_certificate_q d.p q B i
  unfold checkRationalGapOutput
  rw [hc,he]
  have ha : (fullRationalCertificate d.p q B).anchors=d.p := rfl
  rw [decide_eq_true hs,decide_eq_true ha]
  rfl

end SparseCompletion
