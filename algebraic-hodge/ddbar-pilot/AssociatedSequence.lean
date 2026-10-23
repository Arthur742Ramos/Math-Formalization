module

public import Degeneration

/-! A conventional E1 mathlib spectral sequence with the actual column-filtered quotient pages. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

noncomputable abbrev pageObject (r : ℤ) (pq : ℤ × ℤ) : ModuleCat k :=
  ModuleCat.of k (Filtered.Page (filtered K) r pq.1 (pq.1 + pq.2))

noncomputable def differentialTo (r : ℤ) (pq pq' : ℤ × ℤ)
    (h : pq + (r, 1 - r) = pq') : pageObject K r pq ⟶ pageObject K r pq' :=
  ModuleCat.ofHom (Filtered.differential (filtered K) r pq.1 (pq.1 + pq.2)) ≫
    eqToHom (by
      have hp : pq.1 + r = pq'.1 := congrArg Prod.fst h
      have hq : pq.2 + (1 - r) = pq'.2 := congrArg Prod.snd h
      have hn : pq.1 + pq.2 + 1 = pq'.1 + pq'.2 := by lia -abstractProof
      change ModuleCat.of k (Filtered.Page (filtered K) r (pq.1 + r) (pq.1 + pq.2 + 1)) = _
      rw [hp, hn])

noncomputable def pageDifferential (r : ℤ) (pq pq' : ℤ × ℤ) :
    pageObject K r pq ⟶ pageObject K r pq' :=
  if h : pq + (r, 1 - r) = pq' then differentialTo K r pq pq' h else 0

theorem pageDifferential_zero (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) : pageDifferential K r pq pq' = 0 := by
  unfold pageDifferential
  split_ifs
  · dsimp only [differentialTo]
    rw [all_differentials_zero K hdd r pq.1 (pq.1 + pq.2) hr]
    exact zero_comp
  · rfl

/-- The differential is the actual induced total differential, with conventional bidegree. -/
noncomputable def pageComplex (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r : ℤ) (hr : 1 ≤ r) :
    HomologicalComplex (ModuleCat k) (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) where
  X := pageObject K r
  d := pageDifferential K r
  shape _ _ h := dite_eq_right h
  d_comp_d' pq pq' pq'' _ _ := by
    rw [pageDifferential_zero K hdd r hr pq pq', zero_comp]

noncomputable def zeroPageHomologyIso (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    (pageComplex K hdd r hr).homology pq ≅ pageObject K r pq :=
  (ShortComplex.LeftHomologyData.ofZeros ((pageComplex K hdd r hr).sc pq)
    (pageDifferential_zero K hdd r hr _ _)
    (pageDifferential_zero K hdd r hr _ _)).homologyIso

noncomputable def associatedSequence (hdd : ∀ p q : ℤ, ImageKernel K p q) :
    CohomologicalSpectralSequence (ModuleCat k) 1 where
  page r hr := pageComplex K hdd r hr
  iso r r' pq hrr' hr :=
    zeroPageHomologyIso K hdd r hr pq ≪≫
      pageIso K r pq.1 pq.2 (pq.1 + pq.2) rfl hr
        (hdd (pq.1 - 1) pq.2) (hdd pq.1 pq.2) ≪≫
      (pageIso K r' pq.1 pq.2 (pq.1 + pq.2) rfl (by lia -abstractProof)
        (hdd (pq.1 - 1) pq.2) (hdd pq.1 pq.2)).symm

theorem associatedSequence_d_zero (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((associatedSequence K hdd).page r hr).d pq pq' = 0 :=
  pageDifferential_zero K hdd r hr pq pq'

end AlgebraicHodgePilot.Column
