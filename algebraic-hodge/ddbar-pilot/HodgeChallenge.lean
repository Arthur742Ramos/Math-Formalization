module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Algebraic column E1 degeneration and bounded abutment
This proof-complete statement surface uses actual bicomplex operators, filtered
quotients and total cohomology. The hypothesis is a componentwise image/kernel
identity. It is conditional algebraic mathematics, without analytic Kähler claims.
Definitions are literal and all selected proofs are supplied. Generated from the
modular development by dependency selection and declaration-header reflow;
verification/challenge-source-map.json records the retained source declarations.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits
namespace AlgebraicHodgePilot
abbrev Bicomplex (k : Type) [Field k] :=
  HomologicalComplex₂ (ModuleCat k) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
noncomputable abbrev total {k : Type} [Field k] (K : Bicomplex k) : CochainComplex (ModuleCat k) ℤ := K.total (ComplexShape.up ℤ)
end AlgebraicHodgePilot
namespace AlgebraicHodgePilot
variable {k : Type} [Field k] (K : Bicomplex k)
abbrev horizontal (p q : ℤ) := ((K.d p (p + 1)).f q).hom
abbrev vertical (p q : ℤ) := ((K.X p).d q (q + 1)).hom
abbrev incomingVertical (p q : ℤ) := ((K.X p).d (q - 1) q).hom
def ImageKernel (p q : ℤ) : Prop :=
  LinearMap.range (horizontal K p q) ⊓ LinearMap.ker (vertical K (p + 1) q) =
    LinearMap.range ((horizontal K p q).comp (incomingVertical K p q))
theorem exists_closed_correction (p q : ℤ) (hdd : ImageKernel K p q) (x : (K.X p).X q) (hx : vertical K p q x = 0) : ∃ b : (K.X p).X (q - 1), horizontal K p q (x - incomingVertical K p q b) = 0 ∧ vertical K p q (x - incomingVertical K p q
    b) = 0 := by
  have hcomm : vertical K (p + 1) q (horizontal K p q x) =
      horizontal K p (q + 1) (vertical K p q x) :=
    congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom (K.d_comm p (p + 1) q (q + 1)))
  have hmem : horizontal K p q x ∈
      LinearMap.range (horizontal K p q) ⊓ LinearMap.ker (vertical K (p + 1) q) := by
    exact ⟨⟨x, rfl⟩, by simpa [hx] using hcomm⟩
  rw [hdd] at hmem
  obtain ⟨b, hb⟩ := hmem
  change horizontal K p q (incomingVertical K p q b) = horizontal K p q x at hb
  refine ⟨b, ?_, ?_⟩
  · rw [map_sub, ← hb]
    exact sub_self _
  · have hvv : vertical K p q (incomingVertical K p q b) = 0 := by
      have h := congrArg (fun f => f b) (congrArg ModuleCat.Hom.hom
        ((K.X p).d_comp_d (q - 1) q (q + 1)))
      exact h
    rw [map_sub, hx, hvv, sub_self]
abbrev verticalSC (p q : ℤ) := (K.X p).sc' (q - 1) q (q + 1)
noncomputable def verticalHomologyIso (p q : ℤ) : (K.X p).homology q ≅ (verticalSC K p q).homology :=
  (K.X p).homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)
noncomputable def verticalClass (p q : ℤ) (z : LinearMap.ker (vertical K p q)) : (K.X p).homology q :=
  (verticalHomologyIso K p q).inv
    ((verticalSC K p q).moduleCatHomologyIso.inv
      ((verticalSC K p q).moduleCatLeftHomologyData.π z))
theorem exists_closed_representative (p q : ℤ) (hdd : ImageKernel K p q) (c : (K.X p).homology q) : ∃ z : LinearMap.ker (vertical K p q), horizontal K p q z = 0 ∧ verticalClass K p q z = c := by
  let S := verticalSC K p q
  let c' := S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)
  obtain ⟨x, hx⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective c'
  let x₀ : LinearMap.ker (vertical K p q) := x
  change S.moduleCatLeftHomologyData.π x₀ = c' at hx
  obtain ⟨b, hb, hv⟩ := exists_closed_correction K p q hdd x₀.val x₀.property
  let y : LinearMap.ker (vertical K p q) := ⟨x₀.val - incomingVertical K p q b, hv⟩
  refine ⟨y, hb, ?_⟩
  have hxy : S.moduleCatLeftHomologyData.π y = S.moduleCatLeftHomologyData.π x₀ := by
    apply (Submodule.Quotient.eq _).2
    refine ⟨-b, ?_⟩
    apply Subtype.ext
    change incomingVertical K p q (-b) = (x₀.val - incomingVertical K p q b) - x₀.val
    simp [map_neg, sub_sub_cancel_left]
  dsimp [verticalClass]
  rw [hxy]
  change (verticalHomologyIso K p q).inv (S.moduleCatHomologyIso.inv (_)) = c
  rw [hx]
  simp [c']
end AlgebraicHodgePilot
namespace AlgebraicHodgePilot
variable {k : Type} [Field k] (K : Bicomplex k)
theorem total_closed_of_biclosed (p q : ℤ) (x : (K.X p).X q) (hh : horizontal K p q x = 0) (hv : vertical K p q x = 0) : ((total K).d (p + q) (p + q + 1)).hom ((K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl).hom x) = 0 := by
  change ((K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
    (K.total (ComplexShape.up ℤ)).d (p + q) (p + q + 1)).hom) x = 0
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  rw [K.d₁_eq' (ComplexShape.up ℤ) (i₁ := p) (i₁' := p + 1) (by rfl),
    K.d₂_eq' (ComplexShape.up ℤ) p (i₂ := q) (i₂' := q + 1) (by rfl)]
  simp only [horizontal, vertical] at hh hv
  simp [ModuleCat.hom_comp, hh, hv]
end AlgebraicHodgePilot
namespace AlgebraicHodgePilot.Filtered
variable {k : Type} [Field k]
structure Filtration (C : CochainComplex (ModuleCat k) ℤ) where
  F : (p n : ℤ) → Submodule k (C.X n)
  antitone (n : ℤ) : Antitone (fun p => F p n)
  preserves (p n m : ℤ) : F p n ≤ (F p m).comap (C.d n m).hom
variable {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)
def cycles (r p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ (F.F (p + r) (n + 1)).comap (C.d n (n + 1)).hom
def boundaries (r p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ (F.F (p - r) (n - 1)).map (C.d (n - 1) n).hom
def denominator (r p n : ℤ) : Submodule k (C.X n) :=
  cycles F (r - 1) (p + 1) n ⊔ boundaries F (r - 1) p n
theorem differential_squared (n : ℤ) (x : C.X n) : (C.d (n + 1) (n + 1 + 1)).hom ((C.d n (n + 1)).hom x) = 0 :=
  congrArg (fun f => f.hom x) (C.d_comp_d n (n + 1) (n + 1 + 1))
theorem boundary_closed (r p n : ℤ) {x : C.X n} (hx : x ∈ boundaries F r p n) : (C.d n (n + 1)).hom x = 0 := by
  obtain ⟨u, _, hu⟩ := hx.2
  rw [← hu]
  exact congrArg (fun f => f.hom u) (C.d_comp_d (n - 1) n (n + 1))
theorem denominator_le_cycles (r p n : ℤ) : denominator F r p n ≤ cycles F r p n := by
  apply sup_le
  · intro x hx
    refine ⟨F.antitone n (by lia -abstractProof) hx.1, ?_⟩
    have h : (p + 1) + (r - 1) = p + r := by lia -abstractProof
    simpa only [h] using hx.2
  · intro x hx
    exact ⟨hx.1, by change (C.d n (n + 1)).hom x ∈ F.F (p + r) (n + 1)
                    rw [boundary_closed F (r - 1) p n hx]
                    exact (F.F (p + r) (n + 1)).zero_mem⟩
abbrev Page (r p n : ℤ) :=
  cycles F r p n ⧸ (denominator F r p n).comap (cycles F r p n).subtype
def differentialOnCycles (r p n : ℤ) : cycles F r p n →ₗ[k] cycles F r (p + r) (n + 1) :=
  ((C.d n (n + 1)).hom.comp (cycles F r p n).subtype).codRestrict _ fun x =>
    ⟨x.property.2, by
      change (C.d (n + 1) (n + 1 + 1)).hom ((C.d n (n + 1)).hom x.val) ∈ F.F (p + r + r) (n + 1 + 1)
      rw [differential_squared n x.val]
      exact (F.F (p + r + r) (n + 1 + 1)).zero_mem⟩
theorem differential_denominator (r p n : ℤ) (x : cycles F r p n) (hx : x ∈ (denominator F r p n).comap (cycles F r p n).subtype) : differentialOnCycles F r p n x ∈ (denominator F r (p + r) (n + 1)).comap (cycles F r (p + r) (n +
    1)).subtype := by
  change (C.d n (n + 1)).hom x.val ∈ denominator F r (p + r) (n + 1)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  change a + b = x.val at hab
  rw [← hab, map_add, boundary_closed F (r - 1) p n hb, add_zero]
  apply (le_sup_right : boundaries F (r - 1) (p + r) (n + 1) ≤
    denominator F r (p + r) (n + 1))
  change (C.d n (n + 1)).hom a ∈ boundaries F (r - 1) (p + r) (n + 1)
  refine ⟨?_, ?_⟩
  · have h : p + 1 + (r - 1) = p + r := by lia -abstractProof
    have hh : (C.d n (n + 1)).hom a ∈ F.F (p + 1 + (r - 1)) (n + 1) := ha.2
    rw [h] at hh
    exact hh
  · have h : p + r - (r - 1) = p + 1 := by lia -abstractProof
    rw [show n + 1 - 1 = n by lia -abstractProof, h]
    exact ⟨a, ha.1, rfl⟩
def differential (r p n : ℤ) : Page F r p n →ₗ[k] Page F r (p + r) (n + 1) :=
  (denominator F r p n).comap (cycles F r p n).subtype |>.liftQ
    (((denominator F r (p + r) (n + 1)).comap
      (cycles F r (p + r) (n + 1)).subtype).mkQ.comp (differentialOnCycles F r p n))
    (by
      intro x hx
      change _ = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (differential_denominator F r p n x hx))
def quotient (r p n : ℤ) : cycles F r p n →ₗ[k] Page F r p n :=
  ((denominator F r p n).comap (cycles F r p n).subtype).mkQ
theorem quotient_surjective (r p n : ℤ) : Function.Surjective (quotient F r p n) :=
  Submodule.mkQ_surjective _
@[simp]
theorem differential_quotient (r p n : ℤ) (x : cycles F r p n) : differential F r p n (quotient F r p n x) = quotient F r (p + r) (n + 1) (differentialOnCycles F r p n x) := rfl
end AlgebraicHodgePilot.Filtered
namespace AlgebraicHodgePilot.Column
variable {k : Type} [Field k] (K : Bicomplex k)
noncomputable def inclusion (p q n : ℤ) (h : p + q = n) : (K.X p).X q ⟶ (total K).X n :=
  K.ιTotal (ComplexShape.up ℤ) p q n h
noncomputable def projection (p q n : ℤ) : (total K).X n ⟶ (K.X p).X q :=
  K.totalDesc (c₁₂ := ComplexShape.up ℤ) (i₁₂ := n) fun a b _ =>
    if h : a = p ∧ b = q then
      (K.XXIsoOfEq _ _ _ h.1 h.2).hom
    else 0
theorem inclusion_projection_self (p q : ℤ) : inclusion K p q (p + q) rfl ≫ projection K p q (p + q) = 𝟙 _ := by
  dsimp only [inclusion, projection, AlgebraicHodgePilot.total]
  rw [K.ι_totalDesc]
  simp [HomologicalComplex₂.XXIsoOfEq]
@[reassoc]
theorem inclusion_projection_ne (a b p q n : ℤ) (hab : a + b = n) (h : ¬ (a = p ∧ b = q)) : inclusion K a b n hab ≫ projection K p q n = 0 := by
  dsimp only [inclusion, projection, AlgebraicHodgePilot.total]
  rw [K.ι_totalDesc]
  simp [h]
@[reassoc]
theorem inclusion_projection_eq (p q n : ℤ) (h : p + q = n) : inclusion K p q n h ≫ projection K p q n = 𝟙 _ := by
  subst n
  exact inclusion_projection_self K p q
noncomputable def filtration (p n : ℤ) : Submodule k ((total K).X n) :=
  ⨆ (a : ℤ) (b : ℤ) (h : a + b = n) (_ : p ≤ a),
    LinearMap.range (inclusion K a b n h).hom
theorem inclusion_mem_filtration (p a b n : ℤ) (h : a + b = n) (hp : p ≤ a) (x : (K.X a).X b) : (inclusion K a b n h).hom x ∈ filtration K p n := by
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem h (Submodule.mem_iSup_of_mem hp ⟨x, rfl⟩)))
theorem filtration_antitone (n : ℤ) : Antitone (fun p => filtration K p n) := by
  intro p p' hpp
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun hp => ?_
  rintro _ ⟨x, rfl⟩
  exact inclusion_mem_filtration K p a b n hab (hpp.trans hp) x
theorem projection_kills_next (p q n : ℤ) : filtration K (p + 1) n ≤ LinearMap.ker (projection K p q n).hom := by
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun hp => ?_
  rintro _ ⟨x, rfl⟩
  have h := inclusion_projection_ne K a b p q n hab (by intro he; lia -abstractProof)
  exact congrArg (fun f => f.hom x) h
theorem filtration_split (p q n : ℤ) (h : p + q = n) : filtration K p n = LinearMap.range (inclusion K p q n h).hom ⊔ filtration K (p + 1) n := by
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun hp => ?_
    by_cases ha : a = p
    · have hb : b = q := by lia -abstractProof
      subst a b
      exact le_sup_left
    · rintro _ ⟨x, rfl⟩
      exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, _,
        inclusion_mem_filtration K (p + 1) a b n hab (by lia -abstractProof) x, zero_add _⟩
  · apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact inclusion_mem_filtration K p p q n h (le_refl p) x
    · exact filtration_antitone K n (by lia -abstractProof)
theorem mem_next_of_projection_zero (p q n : ℤ) (h : p + q = n) (x : (total K).X n) (hx : x ∈ filtration K p n) (hz : (projection K p q n).hom x = 0) : x ∈ filtration K (p + 1) n := by
  rw [filtration_split K p q n h] at hx
  obtain ⟨a, ⟨u, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  have hu : u = 0 := by
    have hcomp := congrArg (fun f => f.hom u) (inclusion_projection_eq K p q n h)
    have hbz := projection_kills_next K p q n hb
    change (projection K p q n).hom b = 0 at hbz
    rw [← hab, map_add, hbz, add_zero] at hz
    exact hcomp.symm.trans hz
  subst u
  have hb' : b = x := by simpa using hab
  exact hb' ▸ hb
theorem inclusionOrZero_mem_filtration (p a b n : ℤ) (hp : p ≤ a) (x : (K.X a).X b) : (K.ιTotalOrZero (ComplexShape.up ℤ) a b n).hom x ∈ filtration K p n := by
  by_cases h : a + b = n
  · rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) a b n h]
    exact inclusion_mem_filtration K p a b n h hp x
  · rw [K.ιTotalOrZero_eq_zero (ComplexShape.up ℤ) a b n h]
    exact (filtration K p n).zero_mem
theorem differential_preserves_filtration (p n m : ℤ) : filtration K p n ≤ (filtration K p m).comap ((total K).d n m).hom := by
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun hp => ?_
  rintro _ ⟨x, rfl⟩
  change ((inclusion K a b n hab ≫ (total K).d n m).hom) x ∈ filtration K p m
  dsimp only [AlgebraicHodgePilot.total]
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add]
  change ((K.ιTotal (ComplexShape.up ℤ) a b n hab ≫ K.D₁ (ComplexShape.up ℤ) n m +
    K.ιTotal (ComplexShape.up ℤ) a b n hab ≫ K.D₂ (ComplexShape.up ℤ) n m).hom) x ∈ filtration K p m
  rw [HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    K.d₁_eq' (ComplexShape.up ℤ) (i₁ := a) (i₁' := a + 1) (by rfl),
    K.d₂_eq' (ComplexShape.up ℤ) a (i₂ := b) (i₂' := b + 1) (by rfl)]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  apply Submodule.add_mem
  · have hs : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (a, b) = 1 := rfl
    rw [hs, one_smul]
    exact inclusionOrZero_mem_filtration K p (a + 1) b m (by lia -abstractProof)
      (((K.d a (a + 1)).f b).hom x)
  · exact (filtration K p m).toAddSubgroup.zsmul_mem
      (inclusionOrZero_mem_filtration K p a (b + 1) m hp (((K.X a).d b (b + 1)).hom x))
      (a.negOnePow : ℤ)
noncomputable def filtered : Filtered.Filtration (total K) where
  F := filtration K
  antitone := filtration_antitone K
  preserves := differential_preserves_filtration K
theorem inclusionOrZero_projection_ne (a b p q n : ℤ) (h : ¬ (a = p ∧ b = q)) : K.ιTotalOrZero (ComplexShape.up ℤ) a b n ≫ projection K p q n = 0 := by
  by_cases hab : a + b = n
  · rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) a b n hab]
    exact inclusion_projection_ne K a b p q n hab h
  · rw [K.ιTotalOrZero_eq_zero (ComplexShape.up ℤ) a b n hab, zero_comp]
theorem inclusionOrZero_projection_eq (p q n : ℤ) (h : p + q = n) : K.ιTotalOrZero (ComplexShape.up ℤ) p q n ≫ projection K p q n = 𝟙 _ := by
  rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) p q n h]
  exact inclusion_projection_eq K p q n h
theorem inclusion_d (a b n m : ℤ) (hab : a + b = n) : inclusion K a b n hab ≫ (total K).d n m = (K.d a (a + 1)).f b ≫ K.ιTotalOrZero (ComplexShape.up ℤ) (a + 1) b m + a.negOnePow • ((K.X a).d b (b + 1) ≫ K.ιTotalOrZero (ComplexShape.up ℤ) a
    (b + 1) m) := by
  dsimp only [inclusion, AlgebraicHodgePilot.total]
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    K.d₁_eq' (ComplexShape.up ℤ) (i₁ := a) (i₁' := a + 1) (by rfl),
    K.d₂_eq' (ComplexShape.up ℤ) a (i₂ := b) (i₂' := b + 1) (by rfl)]
  simp [ComplexShape.ε₁, ComplexShape.ε₂]
theorem d_projection (p q n : ℤ) (hn : p + q = n + 1) : (total K).d n (n + 1) ≫ projection K p q (n + 1) = projection K (p - 1) q n ≫ (K.d (p - 1) p).f q + p.negOnePow • (projection K p (q - 1) n ≫ (K.X p).d (q - 1) q) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  change inclusion K a b n hab ≫ _ = inclusion K a b n hab ≫ _
  rw [← Category.assoc, inclusion_d, Preadditive.add_comp,
    Linear.units_smul_comp]
  simp only [Preadditive.comp_add, Linear.comp_units_smul, Category.assoc]
  by_cases ha : a = p - 1
  · have hb : b = q := by lia -abstractProof
    subst a b
    rw [show p - 1 + 1 = p by lia -abstractProof]
    rw [inclusionOrZero_projection_eq K p q (n + 1) hn,
      inclusionOrZero_projection_ne K (p - 1) (q + 1) p q (n + 1) (by intro h; lia -abstractProof),
      inclusion_projection_eq_assoc K (p - 1) q n hab,
      inclusion_projection_ne_assoc K (p - 1) q p (q - 1) n hab (by intro h; lia -abstractProof)]
    simp
  · by_cases ha' : a = p
    · have hb : b = q - 1 := by lia -abstractProof
      subst a b
      rw [show q - 1 + 1 = q by lia -abstractProof]
      rw [inclusionOrZero_projection_ne K (p + 1) (q - 1) p q (n + 1) (by intro h; lia -abstractProof),
        inclusionOrZero_projection_eq K p q (n + 1) hn,
        inclusion_projection_ne_assoc K p (q - 1) (p - 1) q n hab (by intro h; lia -abstractProof),
        inclusion_projection_eq_assoc K p (q - 1) n hab]
      simp
    · rw [inclusionOrZero_projection_ne K (a + 1) b p q (n + 1) (by intro h; lia -abstractProof),
        inclusionOrZero_projection_ne K a (b + 1) p q (n + 1) (by intro h; lia -abstractProof),
        inclusion_projection_ne_assoc K a b (p - 1) q n hab (by intro h; exact ha h.1),
        inclusion_projection_ne_assoc K a b p (q - 1) n hab (by intro h; exact ha' h.1)]
      simp
theorem d_projection_apply (p q n : ℤ) (hn : p + q = n + 1) (x : (total K).X n) : (projection K p q (n + 1)).hom (((total K).d n (n + 1)).hom x) = ((K.d (p - 1) p).f q).hom ((projection K (p - 1) q n).hom x) + p.negOnePow • ((K.X p).d (q -
    1) q).hom ((projection K p (q - 1) n).hom x) := by
  exact congrArg (fun f => f.hom x) (d_projection K p q n hn)
end AlgebraicHodgePilot.Column
namespace AlgebraicHodgePilot
variable {k : Type} [Field k] (K : Bicomplex k)
noncomputable def verticalClassMap (p q : ℤ) : LinearMap.ker (vertical K p q) →ₗ[k] (K.X p).homology q :=
  (verticalHomologyIso K p q).inv.hom.comp
    ((verticalSC K p q).moduleCatHomologyIso.inv.hom.comp
      (verticalSC K p q).moduleCatLeftHomologyData.π.hom)
theorem verticalClassMap_apply (p q : ℤ) (z : LinearMap.ker (vertical K p q)) : verticalClassMap K p q z = verticalClass K p q z := rfl
theorem verticalClassMap_surjective (p q : ℤ) : Function.Surjective (verticalClassMap K p q) := by
  intro c
  let S := verticalSC K p q
  let c' := S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)
  obtain ⟨x, hx⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective c'
  let z : LinearMap.ker (vertical K p q) := x
  change S.moduleCatLeftHomologyData.π z = c' at hx
  refine ⟨z, ?_⟩
  change (verticalHomologyIso K p q).inv
    (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = c
  rw [hx]
  simp [c']
theorem verticalClassMap_eq_zero_iff (p q : ℤ) (z : LinearMap.ker (vertical K p q)) : verticalClassMap K p q z = 0 ↔ ∃ b : (K.X p).X (q - 1), incomingVertical K p q b = z.val := by
  let S := verticalSC K p q
  constructor
  · intro h
    have hh := congrArg
      (fun c => S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)) h
    have hq : S.moduleCatLeftHomologyData.π z = 0 := by
      simp [verticalClassMap, S] at hh
      exact hh
    have hm : z ∈ LinearMap.range S.moduleCatToCycles :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hz : S.moduleCatToCycles b = z := Subtype.ext hb
    have hq : S.moduleCatLeftHomologyData.π z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hz⟩
    change (verticalHomologyIso K p q).inv
      (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = 0
    rw [hq]
    simp
end AlgebraicHodgePilot
namespace AlgebraicHodgePilot.Column
variable {k : Type} [Field k] (K : Bicomplex k)
theorem leading_vertical_closed (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (x : (total K).X n) (hx : x ∈ Filtered.cycles (filtered K) r p n) : vertical K p q ((projection K p q n).hom x) = 0 := by
  have hlo : (projection K (p - 1) (q + 1) n).hom x = 0 := by
    apply projection_kills_next K (p - 1) (q + 1) n
    rw [show p - 1 + 1 = p by lia -abstractProof]
    exact hx.1
  have hhi : (projection K p (q + 1) (n + 1)).hom
      (((total K).d n (n + 1)).hom x) = 0 := by
    apply projection_kills_next K p (q + 1) (n + 1)
    exact filtration_antitone K (n + 1) (show p + 1 ≤ p + r by lia -abstractProof) hx.2
  have hd := congrArg (fun f => f.hom x) (d_projection K p (q + 1) n (by lia -abstractProof))
  rw [show q + 1 - 1 = q by lia -abstractProof] at hd
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hd
  rw [hhi, hlo, map_zero, zero_add] at hd
  have hs := congrArg (fun y => p.negOnePow • y) hd.symm
  simpa [smul_smul, Int.units_mul_self] using hs
noncomputable def leadingCycleMap (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) : Filtered.cycles (filtered K) r p n →ₗ[k] LinearMap.ker (vertical K p q) :=
  ((projection K p q n).hom.domRestrict (Filtered.cycles (filtered K) r p n)).codRestrict _
    fun x => leading_vertical_closed K r p q n hn hr x.val x.property
noncomputable def leadingClassMap (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) : Filtered.cycles (filtered K) r p n →ₗ[k] (K.X p).homology q :=
  (verticalClassMap K p q).comp (leadingCycleMap K r p q n hn hr)
theorem leadingClassMap_zero_of_next (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (x : Filtered.cycles (filtered K) r p n) (hx : x.val ∈ filtration K (p + 1) n) : leadingClassMap K r p q n hn hr x = 0 := by
  have hz : leadingCycleMap K r p q n hn hr x = 0 := by
    apply Subtype.ext
    exact projection_kills_next K p q n hx
  change verticalClassMap K p q (leadingCycleMap K r p q n hn hr x) = 0
  rw [hz, map_zero]
theorem pure_vertical_cycle_mem (p q n : ℤ) (hn : p + q = n) (z : LinearMap.ker (vertical K p q)) : (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) 1 p n := by
  refine ⟨inclusion_mem_filtration K p p q n hn (le_refl p) z.val, ?_⟩
  have hd := congrArg (fun f => f.hom z.val) (inclusion_d K p q n (n + 1) hn)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hd
  change ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) ∈
    filtration K (p + 1) (n + 1)
  rw [hd]
  have hz := z.property
  change ((K.X p).d q (q + 1)).hom z.val = 0 at hz
  rw [hz, map_zero, smul_zero, add_zero]
  exact inclusionOrZero_mem_filtration K (p + 1) (p + 1) q (n + 1) (le_refl _) _
theorem pure_biclosed_mem (r p q n : ℤ) (hn : p + q = n) (z : LinearMap.ker (vertical K p q)) (hz : horizontal K p q z.val = 0) : (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) r p n := by
  refine ⟨inclusion_mem_filtration K p p q n hn (le_refl p) z.val, ?_⟩
  change ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) ∈
    filtration K (p + r) (n + 1)
  subst n
  dsimp only [inclusion]
  rw [total_closed_of_biclosed K p q z.val hz z.property]
  exact (filtration K (p + r) (p + q + 1)).zero_mem
theorem leadingCycleMap_pure (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (z : LinearMap.ker (vertical K p q)) (hz : (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) r p n) : leadingCycleMap K r p q n hn hr ⟨_, hz⟩ = z := by
  apply Subtype.ext
  exact congrArg (fun f => f.hom z.val) (inclusion_projection_eq K p q n hn)
theorem projection_d_pure (p q n : ℤ) (hn : p + q = n) (b : (K.X p).X (q - 1)) : (projection K p q n).hom (((total K).d (n - 1) n).hom ((inclusion K p (q - 1) (n - 1) (by lia -abstractProof)).hom b)) = p.negOnePow • incomingVertical K p q b := by
  let u := (inclusion K p (q - 1) (n - 1) (by lia -abstractProof)).hom b
  have hu : u ∈ filtration K p (n - 1) :=
    inclusion_mem_filtration K p p (q - 1) (n - 1) (by lia -abstractProof) (le_refl p) b
  have hlo : (projection K (p - 1) q (n - 1)).hom u = 0 := by
    apply projection_kills_next K (p - 1) q (n - 1)
    rw [show p - 1 + 1 = p by lia -abstractProof]
    exact hu
  have hp : (projection K p (q - 1) (n - 1)).hom u = b :=
    congrArg (fun f => f.hom b) (inclusion_projection_eq K p (q - 1) (n - 1) (by lia -abstractProof))
  have hd := d_projection_apply K p q (n - 1) (by lia -abstractProof) u
  rw [show n - 1 + 1 = n by lia -abstractProof, hlo, hp, map_zero, zero_add] at hd
  exact hd
theorem leading_class_zero_mem_denominator (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (x : Filtered.cycles (filtered K) r p n) (hx : leadingClassMap K r p q n hn hr x = 0) : x.val ∈ Filtered.denominator (filtered K) r p n := by
  obtain ⟨b, hb⟩ := (verticalClassMap_eq_zero_iff K p q
    (leadingCycleMap K r p q n hn hr x)).mp hx
  change incomingVertical K p q b = (projection K p q n).hom x.val at hb
  let u := (inclusion K p (q - 1) (n - 1) (by lia -abstractProof)).hom (p.negOnePow • b)
  let du := ((total K).d (n - 1) n).hom u
  have hu : u ∈ filtration K p (n - 1) :=
    inclusion_mem_filtration K p p (q - 1) (n - 1) (by lia -abstractProof) (le_refl _) _
  have hdu : du ∈ filtration K p n := differential_preserves_filtration K p (n - 1) n hu
  have hproj : (projection K p q n).hom du = (projection K p q n).hom x.val := by
    have hd := projection_d_pure K p q n hn (p.negOnePow • b)
    change (projection K p q n).hom du = _ at hd
    rw [hd]
    simpa [Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self] using hb
  have hddu : ((total K).d n (n + 1)).hom du = 0 :=
    congrArg (fun f => f.hom u) ((total K).d_comp_d (n - 1) n (n + 1))
  let y := x.val - du
  have hy : y ∈ filtration K (p + 1) n := by
    apply mem_next_of_projection_zero K p q n hn
    · exact (filtration K p n).sub_mem x.property.1 hdu
    · change (projection K p q n).hom (x.val - du) = 0
      rw [map_sub, hproj, sub_self]
  have hyc : y ∈ Filtered.cycles (filtered K) (r - 1) (p + 1) n := by
    refine ⟨hy, ?_⟩
    change ((total K).d n (n + 1)).hom (x.val - du) ∈
      filtration K (p + 1 + (r - 1)) (n + 1)
    rw [map_sub, hddu, sub_zero, show p + 1 + (r - 1) = p + r by lia -abstractProof]
    exact x.property.2
  have hdb : du ∈ Filtered.boundaries (filtered K) (r - 1) p n :=
    ⟨hdu, u, filtration_antitone K (n - 1) (show p - (r - 1) ≤ p by lia -abstractProof) hu, rfl⟩
  exact Submodule.mem_sup.mpr ⟨y, hyc, du, hdb, sub_add_cancel x.val du⟩
theorem boundary_leading_exact_of_primitive_mem (p q n : ℤ) (hn : p + q = n) (u : (total K).X (n - 1)) (hu : u ∈ filtration K p (n - 1)) : ∃ b : (K.X p).X (q - 1), incomingVertical K p q b = (projection K p q n).hom (((total K).d (n - 1)
    n).hom u) := by
  have hlo : (projection K (p - 1) q (n - 1)).hom u = 0 := by
    apply projection_kills_next K (p - 1) q (n - 1)
    rw [show p - 1 + 1 = p by lia -abstractProof]
    exact hu
  have hd := d_projection_apply K p q (n - 1) (by lia -abstractProof) u
  rw [show n - 1 + 1 = n by lia -abstractProof, hlo, map_zero, zero_add] at hd
  refine ⟨p.negOnePow • (projection K p (q - 1) (n - 1)).hom u, ?_⟩
  simpa using hd.symm
theorem boundary_leading_exact (p q n : ℤ) (hn : p + q = n) (hdd : ImageKernel K (p - 1) q) (u : (total K).X (n - 1)) (hu : ((total K).d (n - 1) n).hom u ∈ filtration K p n) : ∃ b : (K.X p).X (q - 1), incomingVertical K p q b = (projection
    K p q n).hom (((total K).d (n - 1) n).hom u) := by
  let a := (projection K (p - 1) q (n - 1)).hom u
  let b := (projection K p (q - 1) (n - 1)).hom u
  let c := (projection K (p - 1 - 1) (q + 1) (n - 1)).hom u
  have hd := d_projection_apply K p q (n - 1) (by lia -abstractProof) u
  rw [show n - 1 + 1 = n by lia -abstractProof] at hd
  change (projection K p q n).hom (((total K).d (n - 1) n).hom u) =
    ((K.d (p - 1) p).f q).hom a + p.negOnePow • incomingVertical K p q b at hd
  have hlo : (projection K (p - 1) (q + 1) n).hom
      (((total K).d (n - 1) n).hom u) = 0 := by
    apply projection_kills_next K (p - 1) (q + 1) n
    rw [show p - 1 + 1 = p by lia -abstractProof]
    exact hu
  have hdlo := d_projection_apply K (p - 1) (q + 1) (n - 1) (by lia -abstractProof) u
  rw [show n - 1 + 1 = n by lia -abstractProof, show q + 1 - 1 = q by lia -abstractProof, hlo] at hdlo
  change 0 = ((K.d (p - 1 - 1) (p - 1)).f (q + 1)).hom c +
    (p - 1).negOnePow • vertical K (p - 1) q a at hdlo
  have hhzero : ((K.d (p - 1) p).f (q + 1)).hom
      (((K.d (p - 1 - 1) (p - 1)).f (q + 1)).hom c) = 0 :=
    congrArg (fun f => f.hom c) (K.d_f_comp_d_f (p - 1 - 1) (p - 1) p (q + 1))
  have hcomm : vertical K p q (((K.d (p - 1) p).f q).hom a) =
      ((K.d (p - 1) p).f (q + 1)).hom (vertical K (p - 1) q a) :=
    congrArg (fun f => f.hom a) (K.d_comm (p - 1) p q (q + 1))
  have hv : vertical K p q (((K.d (p - 1) p).f q).hom a) = 0 := by
    have he := congrArg (fun t => ((K.d (p - 1) p).f (q + 1)).hom t) hdlo
    simp only [Units.smul_def, map_zero, map_add, map_zsmul] at he
    rw [hhzero, zero_add, ← hcomm] at he
    have hs := congrArg (fun t => ((p - 1).negOnePow : ℤ) • t) he.symm
    simpa [smul_smul, ← Units.val_mul, Int.units_mul_self] using hs
  dsimp only [ImageKernel, horizontal] at hdd
  rw [show p - 1 + 1 = p by lia -abstractProof] at hdd
  have hm : ((K.d (p - 1) p).f q).hom a ∈
      LinearMap.range ((K.d (p - 1) p).f q).hom ⊓ LinearMap.ker (vertical K p q) :=
    ⟨⟨a, rfl⟩, hv⟩
  rw [hdd] at hm
  obtain ⟨w, hw⟩ := hm
  have hc : incomingVertical K p q (((K.d (p - 1) p).f (q - 1)).hom w) =
      ((K.d (p - 1) p).f q).hom (incomingVertical K (p - 1) q w) :=
    congrArg (fun f => f.hom w) (K.d_comm (p - 1) p (q - 1) q)
  refine ⟨((K.d (p - 1) p).f (q - 1)).hom w + p.negOnePow • b, ?_⟩
  change ((K.d (p - 1) p).f q).hom (incomingVertical K (p - 1) q w) =
    ((K.d (p - 1) p).f q).hom a at hw
  rw [map_add, hc, hw, hd]
  simp
theorem leading_zero_of_boundary (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hdd : ImageKernel K (p - 1) q) (x : Filtered.cycles (filtered K) r p n) (hx : x.val ∈ Filtered.boundaries (filtered K) (r - 1) p n) : leadingClassMap K r p q n hn
    hr x = 0 := by
  obtain ⟨u, _, hu⟩ := hx.2
  have huf : ((total K).d (n - 1) n).hom u ∈ filtration K p n := by
    rw [hu]
    exact hx.1
  obtain ⟨b, hb⟩ := boundary_leading_exact K p q n hn hdd u huf
  change verticalClassMap K p q (leadingCycleMap K r p q n hn hr x) = 0
  apply (verticalClassMap_eq_zero_iff K p q _).mpr
  refine ⟨b, ?_⟩
  change incomingVertical K p q b = (projection K p q n).hom x.val
  rw [← hu]
  exact hb
theorem leading_zero_of_boundary_e1 (p q n : ℤ) (hn : p + q = n) (x : Filtered.cycles (filtered K) 1 p n) (hx : x.val ∈ Filtered.boundaries (filtered K) (1 - 1) p n) : leadingClassMap K 1 p q n hn (le_refl 1) x = 0 := by
  obtain ⟨u, hup, hu⟩ := hx.2
  have hup' : u ∈ filtration K p (n - 1) := by
    simp only [sub_self, sub_zero] at hup
    exact hup
  obtain ⟨b, hb⟩ := boundary_leading_exact_of_primitive_mem K p q n hn u hup'
  change verticalClassMap K p q (leadingCycleMap K 1 p q n hn (le_refl 1) x) = 0
  apply (verticalClassMap_eq_zero_iff K p q _).mpr
  refine ⟨b, ?_⟩
  change incomingVertical K p q b = (projection K p q n).hom x.val
  rw [← hu]
  exact hb
theorem leading_kills_denominator_of_boundary (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hbzero : ∀ x : Filtered.cycles (filtered K) r p n, x.val ∈ Filtered.boundaries (filtered K) (r - 1) p n → leadingClassMap K r p q n hn hr x = 0) :
    (Filtered.denominator (filtered K) r p n).comap (Filtered.cycles (filtered K) r p n).subtype ≤ LinearMap.ker (leadingClassMap K r p q n hn hr) := by
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  have hac : a ∈ Filtered.cycles (filtered K) r p n :=
    Filtered.denominator_le_cycles (filtered K) r p n
      ((show Filtered.cycles (filtered K) (r - 1) (p + 1) n ≤
        Filtered.denominator (filtered K) r p n from le_sup_left) ha)
  have hbc : b ∈ Filtered.cycles (filtered K) r p n :=
    Filtered.denominator_le_cycles (filtered K) r p n
      ((show Filtered.boundaries (filtered K) (r - 1) p n ≤
        Filtered.denominator (filtered K) r p n from le_sup_right) hb)
  have hx' : (⟨a, hac⟩ : Filtered.cycles (filtered K) r p n) + ⟨b, hbc⟩ = x :=
    Subtype.ext hab
  change leadingClassMap K r p q n hn hr x = 0
  rw [← hx', map_add, leadingClassMap_zero_of_next K r p q n hn hr ⟨a, hac⟩ ha.1,
    hbzero ⟨b, hbc⟩ hb, add_zero]
noncomputable def pageClassMap (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hdd : ImageKernel K (p - 1) q) : Filtered.Page (filtered K) r p n →ₗ[k] (K.X p).homology q :=
  ((Filtered.denominator (filtered K) r p n).comap
    (Filtered.cycles (filtered K) r p n).subtype).liftQ
      (leadingClassMap K r p q n hn hr)
      (leading_kills_denominator_of_boundary K r p q n hn hr
        (leading_zero_of_boundary K r p q n hn hr hdd))
noncomputable def firstPageClassMap (p q n : ℤ) (hn : p + q = n) : Filtered.Page (filtered K) 1 p n →ₗ[k] (K.X p).homology q :=
  ((Filtered.denominator (filtered K) 1 p n).comap
    (Filtered.cycles (filtered K) 1 p n).subtype).liftQ
      (leadingClassMap K 1 p q n hn (le_refl 1))
      (leading_kills_denominator_of_boundary K 1 p q n hn (le_refl 1)
        (leading_zero_of_boundary_e1 K p q n hn))
@[simp]
theorem pageClassMap_quotient (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hdd : ImageKernel K (p - 1) q) (x : Filtered.cycles (filtered K) r p n) : pageClassMap K r p q n hn hr hdd (Filtered.quotient (filtered K) r p n x) = leadingClassMap
    K r p q n hn hr x := rfl
@[simp]
theorem firstPageClassMap_quotient (p q n : ℤ) (hn : p + q = n) (x : Filtered.cycles (filtered K) 1 p n) : firstPageClassMap K p q n hn (Filtered.quotient (filtered K) 1 p n x) = leadingClassMap K 1 p q n hn (le_refl 1) x := rfl
theorem pageClassMap_injective (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hdd : ImageKernel K (p - 1) q) : Function.Injective (pageClassMap K r p q n hn hr hdd) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  obtain ⟨x, rfl⟩ := Filtered.quotient_surjective (filtered K) r p n z
  change pageClassMap K r p q n hn hr hdd (Filtered.quotient (filtered K) r p n x) = 0 at hz
  rw [pageClassMap_quotient] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (leading_class_zero_mem_denominator K r p q n hn hr x hz)
theorem firstPageClassMap_injective (p q n : ℤ) (hn : p + q = n) : Function.Injective (firstPageClassMap K p q n hn) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  obtain ⟨x, rfl⟩ := Filtered.quotient_surjective (filtered K) 1 p n z
  change firstPageClassMap K p q n hn (Filtered.quotient (filtered K) 1 p n x) = 0 at hz
  rw [firstPageClassMap_quotient] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (leading_class_zero_mem_denominator K 1 p q n hn (le_refl 1) x hz)
theorem firstPageClassMap_surjective (p q n : ℤ) (hn : p + q = n) : Function.Surjective (firstPageClassMap K p q n hn) := by
  intro c
  obtain ⟨z, hz⟩ := verticalClassMap_surjective K p q c
  let x : Filtered.cycles (filtered K) 1 p n :=
    ⟨(inclusion K p q n hn).hom z.val, pure_vertical_cycle_mem K p q n hn z⟩
  refine ⟨Filtered.quotient (filtered K) 1 p n x, ?_⟩
  rw [firstPageClassMap_quotient]
  change verticalClassMap K p q (leadingCycleMap K 1 p q n hn (le_refl 1) x) = c
  rw [leadingCycleMap_pure]
  exact hz
theorem pageClassMap_surjective (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hddIn : ImageKernel K (p - 1) q) (hddOut : ImageKernel K p q) : Function.Surjective (pageClassMap K r p q n hn hr hddIn) := by
  intro c
  obtain ⟨z, hz, hc⟩ := exists_closed_representative K p q hddOut c
  let x : Filtered.cycles (filtered K) r p n :=
    ⟨(inclusion K p q n hn).hom z.val, pure_biclosed_mem K r p q n hn z hz⟩
  refine ⟨Filtered.quotient (filtered K) r p n x, ?_⟩
  rw [pageClassMap_quotient]
  change verticalClassMap K p q (leadingCycleMap K r p q n hn hr x) = c
  rw [leadingCycleMap_pure, verticalClassMap_apply]
  exact hc
noncomputable def firstPageIso (p q n : ℤ) (hn : p + q = n) : ModuleCat.of k (Filtered.Page (filtered K) 1 p n) ≅ (K.X p).homology q :=
  (LinearEquiv.ofBijective (firstPageClassMap K p q n hn)
    ⟨firstPageClassMap_injective K p q n hn, firstPageClassMap_surjective K p q n hn⟩).toModuleIso
noncomputable def pageIso (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hddIn : ImageKernel K (p - 1) q) (hddOut : ImageKernel K p q) : ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅ (K.X p).homology q :=
  (LinearEquiv.ofBijective (pageClassMap K r p q n hn hr hddIn)
    ⟨pageClassMap_injective K r p q n hn hr hddIn,
      pageClassMap_surjective K r p q n hn hr hddIn hddOut⟩).toModuleIso
theorem boundary_leading_exact_next (p q n : ℤ) (hn : p + q = n + 1) (hdd : ImageKernel K (p - 1) q) (u : (total K).X n) (hu : ((total K).d n (n + 1)).hom u ∈ filtration K p (n + 1)) : ∃ b : (K.X p).X (q - 1), incomingVertical K p q b =
    (projection K p q (n + 1)).hom (((total K).d n (n + 1)).hom u) := by
  have h := boundary_leading_exact K p q (n + 1) hn hdd
  rw [show n + 1 - 1 = n by lia -abstractProof] at h
  exact h u hu
theorem all_differentials_zero (hdd : ∀ p q : ℤ, ImageKernel K p q) (r p n : ℤ) (hr : 1 ≤ r) : Filtered.differential (filtered K) r p n = 0 := by
  apply LinearMap.ext
  intro c
  apply pageClassMap_injective K r (p + r) (n + 1 - (p + r)) (n + 1) (by lia -abstractProof) hr
    (hdd (p + r - 1) (n + 1 - (p + r)))
  simp only [LinearMap.zero_apply, map_zero]
  obtain ⟨x, rfl⟩ := Filtered.quotient_surjective (filtered K) r p n c
  rw [Filtered.differential_quotient, pageClassMap_quotient]
  change verticalClassMap K (p + r) (n + 1 - (p + r))
    (leadingCycleMap K r (p + r) (n + 1 - (p + r)) (n + 1) (by lia -abstractProof) hr
      (Filtered.differentialOnCycles (filtered K) r p n x)) = 0
  apply (verticalClassMap_eq_zero_iff K (p + r) (n + 1 - (p + r)) _).mpr
  obtain ⟨b, hb⟩ := boundary_leading_exact_next K (p + r) (n + 1 - (p + r)) n (by lia -abstractProof)
    (hdd (p + r - 1) (n + 1 - (p + r))) x.val x.property.2
  exact ⟨b, hb⟩
noncomputable abbrev pageObject (r : ℤ) (pq : ℤ × ℤ) : ModuleCat k :=
  ModuleCat.of k (Filtered.Page (filtered K) r pq.1 (pq.1 + pq.2))
noncomputable def differentialTo (r : ℤ) (pq pq' : ℤ × ℤ) (h : pq + (r, 1 - r) = pq') : pageObject K r pq ⟶ pageObject K r pq' :=
  ModuleCat.ofHom (Filtered.differential (filtered K) r pq.1 (pq.1 + pq.2)) ≫
    eqToHom (by
      have hp : pq.1 + r = pq'.1 := congrArg Prod.fst h
      have hq : pq.2 + (1 - r) = pq'.2 := congrArg Prod.snd h
      have hn : pq.1 + pq.2 + 1 = pq'.1 + pq'.2 := by lia -abstractProof
      change ModuleCat.of k (Filtered.Page (filtered K) r (pq.1 + r) (pq.1 + pq.2 + 1)) = _
      rw [hp, hn])
noncomputable def pageDifferential (r : ℤ) (pq pq' : ℤ × ℤ) : pageObject K r pq ⟶ pageObject K r pq' :=
  if h : pq + (r, 1 - r) = pq' then differentialTo K r pq pq' h else 0
theorem pageDifferential_zero (hdd : ∀ p q : ℤ, ImageKernel K p q) (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) : pageDifferential K r pq pq' = 0 := by
  unfold pageDifferential
  split_ifs
  · dsimp only [differentialTo]
    rw [all_differentials_zero K hdd r pq.1 (pq.1 + pq.2) hr]
    exact zero_comp
  · rfl
noncomputable def pageComplex (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r : ℤ) (hr : 1 ≤ r) :
    HomologicalComplex (ModuleCat k) (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) where
  X := pageObject K r
  d := pageDifferential K r
  shape _ _ h := dite_eq_right h
  d_comp_d' pq pq' pq'' _ _ := by
    rw [pageDifferential_zero K hdd r hr pq pq', zero_comp]
noncomputable def zeroPageHomologyIso (hdd : ∀ p q : ℤ, ImageKernel K p q) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) : (pageComplex K hdd r hr).homology pq ≅ pageObject K r pq :=
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
theorem zeroPageHomologyIso_π (hdd : ∀ p q : ℤ, ImageKernel K p q) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) : (pageComplex K hdd r hr).homologyπ pq ≫ (zeroPageHomologyIso K hdd r hr pq).hom = (pageComplex K hdd r hr).iCycles pq := by
  let h := ShortComplex.LeftHomologyData.ofZeros ((pageComplex K hdd r hr).sc pq)
    (pageDifferential_zero K hdd r hr _ _) (pageDifferential_zero K hdd r hr _ _)
  exact h.homologyπ_comp_homologyIso_hom.trans h.cyclesIso_hom_comp_i
theorem page_comparison_common_representative (hdd : ∀ p q : ℤ, ImageKernel K p q) (r s p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hs : 1 ≤ s) (x : (total K).X n) (hx : x ∈ Filtered.cycles (filtered K) r p n) (hx' : x ∈ Filtered.cycles
    (filtered K) s p n) : (pageIso K s p q n hn hs (hdd (p - 1) q) (hdd p q)).inv ((pageIso K r p q n hn hr (hdd (p - 1) q) (hdd p q)).hom (Filtered.quotient (filtered K) r p n ⟨x, hx⟩)) = Filtered.quotient (filtered K) s p n ⟨x, hx'⟩ := by
  apply (ModuleCat.mono_iff_injective
    (pageIso K s p q n hn hs (hdd (p - 1) q) (hdd p q)).hom).mp inferInstance
  rw [Iso.inv_hom_id_apply]
  change pageClassMap K r p q n hn hr (hdd (p - 1) q)
      (Filtered.quotient (filtered K) r p n ⟨x, hx⟩) =
    pageClassMap K s p q n hn hs (hdd (p - 1) q)
      (Filtered.quotient (filtered K) s p n ⟨x, hx'⟩)
  rw [pageClassMap_quotient, pageClassMap_quotient]
  apply congrArg (verticalClassMap K p q)
  apply Subtype.ext
  rfl
theorem associatedSequence_transition (hdd : ∀ p q : ℤ, ImageKernel K p q) (r s : ℤ) (hrs : r + 1 = s) (hr : 1 ≤ r) (p q : ℤ) (x : (total K).X (p + q)) (hx : x ∈ Filtered.cycles (filtered K) r p (p + q)) (hx' : x ∈ Filtered.cycles (filtered
    K) s p (p + q)) : ((associatedSequence K hdd).iso r s (p, q) hrs hr).hom ((zeroPageHomologyIso K hdd r hr (p, q)).inv (Filtered.quotient (filtered K) r p (p + q) ⟨x, hx⟩)) = Filtered.quotient (filtered K) s p (p + q) ⟨x, hx'⟩ := by
  change (pageIso K s p q (p + q) rfl (by lia -abstractProof) (hdd (p - 1) q) (hdd p q)).inv
    ((pageIso K r p q (p + q) rfl hr (hdd (p - 1) q) (hdd p q)).hom
      ((zeroPageHomologyIso K hdd r hr (p, q)).hom
        ((zeroPageHomologyIso K hdd r hr (p, q)).inv
          (Filtered.quotient (filtered K) r p (p + q) ⟨x, hx⟩)))) = _
  rw [Iso.inv_hom_id_apply]
  exact page_comparison_common_representative K hdd r s p q (p + q) rfl hr (by lia -abstractProof) x hx hx'
end AlgebraicHodgePilot.Column
namespace AlgebraicHodgePilot.Filtered
variable {k : Type} [Field k] {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)
def closedCycles (p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ LinearMap.ker (C.d n (n + 1)).hom
def closedBoundaries (p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ LinearMap.range (C.d (n - 1) n).hom
def closedDenominator (p n : ℤ) : Submodule k (C.X n) :=
  closedCycles F (p + 1) n ⊔ closedBoundaries F p n
theorem closedCycles_le_cycles (r p n : ℤ) : closedCycles F p n ≤ cycles F r p n := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  change (C.d n (n + 1)).hom x ∈ F.F (p + r) (n + 1)
  rw [hx.2]
  exact (F.F (p + r) (n + 1)).zero_mem
def closedToCycles (r p n : ℤ) : closedCycles F p n →ₗ[k] cycles F r p n :=
  Submodule.inclusion (closedCycles_le_cycles F r p n)
theorem closedDenominator_le_closedCycles (p n : ℤ) : closedDenominator F p n ≤ closedCycles F p n := by
  apply sup_le
  · intro x hx
    exact ⟨F.antitone n (show p ≤ p + 1 by lia -abstractProof) hx.1, hx.2⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨u, hu⟩ := hx.2
    change (C.d n (n + 1)).hom x = 0
    rw [← hu]
    exact congrArg (fun f => f.hom u) (C.d_comp_d (n - 1) n (n + 1))
abbrev InfinityPage (p n : ℤ) :=
  closedCycles F p n ⧸ (closedDenominator F p n).comap (closedCycles F p n).subtype
def infinityQuotient (p n : ℤ) : closedCycles F p n →ₗ[k] InfinityPage F p n :=
  ((closedDenominator F p n).comap (closedCycles F p n).subtype).mkQ
theorem infinityQuotient_surjective (p n : ℤ) : Function.Surjective (infinityQuotient F p n) := Submodule.mkQ_surjective _
end AlgebraicHodgePilot.Filtered
namespace AlgebraicHodgePilot.Column
variable {k : Type} [Field k] (K : Bicomplex k)
def HorizontalSupport (L U : ℤ) : Prop :=
  ∀ p q, p < L ∨ U < p → Subsingleton ((K.X p).X q)
def RectangularSupport (L U B T : ℤ) : Prop :=
  ∀ p q, p < L ∨ U < p ∨ q < B ∨ T < q → Subsingleton ((K.X p).X q)
theorem rectangularSupport_horizontal (L U B T : ℤ) (hs : RectangularSupport K L U B T) : HorizontalSupport K L U := by
  intro p q hp
  exact hs p q (hp.elim Or.inl (fun h => Or.inr (Or.inl h)))
theorem filtration_eq_bot (L U : ℤ) (hs : HorizontalSupport K L U) (p n : ℤ) (hp : U < p) : filtration K p n = ⊥ := by
  apply le_antisymm ?_ bot_le
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun ha => ?_
  rintro _ ⟨x, rfl⟩
  have hx : x = 0 := @Subsingleton.elim _ (hs a b (Or.inr (by lia -abstractProof))) x 0
  simp [hx]
theorem filtration_eq_top (L U : ℤ) (hs : HorizontalSupport K L U) (p n : ℤ) (hp : p ≤ L) : filtration K p n = ⊤ := by
  let f : (total K).X n ⟶ ModuleCat.of k ((total K).X n ⧸ filtration K p n) :=
    ModuleCat.ofHom (filtration K p n).mkQ
  have hf : f = 0 := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    by_cases ha : p ≤ a
    · exact (Submodule.Quotient.mk_eq_zero _).mpr
        (inclusion_mem_filtration K p a b n hab ha x)
    · have hx : x = 0 := @Subsingleton.elim _ (hs a b (Or.inl (by lia -abstractProof))) x 0
      simp [hx]
  apply top_unique
  intro x _
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact congrArg (fun g => g.hom x) hf
theorem cycles_stable (L U : ℤ) (hs : HorizontalSupport K L U) (r p n : ℤ) (hr : U < p + r) : Filtered.cycles (filtered K) r p n = Filtered.closedCycles (filtered K) p n := by
  unfold Filtered.cycles Filtered.closedCycles
  change filtration K p n ⊓ (filtration K (p + r) (n + 1)).comap _ = _
  rw [filtration_eq_bot K L U hs (p + r) (n + 1) hr]
  rfl
theorem boundaries_stable (L U : ℤ) (hs : HorizontalSupport K L U) (r p n : ℤ) (hr : p - r ≤ L) : Filtered.boundaries (filtered K) r p n = Filtered.closedBoundaries (filtered K) p n := by
  unfold Filtered.boundaries Filtered.closedBoundaries
  change filtration K p n ⊓ (filtration K (p - r) (n - 1)).map _ = _
  rw [filtration_eq_top K L U hs (p - r) (n - 1) hr, Submodule.map_top]
  rfl
theorem denominator_stable (L U : ℤ) (hs : HorizontalSupport K L U) (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) : Filtered.denominator (filtered K) r p n = Filtered.closedDenominator (filtered K) p n := by
  unfold Filtered.denominator Filtered.closedDenominator
  rw [cycles_stable K L U hs (r - 1) (p + 1) n (by lia -abstractProof),
    boundaries_stable K L U hs (r - 1) p n (by lia -abstractProof)]
noncomputable def stablePageIso (L U : ℤ) (hs : HorizontalSupport K L U) (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) : ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅ ModuleCat.of k (Filtered.InfinityPage (filtered K) p n) :=
  eqToIso (by
    unfold Filtered.Page Filtered.InfinityPage
    rw [cycles_stable K L U hs r p n hu, denominator_stable K L U hs r p n hu hl])
theorem eventually_stable (L U : ℤ) (hs : HorizontalSupport K L U) (p n : ℤ) : ∃ R : ℤ, 1 ≤ R ∧ ∀ r : ℤ, R ≤ r → Filtered.cycles (filtered K) r p n = Filtered.closedCycles (filtered K) p n ∧ Filtered.denominator (filtered K) r p n =
    Filtered.closedDenominator (filtered K) p n := by
  refine ⟨max 1 (max (U - p + 1) (p - L + 1)), le_max_left _ _, ?_⟩
  intro r hr
  have hu : U < p + r := by omega
  have hl : p - r + 1 ≤ L := by omega
  exact ⟨cycles_stable K L U hs r p n hu, denominator_stable K L U hs r p n hu hl⟩
end AlgebraicHodgePilot.Column
namespace AlgebraicHodgePilot.Filtered
variable {k : Type} [Field k] (C : CochainComplex (ModuleCat k) ℤ)
abbrev cohomologySC (n : ℤ) := C.sc' (n - 1) n (n + 1)
noncomputable def cohomologyIso (n : ℤ) : C.homology n ≅ (cohomologySC C n).homology :=
  C.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
noncomputable def cohomologyClassMap (n : ℤ) : LinearMap.ker (C.d n (n + 1)).hom →ₗ[k] C.homology n :=
  (cohomologyIso C n).inv.hom.comp
    ((cohomologySC C n).moduleCatHomologyIso.inv.hom.comp
      (cohomologySC C n).moduleCatLeftHomologyData.π.hom)
theorem cohomologyClassMap_surjective (n : ℤ) : Function.Surjective (cohomologyClassMap C n) := by
  intro c
  let S := cohomologySC C n
  let c' := S.moduleCatHomologyIso.hom ((cohomologyIso C n).hom c)
  obtain ⟨x, hx⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective c'
  let z : LinearMap.ker (C.d n (n + 1)).hom := x
  change S.moduleCatLeftHomologyData.π z = c' at hx
  refine ⟨z, ?_⟩
  change (cohomologyIso C n).inv
    (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = c
  rw [hx]
  simp [c']
theorem cohomologyClassMap_eq_zero_iff (n : ℤ) (z : LinearMap.ker (C.d n (n + 1)).hom) : cohomologyClassMap C n z = 0 ↔ ∃ b : C.X (n - 1), (C.d (n - 1) n).hom b = z.val := by
  let S := cohomologySC C n
  constructor
  · intro h
    have hh := congrArg
      (fun c => S.moduleCatHomologyIso.hom ((cohomologyIso C n).hom c)) h
    have hq : S.moduleCatLeftHomologyData.π z = 0 := by
      simp [cohomologyClassMap, S] at hh
      exact hh
    have hm : z ∈ LinearMap.range S.moduleCatToCycles :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hz : S.moduleCatToCycles b = z := Subtype.ext hb
    have hq : S.moduleCatLeftHomologyData.π z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hz⟩
    change (cohomologyIso C n).inv
      (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = 0
    rw [hq]
    simp
end AlgebraicHodgePilot.Filtered
namespace AlgebraicHodgePilot.Filtered
variable {k : Type} [Field k] {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)
def closedCycleToCycle (p n : ℤ) : closedCycles F p n →ₗ[k] LinearMap.ker (C.d n (n + 1)).hom :=
  (closedCycles F p n).subtype.codRestrict _ fun x => x.property.2
noncomputable def closedClassMap (p n : ℤ) : closedCycles F p n →ₗ[k] C.homology n :=
  (cohomologyClassMap C n).comp (closedCycleToCycle F p n)
noncomputable def cohomologyFiltration (p n : ℤ) : Submodule k (C.homology n) :=
  LinearMap.range (closedClassMap F p n)
noncomputable def closedClassToFiltration (p n : ℤ) : closedCycles F p n →ₗ[k] cohomologyFiltration F p n :=
  (closedClassMap F p n).codRestrict _ fun x => ⟨x, rfl⟩
abbrev GradedCohomology (p n : ℤ) :=
  cohomologyFiltration F p n ⧸
    (cohomologyFiltration F (p + 1) n).comap (cohomologyFiltration F p n).subtype
noncomputable def closedToGraded (p n : ℤ) : closedCycles F p n →ₗ[k] GradedCohomology F p n :=
  ((cohomologyFiltration F (p + 1) n).comap
    (cohomologyFiltration F p n).subtype).mkQ.comp (closedClassToFiltration F p n)
theorem closedToGraded_zero_iff (p n : ℤ) (x : closedCycles F p n) : closedToGraded F p n x = 0 ↔ x.val ∈ closedDenominator F p n := by
  have hzero : closedToGraded F p n x = 0 ↔
      closedClassMap F p n x ∈ cohomologyFiltration F (p + 1) n :=
    Submodule.Quotient.mk_eq_zero _
  rw [hzero]
  constructor
  · rintro ⟨y, hy⟩
    let xp := closedCycleToCycle F p n x
    let yp := closedCycleToCycle F (p + 1) n y
    have hclass : cohomologyClassMap C n (xp - yp) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hy.symm
    obtain ⟨b, hb⟩ := (cohomologyClassMap_eq_zero_iff C n (xp - yp)).mp hclass
    have hdiff : x.val - y.val ∈ closedBoundaries F p n := by
      refine ⟨(F.F p n).sub_mem x.property.1
        (F.antitone n (show p ≤ p + 1 by lia -abstractProof) y.property.1), b, ?_⟩
      exact hb
    exact Submodule.mem_sup.mpr ⟨y.val, y.property, x.val - y.val, hdiff,
      add_sub_cancel _ _⟩
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have hbc : b ∈ closedCycles F p n :=
      closedDenominator_le_closedCycles F p n
        ((show closedBoundaries F p n ≤ closedDenominator F p n from le_sup_right) hb)
    have hbb : cohomologyClassMap C n (closedCycleToCycle F p n ⟨b, hbc⟩) = 0 :=
      (cohomologyClassMap_eq_zero_iff C n _).mpr hb.2
    have hac : a ∈ closedCycles F p n :=
      ⟨F.antitone n (show p ≤ p + 1 by lia -abstractProof) ha.1, ha.2⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    have he : (⟨a, hac⟩ : closedCycles F p n) + ⟨b, hbc⟩ = x := Subtype.ext hab
    rw [← he, map_add]
    change closedClassMap F (p + 1) n ⟨a, ha⟩ =
      closedClassMap F p n ⟨a, hac⟩ + cohomologyClassMap C n (closedCycleToCycle F p n ⟨b, hbc⟩)
    rw [hbb, add_zero]
    rfl
noncomputable def infinityToGraded (p n : ℤ) : InfinityPage F p n →ₗ[k] GradedCohomology F p n :=
  ((closedDenominator F p n).comap (closedCycles F p n).subtype).liftQ
    (closedToGraded F p n) fun x hx => (closedToGraded_zero_iff F p n x).mpr hx
@[simp]
theorem infinityToGraded_quotient (p n : ℤ) (x : closedCycles F p n) : infinityToGraded F p n (infinityQuotient F p n x) = closedToGraded F p n x := rfl
theorem infinityToGraded_injective (p n : ℤ) : Function.Injective (infinityToGraded F p n) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  obtain ⟨x, rfl⟩ := infinityQuotient_surjective F p n z
  change infinityToGraded F p n (infinityQuotient F p n x) = 0 at hz
  rw [infinityToGraded_quotient] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((closedToGraded_zero_iff F p n x).mp hz)
theorem infinityToGraded_surjective (p n : ℤ) : Function.Surjective (infinityToGraded F p n) := by
  intro c
  obtain ⟨h, rfl⟩ := ((cohomologyFiltration F (p + 1) n).comap
    (cohomologyFiltration F p n).subtype).mkQ_surjective c
  obtain ⟨x, hx⟩ := h.property
  refine ⟨infinityQuotient F p n x, ?_⟩
  rw [infinityToGraded_quotient]
  change _ = Submodule.mkQ _ h
  apply congrArg (Submodule.mkQ _)
  apply Subtype.ext
  exact hx
noncomputable def infinityGradedIso (p n : ℤ) : ModuleCat.of k (InfinityPage F p n) ≅ ModuleCat.of k (GradedCohomology F p n) :=
  (LinearEquiv.ofBijective (infinityToGraded F p n)
    ⟨infinityToGraded_injective F p n, infinityToGraded_surjective F p n⟩).toModuleIso
@[simp]
theorem infinityGradedIso_quotient (p n : ℤ) (x : closedCycles F p n) : (infinityGradedIso F p n).hom (infinityQuotient F p n x) = closedToGraded F p n x := rfl
end AlgebraicHodgePilot.Filtered
namespace AlgebraicHodgePilot.Column
variable {k : Type} [Field k] (K : Bicomplex k)
noncomputable def boundedStableGradedIso (L U : ℤ) (hs : HorizontalSupport K L U) (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) : ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅ ModuleCat.of k (Filtered.GradedCohomology (filtered K)
    p n) :=
  stablePageIso K L U hs r p n hu hl ≪≫ Filtered.infinityGradedIso (filtered K) p n
theorem bounded_e1_degeneration (hdd : ∀ p q : ℤ, ImageKernel K p q) (L U B T : ℤ) (hs : RectangularSupport K L U B T) : (∀ r : ℤ, 1 ≤ r → ∀ p n : ℤ, Filtered.differential (filtered K) r p n = 0) ∧ (∀ p n : ℤ, ∃ R : ℤ, 1 ≤ R ∧ ∀ r : ℤ, R ≤
    r → Filtered.cycles (filtered K) r p n = Filtered.closedCycles (filtered K) p n ∧ Filtered.denominator (filtered K) r p n = Filtered.closedDenominator (filtered K) p n) := by
  constructor
  · intro r hr p n
    exact all_differentials_zero K hdd r p n hr
  · intro p n
    exact eventually_stable K L U (rectangularSupport_horizontal K L U B T hs) p n
end AlgebraicHodgePilot.Column
namespace AlgebraicHodgePilot.Filtered
variable {k : Type} [Field k] {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)
theorem cycles_succ_le (r p n : ℤ) : cycles F (r + 1) p n ≤ cycles F r p n := by
  intro x hx
  exact ⟨hx.1, F.antitone (n + 1) (show p + r ≤ p + (r + 1) by lia -abstractProof) hx.2⟩
theorem cohomologyFiltration_eq_top_of_top (p n : ℤ) (hF : F.F p n = ⊤) : cohomologyFiltration F p n = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro c
  obtain ⟨z, hz⟩ := cohomologyClassMap_surjective C n c
  refine ⟨⟨z.val, ?_, z.property⟩, ?_⟩
  · rw [hF]
    trivial
  · exact hz
theorem cohomologyFiltration_eq_bot_of_bot (p n : ℤ) (hF : F.F p n = ⊥) : cohomologyFiltration F p n = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro _ ⟨z, rfl⟩
  have hzval : z.val = 0 := by
    have hz := z.property.1
    rw [hF] at hz
    exact hz
  have hz : z = 0 := Subtype.ext hzval
  change closedClassMap F p n z = 0
  rw [hz, map_zero]
end AlgebraicHodgePilot.Filtered
namespace AlgebraicHodgePilot.Column
variable {k : Type} [Field k] (K : Bicomplex k)
theorem associatedSequence_transition_next (hdd : ∀ p q : ℤ, ImageKernel K p q) (r p q : ℤ) (hr : 1 ≤ r) (x : Filtered.cycles (filtered K) (r + 1) p (p + q)) : ((associatedSequence K hdd).iso r (r + 1) (p, q) rfl hr).hom
    ((zeroPageHomologyIso K hdd r hr (p, q)).inv (Filtered.quotient (filtered K) r p (p + q) ⟨x.val, Filtered.cycles_succ_le (filtered K) r p (p + q) x.property⟩)) = Filtered.quotient (filtered K) (r + 1) p (p + q) x :=
  associatedSequence_transition K hdd r (r + 1) rfl hr p q x.val
    (Filtered.cycles_succ_le (filtered K) r p (p + q) x.property) x.property
theorem associatedSequence_transition_covers (hdd : ∀ p q : ℤ, ImageKernel K p q) (r p q : ℤ) (hr : 1 ≤ r) (c : Filtered.Page (filtered K) (r + 1) p (p + q)) : ∃ x : Filtered.cycles (filtered K) (r + 1) p (p + q), Filtered.quotient
    (filtered K) (r + 1) p (p + q) x = c ∧ ((associatedSequence K hdd).iso r (r + 1) (p, q) rfl hr).hom ((zeroPageHomologyIso K hdd r hr (p, q)).inv (Filtered.quotient (filtered K) r p (p + q) ⟨x.val, Filtered.cycles_succ_le (filtered K) r
    p (p + q) x.property⟩)) = c := by
  obtain ⟨x, hx⟩ := Filtered.quotient_surjective (filtered K) (r + 1) p (p + q) c
  exact ⟨x, hx, (associatedSequence_transition_next K hdd r p q hr x).trans hx⟩
theorem cohomologyFiltration_eq_top (L U : ℤ) (hs : HorizontalSupport K L U) (p n : ℤ) (hp : p ≤ L) : Filtered.cohomologyFiltration (filtered K) p n = ⊤ :=
  Filtered.cohomologyFiltration_eq_top_of_top (filtered K) p n
    (filtration_eq_top K L U hs p n hp)
theorem cohomologyFiltration_eq_bot (L U : ℤ) (hs : HorizontalSupport K L U) (p n : ℤ) (hp : U < p) : Filtered.cohomologyFiltration (filtered K) p n = ⊥ :=
  Filtered.cohomologyFiltration_eq_bot_of_bot (filtered K) p n
    (filtration_eq_bot K L U hs p n hp)
theorem cohomologyFiltration_exhaustive_separated (L U : ℤ) (hs : HorizontalSupport K L U) (n : ℤ) : (⨆ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n) = ⊤ ∧ (⨅ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n) = ⊥ := by
  constructor
  · apply top_unique
    calc
      ⊤ = Filtered.cohomologyFiltration (filtered K) L n :=
        (cohomologyFiltration_eq_top K L U hs L n (le_refl L)).symm
      _ ≤ ⨆ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n :=
        le_iSup (fun p : ℤ => Filtered.cohomologyFiltration (filtered K) p n) L
  · apply bot_unique
    calc
      (⨅ p : ℤ, Filtered.cohomologyFiltration (filtered K) p n) ≤
          Filtered.cohomologyFiltration (filtered K) (U + 1) n :=
        iInf_le (fun p : ℤ => Filtered.cohomologyFiltration (filtered K) p n) (U + 1)
      _ = ⊥ := cohomologyFiltration_eq_bot K L U hs (U + 1) n (by lia -abstractProof)
theorem quotient_cast_class {M : Type} [AddCommGroup M] [Module k M] (A B S T : Submodule k M) (hA : A = B) (hD : S = T) (he : ModuleCat.of k (A ⧸ S.comap A.subtype) = ModuleCat.of k (B ⧸ T.comap B.subtype)) (x : M) (hx : x ∈ A) (hx' : x ∈
    B) : (eqToIso he).hom ((S.comap A.subtype).mkQ ⟨x, hx⟩) = (T.comap B.subtype).mkQ ⟨x, hx'⟩ := by
  subst B T
  have hh : he = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl
theorem stablePageIso_quotient (L U : ℤ) (hs : HorizontalSupport K L U) (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) (x : Filtered.closedCycles (filtered K) p n) : (stablePageIso K L U hs r p n hu hl).hom (Filtered.quotient (filtered
    K) r p n (Filtered.closedToCycles (filtered K) r p n x)) = Filtered.infinityQuotient (filtered K) p n x := by
  exact quotient_cast_class (Filtered.cycles (filtered K) r p n)
    (Filtered.closedCycles (filtered K) p n) (Filtered.denominator (filtered K) r p n)
    (Filtered.closedDenominator (filtered K) p n) (cycles_stable K L U hs r p n hu)
    (denominator_stable K L U hs r p n hu hl) _ x.val
    (Filtered.closedCycles_le_cycles (filtered K) r p n x.property) x.property
theorem boundedStableGradedIso_closed (L U : ℤ) (hs : HorizontalSupport K L U) (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) (x : Filtered.closedCycles (filtered K) p n) : (boundedStableGradedIso K L U hs r p n hu hl).hom
    (Filtered.quotient (filtered K) r p n (Filtered.closedToCycles (filtered K) r p n x)) = Filtered.closedToGraded (filtered K) p n x := by
  change (Filtered.infinityGradedIso (filtered K) p n).hom
    ((stablePageIso K L U hs r p n hu hl).hom _) = _
  rw [stablePageIso_quotient, Filtered.infinityGradedIso_quotient]
end AlgebraicHodgePilot.Column
