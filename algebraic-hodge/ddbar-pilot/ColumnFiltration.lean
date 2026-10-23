module

public import TotalRepresentative
public import FilteredPages

/-! The column filtration consists of submodules of the genuine total complex. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

noncomputable def inclusion (p q n : ℤ) (h : p + q = n) :
    (K.X p).X q ⟶ (total K).X n :=
  K.ιTotal (ComplexShape.up ℤ) p q n h

noncomputable def projection (p q n : ℤ) :
    (total K).X n ⟶ (K.X p).X q :=
  K.totalDesc (c₁₂ := ComplexShape.up ℤ) (i₁₂ := n) fun a b _ =>
    if h : a = p ∧ b = q then
      (K.XXIsoOfEq _ _ _ h.1 h.2).hom
    else 0

theorem inclusion_projection_self (p q : ℤ) :
    inclusion K p q (p + q) rfl ≫ projection K p q (p + q) = 𝟙 _ := by
  dsimp only [inclusion, projection, AlgebraicHodgePilot.total]
  rw [K.ι_totalDesc]
  simp [HomologicalComplex₂.XXIsoOfEq]

@[reassoc]
theorem inclusion_projection_ne (a b p q n : ℤ) (hab : a + b = n)
    (h : ¬ (a = p ∧ b = q)) :
    inclusion K a b n hab ≫ projection K p q n = 0 := by
  dsimp only [inclusion, projection, AlgebraicHodgePilot.total]
  rw [K.ι_totalDesc]
  simp [h]

@[reassoc]
theorem inclusion_projection_eq (p q n : ℤ) (h : p + q = n) :
    inclusion K p q n h ≫ projection K p q n = 𝟙 _ := by
  subst n
  exact inclusion_projection_self K p q

/-- The span of exactly those total summands whose column is at least `p`. -/
noncomputable def filtration (p n : ℤ) : Submodule k ((total K).X n) :=
  ⨆ (a : ℤ) (b : ℤ) (h : a + b = n) (_ : p ≤ a),
    LinearMap.range (inclusion K a b n h).hom

theorem inclusion_mem_filtration (p a b n : ℤ) (h : a + b = n) (hp : p ≤ a)
    (x : (K.X a).X b) : (inclusion K a b n h).hom x ∈ filtration K p n :=
  Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem h (Submodule.mem_iSup_of_mem hp ⟨x, rfl⟩)))

theorem filtration_antitone (n : ℤ) : Antitone (fun p => filtration K p n) := by
  intro p p' hpp
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun hp => ?_
  rintro _ ⟨x, rfl⟩
  exact inclusion_mem_filtration K p a b n hab (hpp.trans hp) x

theorem projection_kills_next (p q n : ℤ) :
    filtration K (p + 1) n ≤ LinearMap.ker (projection K p q n).hom := by
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun hp => ?_
  rintro _ ⟨x, rfl⟩
  have h := inclusion_projection_ne K a b p q n hab (by intro he; lia -abstractProof)
  exact congrArg (fun f => f.hom x) h

theorem filtration_split (p q n : ℤ) (h : p + q = n) :
    filtration K p n = LinearMap.range (inclusion K p q n h).hom ⊔
      filtration K (p + 1) n := by
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

theorem mem_next_of_projection_zero (p q n : ℤ) (h : p + q = n)
    (x : (total K).X n) (hx : x ∈ filtration K p n)
    (hz : (projection K p q n).hom x = 0) : x ∈ filtration K (p + 1) n :=
  match Submodule.mem_sup.mp
      (Eq.mp (congrArg (fun S : Submodule k ((total K).X n) => x ∈ S)
        (filtration_split K p q n h)) hx) with
  | ⟨_, ⟨u, rfl⟩, b, hb, hab⟩ =>
    have hcomp := congrArg (fun f => f.hom u) (inclusion_projection_eq K p q n h)
    have hbz : (projection K p q n).hom b = 0 := projection_kills_next K p q n hb
    have hu : u = 0 := hcomp.symm.trans (calc
      (projection K p q n).hom ((inclusion K p q n h).hom u) =
          (projection K p q n).hom ((inclusion K p q n h).hom u) +
            (projection K p q n).hom b := by rw [hbz, add_zero]
      _ = (projection K p q n).hom ((inclusion K p q n h).hom u + b) :=
        (map_add (projection K p q n).hom _ _).symm
      _ = (projection K p q n).hom x := congrArg (projection K p q n).hom hab
      _ = 0 := hz)
    have hb' : b = x := by simpa only [hu, map_zero, zero_add] using hab
    hb' ▸ hb

theorem subtract_leading_mem_next (p q n : ℤ) (h : p + q = n)
    (x : (total K).X n) (hx : x ∈ filtration K p n) :
    x - (inclusion K p q n h).hom ((projection K p q n).hom x) ∈
      filtration K (p + 1) n := by
  apply mem_next_of_projection_zero K p q n h
  · exact (filtration K p n).sub_mem hx
      (inclusion_mem_filtration K p p q n h (le_refl p) _)
  · rw [map_sub]
    have hcomp := congrArg (fun f => f.hom ((projection K p q n).hom x))
      (inclusion_projection_eq K p q n h)
    exact sub_eq_zero.mpr hcomp.symm

theorem inclusionOrZero_mem_filtration (p a b n : ℤ) (hp : p ≤ a)
    (x : (K.X a).X b) :
    (K.ιTotalOrZero (ComplexShape.up ℤ) a b n).hom x ∈ filtration K p n := by
  by_cases h : a + b = n
  · rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) a b n h]
    exact inclusion_mem_filtration K p a b n h hp x
  · rw [K.ιTotalOrZero_eq_zero (ComplexShape.up ℤ) a b n h]
    exact (filtration K p n).zero_mem

theorem differential_preserves_filtration (p n m : ℤ) :
    filtration K p n ≤
      (filtration K p m).comap ((total K).d n m).hom :=
  iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun hp =>
    fun _ hx => by
      rcases hx with ⟨x, rfl⟩
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

end AlgebraicHodgePilot.Column
