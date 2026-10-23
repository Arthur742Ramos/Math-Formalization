module

public import HodgeSolution

-- BEGIN material-imported-definition audit
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace HodgeMaterialAudit
variable {k : Type} [Field k] (K : AlgebraicHodgePilot.Bicomplex k)
variable {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
example (f : M →ₗ[k] N) (x : M) : x ∈ LinearMap.ker f ↔ f x = 0 := Iff.rfl
example (f : M →ₗ[k] N) (y : N) : y ∈ LinearMap.range f ↔ ∃ x, f x = y := Iff.rfl
example (f : M →ₗ[k] N) (S : Submodule k M) (y : N) :
    y ∈ S.map f ↔ ∃ x, x ∈ S ∧ f x = y := Iff.rfl
example (f : M →ₗ[k] N) (S : Submodule k N) (x : M) :
    x ∈ S.comap f ↔ f x ∈ S := Iff.rfl
example (S : Submodule k M) (x y : M) : S.quotientRel x y ↔ x - y ∈ S :=
  Submodule.quotientRel_def S
example (S : Submodule k M) (x : M) : S.mkQ x = 0 ↔ x ∈ S :=
  Submodule.Quotient.mk_eq_zero S
example (S : Submodule k M) (f : M →ₗ[k] N) (hf : S ≤ LinearMap.ker f) (x : M) :
    S.liftQ f hf (S.mkQ x) = f x := rfl
example (f : M →ₗ[k] N) (a : k) (x y : M) : f (x + a • y) = f x + a • f y := by
  rw [map_add, map_smul]
example (S : Submodule k M) (a : k) (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    x + a • y ∈ S := S.add_mem hx (S.smul_mem a hy)
example (p q : ℤ) : AlgebraicHodgePilot.ImageKernel K p q ↔
    LinearMap.range (AlgebraicHodgePilot.horizontal K p q) ⊓
      LinearMap.ker (AlgebraicHodgePilot.vertical K (p + 1) q) =
    LinearMap.range ((AlgebraicHodgePilot.horizontal K p q).comp
      (AlgebraicHodgePilot.incomingVertical K p q)) := Iff.rfl
example (p q : ℤ) : AlgebraicHodgePilot.vertical K p q = ((K.X p).d q (q + 1)).hom := rfl
example (p q : ℤ) : AlgebraicHodgePilot.horizontal K p q = ((K.d p (p + 1)).f q).hom := rfl
example (p q : ℤ) : (AlgebraicHodgePilot.total K).d (p + q) (p + q + 1) =
    (K.total (ComplexShape.up ℤ)).d (p + q) (p + q + 1) := rfl
example (p q n : ℤ) (h : p + q = n) :
    AlgebraicHodgePilot.Column.inclusion K p q n h = K.ιTotal (ComplexShape.up ℤ) p q n h := rfl
example (C : CochainComplex (ModuleCat k) ℤ) (n : ℤ) :
    C.d n (n + 1) ≫ C.d (n + 1) (n + 2) = 0 := C.d_comp_d _ _ _
example (i j : ℤ) : (ComplexShape.up ℤ).Rel i j ↔ i + 1 = j := Iff.rfl
example (r : ℤ) (pq pq' : ℤ × ℤ) :
    (ComplexShape.up' (r, 1-r)).Rel pq pq' ↔ pq + (r, 1-r) = pq' := Iff.rfl
example (S : ShortComplex (ModuleCat k)) :
    S.moduleCatLeftHomologyData.H = ModuleCat.of k
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) := rfl
example (S : ShortComplex (ModuleCat k)) :
    S.moduleCatLeftHomologyData.π.hom = (LinearMap.range S.moduleCatToCycles).mkQ := rfl
example (S : ShortComplex (ModuleCat k)) :
    S.homology ≅ ModuleCat.of k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
  S.moduleCatHomologyIso
example (S : ShortComplex (ModuleCat k)) (hf : S.f = 0) (hg : S.g = 0) :
    (ShortComplex.LeftHomologyData.ofZeros S hf hg).π = 𝟙 S.X₂ := rfl
example (C : CochainComplex (ModuleCat k) ℤ) (n : ℤ) : C.homology n = (C.sc n).homology := rfl
example (X Y : ModuleCat k) (e : X ≅ Y) : e.hom ≫ e.inv = 𝟙 X := e.hom_inv_id
example (E : CohomologicalSpectralSequence (ModuleCat k) 1) (r : ℤ) (hr : 1 ≤ r) :
    HomologicalComplex (ModuleCat k) (ComplexShape.up' (⟨r, 1-r⟩ : ℤ × ℤ)) := E.page r hr
example (E : CohomologicalSpectralSequence (ModuleCat k) 1) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    (E.page r hr).homology pq ≅ (E.page (r + 1) (by lia)).X pq := E.iso r (r+1) pq rfl hr
example (e : M ≃ₗ[k] N) (x : M) : e.symm (e x) = x := e.symm_apply_apply x
example (e : M ≃ₗ[k] N) : e.toModuleIso.hom.hom = e.toLinearMap := rfl
example (f : M →ₗ[k] N) (hf : Function.Bijective f) (x : M) :
    LinearEquiv.ofBijective f hf x = f x := rfl
example (X : ModuleCat k) : Module k X := X.isModule
example (f : ModuleCat.of k M ⟶ ModuleCat.of k N) : M →ₗ[k] N := f.hom
example (S : ShortComplex (ModuleCat k)) (h : S.LeftHomologyData) :
    Limits.IsLimit (Limits.KernelFork.ofι h.i h.wi) := h.hi
example (S : ShortComplex (ModuleCat k)) (h : S.LeftHomologyData) :
    Limits.IsColimit (Limits.CokernelCofork.ofπ h.π h.wπ) := h.hπ
example (S : ShortComplex (ModuleCat k)) (h : S.RightHomologyData) :
    Limits.IsColimit (Limits.CokernelCofork.ofπ h.p h.wp) := h.hp
example (S : ShortComplex (ModuleCat k)) (h : S.HomologyData) : h.left.H ≅ h.right.H := h.iso
example (S : ShortComplex (ModuleCat k)) : S.HasHomology := inferInstance
example (S : ShortComplex (ModuleCat k)) : S.homology = S.homologyData.left.H := rfl
example (S : ShortComplex (ModuleCat k)) (h : S.LeftHomologyData) : S.homology ≅ h.H := h.homologyIso
example (p : ℤ) : Int.negOnePow p = (-1 : ℤˣ)^p := rfl
example (p q : ℤ) : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (p,q) = 1 := rfl
example (p q : ℤ) : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (p,q) = Int.negOnePow p := rfl
variable {C : CochainComplex (ModuleCat k) ℤ} (F : AlgebraicHodgePilot.Filtered.Filtration C)
example (r p n : ℤ) (x : C.X n) :
    x ∈ AlgebraicHodgePilot.Filtered.cycles F r p n ↔
      x ∈ F.F p n ∧ (C.d n (n+1)).hom x ∈ F.F (p+r) (n+1) := Iff.rfl
example (r p n : ℤ) (x : C.X n) :
    x ∈ AlgebraicHodgePilot.Filtered.boundaries F r p n ↔
      x ∈ F.F p n ∧ ∃ u, u ∈ F.F (p-r) (n-1) ∧ (C.d (n-1) n).hom u = x := Iff.rfl
example (p n : ℤ) (x : C.X n) :
    x ∈ AlgebraicHodgePilot.Filtered.closedCycles F p n ↔
      x ∈ F.F p n ∧ (C.d n (n+1)).hom x = 0 := Iff.rfl
example (p n : ℤ) (c : C.homology n) :
    c ∈ AlgebraicHodgePilot.Filtered.cohomologyFiltration F p n ↔
      ∃ x, AlgebraicHodgePilot.Filtered.closedClassMap F p n x = c := Iff.rfl
example (r p n : ℤ) : AlgebraicHodgePilot.Filtered.Page F r p n =
    (AlgebraicHodgePilot.Filtered.cycles F r p n ⧸
      (AlgebraicHodgePilot.Filtered.denominator F r p n).comap
        (AlgebraicHodgePilot.Filtered.cycles F r p n).subtype) := rfl
example (p n : ℤ) : AlgebraicHodgePilot.Filtered.GradedCohomology F p n =
    (AlgebraicHodgePilot.Filtered.cohomologyFiltration F p n ⧸
      (AlgebraicHodgePilot.Filtered.cohomologyFiltration F (p+1) n).comap
        (AlgebraicHodgePilot.Filtered.cohomologyFiltration F p n).subtype) := rfl
end HodgeMaterialAudit
-- END material-imported-definition audit
