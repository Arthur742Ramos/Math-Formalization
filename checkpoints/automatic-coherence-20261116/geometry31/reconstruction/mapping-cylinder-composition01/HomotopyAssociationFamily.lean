module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! SOURCE ONLY / UNCOMPILED. Jointly continuous associativity of three
homotopies, using the pinned scalar path reparameterization rather than
evaluation on a function space with an arbitrary source domain. -/
@[expose] public section
noncomputable section
open ContinuousMap
open scoped Topology
namespace AutomaticCoherence.HomotopyAssociationFamily01

abbrev I := unitInterval

def parameter (u : I) : I :=
  ⟨Path.Homotopy.transAssocReparamAux u,
    Path.Homotopy.transAssocReparamAux_mem_I u⟩

lemma continuous_parameter : Continuous parameter :=
  Path.Homotopy.continuous_transAssocReparamAux.subtype_mk _

@[simp] lemma parameter_zero : parameter 0 = 0 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_zero
@[simp] lemma parameter_one : parameter 1 = 1 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_one

def blend (v u : I) : I := Set.Icc.convexComb (parameter u) u v

lemma continuous_blend : Continuous (fun p : I × I => blend p.1 p.2) :=
  Set.Icc.continuous_convexComb_prod.comp
    ((continuous_parameter.comp continuous_snd).prodMk
      (continuous_snd.prodMk continuous_fst))

@[simp] lemma blend_zero (u : I) : blend 0 u = parameter u := by simp [blend]
@[simp] lemma blend_one (u : I) : blend 1 u = u := by simp [blend]
@[simp] lemma blend_left (v : I) : blend v 0 = 0 := by simp [blend]
@[simp] lemma blend_right (v : I) : blend v 1 = 1 := by simp [blend]

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f₀ f₁ f₂ f₃ : C(X,Y)}

def atPath (H : f₀.Homotopy f₁) (x : X) : Path (f₀ x) (f₁ x) where
  toFun t := H (t,x)
  continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
  source' := H.map_zero_left x
  target' := H.map_one_left x

@[simp] lemma atPath_apply (H : f₀.Homotopy f₁) (x : X) (t : I) :
    atPath H x t = H (t,x) := rfl

lemma atPath_trans (H : f₀.Homotopy f₁) (K : f₁.Homotopy f₂) (x : X) :
    atPath (H.trans K) x = (atPath H x).trans (atPath K x) := by
  apply Path.ext
  funext t
  change (H.trans K) (t,x) = ((atPath H x).trans (atPath K x)) t
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

variable (H : f₀.Homotopy f₁) (K : f₁.Homotopy f₂) (L : f₂.Homotopy f₃)

lemma association_apply (u : I) (x : X) :
    ((H.trans K).trans L) (u,x) = (H.trans (K.trans L)) (parameter u,x) := by
  have h := Path.Homotopy.trans_assoc_reparam
    (atPath H x) (atPath K x) (atPath L x)
  have he := congrArg (fun p : Path (f₀ x) (f₃ x) => p u) h
  simpa only [← atPath_trans, atPath_apply, Path.coe_reparam,
    Function.comp_apply, parameter] using he

/-- The outer variable is the homotopy time; the inner variable is path time. -/
def family : C(I × (I × X),Y) where
  toFun p := (H.trans (K.trans L)) (blend p.1 p.2.1,p.2.2)
  continuous_toFun := (H.trans (K.trans L)).continuous.comp
    ((continuous_blend.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))

lemma family_zero (u : I) (x : X) :
    family H K L (0,(u,x)) = ((H.trans K).trans L) (u,x) := by
  change (H.trans (K.trans L)) (blend 0 u,x) = _
  rw [blend_zero]
  exact (association_apply H K L u x).symm

lemma family_one (u : I) (x : X) :
    family H K L (1,(u,x)) = (H.trans (K.trans L)) (u,x) := by
  change (H.trans (K.trans L)) (blend 1 u,x) = _
  rw [blend_one]

lemma family_left (v : I) (x : X) : family H K L (v,(0,x)) = f₀ x := by
  change (H.trans (K.trans L)) (blend v 0,x) = _
  rw [blend_left]
  exact (H.trans (K.trans L)).map_zero_left x

lemma family_right (v : I) (x : X) : family H K L (v,(1,x)) = f₃ x := by
  change (H.trans (K.trans L)) (blend v 1,x) = _
  rw [blend_right]
  exact (H.trans (K.trans L)).map_one_left x

end AutomaticCoherence.HomotopyAssociationFamily01
