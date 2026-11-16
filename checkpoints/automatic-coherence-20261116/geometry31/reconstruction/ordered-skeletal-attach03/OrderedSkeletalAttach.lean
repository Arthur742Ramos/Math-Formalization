import FiniteOrderedFaces
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! SOURCE ONLY / UNCOMPILED. Actual skeletal pushout descent, not an assumed
gluing theorem. Boundary compatibility is a local face equation, explicitly
kept as an obligation when specializing the adapter to an actual F and shared D.
The returned map is a natural transformation in ALL degrees, including degeneracies. -/
noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace AutomaticCoherence.OrderedSkeletalAttach01
open SSet SSet.relativeCellComplexOfMono

variable {A S Z : SSet.{0}} (i : A ⟶ S) (d : ℕ)

/-- The actual attaching map of an individual boundary, as in Skeleton.t. -/
def boundaryToStage (c : Cell i d) : (∂Δ[d] : SSet) ⟶ skeletonOfMono i d :=
  c.ιSigmaBoundary ≫ t i d

variable (lower : (skeletonOfMono i d : SSet) ⟶ Z)
  (cells : ∀ c : Cell i d, (Δ[d] : SSet) ⟶ Z)
  (agree : ∀ c, boundaryToStage i d c ≫ lower = ∂Δ[d].ι ≫ cells c)

include agree in
lemma square_agrees : t i d ≫ lower = l i d ≫ Sigma.desc cells := by
  apply Sigma.hom_ext
  intro c
  calc
    c.ιSigmaBoundary ≫ t i d ≫ lower = ∂Δ[d].ι ≫ cells c := agree c
    _ = c.ιSigmaBoundary ≫ l i d ≫ Sigma.desc cells := by
      rw [Cell.ι_l_assoc]
      simp

/-- The existence proof is the pinned actual isPushout, with no extra
pushout, surjectivity, compatibility of chosen fillers or coherence premise. -/
def attach : (skeletonOfMono i (d+1) : SSet) ⟶ Z :=
  (SSet.relativeCellComplexOfMono.isPushout i d).desc lower (Sigma.desc cells)
    (square_agrees i d lower cells agree)

lemma attach_lower : r i d ≫ attach i d lower cells agree = lower := by
  exact (SSet.relativeCellComplexOfMono.isPushout i d).inl_desc _ _ _

lemma attach_cell (c : Cell i d) :
    c.ιSigmaStdSimplex ≫ b i d ≫ attach i d lower cells agree = cells c := by
  rw [show b i d ≫ attach i d lower cells agree = Sigma.desc cells from
    (SSet.relativeCellComplexOfMono.isPushout i d).inr_desc _ _ _]
  simp

/-- Exact all-dimensional compatibility is a theorem of the constructed NatTrans,
not a rule selecting new fillers for degenerate cells. -/
lemma attach_naturality {m n : SimplexCategory} (f : m ⟶ n)
    (x : (skeletonOfMono i (d+1) : SSet).obj (op n)) :
    (attach i d lower cells agree).app (op m)
      ((skeletonOfMono i (d+1) : SSet).map f.op x) =
    Z.map f.op ((attach i d lower cells agree).app (op n) x) :=
  ConcreteCategory.congr_hom ((attach i d lower cells agree).naturality f.op) x

/-- At dimension zero the actual boundary is empty, so no compatibility
condition is invented. The range-stage map can retain a prescribed subcomplex. -/
def attachVertices
    (base : (skeletonOfMono i 0 : SSet) ⟶ Z)
    (vertices : ∀ c : Cell i 0, (Δ[0] : SSet) ⟶ Z) :
    (skeletonOfMono i 1 : SSet) ⟶ Z :=
  attach i 0 base vertices (fun _ ↦ SSet.boundary.hom_ext₀)

/-- In positive dimensions it is enough to check the actual finitely many
codimension-one faces; Boundary.hom_ext supplies the whole-boundary equality. -/
lemma boundary_agrees_of_faces (d : ℕ)
    (lower : (skeletonOfMono i (d+1) : SSet) ⟶ Z)
    (cells : ∀ c : Cell i (d+1), (Δ[d+1] : SSet) ⟶ Z)
    (h : ∀ c (j : Fin (d+2)),
      SSet.boundary.ι j ≫ boundaryToStage i (d+1) c ≫ lower =
      SSet.stdSimplex.δ j ≫ cells c) :
    ∀ c, boundaryToStage i (d+1) c ≫ lower = ∂Δ[d+1].ι ≫ cells c := by
  intro c
  apply SSet.boundary.hom_ext
  intro j
  simpa only [Category.assoc, SSet.boundary.ι_ι_assoc] using h c j

/-- Dimension <=2 closes the filtration after the triangle attachments.
This is proved from nondegenerate generation, not posited as a coverage map. -/
lemma stage_three_eq_top [S.HasDimensionLT 3] : skeletonOfMono i 3 = ⊤ := by
  apply le_antisymm (by simp)
  rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
  intro n x hx
  exact (SSet.skeleton_le_skeletonOfMono i 3) _
    (SSet.mem_skeleton S x.val (S.dim_lt_of_nonDegenerate x 3))

/-- Once vertices/edges/triangles have been attached, the full simplicial map
uses this actual subcomplex isomorphism. All higher degenerate values follow. -/
def finish [S.HasDimensionLT 3] (f : (skeletonOfMono i 3 : SSet) ⟶ Z) : S ⟶ Z :=
  (SSet.Subcomplex.topIso S).inv ≫
    (SSet.Subcomplex.eqToIso (stage_three_eq_top i)).inv ≫ f

lemma stage_ι_finish [S.HasDimensionLT 3] (f : (skeletonOfMono i 3 : SSet) ⟶ Z) :
    (skeletonOfMono i 3).ι ≫ finish i f = f := by
  have he : (skeletonOfMono i 3).ι =
      (SSet.Subcomplex.eqToIso (stage_three_eq_top i)).hom ≫
        (SSet.Subcomplex.topIso S).hom := rfl
  change (skeletonOfMono i 3).ι ≫
    (SSet.Subcomplex.topIso S).inv ≫
    (SSet.Subcomplex.eqToIso (stage_three_eq_top i)).inv ≫ f = f
  rw [he]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Two explicit attachment operations suffice after a vertex-stage map.
These are LOCAL face constraints, not an assumed global gluing/coarsening theorem.
The actual-F specialization must discharge both displayed h1/h2 from shared choices. -/
def assembleTwo [S.HasDimensionLT 3]
    (vertices : (skeletonOfMono i 1 : SSet) ⟶ Z)
    (edges : ∀ c : Cell i 1, (Δ[1] : SSet) ⟶ Z)
    (h1 : ∀ c (j : Fin 2),
      SSet.boundary.ι j ≫ boundaryToStage i 1 c ≫ vertices =
      SSet.stdSimplex.δ j ≫ edges c)
    (triangles : ∀ c : Cell i 2, (Δ[2] : SSet) ⟶ Z)
    (h2 : ∀ c (j : Fin 3),
      SSet.boundary.ι j ≫ boundaryToStage i 2 c ≫
        attach i 1 vertices edges (boundary_agrees_of_faces i 0 vertices edges h1) =
      SSet.stdSimplex.δ j ≫ triangles c) : S ⟶ Z :=
  finish i (attach i 2
    (attach i 1 vertices edges (boundary_agrees_of_faces i 0 vertices edges h1))
    triangles (boundary_agrees_of_faces i 1 _ triangles h2))

end AutomaticCoherence.OrderedSkeletalAttach01
