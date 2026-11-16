import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
import Mathlib.Order.Fin.Basic

/-! SOURCE ONLY / UNCOMPILED. Ordered-complex face and finite-index facts.
This file does not identify arbitrary iterated actual subdivision with an order
complex and does not supply a coarsening map as a premise. -/
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
namespace AutomaticCoherence.FiniteOrderedFaces01

variable {V : Type} [PartialOrder V]

/-- Every face of a nondegenerate ordered simplex is again nondegenerate.
This excludes the collapsed-face problem that occurs for general simplicial sets. -/
lemma nerve_face_nonDegenerate {n : ℕ} (s : (nerve V) _⦋n+1⦌)
    (h : s ∈ (nerve V).nonDegenerate (n+1)) (i : Fin (n+2)) :
    (nerve V).δ i s ∈ (nerve V).nonDegenerate n := by
  rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono] at h ⊢
  have hobj : ((nerve V).δ i s).obj = s.obj ∘ i.succAbove := by
    funext j
    exact CategoryTheory.nerve.δ_obj i s j
  rw [hobj]
  exact h.comp (Fin.strictMono_succAbove i)

/-- The same assertion holds in an arbitrary subcomplex of the ordered nerve. -/
lemma subcomplex_face_nonDegenerate (A : (nerve V).Subcomplex) {n : ℕ}
    (s : (A : SSet) _⦋n+1⦌) (h : s ∈ (A : SSet).nonDegenerate (n+1))
    (i : Fin (n+2)) : (A : SSet).δ i s ∈ (A : SSet).nonDegenerate n := by
  apply (A.mem_nonDegenerate_iff _).2
  exact nerve_face_nonDegenerate s.val ((A.mem_nonDegenerate_iff s).1 h) i

/-- For finite vertices the cells in any fixed dimension form a finite set.
The arrow data of a poset nerve are subsingletons; obj is genuinely injective. -/
lemma finite_nerve_simplices [Finite V] (n : ℕ) : Finite ((nerve V) _⦋n⦌) := by
  apply Finite.of_injective (fun s : (nerve V) _⦋n⦌ ↦ s.obj)
  intro s t h
  exact CategoryTheory.nerve.ext_of_isThin h

lemma finite_relative_cells [Finite V] (A B : (nerve V).Subcomplex)
    (i : (A : SSet) ⟶ B) (d : ℕ) :
    Finite (SSet.relativeCellComplexOfMono.Cell i d) := by
  letI : Finite ((nerve V) _⦋d⦌) := finite_nerve_simplices d
  apply Finite.of_injective (fun c : SSet.relativeCellComplexOfMono.Cell i d ↦ c.simplex.val)
  intro c c' h
  apply SSet.relativeCellComplexOfMono.Cell.ext
  exact Subtype.ext h

end AutomaticCoherence.FiniteOrderedFaces01
