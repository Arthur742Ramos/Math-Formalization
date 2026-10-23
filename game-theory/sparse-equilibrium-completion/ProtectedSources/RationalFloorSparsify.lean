/- AI-assisted formalization under the repository Apache-2.0 license.
Follow-on global sparse composition; specifications require zero residual floors. -/
module
public import ProtectedSources.RationalFloorOutputRows
public import ProtectedSources.RationalSparseGapGame
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalUnconstrainedSystem (m : ℕ) : RationalLinearSystem (Fin 0) m :=
  ⟨Fin.elim0,Fin.elim0⟩

def rationalFloorSparsify {k m : ℕ} (d : RationalIntervalParameters k m (Fin m))
    (e : ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m) :
    Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  (rationalSparseGapAlgorithm w.2.K w.2.D w.1 d.M (1-∑ a,w.1 a)
    (w.2.bracket.2+e/((3 : ℕ) : ℚ)) e (rationalUnconstrainedSystem m)).map (fun v =>
      (w.1,{ bracket := (0,w.2.bracket.2+e/((3 : ℕ) : ℚ)+e), q := v.1,
             K := w.2.K, D := w.2.D, B := v.2 }))

def rationalFloorSparseApproximation {k m : ℕ} (d : RationalIntervalParameters k m (Fin m))
    (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a) (ε : ℚ) :
    Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if 0 < ε then
    (rationalFloorApproximation d s hs (ε/((2 : ℕ) : ℚ))).bind
      (rationalFloorSparsify d (ε/((2 : ℕ) : ℚ))) else none

theorem rational_floor_sparsify_origin {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (e : ℚ)
    (w v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSparsify d e w=some v) :
    v.1=w.1 ∧ v.2.K=w.2.K ∧ v.2.D=w.2.D ∧
    v.2.bracket=(0,w.2.bracket.2+e/((3 : ℕ) : ℚ)+e) ∧
    rationalSparseGapAlgorithm w.2.K w.2.D w.1 d.M (1-∑ a,w.1 a)
      (w.2.bracket.2+e/((3 : ℕ) : ℚ)) e (rationalUnconstrainedSystem m)=some (v.2.q,v.2.B) := by
  cases hs : rationalSparseGapAlgorithm w.2.K w.2.D w.1 d.M (1-∑ a,w.1 a)
      (w.2.bracket.2+e/((3 : ℕ) : ℚ)) e (rationalUnconstrainedSystem m) with
  | none => simp only [rationalFloorSparsify,hs,Option.map_none] at hout; cases hout
  | some z =>
    have he := Option.some.inj (by simpa only [rationalFloorSparsify,hs,Option.map_some] using hout)
    subst v
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end SparseCompletion
