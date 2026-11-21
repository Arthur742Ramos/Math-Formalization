module

public import TupleMeans
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V I : Type*}

theorem tuple_coordinates {L : ℕ} (U : Fin L → Finset V) (P : List V) (h : P ∈ tupleSpace (List.ofFn U)) :
    ∃ f : Fin L → V, (∀ k, f k ∈ U k) ∧ List.ofFn f = P := by
  induction L generalizing P with
  | zero =>
    have hp : P=[] := by simpa [tupleSpace] using h
    exact ⟨Fin.elim0,fun k => k.elim0,by simp [hp]⟩
  | succ L ih =>
    rw [List.ofFn_succ] at h
    obtain ⟨⟨x,P⟩,hx,rfl⟩ := mem_map.mp h
    obtain ⟨f,good,eq⟩ := ih (fun k => U k.succ) P (mem_product.mp hx).2
    refine ⟨Fin.cons x f,?_,?_⟩
    · exact Fin.cases (mem_product.mp hx).1 (fun k => good k)
    · change List.ofFn (Fin.cons x f) = x::P
      simp [List.ofFn_succ,eq]

/-- Select one vertex from every disjoint positional pool. The induced degree
into their union is the sum of the tuple counts. -/
theorem realize_auxiliary [Fintype I] (G : SimpleGraph V) (len : I → ℕ) (T : Finset V)
    (U : (i : I) → Fin (len i) → Finset V) (P : I → List V)
    (valid : ∀ i, P i ∈ tupleSpace (List.ofFn (U i)))
    (dis : ∀ a b : (i : I) × Fin (len i), a ≠ b → Disjoint (U a.1 a.2) (U b.1 b.2))
    (away : ∀ i k, Disjoint (U i k) T) :
    ∃ A : Finset V, Disjoint A T ∧ A.card = ∑ i, len i ∧
      ∀ y, degreeOn G A y = ∑ i, tupleDegree (adj G) y (P i) := by
  classical
  choose f hit eq using fun i => tuple_coordinates (U i) (P i) (valid i)
  let emb : ((i : I) × Fin (len i)) ↪ V :=
    ⟨fun a => f a.1 a.2,fun a b same => by
      by_contra ne
      exact disjoint_left.mp (dis a b ne) (hit _ _) (by rw [show f a.1 a.2 = f b.1 b.2 from same]; exact hit b.1 b.2)⟩
  let A := univ.map emb
  refine ⟨A,?_,by simp [A,Fintype.card_sigma],?_⟩
  · apply disjoint_left.mpr
    rintro x hx ht
    obtain ⟨a,_,rfl⟩ := mem_map.mp hx
    exact disjoint_left.mp (away a.1 a.2) (hit a.1 a.2) ht
  · intro y
    have d (i : I) : (tupleDegree (adj G) y (P i):ℝ) =
        ∑ k, if G.Adj y (f i k) then (1:ℝ) else 0 := by
      rw [degree_as_sum,← eq i,List.map_ofFn,List.sum_ofFn]
      rfl
    apply Nat.cast_inj (R:=ℝ) |>.mp
    rw [Nat.cast_sum]
    simp_rw [d]
    rw [← Fintype.sum_sigma (f:=fun a : (i : I) × Fin (len i) => if G.Adj y (f a.1 a.2) then (1:ℝ) else 0)]
    rw [degreeOn,Finset.filter_map,card_map,← sum_boole]
    rfl

end InducedDegreeRepetition.Sampling
