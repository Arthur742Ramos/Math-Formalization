module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Consecutive disjoint blocks of vertices
-/

@[expose] public section

open Function

namespace BoundedEdgeRegularSubgraphs

/-- The consecutive block at the given position. Its endpoints fit
inside the original order by the natural quotient bound. -/
def consecutiveVertexBlock (n m : ℕ) (i : Fin (n / m)) : Finset (Fin n) :=
  Finset.univ.map {
    toFun := fun j : Fin m ↦ ⟨i.val * m + j.val, by
      have h₁ := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
      have h₂ := Nat.div_mul_le_self n m
      have h₃ : i.val * m + j.val < (i.val + 1) * m := by rw [Nat.add_mul]; simp
      exact h₃.trans_le (h₁.trans h₂)⟩
    inj' := fun j j' he ↦ Fin.ext (Nat.add_left_cancel (congrArg Fin.val he)) }

theorem card_consecutiveVertexBlock (n m : ℕ) (i : Fin (n / m)) :
    (consecutiveVertexBlock n m i).card = m := by
  simp only [consecutiveVertexBlock, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem pairwise_disjoint_consecutiveVertexBlock (n m : ℕ) :
    Pairwise (Disjoint on consecutiveVertexBlock n m) := by
  intro i j hij
  rw [Function.onFun, Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hv
  obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hv'
  have h₁ : i.val * m + a.val = v.val := congrArg Fin.val ha
  have h₂ : j.val * m + b.val = v.val := congrArg Fin.val hb
  have hstep (l r : Fin (n / m)) (x y : Fin m) (hl : l < r) :
      l.val * m + x.val < r.val * m + y.val := by
    have hz : l.val * m + x.val < (l.val + 1) * m := by
      rw [Nat.add_mul, one_mul]
      exact Nat.add_lt_add_left x.isLt _
    exact hz.trans_le ((Nat.mul_le_mul_right m (Nat.succ_le_of_lt hl)).trans (Nat.le_add_right _ _))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have h := hstep i j a b hlt
    omega
  · have h := hstep j i b a hlt
    omega

end BoundedEdgeRegularSubgraphs
