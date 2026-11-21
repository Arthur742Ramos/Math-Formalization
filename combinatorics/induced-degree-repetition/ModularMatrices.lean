module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

open Finset Matrix

private theorem kernel_times_image {G H : Type*} [AddGroup G] [AddGroup H] (p : G →+ H) :
    Nat.card p.ker * Nat.card p.range = Nat.card G := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

/-- Lemma 5's strip estimate. Projecting all columns gives p.range, while the columns
on the chosen strip generate T. Their joint restriction has at most q values. -/
theorem strip_card_bound {G H : Type*} [AddCommGroup G] [Finite G] [AddCommGroup H]
    (p : G →+ H) (T : AddSubgroup G) (q : ℕ) (h : Nat.card (p.comp T.subtype).range ≤ q) :
    Nat.card p.range * Nat.card T ≤ q * Nat.card G := by
  let t := p.comp T.subtype
  let incl : t.ker → p.ker := fun x => ⟨x.val.val, x.property⟩
  have hk : Nat.card t.ker ≤ Nat.card p.ker :=
    Nat.card_le_card_of_injective incl fun x y he => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : p.ker => (z : G)) he
  rw [← kernel_times_image t, ← kernel_times_image p]
  calc
    _ ≤ Nat.card p.range * (Nat.card p.ker * q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hk h)
    _ = _ := by ac_rfl

variable {m n : Type*} [Fintype m] [Fintype n] {q : ℕ} [NeZero q]

private theorem sum_dot_character [DecidableEq m] (w : m → ZMod q) :
    (∑ x : m → ZMod q, ZMod.stdAddChar (w ⬝ᵥ x)) =
      (if w = 0 then (Fintype.card (m → ZMod q) : ℂ) else 0) := by
  classical
  by_cases hw : w = 0
  · simp [hw]
  · let p : (m → ZMod q) →+ ZMod q := ⟨⟨dotProduct w, dotProduct_zero _⟩, dotProduct_add _⟩
    let ψ := ZMod.stdAddChar.compAddMonoidHom p
    have hn : ψ ≠ 1 := by
      intro h
      apply hw
      ext i
      have he := DFunLike.congr_fun h (Pi.single i 1)
      change ZMod.stdAddChar (w ⬝ᵥ Pi.single i 1) = 1 at he
      rw [dotProduct_single_one, ← (ZMod.stdAddChar (N := q)).map_zero_eq_one] at he
      exact ZMod.injective_stdAddChar he
    rw [ite_eq_right hw]
    change (∑ x, ψ x) = 0
    exact ψ.sum_eq_zero_of_ne_one hn

private theorem kernel_sum {α β : Type*} [Fintype α] [AddGroup α] [AddGroup β]
    [DecidableEq β] (f : α →+ β) (c : ℂ) :
    (∑ x, if f x = 0 then c else 0) = (Nat.card f.ker : ℂ) * c := by
  classical
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
  congr 2
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype _).symm

/-- The row and column images over Z/qZ have equal cardinality even for composite q
(Lemma 7). Evaluate the same complete character sum in the two possible orders. -/
theorem row_column_image_card (A : Matrix m n (ZMod q)) :
    Nat.card A.mulVecLin.toAddMonoidHom.range = Nat.card A.vecMulLinear.toAddMonoidHom.range := by
  classical
  let f := A.mulVecLin.toAddMonoidHom
  let g := A.vecMulLinear.toAddMonoidHom
  have hs : (Nat.card f.ker : ℂ) * (Fintype.card (m → ZMod q)) =
      (Nat.card g.ker : ℂ) * (Fintype.card (n → ZMod q)) := by
    rw [← kernel_sum f, ← kernel_sum g]
    calc
      _ = ∑ y : n → ZMod q, ∑ x : m → ZMod q, ZMod.stdAddChar ((A *ᵥ y) ⬝ᵥ x) := by
        simp_rw [sum_dot_character]; rfl
      _ = ∑ x : m → ZMod q, ∑ y : n → ZMod q, ZMod.stdAddChar ((x ᵥ* A) ⬝ᵥ y) := by
        rw [sum_comm]
        simp_rw [dotProduct_comm (A *ᵥ _) _, Matrix.dotProduct_mulVec]
      _ = _ := by simp_rw [sum_dot_character]; rfl
  have hn : Nat.card f.ker * Nat.card (m → ZMod q) =
      Nat.card g.ker * Nat.card (n → ZMod q) := by
    simp only [Nat.card_eq_fintype_card] at hs ⊢
    exact_mod_cast hs
  rw [← kernel_times_image g, ← kernel_times_image f] at hn
  rw [Nat.mul_left_comm (Nat.card g.ker) (Nat.card f.ker)] at hn
  exact ((Nat.mul_right_inj (Nat.card_pos (α := g.ker)).ne').mp
    ((Nat.mul_right_inj (Nat.card_pos (α := f.ker)).ne').mp hn)).symm

end InducedDegreeRepetition
