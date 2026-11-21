module

public import RemainingStatements
public import ColumnSpace
public import RectangleScore

public section
namespace InducedDegreeRepetition.Approximation

open Finset Matrix OpenProblems
open scoped Classical
variable {V : Type*} {q : ℕ} [NeZero q]

@[expose] noncomputable def extendMatrix {X Y : Finset V} (A : Matrix X Y (ZMod q)) (x y : V) : ZMod q :=
  if hx : x ∈ X then if hy : y ∈ Y then A ⟨x,hx⟩ ⟨y,hy⟩ else 0 else 0

omit [NeZero q] in
theorem complexity_extend {X Y : Finset V} (A : Matrix X Y (ZMod q)) :
    complexity (extendMatrix A) X Y = Real.log (Nat.card A.mulVecLin.toAddMonoidHom.range) := by
  classical
  have e : column (extendMatrix A) X '' (Y : Set V) = Set.range A.col := by
    ext w
    constructor
    · rintro ⟨y,hy,rfl⟩
      change y ∈ Y at hy
      exact ⟨⟨y,hy⟩,funext fun x => by simp [column,extendMatrix,x.2,hy,Matrix.col_apply]⟩
    · rintro ⟨y,rfl⟩
      exact ⟨y,y.2,funext fun x => by simp [column,extendMatrix,x.2,y.2,Matrix.col_apply]⟩
  unfold complexity colSpace
  rw [e,← Matrix.range_mulVecLin]
  rfl

omit [NeZero q] in
theorem errors_extend {X Y : Finset V} (A : Matrix X Y (ZMod q)) (G : SimpleGraph V) :
    errors (fun x y => extendMatrix A x y ≠ adjMod q G x y) X Y =
      ∑ x : X, ((univ.filter fun y : Y => A x y ≠ adjMod q G x y).card : ℝ) := by
  classical
  unfold errors total
  rw [sum_subtype (F := (inferInstance : Fintype X)) X (fun _ => Iff.rfl)]
  apply sum_congr rfl
  intro x _
  rw [sum_subtype (F := (inferInstance : Fintype Y)) Y (fun _ => Iff.rfl)]
  rw [← sum_boole]
  apply sum_congr rfl
  intro y _
  simp [extendMatrix,x.2,y.2]

omit [NeZero q] in
theorem constant_errors (hq : 3 ≤ q) (G : SimpleGraph V) {B R U : Finset V} {cut τ : ℝ}
    (cuts : CutBounds G B cut τ) (rb : R ⊆ B) (ub : U ⊆ B) (dis : Disjoint R U)
    (lr : cut ≤ R.card) (lu : cut ≤ U.card) (A : V → V → ZMod q) (t : ZMod q)
    (const : ∀ x ∈ R, ∀ y ∈ U, A x y = t) :
    τ*R.card*U.card ≤ errors (fun x y => A x y ≠ adjMod q G x y) R U := by
  classical
  let b : Bool := decide (t = 0)
  apply le_trans (cuts _ rb _ ub dis lr lu b)
  apply sum_le_sum
  intro x hx
  rw [← sum_boole (s := U) (R := ℝ) (p := fun y => adj G x y = b)]
  apply sum_le_sum
  intro y hy
  have nz : (1 : ZMod q) ≠ 0 := by
    let : Fact (1 < q) := ⟨by omega⟩
    exact one_ne_zero
  have ee := const x hx y hy
  by_cases hz : t = 0 <;> by_cases edge : G.Adj x y <;>
    simp [adj,adjMod,b,hz,edge,ee,nz.symm,ite_nonneg]

end InducedDegreeRepetition.Approximation
