/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalFiniteSelection
public import AllocationReservoirValue
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalGridTuples : (k N : ℕ) → List (Fin k → Fin N)
  | 0,_ => [Fin.elim0]
  | k+1,N => (List.finRange N).flatMap (fun a =>
      (rationalGridTuples k N).map (fun z => Fin.cons a z))

theorem rational_grid_tuples_complete (k N : ℕ) (z : Fin k → Fin N) :
    z ∈ rationalGridTuples k N := by
  induction k with
  | zero =>
    have he : z=Fin.elim0 := by funext i; exact Fin.elim0 i
    simp only [rationalGridTuples,he,List.mem_singleton]
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨z 0,by simp only [List.mem_finRange],?_⟩
    apply List.mem_map.mpr
    exact ⟨fun i => z i.succ,ih _,by ext i; exact Fin.cases rfl (fun _ => rfl) i⟩

theorem rational_grid_tuples_length (k N : ℕ) :
    (rationalGridTuples k N).length=N^k := by
  induction k with
  | zero => simp only [rationalGridTuples,List.length_singleton,pow_zero]
  | succ k ih =>
    simp [rationalGridTuples,List.length_flatMap,ih,pow_succ,mul_comm]

def rationalAllocationNodes (k : ℕ) (δ : ℚ) :
    List (Fin k → Fin (1+Nat.floor (1/δ))) := rationalGridTuples k (1+Nat.floor (1/δ))

def rationalAnchorAllocation {k : ℕ} (s : Fin k → ℚ) (δ : ℚ)
    (z : Fin k → Fin (1+Nat.floor (1/δ))) : Fin k → ℚ :=
  fun i => s i+δ*(z i : ℕ)

def rationalReservoirAllocation {k : ℕ} (s : Fin k → ℚ) (δ : ℚ) (j : Fin k)
    (z : Fin k → Fin (1+Nat.floor (1/δ))) : Fin k → ℚ :=
  fun i => rationalAnchorAllocation s δ z i+
    if i=j then 1-∑ a, rationalAnchorAllocation s δ z a else 0

theorem rational_allocation_nodes_complete (k : ℕ) (δ : ℚ)
    (z : Fin k → Fin (1+Nat.floor (1/δ))) : z ∈ rationalAllocationNodes k δ := by
  exact rational_grid_tuples_complete _ _ z


theorem rational_reservoir_allocation_mass {k : ℕ} (s : Fin k → ℚ) (δ : ℚ) (j : Fin k)
    (z : Fin k → Fin (1+Nat.floor (1/δ))) :
    (∑ i, rationalReservoirAllocation s δ j z i)=1 := by
  simp only [rationalReservoirAllocation,Finset.sum_add_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  ring

theorem rational_nat_floor_real_cast (x : ℚ) : Nat.floor (x : ℝ)=Nat.floor x := by
  rw [←Int.floor_toNat,←Int.floor_toNat,Rat.floor_cast]

theorem rational_grid_real_index_bound (δ : ℚ) (n : ℕ)
    (h : n < 1+Nat.floor (1/δ)) : n < 1+Nat.floor (1/(δ : ℝ)) := by
  rw [show (1/(δ : ℝ))=((1/δ : ℚ) : ℝ) by push_cast; rfl,
    rational_nat_floor_real_cast]
  exact h

noncomputable def rationalRealGridIndex {k : ℕ} (δ : ℚ)
    (z : Fin k → Fin (1+Nat.floor (1/δ))) : Fin k → Fin (1+Nat.floor (1/(δ : ℝ))) :=
  fun i => ⟨(z i).val,rational_grid_real_index_bound δ _ (z i).isLt⟩

theorem rational_reservoir_allocation_real {k : ℕ} (s : Fin k → ℚ) (δ : ℚ) (j : Fin k)
    (z : Fin k → Fin (1+Nat.floor (1/δ))) :
    (fun i => (rationalReservoirAllocation s δ j z i : ℝ))=
      reservoirGridAllocation (fun i => (s i : ℝ)) (δ : ℝ) j
        (rationalRealGridIndex δ z) := by
  ext i
  by_cases h : i=j
  · simp only [rationalReservoirAllocation,rationalAnchorAllocation,reservoirGridAllocation,
      transferredResidual,h,ite_true,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast,Rat.cast_sub,
      Rat.cast_one,Rat.cast_sum]
    rfl
  · simp only [rationalReservoirAllocation,rationalAnchorAllocation,reservoirGridAllocation,
      transferredResidual,h,ite_false,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast,Rat.cast_zero]
    rfl

end SparseCompletion
