/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.PiecewiseLinearSlopeCache

/-!
# Linear-size checks for consecutive nonzero witness tails

The actual native witnesses have consecutive stored nodes. Their exact
source binding and cached adjacent differences can therefore be checked
in one pass. The generic proof below identifies this construction with the
sparse nodal-sum definition; it changes no witness or numerical value.
-/

@[expose] public section

namespace ErdosOverlap

def densePLNodes (start : ℕ) : List ℕ → List PLNode
  | [] => []
  | v :: vs => ⟨start, v⟩ :: densePLNodes (start+1) vs

theorem densePLNodes_nodal_before (start : ℕ) (values : List ℕ) (k : ℕ)
    (hk : k < start) : plNodalNumerator (densePLNodes start values) k = 0 := by
  induction values generalizing start with
  | nil => simp [densePLNodes, plNodalNumerator]
  | cons v vs ih =>
      have hne : start ≠ k := by omega
      change (if start = k then v else 0) + plNodalNumerator (densePLNodes (start+1) vs) k = 0
      rw [ite_eq_right hne, zero_add, ih (start+1) (by omega)]

theorem densePLNodes_nodal_at (start : ℕ) (values : List ℕ) (j : ℕ) :
    plNodalNumerator (densePLNodes start values) (start+j) = values.getD j 0 := by
  induction values generalizing start j with
  | nil => simp [densePLNodes, plNodalNumerator]
  | cons v vs ih =>
      cases j with
      | zero =>
          change (if start = start+0 then v else 0) +
            plNodalNumerator (densePLNodes (start+1) vs) (start+0) = _
          rw [ite_eq_left (by omega), densePLNodes_nodal_before (start+1) vs (start+0) (by omega)]
          simp
      | succ j =>
          change (if start = start+(j+1) then v else 0) +
            plNodalNumerator (densePLNodes (start+1) vs) (start+(j+1)) = _
          rw [ite_eq_right (by omega), zero_add,
            show start+(j+1) = (start+1)+j by omega, ih]
          simp

/-- Adjacent differences, including the zero node before and after the tail. -/
def denseDualSlopes (n : ℕ) (tauNumerator : ℤ) (previous : ℕ) : List ℕ → List ℤ
  | [] => [2*tauNumerator + (n : ℤ)*(0-(previous : ℤ))]
  | v :: vs => (2*tauNumerator + (n : ℤ)*((v : ℤ)-(previous : ℤ))) ::
      denseDualSlopes n tauNumerator v vs

theorem denseDualSlopes_length (n : ℕ) (tauNumerator : ℤ) (previous : ℕ)
    (values : List ℕ) :
    (denseDualSlopes n tauNumerator previous values).length = values.length+1 := by
  induction values generalizing previous with
  | nil => rfl
  | cons v vs ih => simp [denseDualSlopes, ih]

theorem denseDualSlopes_getD (n : ℕ) (tauNumerator : ℤ) (previous : ℕ)
    (values : List ℕ) (j : ℕ) (hj : j ≤ values.length) :
    (denseDualSlopes n tauNumerator previous values).getD j 0 =
      2*tauNumerator + (n : ℤ)*((values.getD j 0 : ℤ) -
        (if j = 0 then (previous : ℤ) else (values.getD (j-1) 0 : ℤ))) := by
  induction values generalizing previous j with
  | nil =>
      have hj0 : j = 0 := by simpa using hj
      subst j
      simp [denseDualSlopes]
  | cons v vs ih =>
      cases j with
      | zero => simp [denseDualSlopes]
      | succ j =>
          have hj' : j ≤ vs.length := by simpa using hj
          change (denseDualSlopes n tauNumerator v vs).getD j 0 = _
          rw [ih v j hj']
          cases j <;> simp

theorem plDualNumerator_dense (n first : ℕ) (tauNumerator : ℤ)
    (values : List ℕ) (j : ℕ) (hj : j ≤ values.length) :
    plDualNumerator n (densePLNodes (first+1) values) tauNumerator (first+j) =
      (denseDualSlopes n tauNumerator 0 values).getD j 0 := by
  rw [denseDualSlopes_getD n tauNumerator 0 values j hj]
  unfold plDualNumerator
  rw [show first+j+1 = (first+1)+j by omega, densePLNodes_nodal_at]
  cases j with
  | zero =>
      rw [densePLNodes_nodal_before (first+1) values (first+0) (by omega)]
      simp
  | succ j =>
      rw [show first+(j+1) = (first+1)+j by omega, densePLNodes_nodal_at]
      simp

/-- Two linear-size literal checks imply the full cached sparse-sum check. -/
theorem PLSlopeCache.check_of_dense (cache : PLSlopeCache) (n : ℕ)
    (nodes : List PLNode) (tauNumerator : ℤ) (values : List ℕ)
    (hnodes : nodes = densePLNodes (cache.firstCell+1) values)
    (hslopes : cache.numerators.toList = denseDualSlopes n tauNumerator 0 values) :
    cache.check n nodes tauNumerator = true := by
  have hlen : cache.numerators.size = values.length+1 := by
    rw [← Array.length_toList, hslopes, denseDualSlopes_length]
  apply List.all_eq_true.mpr
  intro j hj
  apply decide_eq_true
  have hj' : j ≤ values.length := by
    have h := List.mem_range.mp hj
    rw [hlen] at h
    omega
  rw [hnodes, plDualNumerator_dense n cache.firstCell tauNumerator values j hj']
  calc
    _ = cache.numerators.toList.getD j 0 := by rw [hslopes]
    _ = cache.numerators.getD j 0 := by simp

end ErdosOverlap
