/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.Integer
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Exact sparse assembly of triangle multipliers

Finite vector updates provide an efficient integer evaluator. Its entries are
proved equal to the sum of the signed triangle contributions. Concrete data
can therefore be bound to their actual multipliers by kernel evaluation of a
single vector equality, without expanding every zero contribution separately.
-/

@[expose] public section

namespace ErdosOverlap.Gram

abbrev IntMatrix (n : ℕ) := Vector (Vector ℤ n) n

def matrixEntry {n : ℕ} (M : IntMatrix n) (i j : Fin n) : ℤ := M[i.val][j.val]

def addEntry {n : ℕ} (M : IntMatrix n) (i j : Fin n) (z : ℤ) : IntMatrix n :=
  M.set i.val ((M[i.val]).set j.val (M[i.val][j.val] + z))

theorem addEntry_apply {n : ℕ} (M : IntMatrix n) (i j p q : Fin n) (z : ℤ) :
    matrixEntry (addEntry M i j z) p q =
      matrixEntry M p q + (if p = i ∧ q = j then z else 0) := by
  simp only [matrixEntry, addEntry, Vector.getElem_set]
  by_cases hpi : p = i
  · subst p
    by_cases hqj : q = j
    · subst q
      simp
    · have hval : j.val ≠ q.val := by
        intro h
        exact hqj (Fin.ext h.symm)
      simp [hval, hqj]
  · have hval : i.val ≠ p.val := by
      intro h
      exact hpi (Fin.ext h.symm)
    simp [hval, hpi]

structure Triangle (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  s0 : ℤ
  s1 : ℤ
  s2 : ℤ
  weight : ℤ
  deriving DecidableEq, Repr

def Triangle.Valid {n : ℕ} (t : Triangle n) : Prop :=
  t.i < t.j ∧ t.j < t.k ∧ 0 ≤ t.weight ∧
    ((t.s0 = 1 ∧ t.s1 = 1 ∧ t.s2 = -1) ∨
      (t.s0 = 1 ∧ t.s1 = -1 ∧ t.s2 = 1) ∨
      (t.s0 = -1 ∧ t.s1 = 1 ∧ t.s2 = 1) ∨
      (t.s0 = -1 ∧ t.s1 = -1 ∧ t.s2 = -1))

instance {n : ℕ} (t : Triangle n) : Decidable t.Valid :=
  inferInstanceAs (Decidable (t.i < t.j ∧ t.j < t.k ∧ 0 ≤ t.weight ∧
    ((t.s0 = 1 ∧ t.s1 = 1 ∧ t.s2 = -1) ∨
      (t.s0 = 1 ∧ t.s1 = -1 ∧ t.s2 = 1) ∨
      (t.s0 = -1 ∧ t.s1 = 1 ∧ t.s2 = 1) ∨
      (t.s0 = -1 ∧ t.s1 = -1 ∧ t.s2 = -1))))

def pairIndicator {n : ℕ} (i j p q : Fin n) : ℤ :=
  (if p = i ∧ q = j then 1 else 0) + (if p = j ∧ q = i then 1 else 0)

def Triangle.coefficient {n : ℕ} (t : Triangle n) (p q : Fin n) : ℤ :=
  t.weight * (t.s0 * pairIndicator t.i t.j p q +
    t.s1 * pairIndicator t.j t.k p q + t.s2 * pairIndicator t.i t.k p q)

def addTriangle {n : ℕ} (M : IntMatrix n) (t : Triangle n) : IntMatrix n :=
  let M := addEntry M t.i t.j (t.weight * t.s0)
  let M := addEntry M t.j t.i (t.weight * t.s0)
  let M := addEntry M t.j t.k (t.weight * t.s1)
  let M := addEntry M t.k t.j (t.weight * t.s1)
  let M := addEntry M t.i t.k (t.weight * t.s2)
  addEntry M t.k t.i (t.weight * t.s2)

theorem addTriangle_apply {n : ℕ} (M : IntMatrix n) (t : Triangle n) (p q : Fin n) :
    matrixEntry (addTriangle M t) p q = matrixEntry M p q + t.coefficient p q := by
  simp only [addTriangle, addEntry_apply, Triangle.coefficient, pairIndicator]
  split_ifs <;> ring

theorem foldTriangles_apply {n : ℕ} (ts : List (Triangle n)) (M : IntMatrix n)
    (p q : Fin n) :
    matrixEntry (ts.foldl addTriangle M) p q =
      matrixEntry M p q + (ts.map (fun t => t.coefficient p q)).sum := by
  induction ts generalizing M with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, addTriangle_apply]
    simp [add_assoc]

def triangleAggregate {n : ℕ} (ts : List (Triangle n)) : IntMatrix n :=
  ts.foldl addTriangle (Vector.replicate n (Vector.replicate n 0))

theorem triangleAggregate_apply {n : ℕ} (ts : List (Triangle n)) (p q : Fin n) :
    matrixEntry (triangleAggregate ts) p q =
      (ts.map (fun t => t.coefficient p q)).sum := by
  rw [triangleAggregate, foldTriangles_apply]
  simp [matrixEntry]

/-- One-row evaluation keeps every concrete assembly check bounded in memory. -/
def addRowEntry {n : ℕ} (v : Vector ℤ n) (row i j : Fin n) (z : ℤ) : Vector ℤ n :=
  if row = i then v.set j.val (v[j.val] + z) else v

theorem addRowEntry_apply {n : ℕ} (v : Vector ℤ n) (row i j q : Fin n) (z : ℤ) :
    (addRowEntry v row i j z)[q.val] =
      v[q.val] + (if row = i ∧ q = j then z else 0) := by
  by_cases hri : row = i
  · by_cases hqj : q = j
    · subst q
      simp [addRowEntry, hri]
    · have hval : j.val ≠ q.val := by
        intro h
        exact hqj (Fin.ext h.symm)
      simp [addRowEntry, hri, hqj, hval]
  · simp [addRowEntry, hri]

def addTriangleRow {n : ℕ} (row : Fin n) (v : Vector ℤ n) (t : Triangle n) : Vector ℤ n :=
  let v := addRowEntry v row t.i t.j (t.weight * t.s0)
  let v := addRowEntry v row t.j t.i (t.weight * t.s0)
  let v := addRowEntry v row t.j t.k (t.weight * t.s1)
  let v := addRowEntry v row t.k t.j (t.weight * t.s1)
  let v := addRowEntry v row t.i t.k (t.weight * t.s2)
  addRowEntry v row t.k t.i (t.weight * t.s2)

theorem addTriangleRow_apply {n : ℕ} (row : Fin n) (v : Vector ℤ n)
    (t : Triangle n) (q : Fin n) :
    (addTriangleRow row v t)[q.val] = v[q.val] + t.coefficient row q := by
  simp only [addTriangleRow, addRowEntry_apply, Triangle.coefficient, pairIndicator]
  split_ifs <;> ring

theorem foldTriangleRows_apply {n : ℕ} (row : Fin n) (ts : List (Triangle n))
    (v : Vector ℤ n) (q : Fin n) :
    (ts.foldl (addTriangleRow row) v)[q.val] =
      v[q.val] + (ts.map (fun t => t.coefficient row q)).sum := by
  induction ts generalizing v with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, addTriangleRow_apply]
    simp [add_assoc]

def triangleRowAggregate {n : ℕ} (row : Fin n) (ts : List (Triangle n)) : Vector ℤ n :=
  ts.foldl (addTriangleRow row) (Vector.replicate n 0)

theorem triangleRowAggregate_apply {n : ℕ} (row : Fin n) (ts : List (Triangle n))
    (q : Fin n) :
    (triangleRowAggregate row ts)[q.val] = (ts.map (fun t => t.coefficient row q)).sum := by
  rw [triangleRowAggregate, foldTriangleRows_apply]
  simp

theorem triangleAggregate_eq_of_rows {n : ℕ} (ts : List (Triangle n)) (M : IntMatrix n)
    (hrows : ∀ row : Fin n, triangleRowAggregate row ts = M[row.val]) :
    triangleAggregate ts = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let p : Fin n := ⟨i, hi⟩
  let q : Fin n := ⟨j, hj⟩
  change matrixEntry (triangleAggregate ts) p q = matrixEntry M p q
  rw [triangleAggregate_apply, ← triangleRowAggregate_apply p ts q]
  rw [hrows p]
  rfl

end ErdosOverlap.Gram
