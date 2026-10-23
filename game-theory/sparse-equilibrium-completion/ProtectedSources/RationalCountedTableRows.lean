/- AI-assisted formalization under the repository Apache-2.0 license.
Instrumented rational arithmetic/comparison calls; not bit or machine cost.
Inputs are genuine finite tables. Index/Boolean bookkeeping is outside this ledger. -/
module
public import ProtectedSources.RationalTableOmitted
public import ProtectedSources.RationalCountedAll
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalCountedTableOmitted {k m s : ℕ} (c : RationalTableCertificate k m s)
    (D : Vector (Vector ℚ k) m) (threshold : ℚ) : Bool × ℕ :=
  if k=0 then
    if s < m then (decide (0 ≤ threshold),1) else (true,0)
  else rationalCountedAll fun i : Fin m =>
    if ∀ j : Fin s,c.labels.get j ≠ i then
      let z := rationalCountedFinDot (D.get i).get c.anchors.get
      (decide (z.1 ≤ threshold),z.2+1)
    else (true,0)

def rationalCountedTableRows {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) : Bool × ℕ :=
  let mass := rationalCountedFinDot c.weights.get (fun _ => 1)
  let threshold := σ+M*mass.1
  let anchor := rationalCountedAll fun h : Fin k =>
    let a := rationalCountedFinDot (K.get h).get c.anchors.get
    let b := rationalCountedFinDot (fun j => (D.get (c.labels.get j)).get h) c.weights.get
    (decide (a.1-b.1 ≤ σ),a.2+b.2+((2 : ℕ)))
  let supported := rationalCountedAll fun i : Fin s =>
    let a := rationalCountedFinDot (D.get (c.labels.get i)).get c.anchors.get
    let b := rationalCountedFinDot (c.residual.get i).get c.weights.get
    (decide (a.1+b.1 ≤ σ),a.2+b.2+((2 : ℕ)))
  let omitted := rationalCountedTableOmitted c D threshold
  (anchor.1 && supported.1 && omitted.1,
    mass.2+((2 : ℕ))+anchor.2+supported.2+omitted.2)

theorem rational_counted_table_omitted_value {k m s : ℕ} (c : RationalTableCertificate k m s)
    (D : Vector (Vector ℚ k) m) (threshold : ℚ) :
    (rationalCountedTableOmitted c D threshold).1=true ↔
      ∀ i,(∀ j,c.labels.get j ≠ i) → ∑ h,(D.get i).get h*c.anchors.get h ≤ threshold := by
  by_cases hk : k=0
  · subst k
    simp only [rationalCountedTableOmitted,ite_true,Finset.univ_eq_empty,Finset.sum_empty]
    by_cases hs : s < m
    · simp only [hs,ite_true,decide_eq_true_eq]
      constructor
      · intro ht _ _; exact ht
      · intro hall
        obtain ⟨i,hi⟩ := (rational_table_omitted_exists c).mpr hs
        exact hall i hi
    · simp only [hs,ite_false]
      constructor
      · intro _ i hi
        exact False.elim (hs ((rational_table_omitted_exists c).mp ⟨i,hi⟩))
      · intro _; trivial
  · simp only [rationalCountedTableOmitted,hk,ite_false,rational_counted_all_value]
    constructor
    · intro hall i hi
      have hh := hall i
      simpa only [ite_eq_left hi,rational_counted_fin_dot_value,decide_eq_true_eq] using hh
    · intro hall i
      by_cases hi : ∀ j,c.labels.get j ≠ i
      · simpa only [ite_eq_left hi,rational_counted_fin_dot_value,decide_eq_true_eq] using hall i hi
      · simp only [ite_eq_right hi]

theorem rational_counted_table_rows_value {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalCountedTableRows c K D M σ).1=true ↔ rationalTableRows c K D M σ := by
  simp only [rationalCountedTableRows,Bool.and_eq_true,rational_counted_all_value,
    rational_counted_fin_dot_value,rational_counted_table_omitted_value,decide_eq_true_eq,mul_one]
  unfold rationalTableRows
  constructor
  · rintro ⟨⟨ha,hr⟩,ho⟩
    refine ⟨ha,hr,?_⟩
    intro i hi
    have hh := ho i hi
    linarith
  · rintro ⟨ha,hr,ho⟩
    refine ⟨⟨ha,hr⟩,?_⟩
    intro i hi
    have hh := ho i hi
    linarith

end SparseCompletion
