/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact verification status is retained in external immutable receipts. Executable aggregate event translation of the actual
Gaussian.kernel on an ALREADY MATERIALIZED List.Vector table. Every repeated
source entry invocation executes its own linear list lookup; no pivot row,
column or quotient cache is introduced. Recursive residual tables and returned
vectors are materialized exactly at the original program's boundaries.

The source expression `List.Vector.ofFn (Gaussian.lift ... w.get)` applies lift
once to form its Fin.cons callback. The head expression is the argument to
Fin.cons, outside that callback's indexed body; this adapter computes that
head once, then materializes the vector. This is the declared applicative
source-event convention. It is not an assertion about compiler optimization,
low-level trace order, native cost or operand-bit work. In contrast, the theta
in rationalFeatureDelete is syntactically INSIDE its indexed lambda and is
not covered by this sharing boundary.
-/
module
public import CountedGaussianPrimitives
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def gaussianCountFirstNonzero : (r : ℕ) → (Fin r → FlowCounted ℚ) →
    FlowCounted (Option (Fin r))
  | 0, _ => (none, {adminEvents := 1})
  | r + 1, a =>
    let head := a 0
    if head.1 = 0 then
      let rest := gaussianCountFirstNonzero r (fun i => a i.succ)
      (rest.1.map Fin.succ,
        flowWorkAdd head.2 (flowWorkAdd {rationalEvents := 1, adminEvents := 3} rest.2))
    else (some 0, flowWorkAdd head.2 {rationalEvents := 1, adminEvents := 2})

theorem gaussian_count_first_nonzero_erase (r : ℕ) (a : Fin r → FlowCounted ℚ) :
    (gaussianCountFirstNonzero r a).1 = Gaussian.firstNonzero r (fun i => (a i).1) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    by_cases hz : (a 0).1 = 0 <;>
      simp [gaussianCountFirstNonzero, Gaussian.firstNonzero, hz, ih]

theorem gaussian_count_first_nonzero_bound (r : ℕ) (a : Fin r → FlowCounted ℚ)
    (B : ℕ) (hb : ∀ i, flowWorkTotal (a i).2 ≤ B) :
    flowWorkTotal (gaussianCountFirstNonzero r a).2 ≤ r * (B + 4) + 1 := by
  induction r with
  | zero => simp [gaussianCountFirstNonzero, flowWorkTotal]
  | succ r ih =>
    have hh := hb 0
    by_cases hz : (a 0).1 = 0
    · have ht := ih (fun i => a i.succ) (fun i => hb i.succ)
      simp only [gaussianCountFirstNonzero, hz, ↓reduceIte]
      rw [flow_work_total_add, flow_work_total_add]
      change flowWorkTotal (a 0).2 +
        (4 + flowWorkTotal (gaussianCountFirstNonzero r (fun i => a i.succ)).2) ≤ _
      nlinarith
    · simp only [gaussianCountFirstNonzero, hz, ↓reduceIte]
      rw [flow_work_total_add]
      change flowWorkTotal (a 0).2 + 3 ≤ _
      nlinarith

def gaussianCountResidualCell {r n : ℕ} (A : Gaussian.QTable r (n + 1))
    (p i : Fin r) (j : Fin n) : FlowCounted ℚ :=
  let a := gaussianCountEntry A i j.succ
  let b := gaussianCountEntry A i 0
  let c := gaussianCountEntry A p j.succ
  let e := gaussianCountEntry A p 0
  (a.1 - b.1 * (c.1 / e.1), flowWorkAdd a.2 (flowWorkAdd b.2
    (flowWorkAdd c.2 (flowWorkAdd e.2 {rationalEvents := 3}))))

theorem gaussian_count_residual_cell_erase {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p i : Fin r) (j : Fin n) :
    (gaussianCountResidualCell A p i j).1 = Gaussian.residual (Gaussian.entry A) p i j := by
  simp only [gaussianCountResidualCell, gaussian_count_entry_erase, Gaussian.residual]

theorem gaussian_count_residual_cell_bound {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p i : Fin r) (j : Fin n) :
    flowWorkTotal (gaussianCountResidualCell A p i j).2 ≤ 8 * (r + n + 1) + 3 := by
  have ha := gaussian_count_entry_bound A i j.succ
  have hb := gaussian_count_entry_bound A i 0
  have hc := gaussian_count_entry_bound A p j.succ
  have he := gaussian_count_entry_bound A p 0
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ _)))) ≤ _
  repeat rw [flow_work_total_add]
  change flowWorkTotal (gaussianCountEntry A i j.succ).2 +
    (flowWorkTotal (gaussianCountEntry A i 0).2 +
      (flowWorkTotal (gaussianCountEntry A p j.succ).2 +
        (flowWorkTotal (gaussianCountEntry A p 0).2 + 3))) ≤ _
  omega

def gaussianCountResidualTable {r n : ℕ} (A : Gaussian.QTable r (n + 1))
    (p : Fin r) : FlowCounted (Gaussian.QTable r n) :=
  gaussianCountTableOfFn (gaussianCountResidualCell A p)

theorem gaussian_count_residual_table_erase {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p : Fin r) :
    (gaussianCountResidualTable A p).1 = Gaussian.tableOfFn (Gaussian.residual (Gaussian.entry A) p) := by
  simp only [gaussianCountResidualTable, gaussian_count_table_ofFn_erase,
    gaussian_count_residual_cell_erase]

theorem gaussian_count_residual_table_bound {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p : Fin r) :
    flowWorkTotal (gaussianCountResidualTable A p).2 ≤
      r * (n * (8 * (r + n + 1) + 5) + 4) + 2 := by
  exact gaussian_count_table_ofFn_bound _ (8 * (r + n + 1) + 3)
    (gaussian_count_residual_cell_bound A p)

def gaussianCountLiftTerm {r n : ℕ} (A : Gaussian.QTable r (n + 1))
    (p : Fin r) (w : Gaussian.QVec n) (j : Fin n) : FlowCounted ℚ :=
  let a := gaussianCountEntry A p j.succ
  let b := gaussianCountEntry A p 0
  let c := gaussianCountVectorGet w j
  ((a.1 / b.1) * c.1,
    flowWorkAdd a.2 (flowWorkAdd b.2 (flowWorkAdd c.2 {rationalEvents := 2})))

theorem gaussian_count_lift_term_erase {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p : Fin r) (w : Gaussian.QVec n) (j : Fin n) :
    (gaussianCountLiftTerm A p w j).1 =
      (Gaussian.entry A p j.succ / Gaussian.entry A p 0) * w.get j := by
  simp only [gaussianCountLiftTerm, gaussian_count_entry_erase, gaussian_count_vector_get_erase]

theorem gaussian_count_lift_term_bound {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p : Fin r) (w : Gaussian.QVec n) (j : Fin n) :
    flowWorkTotal (gaussianCountLiftTerm A p w j).2 ≤ 6 * (r + n + 1) + 2 := by
  have ha := gaussian_count_entry_bound A p j.succ
  have hb := gaussian_count_entry_bound A p 0
  have hc := gaussian_count_vector_get_bound w j
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ (flowWorkAdd _ _))) ≤ _
  repeat rw [flow_work_total_add]
  change flowWorkTotal (gaussianCountEntry A p j.succ).2 +
    (flowWorkTotal (gaussianCountEntry A p 0).2 +
      (flowWorkTotal (gaussianCountVectorGet w j).2 + 2)) ≤ _
  omega

def gaussianCountLiftVector {r n : ℕ} (A : Gaussian.QTable r (n + 1))
    (p : Fin r) (w : Gaussian.QVec n) : FlowCounted (Gaussian.QVec (n + 1)) :=
  let total := gaussianCountFiniteSum (gaussianCountLiftTerm A p w)
  let head := -total.1
  let vector := gaussianCountVectorOfFn (Fin.cases
    (head, ({adminEvents := 1} : FlowWork))
    (fun j =>
      let cell := gaussianCountVectorGet w j
      (cell.1, flowWorkAdd cell.2 {adminEvents := 1})))
  (vector.1, flowWorkAdd total.2 (flowWorkAdd {rationalEvents := 1} vector.2))

theorem gaussian_count_lift_vector_erase {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p : Fin r) (w : Gaussian.QVec n) :
    (gaussianCountLiftVector A p w).1 =
      List.Vector.ofFn (Gaussian.lift (Gaussian.entry A) p w.get) := by
  simp only [gaussianCountLiftVector, gaussian_count_vector_ofFn_erase]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [gaussian_count_finite_sum_erase, gaussian_count_lift_term_erase, Gaussian.lift]
  · simp [gaussian_count_vector_get_erase, Gaussian.lift]

theorem gaussian_count_lift_vector_bound {r n : ℕ}
    (A : Gaussian.QTable r (n + 1)) (p : Fin r) (w : Gaussian.QVec n) :
    flowWorkTotal (gaussianCountLiftVector A p w).2 ≤ 32 * (r + n + 2) ^ 2 := by
  have hs := gaussian_count_finite_sum_bound (gaussianCountLiftTerm A p w)
    (6 * (r + n + 1) + 2) (gaussian_count_lift_term_bound A p w)
  let f : Fin (n + 1) → FlowCounted ℚ := Fin.cases
    (-(gaussianCountFiniteSum (gaussianCountLiftTerm A p w)).1, ({adminEvents := 1} : FlowWork))
    (fun j =>
      let cell := gaussianCountVectorGet w j
      (cell.1, flowWorkAdd cell.2 {adminEvents := 1}))
  have hf : ∀ j, flowWorkTotal (f j).2 ≤ 2 * n + 1 := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change 1 ≤ 2 * n + 1
      omega
    · have hc := gaussian_count_vector_get_bound w j
      change flowWorkTotal (flowWorkAdd _ _) ≤ _
      rw [flow_work_total_add]
      change flowWorkTotal (gaussianCountVectorGet w j).2 + 1 ≤ _
      omega
  have hv := gaussian_count_vector_ofFn_bound f (2 * n + 1) hf
  change flowWorkTotal (flowWorkAdd _ (flowWorkAdd _ (gaussianCountVectorOfFn f).2)) ≤ _
  rw [flow_work_total_add, flow_work_total_add]
  change flowWorkTotal (gaussianCountFiniteSum (gaussianCountLiftTerm A p w)).2 +
    (1 + flowWorkTotal (gaussianCountVectorOfFn f).2) ≤ _
  nlinarith [Nat.zero_le (r ^ 2), Nat.zero_le (n ^ 2), Nat.zero_le (r * n)]

/-- Exact source recursion: one pivot scan, materialized residual, recursive
call on one fewer column, and an output lift only on actual success. -/
def gaussianCountKernel (r : ℕ) : (n : ℕ) → Gaussian.QTable r n →
    FlowCounted (Option (Gaussian.QVec n))
  | 0, _ => (none, {adminEvents := 1})
  | n + 1, A =>
    let pivot := gaussianCountFirstNonzero r (fun i => gaussianCountEntry A i 0)
    match pivot.1 with
    | none =>
      let out := gaussianCountVectorOfFn
        (fun j : Fin (n + 1) => (Fin.cons 1 (fun _ => 0) j, {adminEvents := 1}))
      (some out.1, flowWorkAdd pivot.2 (flowWorkAdd out.2 {adminEvents := 2}))
    | some p =>
      let residual := gaussianCountResidualTable A p
      let tail := gaussianCountKernel r n residual.1
      match tail.1 with
      | none => (none, flowWorkAdd pivot.2
          (flowWorkAdd residual.2 (flowWorkAdd tail.2 {adminEvents := 3})))
      | some w =>
        let out := gaussianCountLiftVector A p w
        (some out.1, flowWorkAdd pivot.2 (flowWorkAdd residual.2
          (flowWorkAdd tail.2 (flowWorkAdd out.2 {adminEvents := 3}))))

theorem gaussian_count_kernel_erase (r n : ℕ) (A : Gaussian.QTable r n) :
    (gaussianCountKernel r n A).1 = Gaussian.kernel r n A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hp : Gaussian.firstNonzero r (fun i => Gaussian.entry A i 0) with
    | none =>
      simp [gaussianCountKernel, gaussian_count_first_nonzero_erase,
        gaussian_count_entry_erase, hp, gaussian_count_vector_ofFn_erase, Gaussian.kernel]
    | some p =>
      cases ht : Gaussian.kernel r n (Gaussian.tableOfFn (Gaussian.residual (Gaussian.entry A) p)) with
      | none =>
        simp [gaussianCountKernel, gaussian_count_first_nonzero_erase,
          gaussian_count_entry_erase, hp, gaussian_count_residual_table_erase, ih, ht, Gaussian.kernel]
      | some w =>
        simp [gaussianCountKernel, gaussian_count_first_nonzero_erase,
          gaussian_count_entry_erase, hp, gaussian_count_residual_table_erase, ih, ht,
          gaussian_count_lift_vector_erase, Gaussian.kernel]

/-- The actual callback budgets below are derived from materialized list
lookup and the proved primitive bounds; no counter/budget is a program input. -/
theorem gaussian_count_kernel_bound (r n : ℕ) (A : Gaussian.QTable r n) :
    flowWorkTotal (gaussianCountKernel r n A).2 ≤
      (n + 1) * (128 * (r + n + 2) ^ 3) := by
  induction n with
  | zero =>
    change 1 ≤ (0 + 1) * (128 * (r + 0 + 2) ^ 3)
    nlinarith [Nat.zero_le (r ^ 2), Nat.zero_le (r ^ 3)]
  | succ n ih =>
    have hp := gaussian_count_first_nonzero_bound r (fun i => gaussianCountEntry A i 0)
      (2 * (r + (n + 1))) (fun i => gaussian_count_entry_bound A i 0)
    cases he : (gaussianCountFirstNonzero r (fun i => gaussianCountEntry A i 0)).1 with
    | none =>
      have hv := gaussian_count_vector_ofFn_bound
        (fun j : Fin (n + 1) => (Fin.cons (1 : ℚ) (fun _ => 0) j, ({adminEvents := 1} : FlowWork)))
        1 (fun _ => le_rfl)
      simp only [gaussianCountKernel, he]
      repeat rw [flow_work_total_add]
      change flowWorkTotal (gaussianCountFirstNonzero r (fun i => gaussianCountEntry A i 0)).2 +
        (flowWorkTotal (gaussianCountVectorOfFn _).2 + 2) ≤ _
      have hfactor : 128 * (r + (n + 1) + 2) ^ 3 ≤
          (n + 1 + 1) * (128 * (r + (n + 1) + 2) ^ 3) := by
        simpa only [Nat.one_mul] using
          Nat.mul_le_mul_right (128 * (r + (n + 1) + 2) ^ 3)
            (show 1 ≤ n + 1 + 1 by omega)
      apply le_trans _ hfactor
      nlinarith only [hp, hv, Nat.zero_le r, Nat.zero_le n,
        Nat.zero_le (r ^ 2), Nat.zero_le (n ^ 2), Nat.zero_le (r * n),
        Nat.zero_le (r ^ 3), Nat.zero_le (n ^ 3),
        Nat.zero_le (r ^ 2 * n), Nat.zero_le (r * n ^ 2)]
    | some p =>
      have hr := gaussian_count_residual_table_bound A p
      have ht := ih (gaussianCountResidualTable A p).1
      have hpow : (r + n + 2) ^ 3 ≤ (r + (n + 1) + 2) ^ 3 :=
        Nat.pow_le_pow_left (by omega) 3
      have ht' : flowWorkTotal (gaussianCountKernel r n (gaussianCountResidualTable A p).1).2 ≤
          (n + 1) * (128 * (r + (n + 1) + 2) ^ 3) := by
        exact le_trans ht (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow))
      cases ho : (gaussianCountKernel r n (gaussianCountResidualTable A p).1).1 with
      | none =>
        simp only [gaussianCountKernel, he, ho]
        repeat rw [flow_work_total_add]
        change flowWorkTotal (gaussianCountFirstNonzero r (fun i => gaussianCountEntry A i 0)).2 +
          (flowWorkTotal (gaussianCountResidualTable A p).2 +
            (flowWorkTotal (gaussianCountKernel r n (gaussianCountResidualTable A p).1).2 + 3)) ≤ _
        nlinarith [Nat.zero_le (r ^ 3), Nat.zero_le (n ^ 3), Nat.zero_le (r ^ 2 * n), Nat.zero_le (r * n ^ 2)]
      | some w =>
        have hl := gaussian_count_lift_vector_bound A p w
        simp only [gaussianCountKernel, he, ho]
        repeat rw [flow_work_total_add]
        change flowWorkTotal (gaussianCountFirstNonzero r (fun i => gaussianCountEntry A i 0)).2 +
          (flowWorkTotal (gaussianCountResidualTable A p).2 +
            (flowWorkTotal (gaussianCountKernel r n (gaussianCountResidualTable A p).1).2 +
              (flowWorkTotal (gaussianCountLiftVector A p w).2 + 3))) ≤ _
        nlinarith [Nat.zero_le (r ^ 3), Nat.zero_le (n ^ 3), Nat.zero_le (r ^ 2 * n), Nat.zero_le (r * n ^ 2)]

theorem gaussian_count_kernel_quartic_bound (r n : ℕ) (A : Gaussian.QTable r n) :
    flowWorkTotal (gaussianCountKernel r n A).2 ≤ 128 * (r + n + 2) ^ 4 := by
  have hb := gaussian_count_kernel_bound r n A
  calc
    _ ≤ (n + 1) * (128 * (r + n + 2) ^ 3) := hb
    _ ≤ (r + n + 2) * (128 * (r + n + 2) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end SparseCompletion
