/- AI-assisted Gaussian global-height continuation; Apache-2.0.
Exact check status is recorded in source-bound receipts outside this source.
The original uncompiled v1 draft is preserved in source-global-height-v1.
Frozen Gaussian kernel APIs are unchanged. No bit-cost or general LP claim.
-/
module
public import ProtectedSources.GaussianScale
public import ProtectedSources.GaussianSchurSylvester
public import Mathlib.Logic.Equiv.Sum
@[expose] public section
open scoped BigOperators Matrix
namespace SparseCompletion.Gaussian

def appendMap {ι α : Type*} (P : ι → α) (p : α) : ι ⊕ Unit → α :=
  Sum.elim P (fun _ => p)

def selectedBlock {r N : ℕ} {ι : Type*}
    (Z : Fin r → Fin N → ℚ) (P : ι → Fin r) (Q : ι → Fin N) : Matrix ι ι ℚ :=
  Matrix.submatrix Z P Q

def selectedBorder {r N : ℕ} {ι : Type*}
    (Z : Fin r → Fin N → ℚ) (P : ι → Fin r) (Q : ι → Fin N)
    (i : Fin r) (j : Fin N) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℚ :=
  Matrix.submatrix Z (appendMap P i) (appendMap Q j)

def unitSumFinTwo : Unit ⊕ Unit ≃ Fin 2 where
  toFun := Sum.elim (fun _ => 0) (fun _ => 1)
  invFun j := if j = 0 then Sum.inl () else Sum.inr ()
  left_inv x := by rcases x with u | u <;> cases u <;> rfl
  right_inv j := by fin_cases j <;> rfl

def appendTwoEquiv (ι : Type*) : ((ι ⊕ Unit) ⊕ Unit) ≃ ι ⊕ Fin 2 :=
  (Equiv.sumAssoc ι Unit Unit).trans
    (Equiv.sumCongr (Equiv.refl ι) unitSumFinTwo)

/-- Concrete selected-row/column Sylvester identity. hC is a usual local
linear-algebra premise; the subsequent actual-stage induction earns hC from
the program's earlier nonzero pivot, rather than receiving it from a caller. -/
theorem selectedBorder_sylvester {r N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Z : Fin r → Fin N → ℚ)
    (P : ι → Fin r) (Q : ι → Fin N) (p i : Fin r) (q j : Fin N)
    (hC : (selectedBlock Z P Q).det ≠ 0) :
    (selectedBorder Z P Q p q).det * (selectedBorder Z P Q i j).det -
      (selectedBorder Z P Q i q).det * (selectedBorder Z P Q p j).det =
      (selectedBlock Z P Q).det *
        (selectedBorder Z (appendMap P p) (appendMap Q q) i j).det := by
  classical
  let C := selectedBlock Z P Q
  let B : Matrix ι (Fin 2) ℚ := fun x t => Z (P x) (if t = 0 then q else j)
  let R : Matrix (Fin 2) ι ℚ := fun t y => Z (if t = 0 then p else i) (Q y)
  let D : Matrix (Fin 2) (Fin 2) ℚ :=
    fun s t => Z (if s = 0 then p else i) (if t = 0 then q else j)
  let _ : Invertible C := Matrix.invertibleOfIsUnitDet (A := C)
    (isUnit_iff_ne_zero.mpr hC)
  have h00 : oneBorder C B R D 0 0 = selectedBorder Z P Q p q := by
    ext x y
    rcases x with x | u <;> rcases y with y | v <;> rfl
  have h01 : oneBorder C B R D 0 1 = selectedBorder Z P Q p j := by
    ext x y
    rcases x with x | u <;> rcases y with y | v <;> rfl
  have h10 : oneBorder C B R D 1 0 = selectedBorder Z P Q i q := by
    ext x y
    rcases x with x | u <;> rcases y with y | v <;> rfl
  have h11 : oneBorder C B R D 1 1 = selectedBorder Z P Q i j := by
    ext x y
    rcases x with x | u <;> rcases y with y | v <;> rfl
  have hmatrix :
      (selectedBorder Z (appendMap P p) (appendMap Q q) i j).submatrix
        (appendTwoEquiv ι).symm (appendTwoEquiv ι).symm =
      Matrix.fromBlocks C B R D := by
    ext x y
    rcases x with x | x
    · rcases y with y | y
      · rfl
      · fin_cases y <;> rfl
    · rcases y with y | y
      · fin_cases x <;> rfl
      · fin_cases x <;> fin_cases y <;> rfl
  have hdet : (Matrix.fromBlocks C B R D).det =
      (selectedBorder Z (appendMap P p) (appendMap Q q) i j).det := by
    rw [← hmatrix, Matrix.det_submatrix_equiv_self]
  simpa only [h00, h01, h10, h11, hdet] using twoBorder_sylvester C B R D

@[reducible] def PrefixIndex : ℕ → Type
  | 0 => PEmpty
  | k+1 => PrefixIndex k ⊕ Unit

instance prefixIndexFintype : (k : ℕ) → Fintype (PrefixIndex k)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | k+1 => by
      change Fintype (PrefixIndex k ⊕ Unit)
      letI : Fintype (PrefixIndex k) := prefixIndexFintype k
      infer_instance

instance prefixIndexDecidableEq : (k : ℕ) → DecidableEq (PrefixIndex k)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | k+1 => by
      change DecidableEq (PrefixIndex k ⊕ Unit)
      letI : DecidableEq (PrefixIndex k) := prefixIndexDecidableEq k
      infer_instance

instance prefixIndexZeroIsEmpty : IsEmpty (PrefixIndex 0) := ⟨PEmpty.elim⟩

theorem prefixIndex_card (k : ℕ) : Fintype.card (PrefixIndex k) = k := by
  induction k with
  | zero => exact Fintype.card_ofIsEmpty
  | succ k ih =>
      simpa only [PrefixIndex, Fintype.card_sum, Fintype.card_unit] using
        (congrArg (fun n : ℕ => n+1) ih)

/-- Ordered operational stages with the actual remaining-column labels. Each
step selects the program's actual pivot row and removes the actual first
column; no minor/rank/height conclusion occurs in the constructor data. -/
inductive MinorStage {r N : ℕ} (A : QTable r N) :
    (k n : ℕ) → (PrefixIndex k → Fin r) → (PrefixIndex k → Fin N) →
      (Fin n → Fin N) → QTable r n → Prop
  | initial : MinorStage A 0 N PEmpty.elim PEmpty.elim id A
  | step {k n : ℕ} {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
      {σ : Fin (n+1) → Fin N} {B : QTable r (n+1)}
      (previous : MinorStage A k (n+1) P Q σ B) (p : Fin r)
      (pivot : firstNonzero r (fun i => entry B i 0) = some p) :
      MinorStage A (k+1) n (appendMap P p) (appendMap Q (σ 0))
        (fun j => σ j.succ) (tableOfFn (residual (entry B) p))

/-- Global invariant for actual reachable stages, including the
initial empty minor. It supplies both nonzero prefix determinants and actual
entry formulas from only real program-step equations. No kernel/minor oracle
or externally supplied invariant is a hypothesis. Check status is recorded in exact-source receipts. -/
theorem minorStage_invariant {r N k n : ℕ} {A : QTable r N}
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage A k n P Q σ B) :
    (selectedBlock (entry A) P Q).det ≠ 0 ∧
      ∀ i j, entry B i j = (selectedBorder (entry A) P Q i (σ j)).det /
        (selectedBlock (entry A) P Q).det := by
  classical
  induction h with
  | initial =>
    let _ : Unique (PrefixIndex 0 ⊕ Unit) :=
      { default := Sum.inr ()
        uniq := by
          intro x
          rcases x with x | u
          · exact PEmpty.elim x
          · cases u
            rfl }
    have h0 : (selectedBlock (entry A)
        (PEmpty.elim : PrefixIndex 0 → Fin r)
        (PEmpty.elim : PrefixIndex 0 → Fin N)).det = 1 := Matrix.det_isEmpty
    constructor
    · rw [h0]
      exact one_ne_zero
    · intro i j
      rw [h0, div_one]
      symm
      exact (Matrix.det_unique (selectedBorder (entry A)
        (PEmpty.elim : PrefixIndex 0 → Fin r)
        (PEmpty.elim : PrefixIndex 0 → Fin N) i j)).trans rfl
  | @step k n P Q σ B previous p hp ih =>
    rcases ih with ⟨hC, hentry⟩
    have hp0 := firstNonzero_some r (fun i => entry B i 0) p hp
    have hnew : (selectedBorder (entry A) P Q p (σ 0)).det ≠ 0 := by
      intro hz
      apply hp0
      rw [hentry p 0, hz, zero_div]
    refine ⟨hnew, ?_⟩
    intro i j
    simp only [entry_tableOfFn, residual]
    rw [hentry i j.succ, hentry i 0, hentry p j.succ, hentry p 0]
    exact residual_shared_minor_step _ _ _ _ _ _ hnew hC
      (selectedBorder_sylvester (entry A) P Q p i (σ 0) (σ j.succ) hC)

/-- General finite-index wrapper around the CHECKED Fin-index quotient bound.
The equivalences occur only in this proof, not in the actual kernel program. -/
theorem minor_quotient_height_any {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι ℤ) (V : Matrix κ κ ℤ) (H : ℕ)
    (hU : ∀ i j, (U i j).natAbs ≤ H) (hV : ∀ i j, (V i j).natAbs ≤ H)
    (hv : V.det ≠ 0) :
    (((U.det : ℚ) / (V.det : ℚ)).num.natAbs ≤
      (Fintype.card ι).factorial * H^(Fintype.card ι)) ∧
    (((U.det : ℚ) / (V.det : ℚ)).den ≤
      (Fintype.card κ).factorial * H^(Fintype.card κ)) := by
  classical
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let eκ : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hdU : (U.submatrix eι eι).det = U.det := Matrix.det_submatrix_equiv_self eι U
  have hdV : (V.submatrix eκ eκ).det = V.det := Matrix.det_submatrix_equiv_self eκ V
  have hb := minor_quotient_height (U.submatrix eι eι) (V.submatrix eκ eκ) H
    (fun i j => hU (eι i) (eι j)) (fun i j => hV (eκ i) (eκ j))
    (by simpa only [hdV] using hv)
  simpa only [hdU, hdV] using hb

theorem intCast_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) :
    Matrix.det (fun i j => (M i j : ℚ)) = (M.det : ℚ) := by
  exact ((Int.castRingHom ℚ).map_det M).symm

/-- Actual stage encoding bound. The input hypothesis is only bounded
integer entries plus an operational trace made from actual program equations.
The minor representation is derived by minorStage_invariant above; no minor
witness, height field, or desired conclusion is assumed. -/
theorem minorStage_integer_height {r N k n : ℕ}
    (Z : Fin r → Fin N → ℤ) (H : ℕ) (hZ : ∀ i j, (Z i j).natAbs ≤ H)
    {P : PrefixIndex k → Fin r} {Q : PrefixIndex k → Fin N}
    {σ : Fin n → Fin N} {B : QTable r n}
    (h : MinorStage (tableOfFn (fun i j => (Z i j : ℚ))) k n P Q σ B) :
    ∀ i j, (entry B i j).num.natAbs ≤ (k+1).factorial * H^(k+1) ∧
      (entry B i j).den ≤ k.factorial * H^k := by
  classical
  intro i j
  let V : Matrix (PrefixIndex k) (PrefixIndex k) ℤ := Matrix.submatrix Z P Q
  let U : Matrix (PrefixIndex k ⊕ Unit) (PrefixIndex k ⊕ Unit) ℤ :=
    Matrix.submatrix Z (appendMap P i) (appendMap Q (σ j))
  have hdV :
      (selectedBlock (entry (tableOfFn (fun i j => (Z i j : ℚ)))) P Q).det =
        (V.det : ℚ) := by
    rw [entry_tableOfFn_function]
    change Matrix.det (fun a b => (V a b : ℚ)) = (V.det : ℚ)
    exact intCast_det V
  have hdU :
      (selectedBorder (entry (tableOfFn (fun i j => (Z i j : ℚ)))) P Q i (σ j)).det =
        (U.det : ℚ) := by
    rw [entry_tableOfFn_function]
    change Matrix.det (fun a b => (U a b : ℚ)) = (U.det : ℚ)
    exact intCast_det U
  have hinv := minorStage_invariant h
  have hv : V.det ≠ 0 := by
    intro hz
    apply hinv.1
    rw [hdV, hz, Int.cast_zero]
  have he : entry B i j = (U.det : ℚ) / (V.det : ℚ) := by
    simpa only [hdU, hdV] using hinv.2 i j
  have hb := minor_quotient_height_any U V H
    (fun a b => hZ (appendMap P i a) (appendMap Q (σ j) b))
    (fun a b => hZ (P a) (Q b)) hv
  rw [he]
  simpa only [Fintype.card_sum, Fintype.card_unit, prefixIndex_card] using hb

/- Source continuation is now in GaussianTerminalTrace and GaussianCramerOutput:
real success extends this operational trace to its real dependent-column stop;
the selected original-row system then supplies actual returned-coordinate
Cramer bounds. Compilation evidence is recorded in source-bound receipts. These results
do not supply an executable bit-complexity bound. -/

end SparseCompletion.Gaussian
