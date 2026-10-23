/- AI-assisted formalization; Apache-2.0, following the parent repository.
Strict module compilation and artifact evidence are retained in attempts/.
No verified polynomial-cost claim.
The program uses rational arithmetic, deterministic finite pivot search, and
materialized finite lists. Classical choice is not used in any definition.
These correctness proofs concern the actual deterministic table algorithm.
-/
module
public import Mathlib.Data.Vector.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic
@[expose] public section
open scoped BigOperators
namespace SparseCompletion.Gaussian

abbrev QVec (n : ℕ) := List.Vector ℚ n
abbrev QTable (r n : ℕ) := List.Vector (QVec n) r

@[simp] theorem vecGet_ofFn {n : ℕ} (f : Fin n → ℚ) :
    (List.Vector.ofFn f).get = f := by
  funext i
  simp

def tableOfFn {r n : ℕ} (A : Fin r → Fin n → ℚ) : QTable r n :=
  List.Vector.ofFn (fun i => List.Vector.ofFn (A i))

def entry {r n : ℕ} (A : QTable r n) (i : Fin r) (j : Fin n) : ℚ :=
  (A.get i).get j

@[simp] theorem entry_tableOfFn {r n : ℕ} (A : Fin r → Fin n → ℚ)
    (i : Fin r) (j : Fin n) : entry (tableOfFn A) i j = A i j := by
  simp [entry, tableOfFn]

@[simp] theorem entry_tableOfFn_function {r n : ℕ} (A : Fin r → Fin n → ℚ) :
    entry (tableOfFn A) = A := by
  funext i j
  exact entry_tableOfFn A i j

def dot {n : ℕ} (a x : Fin n → ℚ) : ℚ := ∑ j, a j * x j

def IsKernel {r n : ℕ} (A : QTable r n) (x : Fin n → ℚ) : Prop :=
  ∀ i, dot (entry A i) x = 0

/-- First nonzero coordinate, in Fin's natural order, by structural recursion.
This does not call an existential decider or a noncomputable finite selector. -/
def firstNonzero : (r : ℕ) → (Fin r → ℚ) → Option (Fin r)
  | 0, _ => none
  | r+1, a => if a 0 = 0 then
      (firstNonzero r (fun i => a i.succ)).map Fin.succ
    else some 0

theorem firstNonzero_none (r : ℕ) (a : Fin r → ℚ) :
    firstNonzero r a = none ↔ ∀ i, a i = 0 := by
  induction r with
  | zero => simp [firstNonzero]
  | succ r ih =>
    by_cases h : a 0 = 0
    · simp only [firstNonzero, h, ↓reduceIte, Option.map_eq_none_iff, ih]
      constructor
      · intro ht i
        refine Fin.cases h (fun j => ht j) i
      · intro ht j
        exact ht j.succ
    · simp only [firstNonzero, h, ↓reduceIte, Option.some_ne_none, false_iff]
      intro ht
      exact h (ht 0)

theorem firstNonzero_some (r : ℕ) (a : Fin r → ℚ) (p : Fin r)
    (h : firstNonzero r a = some p) : a p ≠ 0 := by
  induction r with
  | zero => exact Fin.elim0 p
  | succ r ih =>
    by_cases hz : a 0 = 0
    · cases he : firstNonzero r (fun i => a i.succ) with
      | none => simp [firstNonzero, hz, he] at h
      | some q =>
        have hp : q.succ = p := by simpa [firstNonzero, hz, he] using h
        subst p
        exact ih (fun i => a i.succ) q he
    · have hp : (0 : Fin (r+1)) = p := by simpa [firstNonzero, hz] using h
      subst p
      exact hz

/-- Schur residual after the first column has a nonzero pivot in row p. -/
def residual {r n : ℕ} (A : Fin r → Fin (n+1) → ℚ) (p : Fin r) :
    Fin r → Fin n → ℚ :=
  fun i j => A i j.succ - A i 0 * (A p j.succ / A p 0)

/-- Restore the eliminated first coordinate. The returned tail is unchanged. -/
def lift {r n : ℕ} (A : Fin r → Fin (n+1) → ℚ) (p : Fin r)
    (w : Fin n → ℚ) : Fin (n+1) → ℚ :=
  Fin.cons (-(∑ j, (A p j.succ / A p 0) * w j)) w

@[simp] theorem lift_succ {r n : ℕ} (A : Fin r → Fin (n+1) → ℚ)
    (p : Fin r) (w : Fin n → ℚ) (j : Fin n) :
    lift A p w j.succ = w j := by simp [lift]

/-- Exact algebraic identity; no pivot assumption is necessary for this identity. -/
theorem dot_lift {r n : ℕ} (A : Fin r → Fin (n+1) → ℚ)
    (p i : Fin r) (w : Fin n → ℚ) :
    dot (A i) (lift A p w) = dot (residual A p i) w := by
  simp only [dot, Fin.sum_univ_succ, lift, Fin.cons_zero, Fin.cons_succ,
    residual, sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.mul_sum]
  simp_rw [mul_assoc]
  ring

/-- A relation determines its eliminated coordinate from the pivot equation. -/
theorem lift_tail_of_kernel {r n : ℕ} (A : Fin r → Fin (n+1) → ℚ)
    (p : Fin r) (hp : A p 0 ≠ 0) (v : Fin (n+1) → ℚ)
    (hv : dot (A p) v = 0) :
    lift A p (fun j => v j.succ) = v := by
  funext j
  refine Fin.cases ?_ (fun _ => by simp [lift]) j
  have hs : A p 0 * v 0 + ∑ j : Fin n, A p j.succ * v j.succ = 0 := by
    simpa only [dot, Fin.sum_univ_succ] using hv
  have ht : (∑ j : Fin n, (A p j.succ / A p 0) * v j.succ) =
      (∑ j : Fin n, A p j.succ * v j.succ) / A p 0 := by
    simp_rw [div_mul_eq_mul_div₀]
    exact (Finset.sum_div _ _ _).symm
  change -(∑ j : Fin n, (A p j.succ / A p 0) * v j.succ) = v 0
  rw [ht]
  rw [← neg_div]
  apply (div_eq_iff hp).2
  linarith

/-- Each call strictly decreases the number of columns. Every residual matrix
and returned vector is materialized with Vector.ofFn before it is reused.
No solver, kernel witness, rank witness, or choice function is program input. -/
def kernel (r : ℕ) : (n : ℕ) → QTable r n → Option (QVec n)
  | 0, _ => none
  | n+1, A =>
    match firstNonzero r (fun i => entry A i 0) with
    | none => some (List.Vector.ofFn (Fin.cons 1 (fun _ => 0)))
    | some p =>
      let B := tableOfFn (residual (entry A) p)
      (kernel r n B).map (fun w => List.Vector.ofFn (lift (entry A) p w.get))

/-- A returned value is a nonzero homogeneous relation. -/
theorem kernel_sound (r n : ℕ) (A : QTable r n) (w : QVec n)
    (h : kernel r n A = some w) :
    IsKernel A w.get ∧ ∃ j, w.get j ≠ 0 := by
  induction n with
  | zero => simp [kernel] at h
  | succ n ih =>
    cases hp : firstNonzero r (fun i => entry A i 0) with
    | none =>
      have hw : List.Vector.ofFn (Fin.cons 1 (fun _ : Fin n => 0)) = w := by
        simpa [kernel, hp] using h
      subst w
      have hz := (firstNonzero_none r (fun i => entry A i 0)).mp hp
      constructor
      · intro i
        simp [dot, Fin.sum_univ_succ, hz i]
      · exact ⟨0, by simp⟩
    | some p =>
      cases hk : kernel r n (tableOfFn (residual (entry A) p)) with
      | none => simp [kernel, hp, hk] at h
      | some v =>
        have hw : List.Vector.ofFn (lift (entry A) p v.get) = w := by
          simpa [kernel, hp, hk] using h
        subst w
        obtain ⟨hv, j, hj⟩ := ih _ v hk
        constructor
        · intro i
          simpa only [vecGet_ofFn, dot_lift, IsKernel,
            entry_tableOfFn_function] using hv i
        · exact ⟨j.succ, by simpa using hj⟩

/-- The relation has an exactly normalized coordinate; normalization does not
need an additional division after discovery. This is useful for its Cramer
description once the selected pivot-minor invariant is established. -/
theorem kernel_has_unit_coordinate (r n : ℕ) (A : QTable r n) (w : QVec n)
    (h : kernel r n A = some w) : ∃ j, w.get j = 1 := by
  induction n with
  | zero => simp [kernel] at h
  | succ n ih =>
    cases hp : firstNonzero r (fun i => entry A i 0) with
    | none =>
      have hw : List.Vector.ofFn (Fin.cons 1 (fun _ : Fin n => 0)) = w := by
        simpa [kernel, hp] using h
      subst w
      exact ⟨0, by simp⟩
    | some p =>
      cases hk : kernel r n (tableOfFn (residual (entry A) p)) with
      | none => simp [kernel, hp, hk] at h
      | some v =>
        have hw : List.Vector.ofFn (lift (entry A) p v.get) = w := by
          simpa [kernel, hp, hk] using h
        subst w
        obtain ⟨j, hj⟩ := ih _ v hk
        exact ⟨j.succ, by simpa using hj⟩

/-- Failure certifies injectivity, rather than merely bounded-fuel failure. -/
theorem kernel_none_injective (r n : ℕ) (A : QTable r n)
    (h : kernel r n A = none) (v : Fin n → ℚ) (hv : IsKernel A v) :
    ∀ j, v j = 0 := by
  induction n with
  | zero => exact fun j => Fin.elim0 j
  | succ n ih =>
    cases hp : firstNonzero r (fun i => entry A i 0) with
    | none => simp [kernel, hp] at h
    | some p =>
      have hn : kernel r n (tableOfFn (residual (entry A) p)) = none := by
        simpa only [kernel, hp, Option.map_eq_none_iff] using h
      have hp0 := firstNonzero_some r (fun i => entry A i 0) p hp
      have he := lift_tail_of_kernel (entry A) p hp0 v (hv p)
      have ht : IsKernel (tableOfFn (residual (entry A) p))
          (fun j => v j.succ) := by
        intro i
        simpa only [IsKernel, entry_tableOfFn_function, ← dot_lift, he] using hv i
      have hz := ih _ hn (fun j => v j.succ) ht
      intro j
      refine Fin.cases ?_ hz j
      have hh := congrFun he 0
      simpa [lift, hz] using hh.symm

theorem kernel_complete (r n : ℕ) (A : QTable r n)
    (v : Fin n → ℚ) (hv : IsKernel A v) (hn : ∃ j, v j ≠ 0) :
    ∃ w, kernel r n A = some w := by
  cases he : kernel r n A with
  | some w => exact ⟨w, rfl⟩
  | none =>
    obtain ⟨j, hj⟩ := hn
    exact False.elim (hj (kernel_none_injective r n A he v hv j))

theorem kernel_none_iff (r n : ℕ) (A : QTable r n) :
    kernel r n A = none ↔
      ∀ v : Fin n → ℚ, IsKernel A v → ∀ j, v j = 0 := by
  constructor
  · exact fun h v hv => kernel_none_injective r n A h v hv
  · intro h
    cases he : kernel r n A with
    | none => rfl
    | some w =>
      obtain ⟨hw, j, hj⟩ := kernel_sound r n A w he
      exact False.elim (hj (h w.get hw j))

end SparseCompletion.Gaussian
