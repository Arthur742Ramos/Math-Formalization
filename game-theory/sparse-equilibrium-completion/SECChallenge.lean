module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.List.MinMax


/- Fixed source body: SparseCompletion.lean -/
/-
Copyright (c) 2026. Licensed under Apache 2.0.
AI-assisted formalization of the anonymous manuscript
Sharp Sparse Witnesses for Incomplete Zero-Sum Games (revision 1a424f2).
Human authorship and responsible maintainer membership remain unconfirmed.
-/

@[expose] public section

open scoped BigOperators

namespace SparseCompletion

noncomputable section

def mass {ι : Type*} (s : Finset ι) (q : ι → ℝ) : ℝ := ∑ i ∈ s, q i

def response {ι : Type*} [Fintype ι] (B : ι → ι → ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, B i j * q j

def IsSkew {ι : Type*} (B : ι → ι → ℝ) : Prop := ∀ i j, B i j = -B j i

def call {ι : Type*} [Fintype ι] (q v : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i, q i * max (v i - z) 0

def envelope (M r z : ℝ) : ℝ := (M * r - z)^2 / (4 * M)

def Cuts {ι : Type*} [Fintype ι] (M r : ℝ) (q v : ι → ℝ) : Prop :=
  ∀ s : Finset ι, (∑ i ∈ s, q i * v i) ≤ M * mass s q * (r - mass s q)

theorem skew_weighted_sum {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (B : ι → ι → ℝ) (hB : IsSkew B) :
    (∑ i ∈ s, ∑ j ∈ s, q i * B i j * q j) = 0 := by
  have h : (∑ i ∈ s, ∑ j ∈ s, q i * B i j * q j) =
      -(∑ i ∈ s, ∑ j ∈ s, q i * B i j * q j) := by
    rw [← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hB j i]
    ring
  linarith

theorem response_guard {ι : Type*} [Fintype ι]
    (q t : ι → ℝ) (B : ι → ι → ℝ) (M r ρ : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r)
    (hB : ∀ i j, -M ≤ B i j)
    (hresp : ∀ i, t i + response B q i ≤ ρ) : ∀ i, t i ≤ ρ + M*r := by
  intro i
  have hlow : -M*r ≤ response B q i := by
    calc
      -M*r = ∑ j, (-M)*q j := by rw [← Finset.mul_sum, hr]
      _ ≤ response B q i := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hB i j) (hq j)
  linarith [hresp i]

theorem completion_cuts_necessary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q t : ι → ℝ) (B : ι → ι → ℝ) (M r ρ : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r)
    (hskew : IsSkew B) (hB : ∀ i j, -M ≤ B i j)
    (hresp : ∀ i, t i + response B q i ≤ ρ) : Cuts M r q (fun i => t i - ρ) := by
  intro s
  have hcomp : mass sᶜ q = r - mass s q := by
    have := Finset.sum_add_sum_compl s q
    unfold mass
    linarith
  have hsplit : (∑ i ∈ s, q i * response B q i) =
      ∑ i ∈ s, ∑ j ∈ sᶜ, q i * B i j * q j := by
    simp only [response, Finset.mul_sum]
    have hi := skew_weighted_sum s q B hskew
    have heq : (∑ i ∈ s, ∑ j, q i * (B i j * q j)) =
        (∑ i ∈ s, ∑ j ∈ s, q i * (B i j * q j)) +
        ∑ i ∈ s, ∑ j ∈ sᶜ, q i * (B i j * q j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_sum_compl s _).symm
    simp only [mul_assoc] at hi ⊢
    linarith
  have hlo : -M * mass s q * (r - mass s q) ≤ ∑ i ∈ s, q i * response B q i := by
    rw [hsplit, ← hcomp]
    calc
      -M * mass s q * mass sᶜ q = ∑ i ∈ s, ∑ j ∈ sᶜ, q i * (-M) * q j := by
        simp only [mass, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB i j) (hq i)) (hq j)
  have hup : (∑ i ∈ s, q i * (t i - ρ)) + (∑ i ∈ s, q i * response B q i) ≤ 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_nonpos fun i _ => by
      have := mul_nonpos_of_nonneg_of_nonpos (hq i) (sub_nonpos.mpr (hresp i))
      nlinarith
  linarith

theorem quadratic_duality (M r Q : ℝ) (hM : M ≠ 0) :
    envelope M r (M*r - 2*M*Q) + (M*r - 2*M*Q)*Q = M*Q*(r-Q) := by
  unfold envelope
  field_simp [hM]
  ring

theorem call_bound_implies_cuts {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r)
    (hcall : ∀ z ∈ Set.Icc (-M*r) (M*r), call q v z ≤ envelope M r z) :
    Cuts M r q v := by
  intro s
  classical
  let Q := mass s q
  let z := M*r - 2*M*Q
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => hq i
  have hQr : Q ≤ r := by
    rw [← hr]
    exact Finset.sum_le_univ_sum_of_nonneg fun i => hq i
  have hz : z ∈ Set.Icc (-M*r) (M*r) := by
    constructor <;> dsimp [z] <;> nlinarith
  have hsub : (∑ i ∈ s, q i * v i) - z*Q ≤ call q v z := by
    calc
      _ = ∑ i ∈ s, q i * (v i-z) := by simp only [Q, mass, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]; ring
      _ ≤ ∑ i ∈ s, q i * max (v i-z) 0 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (le_max_left _ _) (hq i)
      _ ≤ call q v z := Finset.sum_le_univ_sum_of_nonneg fun i => mul_nonneg (hq i) (le_max_right _ _)
  have he := quadratic_duality M r Q (ne_of_gt hM)
  have hc := hcall z hz
  dsimp [z] at hc hsub
  dsimp [Q] at he
  linarith

theorem quadratic_grid_identity (η u l : ℝ) :
    (u-2*η*l^2)*(2*η*(l+1)^2-u)-η*(2*u+η) =
      -(u-2*η*l*(l+1))^2-η^2 := by ring

theorem truncated_grid_error (η u l b : ℝ)
    (ha : 2*η*l^2 ≤ u) (hb : b ≤ 2*η*(l+1)^2) :
    (u-2*η*l^2)*(b-u) ≤ η*(2*u+η) := by
  have hprod := mul_le_mul_of_nonneg_left (sub_le_sub_right hb u) (sub_nonneg.mpr ha)
  have hs := sq_nonneg (u-2*η*l*(l+1))
  have ht := sq_nonneg η
  have hid := quadratic_grid_identity η u l
  nlinarith

theorem cuts_imply_call_bound {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 < M)
    (hcuts : Cuts M r q v) (z : ℝ) : call q v z ≤ envelope M r z := by
  classical
  let s := Finset.univ.filter fun i => 0 < v i-z
  let Q := mass s q
  have heq : call q v z = (∑ i ∈ s, q i*v i)-z*Q := by
    have hh : call q v z = ∑ i ∈ s, q i*(v i-z) := by
      unfold call
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => 0 < v i-z)]
      have hz : (∑ i ∈ Finset.univ.filter (fun i => ¬0 < v i-z), q i*max (v i-z) 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have := (Finset.mem_filter.mp hi).2
        rw [max_eq_right (le_of_not_gt this), mul_zero]
      rw [hz, add_zero]
      exact Finset.sum_congr rfl fun i hi => by rw [max_eq_left (le_of_lt (Finset.mem_filter.mp hi).2)]
    rw [hh]
    simp only [Q, mass, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [mul_comm]
  have hc := hcuts s
  have hs := sq_nonneg (2*M*Q - (M*r-z))
  have he : 4*M*envelope M r z = (M*r-z)^2 := by
    unfold envelope
    field_simp
  rw [heq]
  apply (mul_le_mul_iff_right₀ (show 0 < 4*M by positivity)).mp
  dsimp [Q] at hs
  nlinarith

theorem cuts_iff_call_bound {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r) :
    Cuts M r q v ↔ ∀ z ∈ Set.Icc (-M*r) (M*r), call q v z ≤ envelope M r z := by
  constructor
  · intro hc z _
    exact cuts_imply_call_bound q v M r hM hc z
  · exact call_bound_implies_cuts q v M r hM hq hr

theorem call_convex {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (x y θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    call q v (θ*x+(1-θ)*y) ≤ θ*call q v x+(1-θ)*call q v y := by
  unfold call
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hx := mul_le_mul_of_nonneg_left (le_max_left (v i-x) 0) hθ
  have hy := mul_le_mul_of_nonneg_left (le_max_left (v i-y) 0) (sub_nonneg.mpr hθ1)
  have h0 : 0 ≤ θ*max (v i-x) 0+(1-θ)*max (v i-y) 0 :=
    add_nonneg (mul_nonneg hθ (le_max_right _ _))
      (mul_nonneg (sub_nonneg.mpr hθ1) (le_max_right _ _))
  have hm : max (v i-(θ*x+(1-θ)*y)) 0 ≤
      θ*max (v i-x) 0+(1-θ)*max (v i-y) 0 := max_le (by nlinarith) h0
  have := mul_le_mul_of_nonneg_left hm (hq i)
  nlinarith

theorem call_secant {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (M r a b u : ℝ) (hM : 0 < M) (hab : a < b) (hau : a ≤ u) (hub : u ≤ b)
    (ha : call q v (M*r-a) ≤ a^2/(4*M))
    (hb : call q v (M*r-b) ≤ b^2/(4*M)) :
    call q v (M*r-u) ≤ (u^2+(u-a)*(b-u))/(4*M) := by
  let θ := (b-u)/(b-a)
  have hd : 0 < b-a := sub_pos.mpr hab
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hub) (le_of_lt hd)
  have hθ1 : θ ≤ 1 := (div_le_one hd).mpr (by linarith)
  have he : θ*(M*r-a)+(1-θ)*(M*r-b) = M*r-u := by
    dsimp [θ]
    field_simp
    ring
  have hc := call_convex q v hq (M*r-a) (M*r-b) θ hθ hθ1
  rw [he] at hc
  have hbound := add_le_add (mul_le_mul_of_nonneg_left ha hθ)
    (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hθ1))
  have hchord : θ*(a^2/(4*M))+(1-θ)*(b^2/(4*M)) =
      (u^2+(u-a)*(b-u))/(4*M) := by
    dsimp [θ]
    field_simp
    ring
  linarith

def gridNode (M r η : ℝ) (l : ℕ) : ℝ := min (2*η*(l:ℝ)^2) (2*M*r)

theorem grid_interval_cover (M r η : ℝ) (_hη : 0 < η) (hMr : 0 ≤ 2*M*r)
    (H : ℕ) (u : ℝ) (hu : 0 < u) (huH : u ≤ gridNode M r η H) :
    ∃ l : ℕ, l < H ∧ gridNode M r η l < u ∧ u ≤ gridNode M r η (l+1) := by
  induction H with
  | zero => simp [gridNode, min_eq_left hMr] at huH; linarith
  | succ H ih =>
    by_cases h : u ≤ gridNode M r η H
    · obtain ⟨l, hl, ha, hb⟩ := ih h
      exact ⟨l, Nat.lt_trans hl (Nat.lt_succ_self H), ha, hb⟩
    · exact ⟨H, Nat.lt_succ_self H, lt_of_not_ge h, huH⟩

theorem finite_grid_implication {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r η : ℝ) (H : ℕ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hH : M*r ≤ η*(H:ℝ)^2) (hq : ∀ i, 0 ≤ q i)
    (hcap : ∀ i, q i ≠ 0 → v i ≤ M*r)
    (hgrid : ∀ l : ℕ, 1 ≤ l → l ≤ H →
      call q v (M*r-gridNode M r η l) ≤ envelope M r (M*r-gridNode M r η l)) :
    ∀ z ∈ Set.Icc (-M*r) (M*r), call q (fun i => v i-η) z ≤ envelope M r z := by
  have htop : ∀ w, M*r ≤ w → call q v w = 0 := by
    intro w hw
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : q i = 0
    · rw [hi, zero_mul]
    · rw [max_eq_right (by linarith [hcap i hi]), mul_zero]
  have hnode : ∀ l, l ≤ H → call q v (M*r-gridNode M r η l) ≤ (gridNode M r η l)^2/(4*M) := by
    intro l hlH
    by_cases hl : l = 0
    · subst l
      have hMr : 0 ≤ 2*M*r := by positivity
      have hn : gridNode M r η 0 = 0 := by simp [gridNode, min_eq_left hMr]
      rw [hn, sub_zero, htop (M*r) le_rfl]
      simp
    · have := hgrid l (Nat.one_le_iff_ne_zero.mpr hl) hlH
      simpa only [envelope, sub_sub_cancel] using this
  intro z hz
  have hshift : call q (fun i => v i-η) z = call q v (z+η) := by
    unfold call
    congr 1
    funext i
    congr 2
    ring
  rw [hshift]
  by_cases hw : M*r ≤ z+η
  · rw [htop _ hw]
    exact div_nonneg (sq_nonneg _) (by positivity)
  · let u := M*r-(z+η)
    have hu : 0 < u := by dsimp [u]; linarith
    have huH : u ≤ gridNode M r η H := by
      have hge : gridNode M r η H = 2*M*r := min_eq_right (by nlinarith)
      rw [hge]
      dsimp [u]
      linarith [hz.1]
    obtain ⟨l, hl, ha, hb⟩ := grid_interval_cover M r η hη (by positivity) H u hu huH
    let a := gridNode M r η l
    let b := gridNode M r η (l+1)
    have hau : a ≤ u := le_of_lt ha
    have hab : a < b := lt_of_lt_of_le ha hb
    have haFull : a = 2*η*(l:ℝ)^2 := by
      apply min_eq_left
      have hsmall : gridNode M r η l < 2*M*r := lt_of_lt_of_le ha (le_trans hb (min_le_right _ _))
      dsimp [gridNode] at hsmall
      exact le_of_lt ((min_lt_iff.mp hsmall).resolve_right (lt_irrefl _))
    have hbFull : b ≤ 2*η*((l:ℝ)+1)^2 := by
      simpa only [b, gridNode, Nat.cast_add, Nat.cast_one] using min_le_left (2*η*((l+1:ℕ):ℝ)^2) (2*M*r)
    have hs := call_secant q v hq M r a b u hM hab hau hb (hnode l (le_of_lt hl)) (hnode (l+1) (Nat.succ_le_iff.mpr hl))
    have herr := truncated_grid_error η u (l:ℝ) b (by simpa only [← haFull] using hau) hbFull
    have hupper : (u^2+(u-a)*(b-u))/(4*M) ≤ (u+η)^2/(4*M) := by
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4*M)).mpr
      rw [haFull]
      nlinarith
    have harg : M*r-u = z+η := by dsimp [u]; ring
    have hend : (u+η)^2/(4*M) = envelope M r z := by dsimp [u, envelope]; ring
    rw [harg] at hs
    exact le_trans hs (hend ▸ hupper)

def gridSize (M r η : ℝ) : ℕ := Nat.ceil (Real.sqrt (M*r/η))

theorem gridSize_bound (M r η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η) :
    M*r ≤ η*(gridSize M r η : ℝ)^2 := by
  have hn : 0 ≤ M*r/η := by positivity
  have hs := Real.sq_sqrt hn
  have hc := Nat.le_ceil (Real.sqrt (M*r/η))
  have hsq : M*r/η ≤ (gridSize M r η : ℝ)^2 := by
    dsimp [gridSize]
    nlinarith [Real.sqrt_nonneg (M*r/η)]
  have := (div_le_iff₀ hη).mp hsq
  nlinarith

theorem canonical_grid_implication {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η) (hq : ∀ i, 0 ≤ q i)
    (hcap : ∀ i, q i ≠ 0 → v i ≤ M*r)
    (hgrid : ∀ l : ℕ, 1 ≤ l → l ≤ gridSize M r η →
      call q v (M*r-gridNode M r η l) ≤ envelope M r (M*r-gridNode M r η l)) :
    ∀ z ∈ Set.Icc (-M*r) (M*r), call q (fun i => v i-η) z ≤ envelope M r z :=
  finite_grid_implication q v M r η (gridSize M r η) hM hr hη
    (gridSize_bound M r η hM hr hη) hq hcap hgrid

theorem supported_response_zero {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (B : ι → ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hskew : IsSkew B)
    (hresp : ∀ i, response B q i ≤ 0) (i : ι) (hi : 0 < q i) :
    response B q i = 0 := by
  have hsum : (∑ j, q j * response B q j) = 0 := by
    simpa only [response, Finset.mul_sum, mul_assoc] using skew_weighted_sum Finset.univ q B hskew
  have hterm : q i * response B q i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hq j) (hresp j))).mp hsum i (Finset.mem_univ i)
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hi)

def compactCompletion {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (M : ℝ) (B : ι → ι → ℝ) (i j : ι) : ℝ :=
  if i ∈ s then (if j ∈ s then B i j else M) else (if j ∈ s then -M else 0)

theorem compactCompletion_skew {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (M : ℝ) (B : ι → ι → ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, B i j = -B j i) : IsSkew (compactCompletion s M B) := by
  intro i j
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
  · simpa only [compactCompletion, ite_eq_left hi, ite_eq_left hj] using hB i hi j hj
  · simp [compactCompletion, hi, hj]
  · simp [compactCompletion, hi, hj]
  · simp [compactCompletion, hi, hj]

theorem compactCompletion_bounds {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (M : ℝ) (B : ι → ι → ℝ) (hM : 0 ≤ M)
    (hB : ∀ i ∈ s, ∀ j ∈ s, -M ≤ B i j ∧ B i j ≤ M) :
    ∀ i j, -M ≤ compactCompletion s M B i j ∧ compactCompletion s M B i j ≤ M := by
  intro i j
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
  · simpa only [compactCompletion, ite_eq_left hi, ite_eq_left hj] using hB i hi j hj
  · simp only [compactCompletion, ite_eq_left hi, ite_eq_right hj]
    constructor <;> linarith
  · simp only [compactCompletion, ite_eq_right hi, ite_eq_left hj]
    constructor <;> linarith
  · simp only [compactCompletion, ite_eq_right hi, ite_eq_right hj]
    constructor <;> linarith

theorem compactCompletion_response_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (M : ℝ) (B : ι → ι → ℝ) (q : ι → ℝ)
    (hs : ∀ j, j ∉ s → q j = 0) (i : ι) (hi : i ∈ s) :
    response (compactCompletion s M B) q i = ∑ j ∈ s, B i j*q j := by
  unfold response
  calc
    _ = ∑ j ∈ s, compactCompletion s M B i j*q j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      rw [hs j hj, mul_zero]
    _ = _ := Finset.sum_congr rfl fun j hj => by simp [compactCompletion, hi, hj]

theorem compactCompletion_response_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (M r : ℝ) (B : ι → ι → ℝ) (q : ι → ℝ)
    (hs : ∀ j, j ∉ s → q j = 0) (hr : ∑ j, q j = r) (i : ι) (hi : i ∉ s) :
    response (compactCompletion s M B) q i = -M*r := by
  unfold response
  calc
    _ = ∑ j, (-M)*q j := Finset.sum_congr rfl fun j _ => by
      by_cases hj : j ∈ s
      · simp [compactCompletion, hi, hj]
      · simp [compactCompletion, hi, hj, hs j hj]
    _ = _ := by rw [← Finset.mul_sum, hr]

theorem compact_certificate_responses_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (M r σ : ℝ) (B : ι → ι → ℝ) (q t : ι → ℝ)
    (hs : ∀ j, j ∉ s → q j = 0) (hr : ∑ j, q j = r) :
    (∀ i, t i+response (compactCompletion s M B) q i ≤ σ) ↔
      (∀ i ∈ s, t i+(∑ j ∈ s, B i j*q j) ≤ σ) ∧
      (∀ i, i ∉ s → t i-M*r ≤ σ) := by
  constructor
  · intro h
    constructor
    · intro i hi
      simpa only [compactCompletion_response_on s M B q hs i hi] using h i
    · intro i hi
      simpa only [compactCompletion_response_off s M r B q hs hr i hi, sub_eq_add_neg, neg_mul] using h i
  · rintro ⟨hon, hoff⟩ i
    by_cases hi : i ∈ s
    · simpa only [compactCompletion_response_on s M B q hs i hi] using hon i hi
    · simpa only [compactCompletion_response_off s M r B q hs hr i hi, sub_eq_add_neg, neg_mul] using hoff i hi

theorem response_perturbation {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℝ) (q : ι → ℝ) (δ r : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r)
    (hAB : ∀ i j, |A i j-B i j| ≤ δ) (i : ι) :
    |response A q i-response B q i| ≤ δ*r := by
  calc
    _ = |∑ j, (A i j-B i j)*q j| := by
      simp only [response, sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ j, |(A i j-B i j)*q j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j-B i j| * q j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (hq j)]
    _ ≤ ∑ j, δ*q j := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hq j)
    _ = _ := by rw [← Finset.mul_sum, hr]

end

end SparseCompletion

/- Fixed source body: MomentCompression.lean -/
/- Classical finite-moment recombination, using Mathlib's Caratheodory theorem.
   Follow-on development for sparse equilibrium completion.
   AI-assisted formalization under the repository Apache-2.0 license. -/

@[expose] public section

open scoped BigOperators
open Set

namespace SparseCompletion
noncomputable section

def pushWeights {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (i : ι) : ℝ :=
  ∑ j, if label j = i then w j else 0

theorem pushWeights_nonneg {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∀ i, 0 ≤ pushWeights label w i := by
  intro i
  exact Finset.sum_nonneg fun j _ => by
    split
    · exact hw j
    · exact le_rfl

theorem pushWeights_mass {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) : ∑ i, pushWeights label w i = ∑ j, w j := by
  simp only [pushWeights]
  rw [Finset.sum_comm]
  simp

theorem pushWeights_moment {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (f : ι → ℝ) :
    (∑ i, pushWeights label w i*f i) = ∑ j, w j*f (label j) := by
  simp only [pushWeights, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

theorem pushWeights_zero_outside {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) (s : Finset ι) (hs : ∀ j, label j ∈ s)
    (i : ι) (hi : i ∉ s) : pushWeights label w i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : label j ≠ i := by intro he; exact hi (he ▸ hs j)
  simp only [ite_eq_right hj]

theorem pushWeights_support_card {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (label : κ → ι) (w : κ → ℝ) :
    (Finset.univ.filter fun i => pushWeights label w i ≠ 0).card ≤ Fintype.card κ := by
  classical
  apply le_trans (Finset.card_le_card (show
    Finset.univ.filter (fun i => pushWeights label w i ≠ 0) ⊆ Finset.univ.image label from ?_))
    (le_trans (Finset.card_image_le) (by simp))
  intro i hi
  have hne := (Finset.mem_filter.mp hi).2
  by_contra hn
  apply hne
  apply Finset.sum_eq_zero
  intro j _
  have hj : label j ≠ i := by
    intro he
    exact hn (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he⟩)
  simp only [ite_eq_right hj]

/-- A finite nonnegative weighted sample can be replaced by at most d+1 of
    its original labels while preserving mass and d real features exactly.
    Classical Caratheodory/Tchakaloff recombination is credited to Mathlib. -/
theorem finite_moment_recombination {ι : Type*} (ν : Type) [Fintype ν] (s : Finset ι)
    (q : ι → ℝ) (F : ι → ν → ℝ) (r : ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hr : ∑ i ∈ s, q i = r) (hrpos : 0 < r) :
    ∃ (κ : Type) (_ : Fintype κ) (label : κ → ι) (w : κ → ℝ),
      Function.Injective label ∧ (∀ j, label j ∈ s) ∧
      (∀ j, 0 < w j) ∧ (∑ j, w j = r) ∧
      Fintype.card κ ≤ Fintype.card ν+1 ∧
      (∑ j, w j • F (label j)) = ∑ i ∈ s, q i • F i := by
  classical
  let μ : ν → ℝ := ∑ i ∈ s, (q i/r) • F i
  have hn : ∑ i ∈ s, q i/r = 1 := by
    rw [← Finset.sum_div, hr, div_self (ne_of_gt hrpos)]
  have hμ : μ ∈ convexHull ℝ (F '' (s : Set ι)) := by
    exact (convex_convexHull ℝ (F '' (s : Set ι))).sum_mem (t := s) (z := F)
      (fun i hi => div_nonneg (hq i hi) (le_of_lt hrpos)) hn
      (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)
  obtain ⟨κ, hκ, z, w, hz, hind, hw, hsum, hm⟩ := eq_pos_convex_span_of_mem_convexHull hμ
  let _ : Fintype κ := hκ
  have hlabels : ∀ j, ∃ i, i ∈ s ∧ F i = z j := by
    intro j
    exact hz (mem_range_self j)
  choose label hlabel hfeature using hlabels
  have hinj : Function.Injective label := by
    intro a b hab
    apply hind.injective
    rw [← hfeature a, ← hfeature b, hab]
  refine ⟨κ, hκ, label, fun j => r*w j, hinj, hlabel,
    (fun j => mul_pos hrpos (hw j)), ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, hsum, mul_one]
  · have hc := hind.card_le_finrank_succ
    have hdim := Submodule.finrank_le (vectorSpan ℝ (range z))
    have hc' := le_trans hc (Nat.add_le_add_right hdim 1)
    simpa only [Module.finrank_pi] using hc'
  · calc
      _ = r • (∑ j, w j • z j) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [mul_smul, hfeature j]
      _ = r • μ := by rw [hm]
      _ = ∑ i ∈ s, q i • F i := by
        dsimp [μ]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_smul]
        congr 1
        field_simp

theorem finite_feature_compression {ι : Type*} [Fintype ι]
    (ν : Type) [Fintype ν] (q : ι → ℝ) (F : ι → ν → ℝ) (r : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r) (hrpos : 0 < r) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ Fintype.card ν+1 ∧
      ∀ h, (∑ i, q' i*F i h) = ∑ i, q i*F i h := by
  classical
  let s := Finset.univ.filter fun i => q i ≠ 0
  have hs : ∑ i ∈ s, q i = r := by
    simpa only [s, Finset.sum_filter_ne_zero] using hr
  obtain ⟨κ, hκ, label, w, _hinj, hlabel, hw, hmass, hcard, hm⟩ :=
    finite_moment_recombination ν s q F r (fun i _ => hq i) hs hrpos
  let _ : Fintype κ := hκ
  refine ⟨pushWeights label w, pushWeights_nonneg label w (fun j => le_of_lt (hw j)), ?_, ?_, ?_, ?_⟩
  · rw [pushWeights_mass, hmass]
  · intro i hi
    exact pushWeights_zero_outside label w s hlabel i (by simp [s, hi])
  · exact le_trans (pushWeights_support_card label w) hcard
  · intro h
    rw [pushWeights_moment]
    have hh := congrArg (fun f : ν → ℝ => f h) hm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    rw [hh]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hnot
    have hqi : q i = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    rw [hqi, zero_mul]

end
end SparseCompletion

/- Fixed source body: GameModel.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human authorship and maintainer membership remain unconfirmed. -/

@[expose] public section

open scoped BigOperators

namespace SparseCompletion
noncomputable section

def blockMatrix {α ι : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B : ι → ι → ℝ) : (α ⊕ ι) → (α ⊕ ι) → ℝ
  | .inl h, .inl h' => K h h'
  | .inl h, .inr i => -D i h
  | .inr i, .inl h => D i h
  | .inr i, .inr j => B i j

def blockWeights {α ι : Type*} (p : α → ℝ) (q : ι → ℝ) : (α ⊕ ι) → ℝ := Sum.elim p q

def score {α ι : Type*} [Fintype α] (D : ι → α → ℝ) (p : α → ℝ) (i : ι) : ℝ :=
  ∑ h, D i h*p h

def anchorResponse {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ) (h : α) : ℝ :=
  (∑ h', K h h'*p h')-∑ i, D i h*q i

theorem blockMatrix_skew {α ι : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B : ι → ι → ℝ) (hK : IsSkew K) (hB : IsSkew B) : IsSkew (blockMatrix K D B) := by
  intro a b
  cases a <;> cases b
  · exact hK _ _
  · rfl
  · simp only [blockMatrix, neg_neg]
  · exact hB _ _

theorem blockWeights_nonneg {α ι : Type*} (p : α → ℝ) (q : ι → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) : ∀ a, 0 ≤ blockWeights p q a := by
  intro a
  cases a with
  | inl h => exact hp h
  | inr i => exact hq i

theorem blockMatrix_bounds {α ι : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B : ι → ι → ℝ) (M : ℝ)
    (hK : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hD : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hB : ∀ i j, -M ≤ B i j ∧ B i j ≤ M) :
    ∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M := by
  intro a b
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact hK h h'
    | inr i =>
      have hi := hD i h
      change -M ≤ -D i h ∧ -D i h ≤ M
      constructor <;> linarith [hi.1, hi.2]
  | inr i =>
    cases b with
    | inl h => exact hD i h
    | inr j => exact hB i j

theorem blockWeights_mass {α ι : Type*} [Fintype α] [Fintype ι] (p : α → ℝ) (q : ι → ℝ) :
    (∑ a, blockWeights p q a) = (∑ h, p h)+(∑ i, q i) := by
  simp only [Fintype.sum_sum_type, blockWeights, Sum.elim_inl, Sum.elim_inr]

theorem block_response_anchor {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (h : α) :
    response (blockMatrix K D B) (blockWeights p q) (.inl h) = anchorResponse K D p q h := by
  simp only [response, Fintype.sum_sum_type, blockMatrix, blockWeights,
    Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, anchorResponse, sub_eq_add_neg]

theorem block_response_residual {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (i : ι) :
    response (blockMatrix K D B) (blockWeights p q) (.inr i) = score D p i+response B q i := by
  simp only [response, Fintype.sum_sum_type, blockMatrix, blockWeights,
    Sum.elim_inl, Sum.elim_inr, score]

theorem block_response_bounds_iff {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (ρ : ℝ) :
    (∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) ↔
      (∀ h, anchorResponse K D p q h ≤ ρ) ∧ (∀ i, score D p i+response B q i ≤ ρ) := by
  constructor
  · intro h
    exact ⟨fun a => (block_response_anchor K D B p q a) ▸ h (.inl a),
      fun i => (block_response_residual K D B p q i) ▸ h (.inr i)⟩
  · rintro ⟨hA, hR⟩ a
    cases a with
    | inl h => simpa only [block_response_anchor] using hA h
    | inr i => simpa only [block_response_residual] using hR i

theorem response_bounds {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (B : ι → ι → ℝ) (M r : ℝ) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : ∀ i j, -M ≤ B i j ∧ B i j ≤ M) :
    ∀ i, -M*r ≤ response B q i ∧ response B q i ≤ M*r := by
  intro i
  constructor
  · calc
      -M*r = ∑ j, (-M)*q j := by rw [← Finset.mul_sum, hmass]
      _ ≤ response B q i := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hB i j).1 (hq j)
  · calc
      response B q i ≤ ∑ j, M*q j := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hB i j).2 (hq j)
      _ = M*r := by rw [← Finset.mul_sum, hmass]

theorem compact_block_certificate_iff {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r σ : ℝ)
    (hs : ∀ i, i ∉ s → q i = 0) (hmass : ∑ i, q i = r) :
    (∀ a, response (blockMatrix K D (compactCompletion s M B)) (blockWeights p q) a ≤ σ) ↔
      (∀ h, anchorResponse K D p q h ≤ σ) ∧
      (∀ i ∈ s, score D p i+(∑ j ∈ s, B i j*q j) ≤ σ) ∧
      (∀ i, i ∉ s → score D p i-M*r ≤ σ) := by
  rw [block_response_bounds_iff, compact_certificate_responses_iff s M r σ B q (score D p) hs hmass]

theorem exact_supported_residual_zero {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hK : IsSkew K) (hB : IsSkew B)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∀ i, q i ≠ 0 → score D p i+response B q i = 0 := by
  intro i hi
  have hqi : 0 < q i := lt_of_le_of_ne (hq i) hi.symm
  have hz := supported_response_zero (blockWeights p q) (blockMatrix K D B)
    (blockWeights_nonneg p q hp hq) (blockMatrix_skew K D B hK hB) hresp (.inr i) hqi
  simpa only [block_response_residual] using hz

theorem exact_score_bounds {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r : ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∀ i, q i ≠ 0 → |score D p i| ≤ M*r := by
  intro i hi
  have hz := exact_supported_residual_zero K D B p q hp hq hK hB hresp i hi
  have hb := response_bounds q B M r hq hmass hbound i
  exact abs_le.mpr ⟨by linarith [hb.2], by linarith [hb.1]⟩

theorem exact_score_mean_zero {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hK : IsSkew K) (hB : IsSkew B)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∑ i, q i*score D p i = 0 := by
  have heq : (∑ i, q i*score D p i) = -(∑ i, q i*response B q i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : q i = 0
    · simp only [hi, zero_mul, neg_zero]
    · have hz := exact_supported_residual_zero K D B p q hp hq hK hB hresp i hi
      have ht : score D p i = -response B q i := by linarith
      rw [ht]
      ring
  have hb := skew_weighted_sum Finset.univ q B hB
  simp only [response, Finset.mul_sum] at heq
  simp only [mul_assoc] at hb
  rw [hb, neg_zero] at heq
  exact heq

end
end SparseCompletion

/- Fixed source body: SparseWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human authorship and maintainer membership remain unconfirmed. -/

@[expose] public section

open scoped BigOperators

namespace SparseCompletion
noncomputable section

theorem supported_score_cap {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 < M) (hq : ∀ i, 0 ≤ q i)
    (hc : Cuts M r q v) : ∀ i, q i ≠ 0 → v i ≤ M*r := by
  classical
  intro i hi
  have hqi : 0 < q i := lt_of_le_of_ne (hq i) hi.symm
  have hcut := hc {i}
  simp only [Finset.sum_singleton, mass] at hcut
  have hsq := mul_nonneg (le_of_lt hM) (sq_nonneg (q i))
  by_contra hv
  have hprod := mul_pos hqi (sub_pos.mpr (lt_of_not_ge hv))
  nlinarith

def sparseFeatures {ι : Type*} (k H : ℕ) (D : ι → Fin k → ℝ)
    (v : ι → ℝ) (M r η : ℝ) (i : ι) : (Fin k ⊕ Fin H) → ℝ :=
  Sum.elim (D i) (fun l => max (v i-(M*r-gridNode M r η (l.val+1))) 0)

/-- The analytic sparse-witness step: exact anchor moments, original labels,
    and all completion cuts after additive slack. Bounded-game reconstruction
    is a separate cut-sufficiency theorem, not an assumption hidden here. -/
theorem sparse_cut_witness {ι : Type*} [Fintype ι]
    (k H : ℕ) (D : ι → Fin k → ℝ) (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hH : M*r ≤ η*(H:ℝ)^2) (hq : ∀ i, 0 ≤ q i)
    (hmass : ∑ i, q i = r) (hcuts : Cuts M r q v) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+H ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      Cuts M r q' (fun i => v i-η) := by
  classical
  obtain ⟨q', hq', hmass', hsupp, hcard, hmom⟩ :=
    finite_feature_compression (Fin k ⊕ Fin H) q (sparseFeatures k H D v M r η) r hq hmass hr
  refine ⟨q', hq', hmass', hsupp, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_right_comm k H 1] using hcard
  · intro h
    exact hmom (Sum.inl h)
  · apply call_bound_implies_cuts q' (fun i => v i-η) M r hM hq' hmass'
    apply finite_grid_implication q' v M r η H hM (le_of_lt hr) hη hH hq'
    · intro i hi
      exact supported_score_cap q v M r hM hq hcuts i (fun hzero => hi (hsupp i hzero))
    · intro l hl hlH
      let j : Fin H := ⟨l-1, by omega⟩
      have hj : j.val+1 = l := by dsimp [j]; omega
      have hm := hmom (Sum.inr j)
      change (∑ i, q' i*max (v i-(M*r-gridNode M r η (j.val+1))) 0) =
        ∑ i, q i*max (v i-(M*r-gridNode M r η (j.val+1))) 0 at hm
      rw [hj] at hm
      change (∑ i, q' i*max (v i-(M*r-gridNode M r η l)) 0) ≤ _
      rw [hm]
      exact cuts_imply_call_bound q v M r hM hcuts _

theorem linear_score_moment_preserved {ι : Type*} [Fintype ι]
    (k : ℕ) (D : ι → Fin k → ℝ) (p : Fin k → ℝ) (q q' v : ι → ℝ)
    (hv : ∀ i, v i = ∑ h, D i h*p h)
    (hm : ∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) :
    (∑ i, q' i*v i) = ∑ i, q i*v i := by
  simp_rw [hv]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i h => q i*(D i h*p h))]
  apply Finset.sum_congr rfl
  intro h _
  simp only [← mul_assoc, ← Finset.sum_mul]
  rw [hm h]

theorem bottom_call_of_zero_mean {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hmass : ∑ i, q i = r)
    (hmean : ∑ i, q i*v i = 0) (hlow : ∀ i, q i ≠ 0 → -M*r ≤ v i) :
    call q v (-M*r) = M*r^2 := by
  have heq : call q v (-M*r) = ∑ i, q i*(v i+M*r) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : q i = 0
    · simp only [hi, zero_mul]
    · rw [max_eq_left (by linarith [hlow i hi])]
      congr 1
      ring
  rw [heq]
  simp only [mul_add, Finset.sum_add_distrib, hmean, zero_add, ← Finset.sum_mul, hmass]
  ring

theorem exact_sparse_cut_witness {ι : Type*} [Fintype ι]
    (k H : ℕ) (D : ι → Fin k → ℝ) (p : Fin k → ℝ) (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hH : M*r ≤ η*(H:ℝ)^2) (hq : ∀ i, 0 ≤ q i)
    (hmass : ∑ i, q i = r) (hcuts : Cuts M r q v)
    (hv : ∀ i, v i = ∑ h, D i h*p h) (hmean : ∑ i, q i*v i = 0)
    (hlow : ∀ i, q i ≠ 0 → -M*r ≤ v i) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+H ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      Cuts M r q' (fun i => v i-η) := by
  classical
  have hHpos : 0 < H := by
    by_contra hn
    have hzero : H = 0 := by omega
    subst H
    norm_num at hH
    nlinarith [mul_pos hM hr]
  obtain ⟨q', hq', hmass', hsupp, hcard, hmom⟩ :=
    finite_feature_compression (Fin k ⊕ Fin (H-1)) q (sparseFeatures k (H-1) D v M r η) r hq hmass hr
  have hanchor : ∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h := fun h => hmom (Sum.inl h)
  refine ⟨q', hq', hmass', hsupp, ?_, hanchor, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  · apply call_bound_implies_cuts q' (fun i => v i-η) M r hM hq' hmass'
    apply finite_grid_implication q' v M r η H hM (le_of_lt hr) hη hH hq'
    · intro i hi
      exact supported_score_cap q v M r hM hq hcuts i (fun hzero => hi (hsupp i hzero))
    · intro l hl hlH
      by_cases hlast : l = H
      · subst l
        have hnode : gridNode M r η H = 2*M*r := min_eq_right (by nlinarith)
        rw [hnode]
        have harg : M*r-2*M*r = -M*r := by ring
        rw [harg]
        have hmean' : ∑ i, q' i*v i = 0 :=
          (linear_score_moment_preserved k D p q q' v hv hanchor).trans hmean
        rw [bottom_call_of_zero_mean q' v M r hmass' hmean'
          (fun i hi => hlow i (fun hzero => hi (hsupp i hzero)))]
        have heq : envelope M r (-M*r) = M*r^2 := by
          unfold envelope
          field_simp
          ring
        rw [heq]
      · have hlt : l < H := lt_of_le_of_ne hlH hlast
        let j : Fin (H-1) := ⟨l-1, by omega⟩
        have hj : j.val+1 = l := by dsimp [j]; omega
        have hm := hmom (Sum.inr j)
        change (∑ i, q' i*max (v i-(M*r-gridNode M r η (j.val+1))) 0) =
          ∑ i, q i*max (v i-(M*r-gridNode M r η (j.val+1))) 0 at hm
        rw [hj] at hm
        change (∑ i, q' i*max (v i-(M*r-gridNode M r η l)) 0) ≤ _
        rw [hm]
        exact cuts_imply_call_bound q v M r hM hcuts _

theorem canonical_sparse_cut_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (D : ι → Fin k → ℝ) (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r) (hcuts : Cuts M r q v) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+gridSize M r η ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      Cuts M r q' (fun i => v i-η) :=
  sparse_cut_witness k (gridSize M r η) D q v M r η hM hr hη
    (gridSize_bound M r η hM (le_of_lt hr) hη) hq hmass hcuts

end
end SparseCompletion

/- Fixed source body: GameSparseWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human authorship and maintainer membership remain unconfirmed. -/

@[expose] public section

open scoped BigOperators

namespace SparseCompletion
noncomputable section

theorem anchor_response_of_moments {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q q' : ι → ℝ)
    (hm : ∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) :
    ∀ h, anchorResponse K D p q' h = anchorResponse K D p q h := by
  intro h
  unfold anchorResponse
  congr 1
  simpa only [mul_comm] using hm h

/-- Original-game sparsification through all scalar completion conditions,
    including omitted-row guards. SparseCompletionWitness combines these
    conditions with the weighted completion sufficiency theorem. -/
theorem game_sparse_cut_certificate {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ i, score D p i ≤ (ρ+η)+M*r) ∧
      Cuts M r q' (fun i => score D p i-(ρ+η)) := by
  classical
  have hres := ((block_response_bounds_iff K D B p q ρ).mp hresp).2
  have hcuts := completion_cuts_necessary q (score D p) B M r ρ hq hmass hB hbound hres
  obtain ⟨q', hq', hmass', hsupp, hcard, hfeatures, hc⟩ :=
    canonical_sparse_cut_witness k D q (fun i => score D p i-ρ) M r η hM hr hη hq hmass hcuts
  refine ⟨q', hq', hmass', hsupp, hcard, anchor_response_of_moments k K D p q q' hfeatures, ?_, ?_⟩
  · intro i
    have hg := response_guard q (score D p) B M r ρ hq hmass hbound hres i
    linarith
  · convert hc using 1
    funext i
    ring

theorem exact_game_sparse_cut_certificate {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ i, score D p i ≤ η+M*r) ∧
      Cuts M r q' (fun i => score D p i-η) := by
  classical
  have hres := ((block_response_bounds_iff K D B p q 0).mp hresp).2
  have hcuts0 := completion_cuts_necessary q (score D p) B M r 0 hq hmass hB
    (fun i j => (hbound i j).1) hres
  have hcuts : Cuts M r q (score D p) := by simpa only [sub_zero] using hcuts0
  have hmean := exact_score_mean_zero K D B p q hp hq hK hB hresp
  have hlow : ∀ i, q i ≠ 0 → -M*r ≤ score D p i := by
    intro i hi
    simpa only [neg_mul] using
      (abs_le.mp (exact_score_bounds K D B p q M r hp hq hmass hK hB hbound hresp i hi)).1
  obtain ⟨q', hq', hmass', hsupp, hcard, hfeatures, hc⟩ :=
    exact_sparse_cut_witness k (gridSize M r η) D p q (score D p) M r η hM hr hη
      (gridSize_bound M r η hM (le_of_lt hr) hη) hq hmass hcuts (fun _ => rfl) hmean hlow
  refine ⟨q', hq', hmass', hsupp, hcard, anchor_response_of_moments k K D p q q' hfeatures, ?_, hc⟩
  intro i
  have hg := response_guard q (score D p) B M r 0 hq hmass
    (fun i j => (hbound i j).1) hres i
  linarith

end
end SparseCompletion

/- Fixed source body: CompletionDual.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section

open scoped BigOperators

namespace SparseCompletion
noncomputable section

def lowerPositive {ι : Type*} (a : ℝ) (y : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if 0 < y i then y i-a else 0

def positiveSet {ι : Type*} [Fintype ι] (y : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => 0 < y i

def weightedVariation {ι : Type*} [Fintype ι] (q y : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, q i*q j*|y i-y j|)/(2 : ℕ)

theorem masked_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∑ i, if i ∈ s then f i else 0) = mass s f := by
  unfold mass
  calc
    _ = ∑ i ∈ s, if i ∈ s then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      exact ite_eq_right hi
    _ = _ := Finset.sum_congr rfl fun i hi => ite_eq_left hi

theorem complement_masked_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (q : ι → ℝ) (r : ℝ) (hr : ∑ i, q i = r) :
    (∑ i, if i ∈ s then 0 else q i) = r-mass s q := by
  have heq : (∑ i, if i ∈ s then q i else 0)+(∑ i, if i ∈ s then 0 else q i) = r := by
    rw [← Finset.sum_add_distrib, ← hr]
    exact Finset.sum_congr rfl fun i _ => by split <;> simp_all
  rw [masked_sum] at heq
  linarith

theorem outer_product_sum {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, ∑ j, f i*g j) = (∑ i, f i)*(∑ j, g j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem positive_pair_decomposition {ι : Type*} (a : ℝ) (q y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hmin : ∀ i, 0 < y i → a ≤ y i) (i j : ι) :
    q i*q j*|y i-y j| = q i*q j*|lowerPositive a y i-lowerPositive a y j| +
      a*((if 0 < y i then q i else 0)*(if 0 < y j then 0 else q j)+
         (if 0 < y i then 0 else q i)*(if 0 < y j then q j else 0)) := by
  classical
  by_cases hi : 0 < y i <;> by_cases hj : 0 < y j
  · simp only [lowerPositive, ite_eq_left hi, ite_eq_left hj, mul_zero, zero_mul, add_zero]
    congr 2
    ring
  · have hj0 : y j = 0 := by linarith [hy j]
    have hia : 0 ≤ y i-a := by linarith [hmin i hi]
    simp [lowerPositive, hi, hj0, abs_of_nonneg (hy i), abs_of_nonneg hia]
    ring
  · have hi0 : y i = 0 := by linarith [hy i]
    have hja : y j-a ≥ 0 := by linarith [hmin j hj]
    simp only [lowerPositive, ite_eq_right hi, ite_eq_left hj]
    rw [hi0]
    simp only [zero_sub, abs_neg, abs_of_nonneg (hy j), abs_of_nonneg hja,
      mul_zero]
    ring
  · have hi0 : y i = 0 := by linarith [hy i]
    have hj0 : y j = 0 := by linarith [hy j]
    simp [lowerPositive, hi0, hj0]

theorem variation_lower_positive {ι : Type*} [Fintype ι]
    (a : ℝ) (q y : ι → ℝ) (r : ℝ) (hr : ∑ i, q i = r)
    (hy : ∀ i, 0 ≤ y i) (hmin : ∀ i, 0 < y i → a ≤ y i) :
    weightedVariation q y = weightedVariation q (lowerPositive a y)+
      a*mass (positiveSet y) q*(r-mass (positiveSet y) q) := by
  classical
  let s := positiveSet y
  let f : ι → ℝ := fun i => if i ∈ s then q i else 0
  let g : ι → ℝ := fun i => if i ∈ s then 0 else q i
  have hf : ∑ i, f i = mass s q := masked_sum s q
  have hg : ∑ i, g i = r-mass s q := complement_masked_sum s q r hr
  have hp : ∀ i j, q i*q j*|y i-y j| = q i*q j*|lowerPositive a y i-lowerPositive a y j|+
      a*(f i*g j+g i*f j) := by
    intro i j
    simpa only [f, g, s, positiveSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      positive_pair_decomposition a q y hy hmin i j
  have hcross : (∑ i, ∑ j, a*(f i*g j+g i*f j)) =
      a*((∑ i, f i)*(∑ j, g j)+(∑ i, g i)*(∑ j, f j)) := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum : (∑ i, ∑ j, q i*q j*|y i-y j|) =
      (∑ i, ∑ j, q i*q j*|lowerPositive a y i-lowerPositive a y j|)+
      a*((∑ i, f i)*(∑ j, g j)+(∑ i, g i)*(∑ j, f j)) := by
    simp_rw [hp]
    simp only [Finset.sum_add_distrib]
    rw [hcross]
  rw [hf, hg] at hsum
  unfold weightedVariation
  dsimp [s] at hsum
  linarith

theorem demand_lower_positive {ι : Type*} [Fintype ι]
    (a : ℝ) (q v y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (∑ i, q i*v i*y i) = (∑ i, q i*v i*lowerPositive a y i)+
      a*(∑ i ∈ positiveSet y, q i*v i) := by
  classical
  have hp : ∀ i, q i*v i*y i = q i*v i*lowerPositive a y i+
      a*(if i ∈ positiveSet y then q i*v i else 0) := by
    intro i
    by_cases hi : 0 < y i
    · simp only [lowerPositive, positiveSet, Finset.mem_filter,
        Finset.mem_univ, true_and, ite_eq_left hi]
      ring
    · have hi0 : y i = 0 := by linarith [hy i]
      simp [lowerPositive, positiveSet, hi0]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, masked_sum]
  rfl

/-- Finite layer-cake extension of all subset cuts to every nonnegative
    linear test vector. No separation or completion theorem is assumed. -/
theorem cuts_dual_bound {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hr : ∑ i, q i = r) (hc : Cuts M r q v)
    (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (∑ i, q i*v i*y i) ≤ M*weightedVariation q y := by
  classical
  by_cases hs : (positiveSet y).Nonempty
  · let s := positiveSet y
    let t := s.image y
    have ht : t.Nonempty := hs.image y
    let a := t.min' ht
    have hamem : a ∈ t := Finset.min'_mem t ht
    obtain ⟨i, hi, hai⟩ := Finset.mem_image.mp hamem
    have ha : 0 < a := by
      rw [← hai]
      exact (Finset.mem_filter.mp hi).2
    have hmin : ∀ j, 0 < y j → a ≤ y j := by
      intro j hj
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
    have hnonneg : ∀ j, 0 ≤ lowerPositive a y j := by
      intro j
      dsimp [lowerPositive]
      split
      · rename_i hj
        linarith [hmin j hj]
      · exact le_rfl
    have hsub : positiveSet (lowerPositive a y) ⊆ s.erase i := by
      intro j hj
      have hjpos : 0 < lowerPositive a y j := (Finset.mem_filter.mp hj).2
      have hjy : 0 < y j := by
        by_contra hn
        simp only [lowerPositive, ite_eq_right hn] at hjpos
        linarith
      have hji : j ≠ i := by
        intro he
        subst j
        simp [lowerPositive, hai, ha] at hjpos
      exact Finset.mem_erase.mpr ⟨hji, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjy⟩⟩
    have hcard : (positiveSet (lowerPositive a y)).card < (positiveSet y).card :=
      lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hi)
    have ih := cuts_dual_bound q v M r hr hc (lowerPositive a y) hnonneg
    calc
      _ = (∑ j, q j*v j*lowerPositive a y j)+a*(∑ j ∈ positiveSet y, q j*v j) :=
        demand_lower_positive a q v y hy
      _ ≤ M*weightedVariation q (lowerPositive a y)+a*(M*mass (positiveSet y) q*(r-mass (positiveSet y) q)) :=
        add_le_add ih (mul_le_mul_of_nonneg_left (hc (positiveSet y)) (le_of_lt ha))
      _ = _ := by
        rw [variation_lower_positive a q y r hr hy hmin]
        ring
  · have hy0 : ∀ i, y i = 0 := by
      intro i
      have hn : ¬0 < y i := by
        intro hi
        exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      linarith [hy i]
    simp only [hy0, mul_zero, Finset.sum_const_zero, weightedVariation, sub_self, abs_zero, zero_div, le_refl]
termination_by (positiveSet y).card
decreasing_by exact hcard

end
end SparseCompletion

/- Fixed source body: CompletionGeometry.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section

open scoped BigOperators
open Set

namespace SparseCompletion
noncomputable section

def skewBox {ι : Type*} (M : ℝ) : Set (ι → ι → ℝ) :=
  {B | IsSkew B ∧ ∀ i j, -M ≤ B i j ∧ B i j ≤ M}

def weightedNegResponse {ι : Type*} [Fintype ι] (q : ι → ℝ) :
    (ι → ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun B i := -q i*response B q i
  map_add' B C := by
    ext i
    change -q i*response (B+C) q i = -q i*response B q i+-q i*response C q i
    simp only [response, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' a B := by
    ext i
    change -q i*(∑ j, (a*B i j)*q j) = a*(-q i*∑ j, B i j*q j)
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

theorem skewBox_zero {ι : Type*} (M : ℝ) (hM : 0 ≤ M) :
    (0 : ι → ι → ℝ) ∈ skewBox M := by
  constructor
  · intro i j
    simp
  · intro i j
    exact ⟨neg_nonpos.mpr hM, hM⟩

theorem skewBox_compact {ι : Type*} [Fintype ι] (M : ℝ) : IsCompact (skewBox (ι := ι) M) := by
  have hclosed : IsClosed {B : ι → ι → ℝ | IsSkew B} := by
    have heq : {B : ι → ι → ℝ | IsSkew B} = ⋂ i, ⋂ j, {B | B i j = -B j i} := by
      ext B
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, IsSkew]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  have heq : skewBox (ι := ι) M =
      Set.Icc (fun _ _ => -M) (fun _ _ => M) ∩ {B | IsSkew B} := by
    ext B
    constructor
    · rintro ⟨hsk, hb⟩
      exact ⟨⟨fun i j => (hb i j).1, fun i j => (hb i j).2⟩, hsk⟩
    · rintro ⟨⟨hl, hu⟩, hsk⟩
      exact ⟨hsk, fun i j => ⟨hl i j, hu i j⟩⟩
  rw [heq]
  exact isCompact_Icc.inter_right hclosed

theorem skewBox_convex {ι : Type*} (M : ℝ) : Convex ℝ (skewBox (ι := ι) M) := by
  intro B hB C hC a b ha hb hab
  constructor
  · intro i j
    change a*B i j+b*C i j = -(a*B j i+b*C j i)
    rw [hB.1 i j, hC.1 i j]
    ring
  · intro i j
    change -M ≤ a*B i j+b*C i j ∧ a*B i j+b*C i j ≤ M
    constructor
    · calc
        -M = a*(-M)+b*(-M) := by rw [← add_mul, hab, one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hB.2 i j).1 ha)
          (mul_le_mul_of_nonneg_left (hC.2 i j).1 hb)
    · calc
        _ ≤ a*M+b*M := add_le_add (mul_le_mul_of_nonneg_left (hB.2 i j).2 ha)
          (mul_le_mul_of_nonneg_left (hC.2 i j).2 hb)
        _ = M := by rw [← add_mul, hab, one_mul]

def weightedScoreSet {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) : Set (ι → ℝ) :=
  weightedNegResponse q '' skewBox M

theorem weightedScoreSet_compact {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) :
    IsCompact (weightedScoreSet q M) :=
  (skewBox_compact M).image (weightedNegResponse q).continuous_of_finiteDimensional

theorem weightedScoreSet_convex {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) :
    Convex ℝ (weightedScoreSet q M) := (skewBox_convex M).linear_image (weightedNegResponse q)

theorem weightedScoreSet_zero {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) :
    (0 : ι → ℝ) ∈ weightedScoreSet q M :=
  ⟨0, skewBox_zero M hM, (weightedNegResponse q).map_zero⟩

def upperOrthant {ι : Type*} (d : ι → ℝ) : Set (ι → ℝ) := {z | ∀ i, d i ≤ z i}

theorem upperOrthant_closed {ι : Type*} (d : ι → ℝ) : IsClosed (upperOrthant d) := by
  have heq : upperOrthant d = ⋂ i, {z | d i ≤ z i} := by
    ext z
    simp only [upperOrthant, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)

theorem upperOrthant_convex {ι : Type*} (d : ι → ℝ) : Convex ℝ (upperOrthant d) := by
  intro z hz w hw a b ha hb hab i
  change d i ≤ a*z i+b*w i
  calc
    d i = a*d i+b*d i := by rw [← add_mul, hab, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hz i) ha) (mul_le_mul_of_nonneg_left (hw i) hb)

theorem dual_evaluation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : StrongDual ℝ (ι → ℝ)) (z : ι → ℝ) :
    f z = ∑ i, f (Pi.single i 1)*z i := by
  have hz : z = ∑ i, z i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hz, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  ring

theorem separator_coefficients_nonnegative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (f : StrongDual ℝ (ι → ℝ)) (v : ℝ)
    (hf : ∀ z ∈ upperOrthant d, v < f z) : ∀ i, 0 ≤ f (Pi.single i 1) := by
  intro i
  have hfd : v < f d := hf d (fun _ => le_rfl)
  by_contra hn
  have hneg : f (Pi.single i 1) < 0 := lt_of_not_ge hn
  let a := (f d-v+1)/(-f (Pi.single i 1))
  have ha : 0 ≤ a := le_of_lt (div_pos (by linarith) (neg_pos.mpr hneg))
  have hz : d+a • Pi.single i (1 : ℝ) ∈ upperOrthant d := by
    intro j
    change d j ≤ d j+a*(Pi.single i (1 : ℝ) : ι → ℝ) j
    have hsingle : 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := by
      simp only [Pi.single_apply]
      split <;> norm_num
    exact le_add_of_nonneg_right (mul_nonneg ha hsingle)
  have ht := hf _ hz
  rw [map_add, map_smul] at ht
  have hprod : a*f (Pi.single i 1) = -(f d-v+1) := by
    dsimp [a]
    field_simp [ne_of_lt hneg]
  change v < f d+a*f (Pi.single i 1) at ht
  rw [hprod] at ht
  linarith

theorem skew_dot_identity {ι : Type*} [Fintype ι]
    (q y : ι → ℝ) (B : ι → ι → ℝ) (hB : IsSkew B) :
    (∑ i, y i*weightedNegResponse q B i) =
      (∑ i, ∑ j, q i*q j*(-B i j)*(y i-y j))/2 := by
  let S₁ := ∑ i, ∑ j, q i*q j*B i j*y i
  let S₂ := ∑ i, ∑ j, q i*q j*B i j*y j
  have hdot : (∑ i, y i*weightedNegResponse q B i) = -S₁ := by
    change (∑ i, y i*(-q i*response B q i)) = -S₁
    dsimp [S₁, response]
    rw [← Finset.sum_neg_distrib]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hswap : S₂ = -S₁ := by
    dsimp [S₁, S₂]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hB j i]
    ring
  have hterm : ∀ i j, q i*q j*(-B i j)*(y i-y j) =
      -(q i*q j*B i j*y i)+q i*q j*B i j*y j := by intros; ring
  have hdiff : (∑ i, ∑ j, q i*q j*(-B i j)*(y i-y j)) = -S₁+S₂ := by
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rfl
  rw [hdot, hdiff, hswap]
  ring

def orderedMatrix {ι : Type*} (M : ℝ) (y : ι → ℝ) (i j : ι) : ℝ := by
  classical
  exact if y j < y i then -M else if y i < y j then M else 0

theorem orderedMatrix_skew {ι : Type*} (M : ℝ) (y : ι → ℝ) : IsSkew (orderedMatrix M y) := by
  intro i j
  rcases lt_trichotomy (y i) (y j) with hij | heq | hji
  · simp [orderedMatrix, hij, not_lt.mpr (le_of_lt hij)]
  · simp [orderedMatrix, heq]
  · simp [orderedMatrix, hji, not_lt.mpr (le_of_lt hji)]

theorem orderedMatrix_mem_box {ι : Type*} (M : ℝ) (y : ι → ℝ) (hM : 0 ≤ M) :
    orderedMatrix M y ∈ skewBox M := by
  refine ⟨orderedMatrix_skew M y, ?_⟩
  intro i j
  unfold orderedMatrix
  split_ifs <;> constructor <;> linarith

theorem orderedMatrix_pair {ι : Type*} (M : ℝ) (y : ι → ℝ) (i j : ι) :
    (-orderedMatrix M y i j)*(y i-y j) = M*|y i-y j| := by
  classical
  by_cases hij : y j < y i
  · simp only [orderedMatrix, ite_eq_left hij, neg_neg, abs_of_pos (sub_pos.mpr hij)]
  · by_cases hji : y i < y j
    · simp only [orderedMatrix, ite_eq_right hij, ite_eq_left hji, abs_of_neg (sub_neg.mpr hji)]
      ring
    · have heq : y i = y j := by linarith
      simp [orderedMatrix, heq]

theorem orderedMatrix_dot {ι : Type*} [Fintype ι] (M : ℝ) (q y : ι → ℝ) :
    (∑ i, y i*weightedNegResponse q (orderedMatrix M y) i) = M*weightedVariation q y := by
  rw [skew_dot_identity q y _ (orderedMatrix_skew M y)]
  have ht : ∀ i j, q i*q j*(-orderedMatrix M y i j)*(y i-y j) = M*(q i*q j*|y i-y j|) := by
    intro i j
    calc
      _ = q i*q j*((-orderedMatrix M y i j)*(y i-y j)) := by ring
      _ = _ := by rw [orderedMatrix_pair]; ring
  simp only [ht, ← Finset.mul_sum, weightedVariation]
  ring

/-- Every family of subset cuts has a bounded skew realization in weighted
    coordinates. Zero weights require no cancellation in this theorem. -/
theorem cuts_weighted_completion {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 ≤ M)
    (hr : ∑ i, q i = r) (hc : Cuts M r q v) :
    ∃ B ∈ skewBox M, ∀ i, q i*v i ≤ -q i*response B q i := by
  classical
  let d : ι → ℝ := fun i => q i*v i
  have hinter : (weightedScoreSet q M ∩ upperOrthant d).Nonempty := by
    by_contra hn
    have hdisj : Disjoint (weightedScoreSet q M) (upperOrthant d) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨f, u, w, hleft, huw, hright⟩ :=
      geometric_hahn_banach_compact_closed (weightedScoreSet_convex q M)
        (weightedScoreSet_compact q M) (upperOrthant_convex d)
        (upperOrthant_closed d) hdisj
    let y : ι → ℝ := fun i => f (Pi.single i 1)
    have hy : ∀ i, 0 ≤ y i := separator_coefficients_nonnegative d f w hright
    have hbound : f d ≤ M*weightedVariation q y := by
      rw [dual_evaluation]
      have hterms : (∑ i, f (Pi.single i 1)*d i) = ∑ i, q i*v i*y i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [d, y]
        ring
      rw [hterms]
      exact cuts_dual_bound q v M r hr hc y hy
    have hscore : weightedNegResponse q (orderedMatrix M y) ∈ weightedScoreSet q M :=
      ⟨orderedMatrix M y, orderedMatrix_mem_box M y hM, rfl⟩
    have heval : f (weightedNegResponse q (orderedMatrix M y)) = M*weightedVariation q y := by
      rw [dual_evaluation]
      exact orderedMatrix_dot M q y
    have hl := hleft _ hscore
    have hrgt := hright d (fun _ => le_rfl)
    rw [heval] at hl
    linarith
  obtain ⟨z, ⟨B, hB, rfl⟩, hz⟩ := hinter
  exact ⟨B, hB, hz⟩

end
end SparseCompletion

/- Fixed source body: CompletionCriterion.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- The weighted cuts and global guards reconstruct every row, including
    rows whose prescribed probability is zero. -/
theorem completion_of_cuts_and_guards {ι : Type*} [Fintype ι]
    (q t : ι → ℝ) (M r ρ : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r)
    (hc : Cuts M r q (fun i => t i-ρ)) (hg : ∀ i, t i ≤ ρ+M*r) :
    ∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ρ := by
  classical
  obtain ⟨B, hB, hw⟩ := cuts_weighted_completion q (fun i => t i-ρ) M r hM hr hc
  let s := Finset.univ.filter fun i => q i ≠ 0
  have hs : ∀ j, j ∉ s → q j = 0 := by
    intro j hj
    by_contra hn
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩)
  refine ⟨compactCompletion s M B, compactCompletion_skew s M B (fun i _ j _ => hB.1 i j),
    compactCompletion_bounds s M B hM (fun i _ j _ => hB.2 i j), ?_⟩
  intro i
  by_cases hi : i ∈ s
  · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm (Finset.mem_filter.mp hi).2)
    have hrow : t i+response B q i ≤ ρ := by
      have hh := hw i
      nlinarith
    have hsum : (∑ j ∈ s, B i j*q j) = response B q i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      rw [hs j hj, mul_zero]
    rw [compactCompletion_response_on s M B q hs i hi, hsum]
    exact hrow
  · rw [compactCompletion_response_off s M r B q hs hr i hi]
    linarith [hg i]

/-- Exact weighted completion criterion, with no positivity requirement on
    individual weights and no division by a probability coordinate. -/
theorem weighted_completion_iff {ι : Type*} [Fintype ι]
    (q t : ι → ℝ) (M r ρ : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ρ) ↔
    (∀ i, t i ≤ ρ+M*r) ∧ Cuts M r q (fun i => t i-ρ) := by
  classical
  constructor
  · rintro ⟨B, hsk, hb, hresp⟩
    exact ⟨response_guard q t B M r ρ hq hr (fun i j => (hb i j).1) hresp,
      completion_cuts_necessary q t B M r ρ hq hr hsk (fun i j => (hb i j).1) hresp⟩
  · rintro ⟨hg, hc⟩
    exact completion_of_cuts_and_guards q t M r ρ hM hq hr hc hg

end
end SparseCompletion

/- Fixed source body: SparseCompletionWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- A moment-preserving sparse witness with a reconstructed bounded skew
    completion. Every original row is retained in the response inequality. -/
theorem game_sparse_completion {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  obtain ⟨q', hq', hm', hs, hn, ha, hg, hc⟩ :=
    game_sparse_cut_certificate k K D B p q M r ρ η hM hr hη hq hmass hB hbound hresp
  obtain ⟨B', hsk', hb', hres'⟩ := completion_of_cuts_and_guards q' (score D p)
    M r (ρ+η) (le_of_lt hM) hq' hm' hc hg
  refine ⟨q', B', hq', hm', hs, hn, ha, hsk', hb', ?_⟩
  apply (block_response_bounds_iff K D B' p q' (ρ+η)).mpr
  refine ⟨?_, hres'⟩
  intro h
  rw [ha h]
  have hh := ((block_response_bounds_iff K D B p q ρ).mp hresp).1 h
  linarith

/-- Exact equilibria save the bottom hinge constraint, hence one support
    point, while still producing an actual completion on all original rows. -/
theorem exact_game_sparse_completion {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  obtain ⟨q', hq', hm', hs, hn, ha, hg, hc⟩ :=
    exact_game_sparse_cut_certificate k K D B p q M r η hM hr hη hp hq hmass hK hB hbound hresp
  obtain ⟨B', hsk', hb', hres'⟩ := completion_of_cuts_and_guards q' (score D p)
    M r η (le_of_lt hM) hq' hm' hc hg
  refine ⟨q', B', hq', hm', hs, hn, ha, hsk', hb', ?_⟩
  apply (block_response_bounds_iff K D B' p q' η).mpr
  refine ⟨?_, hres'⟩
  intro h
  rw [ha h]
  have hh := ((block_response_bounds_iff K D B p q 0).mp hresp).1 h
  linarith

end
end SparseCompletion

/- Fixed source body: PaperWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem block_support_card {α ι : Type*} [Fintype α] [Fintype ι]
    (p : α → ℝ) (q : ι → ℝ) :
    (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card =
      (Finset.univ.filter fun h => p h ≠ 0).card+
      (Finset.univ.filter fun i => q i ≠ 0).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_sum_type, blockWeights, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- Normalized, bounded whole-game specialization of the sparse witness.
    The conclusion preserves the prescribed anchor shares literally. -/
theorem normalized_sparse_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+gridSize M r η ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ (2 : ℕ)*k+1+gridSize M r η ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  obtain ⟨q', B', hn, hm, hs, hc, ha, hsk, hb, he⟩ :=
    game_sparse_completion k K D B p q M r ρ η hM hr hη hq hqmass hB
      (fun i j => (hBb i j).1) hresp
  refine ⟨q', B', blockWeights_nonneg p q' hp hn, ?_, fun _ => rfl, hs, hc, ?_, ?_,
    blockMatrix_skew K D B' hK hsk, blockMatrix_bounds K D B' M hKb hDb hb, he⟩
  · rw [blockWeights_mass, hm]
    exact hpmass
  · rw [block_support_card]
    have hanchor : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  · intro h
    have hh := ha h
    unfold anchorResponse at hh
    have hsums : (∑ i, D i h*q' i) = ∑ i, D i h*q i := by linarith
    simpa only [mul_comm] using hsums
/-- Normalized, bounded whole-game specialization of the sparse witness.
    The conclusion preserves the prescribed anchor shares literally. -/
theorem normalized_exact_sparse_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+gridSize M r η ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ (2 : ℕ)*k+gridSize M r η ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  obtain ⟨q', B', hn, hm, hs, hc, ha, hsk, hb, he⟩ :=
    exact_game_sparse_completion k K D B p q M r η hM hr hη hp hq hqmass hK hB hBb hresp
  refine ⟨q', B', blockWeights_nonneg p q' hp hn, ?_, fun _ => rfl, hs, hc, ?_, ?_,
    blockMatrix_skew K D B' hK hsk, blockMatrix_bounds K D B' M hKb hDb hb, he⟩
  · rw [blockWeights_mass, hm]
    exact hpmass
  · rw [block_support_card]
    have hanchor : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  · intro h
    have hh := ha h
    unfold anchorResponse at hh
    have hsums : (∑ i, D i h*q' i) = ∑ i, D i h*q i := by linarith
    simpa only [mul_comm] using hsums

end
end SparseCompletion

/- Fixed source body: PrefixRigidity.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def prefixSet {m : ℕ} (l : ℕ) : Finset (Fin m) := Finset.univ.filter fun j => j.val < l

def prefixMass {m : ℕ} (q : Fin m → ℝ) (l : ℕ) : ℝ := mass (prefixSet l) q

theorem prefix_zero (m : ℕ) : prefixSet (m := m) 0 = ∅ := by
  ext j
  simp [prefixSet]

theorem prefix_full {m : ℕ} : prefixSet (m := m) m = Finset.univ := by
  ext j
  simp [prefixSet]

theorem prefix_succ {m : ℕ} (j : Fin m) :
    prefixSet (j.val+1) = insert j (prefixSet j.val) := by
  ext i
  simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hi
    by_cases he : i = j
    · exact Or.inl he
    · exact Or.inr (by have hn : i.val ≠ j.val := fun h => he (Fin.ext h); omega)
  · rintro (rfl | hi) <;> omega

theorem prefixMass_succ {m : ℕ} (q : Fin m → ℝ) (j : Fin m) :
    prefixMass q (j.val+1) = prefixMass q j.val+q j := by
  classical
  unfold prefixMass mass
  rw [prefix_succ, Finset.sum_insert]
  · ring
  · simp [prefixSet]

theorem prefixMass_zero {m : ℕ} (q : Fin m → ℝ) : prefixMass q 0 = 0 := by
  simp [prefixMass, mass, prefix_zero]

theorem prefixMass_full {m : ℕ} (q : Fin m → ℝ) : prefixMass q m = ∑ j, q j := by
  simp only [prefixMass, prefix_full, mass]

theorem equal_prefixes {m : ℕ} (q q' : Fin m → ℝ)
    (he : ∀ l ≤ m, prefixMass q l = prefixMass q' l) : q = q' := by
  funext j
  have h0 := he j.val (le_of_lt j.isLt)
  have h1 := he (j.val+1) (by omega)
  rw [prefixMass_succ, prefixMass_succ] at h1
  linarith

def orderedBlock {m : ℕ} (M : ℝ) (i j : Fin m) : ℝ :=
  if i < j then -M else if j < i then M else 0

theorem orderedBlock_skew {m : ℕ} (M : ℝ) : IsSkew (orderedBlock (m := m) M) := by
  intro i j
  rcases lt_trichotomy i j with h | h | h
  · simp [orderedBlock, h, not_lt.mpr (le_of_lt h)]
  · simp [orderedBlock, h]
  · simp [orderedBlock, h, not_lt.mpr (le_of_lt h)]

theorem orderedBlock_bounds {m : ℕ} (M : ℝ) (hM : 0 ≤ M) :
    ∀ i j : Fin m, -M ≤ orderedBlock M i j ∧ orderedBlock M i j ≤ M := by
  intro i j
  unfold orderedBlock
  split_ifs <;> constructor <;> linarith

def targetScore {m : ℕ} (q : Fin m → ℝ) (r : ℝ) (j : Fin m) : ℝ :=
  r-(2 : ℕ)*prefixMass q j.val-q j

theorem orderedBlock_response {m : ℕ} (q : Fin m → ℝ) (r : ℝ)
    (hr : ∑ j, q j = r) (j : Fin m) :
    response (orderedBlock 1) q j = -targetScore q r j := by
  classical
  have hterm : ∀ i, orderedBlock 1 j i*q i =
      2*(if i ∈ prefixSet j.val then q i else 0)+(if i=j then q i else 0)-q i := by
    intro i
    rcases lt_trichotomy i j with hi | hi | hi
    · have hnot : ¬(j < i) := not_lt.mpr (le_of_lt hi)
      simp only [orderedBlock, ite_eq_right hnot, prefixSet,
        Finset.mem_filter, Finset.mem_univ, true_and, ← Fin.lt_def, ite_eq_left hi,
        ite_eq_right (ne_of_lt hi), one_mul]
      ring
    · subst i
      simp [orderedBlock, prefixSet]
    · have hnot : ¬(i < j) := not_lt.mpr (le_of_lt hi)
      simp only [orderedBlock, ite_eq_left hi, prefixSet,
        Finset.mem_filter, Finset.mem_univ, true_and, ← Fin.lt_def, ite_eq_right hnot,
        ite_eq_right (ne_of_gt hi), neg_one_mul, mul_zero, add_zero, zero_sub]
  unfold response
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_filter, hr]
  simp only [Finset.filter_eq', Finset.mem_univ, ite_true, Finset.sum_singleton]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  unfold targetScore prefixMass mass
  ring

/-- Every prefixSet cut is tight at the prescribed target distribution. -/
theorem target_prefix_tight {m : ℕ} (q : Fin m → ℝ) (r : ℝ)
    (hr : ∑ j, q j = r) (l : ℕ) :
    (∑ j ∈ prefixSet l, q j*targetScore q r j) = prefixMass q l*(r-prefixMass q l) := by
  classical
  have hcancel := skew_weighted_sum (prefixSet l) q (orderedBlock 1) (orderedBlock_skew 1)
  have hcross : (∑ i ∈ prefixSet l, q i*response (orderedBlock 1) q i) =
      -(prefixMass q l*(r-prefixMass q l)) := by
    have hcompl : (∑ j ∈ (prefixSet l)ᶜ, q j) = r-prefixMass q l := by
      have hh := Finset.sum_add_sum_compl (prefixSet l) q
      unfold prefixMass mass
      linarith
    have hs : (∑ i ∈ prefixSet l, q i*response (orderedBlock 1) q i) =
        (∑ i ∈ prefixSet l, ∑ j ∈ prefixSet l, q i*orderedBlock 1 i j*q j)+
        ∑ i ∈ prefixSet l, ∑ j ∈ (prefixSet l)ᶜ, q i*orderedBlock 1 i j*q j := by
      simp only [response, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [← mul_assoc]
      exact (Finset.sum_add_sum_compl (prefixSet l) _).symm
    rw [hs, hcancel, zero_add]
    have hedges : ∀ (i : Fin m), i ∈ prefixSet l → ∀ (j : Fin m), j ∈ (prefixSet l)ᶜ → orderedBlock 1 i j = -1 := by
      intro i hi j hj
      have hi' : i.val < l := (Finset.mem_filter.mp hi).2
      have hj' : ¬j.val < l := by simpa only [Finset.mem_compl, prefixSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using hj
      have hij : i < j := by change i.val<j.val; omega
      simp only [orderedBlock, ite_eq_left hij]
    have hsums : (∑ i ∈ prefixSet l, ∑ j ∈ (prefixSet l)ᶜ, q i*orderedBlock 1 i j*q j) =
        -(∑ i ∈ prefixSet l, q i)*(∑ j ∈ (prefixSet l)ᶜ, q j) := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hedges j hj i hi]
      ring
    rw [hsums, hcompl]
    simp only [prefixMass, mass, neg_mul]
  have heq : (∑ j ∈ prefixSet l, q j*response (orderedBlock 1) q j) =
      -(∑ j ∈ prefixSet l, q j*targetScore q r j) := by
    simp_rw [orderedBlock_response q r hr]
    simp only [mul_neg, Finset.sum_neg_distrib]
  linarith

theorem prefixMass_nonneg {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (l : ℕ) :
    0 ≤ prefixMass q l := by
  unfold prefixMass mass
  exact Finset.sum_nonneg fun j _ => hq j

theorem prefixMass_mono {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (l n : ℕ) (hln : l ≤ n) : prefixMass q l ≤ prefixMass q n := by
  unfold prefixMass mass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hln⟩
  · exact fun j _ _ => hq j

theorem prefixMass_le_total {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (r : ℝ) (hr : ∑ j, q j = r) (l : ℕ) : prefixMass q l ≤ r := by
  rw [← hr]
  unfold prefixMass mass
  exact Finset.sum_le_univ_sum_of_nonneg fun j => hq j

theorem targetScore_bounds {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (r : ℝ) (hr : ∑ j, q j = r) (j : Fin m) :
    -r ≤ targetScore q r j ∧ targetScore q r j ≤ r := by
  have h0 := prefixMass_nonneg q hq j.val
  have h1 := prefixMass_le_total q hq r hr (j.val+1)
  rw [prefixMass_succ] at h1
  unfold targetScore
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith [hq j]

def prefixGap {m : ℕ} (q t : Fin m → ℝ) (r : ℝ) (l : ℕ) : ℝ :=
  (prefixMass q l)^2-r*prefixMass q l+∑ j ∈ prefixSet l, q j*t j

def exposingWeight {m : ℕ} (qstar : Fin m → ℝ) (r : ℝ) (j : Fin m) : ℝ :=
  (∑ l : Fin m, if j ∈ prefixSet l.val then
    (2 : ℕ)*prefixMass qstar l.val-r+targetScore qstar r j else 0)/(m : ℝ)

def scoreMoment {m : ℕ} (q w : Fin m → ℝ) : ℝ := ∑ j, q j*w j

theorem prefixGap_expansion {m : ℕ} (q qstar : Fin m → ℝ) (r : ℝ)
    (hr : ∑ j, qstar j = r) (l : ℕ) :
    prefixGap q (targetScore qstar r) r l =
      ((2*prefixMass qstar l-r)*(prefixMass q l-prefixMass qstar l)+
        ∑ j ∈ prefixSet l, (q j-qstar j)*targetScore qstar r j)+
      (prefixMass q l-prefixMass qstar l)^2 := by
  have ht := target_prefix_tight qstar r hr l
  unfold prefixGap
  simp only [sub_mul, Finset.sum_sub_distrib]
  nlinarith

theorem prefix_gradient_pairing {m : ℕ} (q qstar t : Fin m → ℝ) (c : ℝ) (l : ℕ) :
    (∑ j, (q j-qstar j)*(if j ∈ prefixSet l then c+t j else 0)) =
      c*(prefixMass q l-prefixMass qstar l)+∑ j ∈ prefixSet l, (q j-qstar j)*t j := by
  classical
  calc
    _ = ∑ j ∈ prefixSet l, (q j-qstar j)*(c+t j) := by
      simp only [mul_ite, mul_zero, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
    _ = _ := by
      simp only [mul_add, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, prefixMass, mass]
      ring

/-- The averaged gradient exposes the target by an exact sum of squared
    prefix deviations, without a uniform-target assumption. -/
theorem prefix_exposing_identity {m : ℕ} (q qstar : Fin m → ℝ) (r : ℝ)
    (hr : ∑ j, qstar j = r) :
    scoreMoment q (exposingWeight qstar r)-scoreMoment qstar (exposingWeight qstar r)+
      (∑ l : Fin m, (prefixMass q l.val-prefixMass qstar l.val)^2)/(m : ℝ) =
      (∑ l : Fin m, prefixGap q (targetScore qstar r) r l)/(m : ℝ) := by
  classical
  have hlinear : scoreMoment q (exposingWeight qstar r)-scoreMoment qstar (exposingWeight qstar r) =
      (∑ l : Fin m, ((2*prefixMass qstar l.val-r)*(prefixMass q l.val-prefixMass qstar l.val)+
        ∑ j ∈ prefixSet l.val, (q j-qstar j)*targetScore qstar r j))/(m : ℝ) := by
    unfold scoreMoment exposingWeight
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    simp only [← mul_div_assoc, Finset.mul_sum]
    rw [← Finset.sum_div, Finset.sum_comm]
    apply congrArg (fun z : ℝ => z/(m : ℝ))
    apply Finset.sum_congr rfl
    intro l _
    simpa only [Nat.cast_ofNat] using prefix_gradient_pairing q qstar (targetScore qstar r)
      (2*prefixMass qstar l.val-r) l.val
  rw [hlinear, ← add_div, ← Finset.sum_add_distrib]
  apply congrArg (fun z : ℝ => z/(m : ℝ))
  exact Finset.sum_congr rfl fun l _ => (prefixGap_expansion q qstar r hr l.val).symm

theorem cut_prefix_gap_nonpositive {m : ℕ} (q t : Fin m → ℝ) (r : ℝ)
    (hc : Cuts 1 r q t) (l : ℕ) : prefixGap q t r l ≤ 0 := by
  have hh := hc (prefixSet l)
  change (∑ j ∈ prefixSet l, q j*t j) ≤ 1*prefixMass q l*(r-prefixMass q l) at hh
  unfold prefixGap
  nlinarith

/-- A single explicitly constructed exposing moment and the prefix cuts
    force the entire target distribution. -/
theorem strict_prefix_rigidity {m : ℕ} (hm : 0 < m) (q qstar : Fin m → ℝ) (r : ℝ)
    (hq : ∑ j, q j = r) (ht : ∑ j, qstar j = r)
    (hc : Cuts 1 r q (targetScore qstar r))
    (hβ : scoreMoment qstar (exposingWeight qstar r) ≤ scoreMoment q (exposingWeight qstar r)) :
    q = qstar := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hid := prefix_exposing_identity q qstar r ht
  have hgap : (∑ l : Fin m, prefixGap q (targetScore qstar r) r l)/(m : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos fun l _ =>
      cut_prefix_gap_nonpositive q (targetScore qstar r) r hc l.val) (le_of_lt hmR)
  have hsq : (∑ l : Fin m, (prefixMass q l.val-prefixMass qstar l.val)^2) = 0 := by
    have hnonneg : 0 ≤ ∑ l : Fin m, (prefixMass q l.val-prefixMass qstar l.val)^2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hle : (∑ l : Fin m, (prefixMass q l.val-prefixMass qstar l.val)^2)/(m : ℝ) ≤ 0 := by
      linarith
    have hh := (div_le_iff₀ hmR).mp hle
    linarith
  apply equal_prefixes q qstar
  intro l hl
  by_cases he : l=m
  · subst l
    rw [prefixMass_full, prefixMass_full, hq, ht]
  · have hlt : l<m := by omega
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg (prefixMass q j.val-prefixMass qstar j.val))).mp hsq ⟨l,hlt⟩ (Finset.mem_univ _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh)

theorem exposing_gradient_bounds {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (r : ℝ) (hr : ∑ j, q j = r) (j : Fin m) (l : ℕ) (hjl : j.val < l) :
    0 ≤ 2*prefixMass q l-r+targetScore q r j ∧
      2*prefixMass q l-r+targetScore q r j ≤ 2*r := by
  have h0 := prefixMass_nonneg q hq j.val
  have h1 := prefixMass_le_total q hq r hr l
  have h2 := prefixMass_mono q hq (j.val+1) l (by omega)
  rw [prefixMass_succ] at h2
  unfold targetScore
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith [hq j]

theorem exposingWeight_bounds {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) (r : ℝ) (hr : ∑ j, q j = r) (j : Fin m) :
    0 ≤ exposingWeight q r j ∧ exposingWeight q r j ≤ 2*r := by
  classical
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hr0 : 0 ≤ r := by rw [← hr]; exact Finset.sum_nonneg fun i _ => hq i
  have hterm : ∀ l : Fin m,
      0 ≤ (if j ∈ prefixSet l.val then (2 : ℕ)*prefixMass q l.val-r+targetScore q r j else 0) ∧
      (if j ∈ prefixSet l.val then (2 : ℕ)*prefixMass q l.val-r+targetScore q r j else 0) ≤ 2*r := by
    intro l
    by_cases h : j ∈ prefixSet l.val
    · simpa only [ite_eq_left h, Nat.cast_ofNat] using
        exposing_gradient_bounds q hq r hr j l.val (Finset.mem_filter.mp h).2
    · simp only [ite_eq_right h, le_refl, true_and]
      positivity
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun l _ => (hterm l).1) (le_of_lt hmR)
  · apply (div_le_iff₀ hmR).mpr
    calc
      _ ≤ ∑ _l : Fin m, (2*r) := Finset.sum_le_sum fun l _ => (hterm l).2
      _ = _ := by simp; ring

theorem cross_response_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (q : ι → ℝ) (B : ι → ι → ℝ) (hB : IsSkew B) :
    (∑ i ∈ s, q i*response B q i) = ∑ i ∈ s, ∑ j ∈ sᶜ, q i*B i j*q j := by
  have hi := skew_weighted_sum s q B hB
  have hs : (∑ i ∈ s, q i*response B q i) =
      (∑ i ∈ s, ∑ j ∈ s, q i*B i j*q j)+∑ i ∈ s, ∑ j ∈ sᶜ, q i*B i j*q j := by
    simp only [response, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← mul_assoc]
    exact (Finset.sum_add_sum_compl s _).symm
  rw [hs, hi, zero_add]

/-- Tight prefix cuts with strictly positive weights determine every
    residual edge, not only the strategy. -/
theorem tight_prefix_completion_unique {m : ℕ} (q : Fin m → ℝ) (r : ℝ)
    (hq : ∀ j, 0 < q j) (hr : ∑ j, q j = r)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (hz : ∀ j, targetScore q r j+response B q j = 0) : B = orderedBlock 1 := by
  classical
  have hearly : ∀ i j : Fin m, i < j → B i j = -1 := by
    intro i j hij
    let s := prefixSet (m := m) (i.val+1)
    have hflow := cross_response_sum s q B hB
    have ht := target_prefix_tight q r hr (i.val+1)
    have hzsum : (∑ a ∈ s, q a*response B q a) = -(∑ a ∈ s, q a*targetScore q r a) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have hh : response B q a = -targetScore q r a := by linarith [hz a]
      rw [hh, mul_neg]
    have hcompl : (∑ b ∈ sᶜ, q b) = r-mass s q := by
      have hh := Finset.sum_add_sum_compl s q
      unfold mass
      linarith
    have hprod : (∑ a ∈ s, ∑ b ∈ sᶜ, q a*q b) = mass s q*(r-mass s q) := by
      rw [← hcompl]
      simp only [mass, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    have hsum : (∑ a ∈ s, ∑ b ∈ sᶜ, q a*(B a b+1)*q b) = 0 := by
      have he : (∑ a ∈ s, ∑ b ∈ sᶜ, q a*(B a b+1)*q b) =
          (∑ a ∈ s, ∑ b ∈ sᶜ, q a*B a b*q b)+(∑ a ∈ s, ∑ b ∈ sᶜ, q a*q b) := by
        simp only [mul_add, mul_one, add_mul, Finset.sum_add_distrib]
      rw [he, ← hflow, hzsum, hprod]
      change -(∑ a ∈ prefixSet (i.val+1), q a*targetScore q r a)+
        prefixMass q (i.val+1)*(r-prefixMass q (i.val+1)) = 0
      rw [ht]
      ring
    have hnonneg : ∀ a b, 0 ≤ q a*(B a b+1)*q b := by
      intro a b
      exact mul_nonneg (mul_nonneg (le_of_lt (hq a)) (by linarith [hb a b])) (le_of_lt (hq b))
    have hi : i ∈ s := by simp [s, prefixSet]
    have hj : j ∈ sᶜ := by
      have hval : i.val < j.val := hij
      simp only [s, Finset.mem_compl, prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hinner : (∑ b ∈ sᶜ, q i*(B i b+1)*q b) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => hnonneg a b)).mp hsum i hi
    have hedge : q i*(B i j+1)*q j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg i b)).mp hinner j hj
    have hqij : 0 < q i*q j := mul_pos (hq i) (hq j)
    nlinarith
  funext i j
  rcases lt_trichotomy i j with hij | heq | hji
  · rw [hearly i j hij]
    simp only [orderedBlock, ite_eq_left hij]
  · subst j
    have hh := hB i i
    simp only [orderedBlock, lt_irrefl, ite_false]
    linarith
  · rw [hB i j, hearly j i hji]
    simp only [orderedBlock, ite_eq_right (not_lt.mpr (le_of_lt hji)), ite_eq_left hji, neg_neg]

theorem cuts_exposing_moment_le {m : ℕ} (hm : 0 < m) (q qstar : Fin m → ℝ)
    (r : ℝ) (ht : ∑ j, qstar j = r) (hc : Cuts 1 r q (targetScore qstar r)) :
    scoreMoment q (exposingWeight qstar r) ≤ scoreMoment qstar (exposingWeight qstar r) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hid := prefix_exposing_identity q qstar r ht
  have hgap : (∑ l : Fin m, prefixGap q (targetScore qstar r) r l)/(m : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos fun l _ =>
      cut_prefix_gap_nonpositive q (targetScore qstar r) r hc l.val) (le_of_lt hmR)
  have hs : 0 ≤ (∑ l : Fin m, (prefixMass q l.val-prefixMass qstar l.val)^2)/(m : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (le_of_lt hmR)
  linarith

theorem exposingWeight_positive {m : ℕ} (hm : 0 < m) (qstar : Fin m → ℝ)
    (r : ℝ) (hq : ∀ j, 0 < qstar j) (hr : ∑ j, qstar j = r)
    (j : Fin m) (hj : j.val+1<m) : 0 < exposingWeight qstar r j := by
  classical
  have hn : ∀ j, 0 ≤ qstar j := fun j => le_of_lt (hq j)
  let l : Fin m := ⟨j.val+1,hj⟩
  have hterm : ∀ a : Fin m, 0 ≤
      (if j ∈ prefixSet a.val then (2 : ℕ)*prefixMass qstar a.val-r+targetScore qstar r j else 0) := by
    intro a
    by_cases h : j ∈ prefixSet a.val
    · simpa only [ite_eq_left h, Nat.cast_ofNat] using
        (exposing_gradient_bounds qstar hn r hr j a.val (Finset.mem_filter.mp h).2).1
    · rw [ite_eq_right h]
  have hl : (if j ∈ prefixSet l.val then (2 : ℕ)*prefixMass qstar l.val-r+targetScore qstar r j else 0) = qstar j := by
    have hmem : j ∈ prefixSet l.val := by simp [l, prefixSet]
    rw [ite_eq_left hmem]
    change (2 : ℕ)*prefixMass qstar (j.val+1)-r+targetScore qstar r j = qstar j
    rw [prefixMass_succ]
    unfold targetScore
    ring
  have hs := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => hterm a) (Finset.mem_univ l)
  rw [hl] at hs
  exact div_pos (lt_of_lt_of_le (hq j) hs) (Nat.cast_pos.mpr hm)

end
end SparseCompletion

/- Fixed source body: TwoAnchorRigidity.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def twoCore (a : ℝ) (i j : Fin 2) : ℝ :=
  if i=j then 0 else if i.val=0 then a else -a

def twoCross {m : ℕ} (t w : Fin m → ℝ) (p : ℝ) (j : Fin m) (h : Fin 2) : ℝ :=
  if h.val=0 then t j/p+w j else t j/p-w j

def twoShares (p : ℝ) : Fin 2 → ℝ := fun _ => p/(2 : ℕ)

theorem twoCore_skew (a : ℝ) : IsSkew (twoCore a) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [twoCore]

theorem two_score {m : ℕ} (t w : Fin m → ℝ) (p : ℝ) (hp : p ≠ 0) :
    score (twoCross t w p) (twoShares p) = t := by
  funext j
  simp only [score, Fin.sum_univ_two, twoCross, twoShares]
  norm_num
  field_simp
  ring

theorem two_anchor_responses {m : ℕ} (t w q : Fin m → ℝ) (p βstar : ℝ) (hp : p ≠ 0) :
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 0 =
      -scoreMoment q t/p-(scoreMoment q w-βstar) ∧
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 1 =
      -scoreMoment q t/p+(scoreMoment q w-βstar) := by
  have hsum : (∑ i, t i/p*q i) = scoreMoment q t/p := by
    unfold scoreMoment
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hw : (∑ i, w i*q i) = scoreMoment q w := by
    unfold scoreMoment
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor <;>
    simp only [anchorResponse, Fin.sum_univ_two, twoCore, twoCross, twoShares] <;>
    norm_num <;>
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hw] <;>
    field_simp <;> ring

/-- Fixed-share equilibrium in the two-anchor encoding forces every
    residual probability, for any prescribed target distribution. -/
theorem two_anchor_strategy_rigidity {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (p r : ℝ) (hp : 0 < p)
    (hq : ∀ j, 0 ≤ q j) (hqm : ∑ j, q j = r) (htm : ∑ j, qstar j = r)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (hresp : ∀ a, response
      (blockMatrix (twoCore (2*scoreMoment qstar (exposingWeight qstar r)/p))
        (twoCross (targetScore qstar r) (exposingWeight qstar r) p) B)
      (blockWeights (twoShares p) q) a ≤ 0) : q = qstar := by
  let t := targetScore qstar r
  let w := exposingWeight qstar r
  let βstar := scoreMoment qstar w
  let K := twoCore (2*βstar/p)
  let D := twoCross t w p
  have hs : score D (twoShares p) = t := two_score t w p (ne_of_gt hp)
  have hmean : scoreMoment q t = 0 := by
    have hh := exact_score_mean_zero K D B (twoShares p) q
      (fun _ => div_nonneg (le_of_lt hp) (by norm_num)) hq (twoCore_skew _) hB hresp
    rw [hs] at hh
    exact hh
  have ha := ((block_response_bounds_iff K D B (twoShares p) q 0).mp hresp).1
  have hf := two_anchor_responses t w q p βstar (ne_of_gt hp)
  have h0 : anchorResponse K D (twoShares p) q 0 ≤ 0 := ha 0
  have h1 : anchorResponse K D (twoShares p) q 1 ≤ 0 := ha 1
  change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 0 ≤ 0 at h0
  change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) q 1 ≤ 0 at h1
  rw [hf.1, hmean] at h0
  rw [hf.2, hmean] at h1
  have hβ : βstar ≤ scoreMoment q w := by simp only [neg_zero, zero_div, zero_sub] at h0; linarith
  have hrows := ((block_response_bounds_iff K D B (twoShares p) q 0).mp hresp).2
  rw [hs] at hrows
  have hc0 := completion_cuts_necessary q t B 1 r 0 hq hqm hB hb hrows
  have hc : Cuts 1 r q t := by simpa only [sub_zero] using hc0
  exact strict_prefix_rigidity hm q qstar r hqm htm hc hβ

theorem target_score_moment_zero {m : ℕ} (q : Fin m → ℝ) (r : ℝ)
    (hr : ∑ j, q j = r) : scoreMoment q (targetScore q r) = 0 := by
  have hh := skew_weighted_sum Finset.univ q (orderedBlock 1) (orderedBlock_skew 1)
  have hz : (∑ j, q j*response (orderedBlock 1) q j) = -scoreMoment q (targetScore q r) := by
    simp_rw [orderedBlock_response q r hr]
    simp only [mul_neg, Finset.sum_neg_distrib, scoreMoment]
  simp only [response, Finset.mul_sum] at hz
  simp only [mul_assoc] at hh
  rw [hh] at hz
  linarith

theorem two_anchor_target_feasible {m : ℕ} (qstar : Fin m → ℝ) (p r : ℝ) (hp : p ≠ 0)
    (htm : ∑ j, qstar j = r) :
    ∀ a, response
      (blockMatrix (twoCore (2*scoreMoment qstar (exposingWeight qstar r)/p))
        (twoCross (targetScore qstar r) (exposingWeight qstar r) p) (orderedBlock 1))
      (blockWeights (twoShares p) qstar) a = 0 := by
  let t := targetScore qstar r
  let w := exposingWeight qstar r
  let βstar := scoreMoment qstar w
  have ht : scoreMoment qstar t = 0 := target_score_moment_zero qstar r htm
  have hs : score (twoCross t w p) (twoShares p) = t := two_score t w p hp
  have hf := two_anchor_responses t w qstar p βstar hp
  intro a
  cases a with
  | inl h =>
    rw [block_response_anchor]
    fin_cases h
    · change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) qstar 0 = 0
      rw [hf.1, ht]
      simp only [βstar, neg_zero, zero_div, sub_self]
    · change anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) (twoShares p) qstar 1 = 0
      rw [hf.2, ht]
      simp only [βstar, neg_zero, zero_div, sub_self, add_zero]
  | inr j =>
    rw [block_response_residual, hs, orderedBlock_response qstar r htm]
    exact add_neg_cancel _

/-- The fixed-share encoding determines both the target mixture and the
    entire otherwise unknown residual block. -/
theorem two_anchor_fixed_share_uniqueness {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (p r : ℝ) (hp : 0 < p)
    (htpos : ∀ j, 0 < qstar j) (hq : ∀ j, 0 ≤ q j)
    (hqm : ∑ j, q j = r) (htm : ∑ j, qstar j = r)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (hresp : ∀ a, response
      (blockMatrix (twoCore ((2 : ℕ)*scoreMoment qstar (exposingWeight qstar r)/p))
        (twoCross (targetScore qstar r) (exposingWeight qstar r) p) B)
      (blockWeights (twoShares p) q) a ≤ 0) : q = qstar ∧ B = orderedBlock 1 := by
  norm_num only [Nat.cast_ofNat] at *
  have hqeq := two_anchor_strategy_rigidity hm qstar q p r hp hq hqm htm B hB hb hresp
  refine ⟨hqeq, ?_⟩
  subst q
  have hs := two_score (targetScore qstar r) (exposingWeight qstar r) p (ne_of_gt hp)
  have hzero := exact_supported_residual_zero
    (twoCore (2*scoreMoment qstar (exposingWeight qstar r)/p))
    (twoCross (targetScore qstar r) (exposingWeight qstar r) p) B (twoShares p) qstar
    (fun _ => div_nonneg (le_of_lt hp) (by norm_num)) hq (twoCore_skew _) hB hresp
  rw [hs] at hzero
  exact tight_prefix_completion_unique qstar r htpos htm B hB hb
    (fun j => hzero j (ne_of_gt (htpos j)))

theorem exposing_moment_bounds {m : ℕ} (hm : 0 < m) (qstar : Fin m → ℝ)
    (r : ℝ) (hq : ∀ j, 0 ≤ qstar j) (hr : ∑ j, qstar j = r) :
    0 ≤ scoreMoment qstar (exposingWeight qstar r) ∧
      scoreMoment qstar (exposingWeight qstar r) ≤ 2*r^2 := by
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (exposingWeight_bounds hm qstar hq r hr j).1
  · calc
      _ ≤ ∑ j, qstar j*(2*r) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (exposingWeight_bounds hm qstar hq r hr j).2 (hq j)
      _ = _ := by rw [← Finset.sum_mul, hr]; ring

/-- The arbitrary-target two-anchor observations are uniformly bounded;
    the construction does not encode probabilities using large payoffs. -/
theorem two_anchor_observed_bounds {m : ℕ} (hm : 0 < m) (qstar : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ qstar j) (hr : ∑ j, qstar j = 1/4) :
    (∀ i j, -1 ≤ twoCore (2*scoreMoment qstar (exposingWeight qstar (1/4))/(3/4)) i j ∧
      twoCore (2*scoreMoment qstar (exposingWeight qstar (1/4))/(3/4)) i j ≤ 1) ∧
    (∀ j h, -1 ≤ twoCross (targetScore qstar (1/4)) (exposingWeight qstar (1/4)) (3/4) j h ∧
      twoCross (targetScore qstar (1/4)) (exposingWeight qstar (1/4)) (3/4) j h ≤ 1) := by
  have hβ := exposing_moment_bounds hm qstar (1/4) hq hr
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp only [twoCore] <;> norm_num <;>
      constructor <;> nlinarith [hβ.1, hβ.2]
  · intro j h
    have ht := targetScore_bounds qstar hq (1/4) hr j
    have hw := exposingWeight_bounds hm qstar hq (1/4) hr j
    fin_cases h <;> simp only [twoCross] <;> norm_num <;>
      constructor <;> nlinarith [ht.1, ht.2, hw.1, hw.2]

def rigidityCore {m : ℕ} (qstar : Fin m → ℝ) : Fin 2 → Fin 2 → ℝ :=
  twoCore ((2 : ℕ)*scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ)))/((3 : ℕ)/(4 : ℕ)))

def rigidityCross {m : ℕ} (qstar : Fin m → ℝ) : Fin m → Fin 2 → ℝ :=
  twoCross (targetScore qstar (1/(4 : ℕ))) (exposingWeight qstar (1/(4 : ℕ))) ((3 : ℕ)/(4 : ℕ))

/-- A normalized bounded two-anchor game realizes any positive residual
    target as its unique fixed-share equilibrium-compatible witness. -/
theorem bounded_two_anchor_fixed_share_rigidity {m : ℕ} (hm : 0 < m)
    (qstar : Fin m → ℝ) (hpos : ∀ j, 0 < qstar j) (hmass : ∑ j, qstar j = 1/(4 : ℕ)) :
    let p := twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))
    let K := rigidityCore qstar
    let D := rigidityCross qstar
    (∀ a, 0 ≤ blockWeights p qstar a) ∧
    (∑ a, blockWeights p qstar a) = 1 ∧
    (∀ h : Fin 2, p h = ((3 : ℕ) : ℝ)/(8 : ℕ)) ∧
    IsSkew (blockMatrix K D (orderedBlock 1)) ∧
    (∀ a b, -1 ≤ blockMatrix K D (orderedBlock 1) a b ∧
      blockMatrix K D (orderedBlock 1) a b ≤ 1) ∧
    (∀ a, response (blockMatrix K D (orderedBlock 1)) (blockWeights p qstar) a = 0) ∧
    (∀ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      (∀ j, 0 ≤ q j) → (∑ j, q j = 1/(4 : ℕ)) → IsSkew B →
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) →
      (∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) →
      q = qstar ∧ B = orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  have hnonneg : ∀ j, 0 ≤ qstar j := fun j => le_of_lt (hpos j)
  have hobs := two_anchor_observed_bounds hm qstar hnonneg hmass
  refine ⟨blockWeights_nonneg _ _ (fun _ => by norm_num [twoShares]) hnonneg,
    ?_, ?_, blockMatrix_skew _ _ _ (twoCore_skew _) (orderedBlock_skew 1),
    blockMatrix_bounds _ _ _ 1 hobs.1 hobs.2 (orderedBlock_bounds 1 (by norm_num)),
    two_anchor_target_feasible qstar (3/4) (1/4) (by norm_num) hmass, ?_⟩
  · rw [blockWeights_mass, hmass]
    norm_num [Fin.sum_univ_two, twoShares]
  · intro h
    norm_num [twoShares]
  · intro q B hq hqm hB hb hresp
    exact two_anchor_fixed_share_uniqueness hm qstar q (3/4) (1/4) (by norm_num)
      hpos hq hqm hmass B hB (fun i j => (hb i j).1) hresp

def uniformTarget (m : ℕ) (r : ℝ) : Fin m → ℝ := fun _ => r/(m : ℝ)

theorem uniformTarget_mass (m : ℕ) (hm : 0 < m) (r : ℝ) :
    (∑ j, uniformTarget m r j) = r := by
  simp only [uniformTarget, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem uniformTarget_positive (m : ℕ) (r : ℝ) (hr : 0 < r) :
    ∀ j, 0 < uniformTarget m r j := by
  intro j
  exact div_pos hr (Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt))

theorem uniform_target_score (m : ℕ) (r : ℝ) (j : Fin m) :
    targetScore (uniformTarget m r) r j = r*(1-((2 : ℕ)*(j.val : ℝ)+1)/(m : ℝ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have heq : prefixSet j.val = Finset.Iio j := by
    ext i
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  unfold targetScore prefixMass mass
  rw [heq]
  simp only [uniformTarget, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]
  ring

theorem uniform_prefix_mass (m : ℕ) (r : ℝ) (j : Fin m) :
    prefixMass (uniformTarget m r) j.val = (j.val : ℝ)*(r/(m : ℝ)) := by
  have heq : prefixSet j.val = Finset.Iio j := by
    ext i
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  unfold prefixMass mass
  rw [heq]
  simp only [uniformTarget, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]

theorem sum_tail_odds (m j : ℕ) :
    (∑ l ∈ Finset.range m, if j<l then (2*(l : ℝ)-2*(j : ℝ)-1) else 0) =
      ((m-j-1 : ℕ) : ℝ)^2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : j<m
    · rw [ite_eq_left h]
      have hsub : ((m-j-1 : ℕ) : ℝ) = (m : ℝ)-(j : ℝ)-1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      have hsub' : ((m+1-j-1 : ℕ) : ℝ) = (m : ℝ)-(j : ℝ) := by
        have hn : m+1-j-1 = m-j := by omega
        rw [hn, Nat.cast_sub (by omega)]
      change ((m-j-1 : ℕ) : ℝ)^2+(2*(m : ℝ)-2*(j : ℝ)-1) = ((m+1-j-1 : ℕ) : ℝ)^2
      rw [hsub, hsub']
      ring
    · rw [ite_eq_right h]
      have h0 : m-j-1=0 := by omega
      have h1 : m+1-j-1=0 := by omega
      simp [h0, h1]

/-- The gradient-defined weights specialize to the paper's explicit
    uniform quadratic weights, with zero-based residual labels. -/
theorem uniform_exposing_weight (m : ℕ) (r : ℝ) (j : Fin m) :
    exposingWeight (uniformTarget m r) r j = r*(((m : ℝ)-1-j.val)/(m : ℝ))^2 := by
  classical
  have hterm : ∀ l : Fin m,
      (if j ∈ prefixSet l.val then (2 : ℕ)*prefixMass (uniformTarget m r) l.val-r+
        targetScore (uniformTarget m r) r j else 0) =
      (r/(m : ℝ))*(if j.val<l.val then 2*(l.val : ℝ)-2*(j.val : ℝ)-1 else 0) := by
    intro l
    by_cases h : j.val<l.val
    · have hj : j ∈ prefixSet l.val := Finset.mem_filter.mpr ⟨Finset.mem_univ j,h⟩
      rw [ite_eq_left hj, ite_eq_left h, uniform_prefix_mass, uniform_target_score]
      norm_num only [Nat.cast_ofNat]
      ring
    · have hj : j ∉ prefixSet l.val := by simpa only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] using h
      rw [ite_eq_right hj, ite_eq_right h, mul_zero]
  unfold exposingWeight
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => if j.val<l then 2*(l : ℝ)-2*(j.val : ℝ)-1 else 0), sum_tail_odds]
  have hsub : ((m-j.val-1 : ℕ) : ℝ) = (m : ℝ)-1-j.val := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hsub]
  ring

/-- The paper's uniform construction is a specialization of the arbitrary
    positive target realization. Every residual coordinate is positive. -/
theorem uniform_two_anchor_dense (m : ℕ) (hm : 0 < m) :
    (∀ j, 0 < uniformTarget m (1/(4 : ℕ)) j) ∧
    (∑ j, uniformTarget m (1/(4 : ℕ)) j) = 1/(4 : ℕ) ∧
    (∀ a, response
      (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) (orderedBlock 1))
      (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) (uniformTarget m (1/(4 : ℕ)))) a = 0) ∧
    (∀ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      (∀ j, 0 ≤ q j) → (∑ j, q j = 1/(4 : ℕ)) → IsSkew B →
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) →
      (∀ a, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) a ≤ 0) →
      q = uniformTarget m (1/(4 : ℕ)) ∧ B = orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  have hp := uniformTarget_positive m (1/4) (by norm_num)
  have hmass := uniformTarget_mass m hm (1/4)
  refine ⟨hp, hmass, two_anchor_target_feasible _ (3/4) (1/4) (by norm_num) hmass, ?_⟩
  intro q B hq hqm hB hb hresp
  exact two_anchor_fixed_share_uniqueness hm _ q (3/4) (1/4) (by norm_num) hp hq hqm hmass
    B hB (fun i j => (hb i j).1) hresp

theorem positive_target_full_support {m : ℕ} (qstar : Fin m → ℝ)
    (hpos : ∀ j, 0 < qstar j) :
    (Finset.univ.filter fun j => qstar j ≠ 0).card = m := by
  have heq : (Finset.univ.filter fun j => qstar j ≠ 0) = Finset.univ := by
    ext j
    simp [ne_of_gt (hpos j)]
  rw [heq]
  simp

end
end SparseCompletion


/- Fixed source body: MinimumShareRigidity.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem two_anchor_variable_responses {m : ℕ} (t w q : Fin m → ℝ)
    (a : Fin 2 → ℝ) (p βstar : ℝ) :
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) a q 0 =
      (2*βstar/p)*a 1-scoreMoment q t/p-scoreMoment q w ∧
    anchorResponse (twoCore (2*βstar/p)) (twoCross t w p) a q 1 =
      -(2*βstar/p)*a 0-scoreMoment q t/p+scoreMoment q w := by
  have hsum : (∑ i, t i/p*q i) = scoreMoment q t/p := by
    unfold scoreMoment
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hw : (∑ i, w i*q i) = scoreMoment q w := by
    unfold scoreMoment
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor <;>
    simp only [anchorResponse, Fin.sum_univ_two, twoCore, twoCross] <;>
    norm_num <;>
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hw] <;>
    ring

theorem exposing_moment_positive {m : ℕ} (hm : 2 ≤ m) (qstar : Fin m → ℝ)
    (r : ℝ) (hpos : ∀ j, 0 < qstar j) (hr : ∑ j, qstar j = r) :
    0 < scoreMoment qstar (exposingWeight qstar r) := by
  let j : Fin m := ⟨0,by omega⟩
  have hn : ∀ i, 0 ≤ qstar i := fun i => le_of_lt (hpos i)
  have hw := exposingWeight_positive (by omega) qstar r hpos hr j (by dsimp [j]; omega)
  have hsum : qstar j*exposingWeight qstar r j ≤ scoreMoment qstar (exposingWeight qstar r) :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hn i) (exposingWeight_bounds (by omega) qstar hn r hr i).1)
      (Finset.mem_univ j)
  exact lt_of_lt_of_le (mul_pos (hpos j) hw) hsum

/-- The real two-anchor observations force minimum-share commitments to
    be tight, then determine both the residual distribution and block. -/
theorem bounded_two_anchor_minimum_share_rigidity {m : ℕ} (hm : 2 ≤ m)
    (qstar q : Fin m → ℝ) (a : Fin 2 → ℝ)
    (htpos : ∀ j, 0 < qstar j) (htm : ∑ j, qstar j = 1/(4 : ℕ))
    (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) (hq : ∀ j, 0 ≤ q j)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1)
    (hresp : ∀ v, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights a q) v ≤ 0) : a = twoShares (((3 : ℕ) : ℝ)/(4 : ℕ)) ∧ q = qstar ∧ B = orderedBlock 1 := by
  norm_num only [Nat.cast_ofNat] at *
  classical
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let P := a 0+a 1
  let R := ∑ j, q j
  let u := P-3/4
  have ha0 : ∀ h, 0 ≤ a h := fun h => by linarith [ha h]
  have hp : 3/4 ≤ P := by dsimp [P]; linarith [ha 0,ha 1]
  have hmass : R+u = 1/4 := by
    dsimp [R,u,P]
    rw [Fin.sum_univ_two] at hnorm
    linarith
  have hsk := blockMatrix_skew (rigidityCore qstar) (rigidityCross qstar) B (twoCore_skew _) hB
  have hzero (h : Fin 2) : anchorResponse (rigidityCore qstar) (rigidityCross qstar) a q h = 0 := by
    have hz := supported_response_zero (blockWeights a q)
      (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights_nonneg a q ha0 hq) hsk hresp (.inl h) (by change 0<a h; linarith [ha h])
    simpa only [block_response_anchor] using hz
  have hf := two_anchor_variable_responses t w q a (3/4) βstar
  have hf0 := hzero 0
  have hf1 := hzero 1
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 0 = 0 at hf0
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 1 = 0 at hf1
  rw [hf.1] at hf0
  rw [hf.2] at hf1
  have hβeq : scoreMoment q w = βstar*P/(3/4) := by dsimp [P]; nlinarith
  have hβpos : 0 < βstar := exposing_moment_positive hm qstar (1/4) htpos htm
  have hβge : βstar ≤ scoreMoment q w := by rw [hβeq]; nlinarith
  have hobs := (two_anchor_observed_bounds (by omega) qstar (fun j => le_of_lt (htpos j)) htm).2
  have hscore : ∀ j, t j-u ≤ score (rigidityCross qstar) a j := by
    intro j
    have hs := congrFun (two_score t w (3/4) (by norm_num)) j
    have hd0 := (hobs j 0).1
    have hd1 := (hobs j 1).1
    have h0 : 0 ≤ (a 0-3/8)*(twoCross t w (3/4) j 0+1) :=
      mul_nonneg (by linarith [ha 0]) (by linarith)
    have h1 : 0 ≤ (a 1-3/8)*(twoCross t w (3/4) j 1+1) :=
      mul_nonneg (by linarith [ha 1]) (by linarith)
    change score (twoCross t w (3/4)) (twoShares (3/4)) j = t j at hs
    simp only [score, Fin.sum_univ_two, twoShares] at hs
    change t j-u ≤ score (twoCross t w (3/4)) a j
    simp only [score, Fin.sum_univ_two]
    dsimp [u,P]
    nlinarith
  have hres := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B a q 0).mp hresp).2
  have hc0 := completion_cuts_necessary q (score (rigidityCross qstar) a) B 1 R 0 hq rfl hB
    (fun i j => (hb i j).1) hres
  have hc : Cuts 1 (1/4) q t := by
    intro s
    have hh := hc0 s
    simp only [sub_zero, one_mul] at hh
    have hsum : (∑ j ∈ s, q j*t j) ≤ (∑ j ∈ s, q j*score (rigidityCross qstar) a j)+u*mass s q := by
      have hpoint := Finset.sum_le_sum (s := s) (f := fun j => q j*t j)
        (g := fun j => q j*(score (rigidityCross qstar) a j+u)) fun j _ =>
          mul_le_mul_of_nonneg_left (by linarith [hscore j]) (hq j)
      simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mass, mul_comm u] using hpoint
    calc
      _ ≤ mass s q*(R-mass s q)+u*mass s q := le_trans hsum (add_le_add hh le_rfl)
      _ = _ := by rw [← hmass]; ring
  have hβle := cuts_exposing_moment_le (by omega) q qstar (1/4) htm hc
  have hβ : scoreMoment q w = βstar := le_antisymm hβle hβge
  have hP : P=3/4 := by rw [hβ] at hβeq; nlinarith
  have haeq : a = twoShares (3/4) := by
    funext h
    fin_cases h
    · change a 0 = (3/4)/(2 : ℕ)
      norm_num
      dsimp [P] at hP
      linarith [ha 0,ha 1]
    · change a 1 = (3/4)/(2 : ℕ)
      norm_num
      dsimp [P] at hP
      linarith [ha 0,ha 1]
  refine ⟨haeq, ?_⟩
  have hqm : ∑ j, q j = 1/4 := by dsimp [u] at hmass; rw [hP] at hmass; dsimp [R] at hmass; linarith
  subst a
  exact two_anchor_fixed_share_uniqueness (by omega) qstar q (3/4) (1/4) (by norm_num)
    htpos hq hqm htm B hB (fun i j => (hb i j).1) hresp

end
end SparseCompletion

/- Fixed source body: PrefixStability.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def prefixError {m : ℕ} (q qstar : Fin m → ℝ) : ℝ :=
  (∑ l : Fin m, (prefixMass q l.val-prefixMass qstar l.val)^2)/(m : ℝ)

theorem shifted_cut_prefix_gap {m : ℕ} (q t : Fin m → ℝ) (r z : ℝ)
    (hc : Cuts 1 r q (fun j => t j-z)) (l : ℕ) :
    prefixGap q t r l ≤ z*prefixMass q l := by
  have hh := hc (prefixSet l)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, one_mul] at hh
  unfold mass at hh
  unfold prefixGap prefixMass mass
  nlinarith

/-- Prefix error stability needs only an upper bound on candidate total
    mass. This includes the variable-mass minimum-share setting. -/
theorem prefix_error_from_cuts {m : ℕ} (hm : 0 < m) (q qstar : Fin m → ℝ)
    (r z a : ℝ) (hq : ∀ j, 0 ≤ q j) (hqm : (∑ j, q j) ≤ r)
    (htm : ∑ j, qstar j = r) (hz : 0 ≤ z)
    (hc : Cuts 1 r q (fun j => targetScore qstar r j-z))
    (hβ : -a ≤ scoreMoment q (exposingWeight qstar r)-scoreMoment qstar (exposingWeight qstar r)) :
    prefixError q qstar ≤ z*r+a := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hid := prefix_exposing_identity q qstar r htm
  have hsum : (∑ l : Fin m, prefixGap q (targetScore qstar r) r l.val)/(m : ℝ) ≤ z*r := by
    apply (div_le_iff₀ hmR).mpr
    calc
      _ ≤ ∑ _l : Fin m, z*r := Finset.sum_le_sum fun l _ =>
        le_trans (shifted_cut_prefix_gap q (targetScore qstar r) r z hc l.val)
          (mul_le_mul_of_nonneg_left (le_trans
            (prefixMass_le_total q hq (∑ j, q j) rfl l.val) hqm) hz)
      _ = _ := by simp; ring
  change scoreMoment q (exposingWeight qstar r)-scoreMoment qstar (exposingWeight qstar r)+
    prefixError q qstar = _ at hid
  linarith

theorem cut_full_moment_bound {ι : Type*} [Fintype ι] (q t : ι → ℝ) (r z : ℝ)
    (hmass : ∑ j, q j = r) (hc : Cuts 1 r q (fun j => t j-z)) :
    (∑ j, q j*t j) ≤ z*r := by
  have hh := hc Finset.univ
  simp only [mass, hmass, sub_self, mul_zero, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul] at hh
  nlinarith

/-- The paper's fixed-share quadratic stability estimate, for every
    prescribed target distribution (not only the uniform target). -/
theorem two_anchor_fixed_share_stability {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hqm : ∑ j, q j = 1/(4 : ℕ)) (htm : ∑ j, qstar j = 1/(4 : ℕ))
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ z) :
    prefixError q qstar ≤ z*(1/(4 : ℕ)+1/(((3 : ℕ) : ℝ)/(4 : ℕ))) := by
  norm_num only [Nat.cast_ofNat] at *
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  have hs : score (rigidityCross qstar) (twoShares (3/4)) = t := two_score t w (3/4) (by norm_num)
  have hres := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B
    (twoShares (3/4)) q z).mp hresp).2
  rw [hs] at hres
  have hc := completion_cuts_necessary q t B 1 (1/4) z hq hqm hB hb hres
  have hα : scoreMoment q t ≤ z*(1/4) := cut_full_moment_bound q t (1/4) z hqm hc
  have hanchor := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B
    (twoShares (3/4)) q z).mp hresp).1 0
  have hf := (two_anchor_responses t w q (3/4) βstar (by norm_num)).1
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 0 ≤ z at hanchor
  rw [hf] at hanchor
  have hβ : -(z/(3/4)) ≤ scoreMoment q w-βstar := by nlinarith
  have hh := prefix_error_from_cuts hm q qstar (1/4) z (z/(3/4)) hq (le_of_eq hqm) htm hz hc hβ
  nlinarith

end
end SparseCompletion

/- Fixed source body: MinimumShareStability.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- A supported row's lower response follows from the whole normalized
    skew game and a lower probability share. -/
theorem response_lower_from_share {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) (hA : IsSkew A)
    (hx : ∀ j, 0 ≤ x j) (hmass : ∑ j, x j = 1)
    (z c : ℝ) (hresp : ∀ j, response A x j ≤ z) (i : ι) (hshare : c ≤ x i) :
    (c-1)*z ≤ c*response A x i := by
  have hcancel := skew_weighted_sum Finset.univ x A hA
  have hzero : (∑ j, x j*response A x j) = 0 := by
    simpa only [response, Finset.mul_sum, mul_assoc] using hcancel
  have hsum : (∑ j, x j*(z-response A x j)) = z := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul, hzero, sub_zero]
  have hn : ∀ j, 0 ≤ x j*(z-response A x j) := fun j =>
    mul_nonneg (hx j) (sub_nonneg.mpr (hresp j))
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hn j) (Finset.mem_univ i)
  rw [hsum] at hi
  have hc := mul_le_mul_of_nonneg_right hshare (sub_nonneg.mpr (hresp i))
  nlinarith

theorem cuts_with_score_lower_shift {ι : Type*} [Fintype ι]
    (q t v : ι → ℝ) (R r u z : ℝ) (hq : ∀ j, 0 ≤ q j) (hmass : R+u=r)
    (hscore : ∀ j, t j-u ≤ v j) (hc : Cuts 1 R q (fun j => v j-z)) :
    Cuts 1 r q (fun j => t j-z) := by
  intro s
  have hh := hc s
  simp only [one_mul] at hh
  have hsum : (∑ j ∈ s, q j*(t j-z)) ≤
      (∑ j ∈ s, q j*(v j-z))+u*mass s q := by
    have hp := Finset.sum_le_sum (s := s) (f := fun j => q j*(t j-z))
      (g := fun j => q j*((v j-z)+u)) fun j _ =>
        mul_le_mul_of_nonneg_left (by linarith [hscore j]) (hq j)
    simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mass, mul_comm u] using hp
  calc
    _ ≤ mass s q*(R-mass s q)+u*mass s q := le_trans hsum (add_le_add hh le_rfl)
    _ = _ := by rw [← hmass]; ring

/-- The same prefix error bound holds with only two minimum-share
    commitments, even when the candidate residual mass is smaller. -/
theorem two_anchor_minimum_share_stability {m : ℕ} (hm : 0 < m)
    (qstar q : Fin m → ℝ) (a : Fin 2 → ℝ)
    (htpos : ∀ j, 0 ≤ qstar j) (htm : ∑ j, qstar j = 1/(4 : ℕ))
    (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) (hq : ∀ j, 0 ≤ q j)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
      (blockWeights a q) v ≤ z) : prefixError q qstar ≤ z*(1/(4 : ℕ)+1/(((3 : ℕ) : ℝ)/(4 : ℕ))) := by
  norm_num only [Nat.cast_ofNat] at *
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let P := a 0+a 1
  let R := ∑ j, q j
  let u := P-3/4
  have ha0 : ∀ h, 0 ≤ a h := fun h => by linarith [ha h]
  have hp : 3/4 ≤ P := by dsimp [P]; linarith [ha 0,ha 1]
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hmass : R+u=1/4 := by dsimp [R,u,P]; rw [Fin.sum_univ_two] at hnorm; linarith
  have hβ0 : 0 ≤ βstar := (exposing_moment_bounds hm qstar (1/4) htpos htm).1
  have hsk := blockMatrix_skew (rigidityCore qstar) (rigidityCross qstar) B (twoCore_skew _) hB
  have hallmass : (∑ v, blockWeights a q v) = 1 := by rw [blockWeights_mass]; exact hnorm
  have hlow := response_lower_from_share (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
    (blockWeights a q) hsk (blockWeights_nonneg a q ha0 hq) hallmass z (3/8) hresp (.inl 1) (ha 1)
  rw [block_response_anchor] at hlow
  have hup := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B a q z).mp hresp).1 0
  have hf := two_anchor_variable_responses t w q a (3/4) βstar
  change (3/8-1)*z ≤ (3/8)*anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 1 at hlow
  change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) a q 0 ≤ z at hup
  rw [hf.2] at hlow
  rw [hf.1] at hup
  have hβprod : 0 ≤ βstar*(P-3/4) := mul_nonneg hβ0 (by linarith)
  have hβ : -(z/(3/4)) ≤ scoreMoment q w-βstar := by dsimp [P] at hβprod; nlinarith
  have hobs := (two_anchor_observed_bounds hm qstar htpos htm).2
  have hscore : ∀ j, t j-u ≤ score (rigidityCross qstar) a j := by
    intro j
    have hs := congrFun (two_score t w (3/4) (by norm_num)) j
    have hd0 := (hobs j 0).1
    have hd1 := (hobs j 1).1
    have h0 : 0 ≤ (a 0-3/8)*(twoCross t w (3/4) j 0+1) :=
      mul_nonneg (by linarith [ha 0]) (by linarith)
    have h1 : 0 ≤ (a 1-3/8)*(twoCross t w (3/4) j 1+1) :=
      mul_nonneg (by linarith [ha 1]) (by linarith)
    change score (twoCross t w (3/4)) (twoShares (3/4)) j = t j at hs
    simp only [score, Fin.sum_univ_two, twoShares] at hs
    change t j-u ≤ score (twoCross t w (3/4)) a j
    simp only [score, Fin.sum_univ_two]
    dsimp [u,P]
    nlinarith
  have hres := ((block_response_bounds_iff (rigidityCore qstar) (rigidityCross qstar) B a q z).mp hresp).2
  have hc0 := completion_cuts_necessary q (score (rigidityCross qstar) a) B 1 R z hq rfl hB hb hres
  have hc := cuts_with_score_lower_shift q t (score (rigidityCross qstar) a) R (1/4) u z hq hmass hscore hc0
  have hR : (∑ j, q j) ≤ 1/4 := by change R ≤ 1/4; linarith
  have hh := prefix_error_from_cuts hm q qstar (1/4) z (z/(3/4)) hq hR htm hz hc hβ
  nlinarith

end
end SparseCompletion

/- Fixed source body: Quantization.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Exact discrete variance decomposition on an arithmetic progression. -/
theorem constant_run_error_identity (L : ℕ) (a d c : ℝ) :
    (∑ i ∈ Finset.range L, (c-(a+d*(i : ℝ)))^2) =
      (L : ℝ)*(c-a-d*((L : ℝ)-1)/2)^2+d^2*(L : ℝ)*((L : ℝ)^2-1)/12 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem constant_run_error_lower (L : ℕ) (a d c : ℝ) :
    d^2*(L : ℝ)*((L : ℝ)^2-1)/12 ≤ ∑ i ∈ Finset.range L, (c-(a+d*(i : ℝ)))^2 := by
  rw [constant_run_error_identity]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg L) (sq_nonneg _))

/-- Cubic run-length Jensen inequality with no positivity floor on runs. -/
theorem cubic_run_bound {κ : Type*} [Fintype κ] (L : κ → ℝ) (hL : ∀ i, 0 ≤ L i) :
    (∑ i, L i)^3 ≤ (Fintype.card κ : ℝ)^2*∑ i, (L i)^3 := by
  simpa only [Finset.card_univ] using
    pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := L) (fun i _ => hL i) 2

theorem pairwise_square_sum {κ : Type*} [Fintype κ] (v : κ → ℝ) :
    (∑ i, ∑ j, (v i-v j)^2) =
      2*((Fintype.card κ : ℝ)*(∑ i, (v i)^2)-(∑ i, v i)^2) := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem first_index_moment (L : ℕ) :
    (∑ i ∈ Finset.range L, (i : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem pairwise_index_square_sum (L : ℕ) :
    (∑ i : Fin L, ∑ j : Fin L, ((i.val : ℝ)-(j.val : ℝ))^2) =
      (L : ℝ)^2*((L : ℝ)^2-1)/6 := by
  have hsum : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact first_index_moment L
  have hsq : (∑ i : Fin L, (i.val : ℝ)^2) =
      (L : ℝ)*(((L : ℝ)-1)/2)^2+(L : ℝ)*((L : ℝ)^2-1)/12 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)^2)]
    simpa only [zero_add, one_mul, zero_sub, neg_sq, one_pow, mul_one, sub_zero] using
      constant_run_error_identity L 0 1 0
  rw [pairwise_square_sum, Fintype.card_fin, hsum, hsq]
  ring

theorem increasing_nat_distance {L n : ℕ} (e : Fin L ↪o Fin n) (i j : Fin L) (hij : i ≤ j) :
    i.val+(e j).val ≥ j.val+(e i).val := by
  have hstep : ∀ k (hk : i.val+k < L), (e i).val+k ≤ (e ⟨i.val+k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk; simpa only [Nat.add_zero] using le_rfl (a := (e i).val)
    | succ k ih =>
      intro hk
      have hk0 : i.val+k < L := by omega
      have hh := ih hk0
      have hlt : (e ⟨i.val+k,hk0⟩).val  <  (e ⟨i.val+(k+1),hk⟩).val :=
        e.strictMono (by change i.val+k < i.val+(k+1); omega)
      omega
  have hval : i.val ≤ j.val := hij
  have hbound : i.val+(j.val-i.val) < L := by omega
  have hh := hstep (j.val-i.val) hbound
  have hsame : (⟨i.val+(j.val-i.val),hbound⟩ : Fin L) = j := Fin.ext (by change i.val+(j.val-i.val)=j.val; omega)
  rw [hsame] at hh
  omega

theorem increasing_square_distance {L n : ℕ} (e : Fin L ↪o Fin n) (i j : Fin L) :
    ((i.val : ℝ)-(j.val : ℝ))^2 ≤ (((e i).val : ℝ)-((e j).val : ℝ))^2 := by
  rcases le_total i j with hij | hji
  · have hh := increasing_nat_distance e i j hij
    have hm : (e i).val ≤ (e j).val := e.monotone hij
    have hval : i.val ≤ j.val := hij
    have hc : (j.val : ℝ)+(e i).val ≤ (i.val : ℝ)+(e j).val := by exact_mod_cast hh
    have hc0 : (i.val : ℝ) ≤ j.val := by exact_mod_cast hval
    nlinarith
  · have hh := increasing_nat_distance e j i hji
    have hval : j.val ≤ i.val := hji
    have hc : (i.val : ℝ)+(e j).val ≤ (j.val : ℝ)+(e i).val := by exact_mod_cast hh
    have hc0 : (j.val : ℝ) ≤ i.val := by exact_mod_cast hval
    nlinarith

/-- Any L distinct integer grid points have at least the variance of L
    consecutive points. No contiguity or chosen run partition is assumed. -/
theorem finite_subset_quantization_bound {n : ℕ} (s : Finset (Fin n)) (a d c : ℝ) :
    d^2*(s.card : ℝ)*((s.card : ℝ)^2-1)/12 ≤
      ∑ j ∈ s, (c-(a+d*(j.val : ℝ)))^2 := by
  classical
  by_cases hs : s.card=0
  · have he : s=∅ := Finset.card_eq_zero.mp hs
    subst s
    simp
  · let L := s.card
    have hL : 0 < (L : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    let e : Fin L ↪o Fin n := s.orderEmbOfFin rfl
    let v : Fin L → ℝ := fun i => c-(a+d*((e i).val : ℝ))
    have hsum : (∑ j ∈ s, (c-(a+d*(j.val : ℝ)))^2) = ∑ i, (v i)^2 := by
      rw [← s.map_orderEmbOfFin_univ rfl, Finset.sum_map]
      rfl
    have hdifference : ∀ i j, (v i-v j)^2 = d^2*(((e i).val : ℝ)-((e j).val : ℝ))^2 := by
      intro i j
      dsimp [v]
      ring
    have hpair : d^2*((L : ℝ)^2*((L : ℝ)^2-1)/6) ≤ ∑ i, ∑ j, (v i-v j)^2 := by
      rw [← pairwise_index_square_sum L]
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [hdifference]
      exact mul_le_mul_of_nonneg_left (increasing_square_distance e i j) (sq_nonneg d)
    rw [pairwise_square_sum, Fintype.card_fin] at hpair
    rw [hsum]
    apply (mul_le_mul_iff_right₀ (show 0 < 2*(L : ℝ) by positivity)).mp
    have hsq := sq_nonneg (∑ i, v i)
    change 2*(L : ℝ)*(d^2*(L : ℝ)*((L : ℝ)^2-1)/12) ≤ 2*(L : ℝ)*∑ i, (v i)^2
    nlinarith

end
end SparseCompletion

/- Fixed source body: SupportQuantization.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def activePrefix {m : ℕ} (q : Fin m → ℝ) (l : ℕ) : Finset (Fin m) := by
  classical
  exact (prefixSet l).filter fun j => q j ≠ 0

def residualSupport {m : ℕ} (q : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j => q j ≠ 0

def supportSize {m : ℕ} (q : Fin m → ℝ) : ℕ := (residualSupport q).card

theorem activePrefix_subset {m : ℕ} (q : Fin m → ℝ) (l : ℕ) :
    activePrefix q l ⊆ residualSupport q := by
  classical
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩

theorem activePrefix_mono {m : ℕ} (q : Fin m → ℝ) (l n : ℕ) (hln : l ≤ n) :
    activePrefix q l ⊆ activePrefix q n := by
  classical
  intro j hj
  obtain ⟨hjl,hq⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j,
    lt_of_lt_of_le (Finset.mem_filter.mp hjl).2 hln⟩,hq⟩

theorem prefixMass_active_sum {m : ℕ} (q : Fin m → ℝ) (l : ℕ) :
    prefixMass q l = ∑ j ∈ activePrefix q l, q j := by
  classical
  unfold prefixMass mass activePrefix
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hn
  by_contra hq
  exact hn (Finset.mem_filter.mpr ⟨hj,hq⟩)

theorem equal_active_card_prefixMass {m : ℕ} (q : Fin m → ℝ) (l n : ℕ)
    (hcard : (activePrefix q l).card = (activePrefix q n).card) :
    prefixMass q l = prefixMass q n := by
  rcases le_total l n with hln | hnl
  · have heq := Finset.eq_of_subset_of_card_le (activePrefix_mono q l n hln) (le_of_eq hcard.symm)
    rw [prefixMass_active_sum, prefixMass_active_sum, heq]
  · have heq := Finset.eq_of_subset_of_card_le (activePrefix_mono q n l hnl) (le_of_eq hcard)
    rw [prefixMass_active_sum, prefixMass_active_sum, heq]

def runLabel {m : ℕ} (q : Fin m → ℝ) (l : ℕ) : Fin (supportSize q+1) :=
  ⟨(activePrefix q l).card, Nat.lt_succ_of_le (Finset.card_le_card (activePrefix_subset q l))⟩

def runSet {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (a : Fin (supportSize q+1)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun l => runLabel q l.val=a

def runValue {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (a : Fin (supportSize q+1)) : ℝ := by
  classical
  exact if hs : (runSet q n a).Nonempty then prefixMass q ((runSet q n a).min' hs).val else 0

theorem prefixMass_on_run {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (a : Fin (supportSize q+1))
    (l : Fin n) (hl : l ∈ runSet q n a) : prefixMass q l.val = runValue q n a := by
  classical
  have hs : (runSet q n a).Nonempty := ⟨l,hl⟩
  unfold runValue
  rw [dite_eq_left hs]
  apply equal_active_card_prefixMass
  have hmin := Finset.min'_mem (runSet q n a) hs
  have hh : runLabel q l.val = runLabel q ((runSet q n a).min' hs).val :=
    (Finset.mem_filter.mp hl).2.trans (Finset.mem_filter.mp hmin).2.symm
  exact congrArg Fin.val hh

theorem run_card_sum {m : ℕ} (q : Fin m → ℝ) (n : ℕ) :
    (∑ a : Fin (supportSize q+1), ((runSet q n a).card : ℝ)) = n := by
  classical
  have hh := Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) (fun l => runLabel q l.val) (fun _ => (1 : ℝ))
  simpa only [runSet, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] using hh

theorem run_error_sum {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (d : ℝ) :
    (∑ l : Fin n, (prefixMass q l.val-d*(l.val : ℝ))^2) =
      ∑ a : Fin (supportSize q+1), ∑ l ∈ runSet q n a,
        (runValue q n a-d*(l.val : ℝ))^2 := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun l : Fin n => runLabel q l.val)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l hl
  rw [prefixMass_on_run q n a l hl]

/-- Quantization error for sparse cumulative mass. The candidate weights
    may even have arbitrary signs; only the number of nonzero entries matters. -/
theorem sparse_cumulative_quantization {m : ℕ} (q : Fin m → ℝ) (n : ℕ) (d : ℝ) :
    d^2/12*((n : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2-(n : ℝ)) ≤
      ∑ l : Fin n, (prefixMass q l.val-d*(l.val : ℝ))^2 := by
  classical
  let L : Fin (supportSize q+1) → ℝ := fun a => (runSet q n a).card
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hJ := cubic_run_bound L (fun a => Nat.cast_nonneg _)
  have htotal : (∑ a, L a) = (n : ℝ) := run_card_sum q n
  rw [htotal] at hJ
  simp only [Fintype.card_fin] at hJ
  have hdiv : (n : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2 ≤ ∑ a, (L a)^3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    calc
      _ ≤ ((supportSize q+1 : ℕ) : ℝ)^2*∑ a, (L a)^3 := hJ
      _ = _ := mul_comm _ _
  calc
    _ ≤ d^2/12*((∑ a, (L a)^3)-(n : ℝ)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hdiv _) (by positivity)
    _ = ∑ a : Fin (supportSize q+1), d^2*(L a)*((L a)^2-1)/12 := by
      rw [← htotal]
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ _ := by
      rw [run_error_sum q n d]
      apply Finset.sum_le_sum
      intro a _
      simpa only [zero_add, L] using finite_subset_quantization_bound (runSet q n a) 0 d (runValue q n a)

end
end SparseCompletion

/- Fixed source body: SupportLowerBound.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem uniform_prefix_error_lower {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ) (r : ℝ) :
    r^2/12*(1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2) ≤
      prefixError q (uniformTarget m r) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hs := sparse_cumulative_quantization q m (r/(m : ℝ))
  have heq : (∑ l : Fin m, (prefixMass q l.val-(r/(m : ℝ))*(l.val : ℝ))^2) =
      ∑ l : Fin m, (prefixMass q l.val-prefixMass (uniformTarget m r) l.val)^2 := by
    apply Finset.sum_congr rfl
    intro l _
    rw [uniform_prefix_mass]
    ring
  rw [heq] at hs
  have halg : ((r/(m : ℝ))^2/12*((m : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2-(m : ℝ)))/(m : ℝ) =
      r^2/12*(1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2) := by
    field_simp
  rw [← halg]
  exact div_le_div_of_nonneg_right hs (le_of_lt hmR)

theorem uniform_prefix_mass_le (m : ℕ) (hm : 0 < m) (r : ℝ) (l : ℕ) (hl : l ≤ m) :
    prefixMass (uniformTarget m r) l = (l : ℝ)*(r/(m : ℝ)) := by
  by_cases he : l=m
  · subst l
    rw [prefixMass_full, uniformTarget_mass m hm r]
    field_simp
  · exact uniform_prefix_mass m r ⟨l,by omega⟩

theorem uniform_full_prefix_error_lower {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ) (r : ℝ)
    (hmass : ∑ j, q j = r) :
    r^2/(12*(m : ℝ)^3)*(((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1)) ≤
      prefixError q (uniformTarget m r) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hs := sparse_cumulative_quantization q (m+1) (r/(m : ℝ))
  have heq : (∑ l : Fin (m+1), (prefixMass q l.val-(r/(m : ℝ))*(l.val : ℝ))^2) =
      ∑ l : Fin m, (prefixMass q l.val-prefixMass (uniformTarget m r) l.val)^2 := by
    rw [Fin.sum_univ_castSucc]
    have hend : prefixMass q m-(r/(m : ℝ))*(m : ℝ) = 0 := by
      rw [prefixMass_full, hmass]
      field_simp
      ring
    simp only [Fin.val_last, hend, zero_pow (by norm_num : 2 ≠ 0), add_zero, Fin.val_castSucc]
    apply Finset.sum_congr rfl
    intro l _
    rw [uniform_prefix_mass]
    ring
  rw [heq] at hs
  have halg : ((r/(m : ℝ))^2/12*(((m+1 : ℕ) : ℝ)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m+1 : ℕ) : ℝ)))/(m : ℝ) =
      r^2/(12*(m : ℝ)^3)*(((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1)) := by
    push_cast
    field_simp
  rw [← halg]
  exact div_le_div_of_nonneg_right hs (le_of_lt hmR)

/-- The full quantitative support lower bound for the uniform observed
    game, specialized to the paper's p=3/4, r=1/4 constants. -/
theorem uniform_fixed_share_support_lower {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqm : ∑ j, q j = 1/(4 : ℕ))
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ z) :
    (((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(304*(m : ℝ)^3) ≤ z := by
  norm_num only [Nat.cast_ofNat] at *
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (supportSize q+1 : ℕ) := by positivity
  have hlower := uniform_full_prefix_error_lower hm q (1/4) hqm
  have hupper := two_anchor_fixed_share_stability hm (uniformTarget m (1/4)) q hq hqm
    (uniformTarget_mass m hm (1/4)) B hB hb z hz hresp
  have hsmall : (((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(192*(m : ℝ)^3) ≤
      prefixError q (uniformTarget m (1/4)) := by convert hlower using 1; ring
  calc
    _ = ((((m : ℝ)+1)^3/((supportSize q+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(192*(m : ℝ)^3))/(19/12) := by
      field_simp
      ring
    _ ≤ prefixError q (uniformTarget m (1/4))/(19/12) :=
      div_le_div_of_nonneg_right hsmall (by norm_num)
    _ ≤ z := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19/12)).mpr (by nlinarith)

/-- The variable-mass support obstruction under the two minimum shares. -/
theorem uniform_minimum_share_support_lower {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (a : Fin 2 → ℝ) (hq : ∀ j, 0 ≤ q j) (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ z) :
    (1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/304 ≤ z := by
  norm_num only [Nat.cast_ofNat] at *
  have hlower := uniform_prefix_error_lower hm q (1/4)
  have hupper := two_anchor_minimum_share_stability hm (uniformTarget m (1/4)) q a
    (fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j))
    (uniformTarget_mass m hm (1/4)) ha hq hnorm B hB hb z hz hresp
  have hsmall : (1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/192 ≤
      prefixError q (uniformTarget m (1/4)) := by convert hlower using 1; ring
  calc
    _ = ((1/((supportSize q+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/192)/(19/12) := by ring
    _ ≤ prefixError q (uniformTarget m (1/4))/(19/12) :=
      div_le_div_of_nonneg_right hsmall (by norm_num)
    _ ≤ z := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19/12)).mpr (by nlinarith)

theorem fixed_rate_simplification (m H : ℕ) (hm : 0 < m) (hdim : 2*H+1 ≤ m) :
    3/(1216*((H+1 : ℕ) : ℝ)^2) ≤
      (((m : ℝ)+1)^3/((H+1 : ℕ) : ℝ)^2-((m : ℝ)+1))/(304*(m : ℝ)^3) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
  have hdimR : 2*((H+1 : ℕ) : ℝ) ≤ (m : ℝ)+1 := by exact_mod_cast (show 2*(H+1) ≤ m+1 by omega)
  have hgap : 0 ≤ ((m : ℝ)+1)*(((m : ℝ)+1)-2*((H+1 : ℕ) : ℝ))*(((m : ℝ)+1)+2*((H+1 : ℕ) : ℝ)) := by
    positivity
  have hcubes : (m : ℝ)^3 ≤ ((m : ℝ)+1)^3 := by gcongr; linarith
  have hscaled : 3*(m : ℝ)^3 ≤ 4*(((m : ℝ)+1)^3-((m : ℝ)+1)*((H+1 : ℕ) : ℝ)^2) := by
    nlinarith
  have hbracket : 3*(m : ℝ)^3/(4*((H+1 : ℕ) : ℝ)^2) ≤
      ((m : ℝ)+1)^3/((H+1 : ℕ) : ℝ)^2-((m : ℝ)+1) := by
    apply (div_le_iff₀ (show 0 < 4*((H+1 : ℕ) : ℝ)^2 by positivity)).mpr
    have heq : (((m : ℝ)+1)^3/((H+1 : ℕ) : ℝ)^2-((m : ℝ)+1))*(4*((H+1 : ℕ) : ℝ)^2) =
        4*(((m : ℝ)+1)^3-((m : ℝ)+1)*((H+1 : ℕ) : ℝ)^2) := by
      field_simp
    rw [heq]
    exact hscaled
  calc
    _ = (3*(m : ℝ)^3/(4*((H+1 : ℕ) : ℝ)^2))/(304*(m : ℝ)^3) := by
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hbracket (by positivity)

theorem minimum_rate_simplification (m H : ℕ) (hm : 0 < m) (hdim : 2*(H+1) ≤ m) :
    3/(1216*((H+1 : ℕ) : ℝ)^2) ≤
      (1/((H+1 : ℕ) : ℝ)^2-1/(m : ℝ)^2)/304 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
  have hdimR : 2*((H+1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdim
  have hpow : 4*((H+1 : ℕ) : ℝ)^2 ≤ (m : ℝ)^2 := by nlinarith
  have hinv : 1/(m : ℝ)^2 ≤ 1/(4*((H+1 : ℕ) : ℝ)^2) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have heq : 1/(4*((H+1 : ℕ) : ℝ)^2) = (1/((H+1 : ℕ) : ℝ)^2)/4 := by ring
  rw [heq] at hinv
  have hconst : 3/(1216*((H+1 : ℕ) : ℝ)^2) = ((1/((H+1 : ℕ) : ℝ)^2)*3/4)/304 := by ring
  rw [hconst]
  nlinarith

theorem uniform_fixed_share_inverse_square {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (hqm : ∑ j, q j = 1/(4 : ℕ))
    (hdim : 2*supportSize q+1 ≤ m)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ z) :
    3/(1216*((supportSize q+1 : ℕ) : ℝ)^2) ≤ z :=
  le_trans (fixed_rate_simplification m (supportSize q) hm hdim)
    (uniform_fixed_share_support_lower hm q hq hqm B hB hb z hz hresp)

theorem uniform_minimum_share_inverse_square {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (a : Fin 2 → ℝ) (hq : ∀ j, 0 ≤ q j) (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1) (hdim : 2*(supportSize q+1) ≤ m)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (z : ℝ) (hz : 0 ≤ z)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ z) :
    3/(1216*((supportSize q+1 : ℕ) : ℝ)^2) ≤ z :=
  le_trans (minimum_rate_simplification m (supportSize q) hm hdim)
    (uniform_minimum_share_support_lower hm q a hq ha hnorm B hB hb z hz hresp)

/-- A witness-wise total support obstruction, valid for every positive
    tolerance and every completion under the two minimum shares. -/
theorem uniform_total_support_lower {m : ℕ} (hm : 0 < m)
    (q : Fin m → ℝ) (a : Fin 2 → ℝ) (hq : ∀ j, 0 ≤ q j) (ha : ∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h)
    (hnorm : (∑ h, a h)+(∑ j, q j) = 1)
    (B : Fin m → Fin m → ℝ) (hB : IsSkew B) (hb : ∀ i j, -1 ≤ B i j)
    (ε : ℝ) (hε : 0 < ε)
    (hresp : ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ ε) :
    Real.sqrt (3/1216)*min ((m : ℝ)+2) (1/Real.sqrt ε) ≤ (supportSize q : ℝ)+2 := by
  norm_num only [Nat.cast_ofNat] at *
  let H := supportSize q
  have hrootε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hC : (Real.sqrt (3/1216))^2 = (3/1216 : ℝ) := Real.sq_sqrt (by norm_num)
  have hC0 : 0 ≤ Real.sqrt (3/1216) := Real.sqrt_nonneg _
  have hChalf : Real.sqrt (3/1216) ≤ 1/2 := by nlinarith
  by_cases hdim : 2*(H+1) ≤ m
  · have hbound := uniform_minimum_share_inverse_square hm q a hq ha hnorm hdim B hB hb ε (le_of_lt hε) hresp
    have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
    have hc : (3/1216 : ℝ) ≤ ε*((H+1 : ℕ) : ℝ)^2 := by
      have hh := (div_le_iff₀ (show 0 < 1216*((H+1 : ℕ) : ℝ)^2 by positivity)).mp hbound
      nlinarith
    have hsq : (Real.sqrt ε*((H+1 : ℕ) : ℝ))^2 = ε*((H+1 : ℕ) : ℝ)^2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hε)]
    have hs : Real.sqrt (3/1216) ≤ Real.sqrt ε*((H+1 : ℕ) : ℝ) := by
      have hnonneg := mul_nonneg (le_of_lt hrootε) (le_of_lt hN)
      nlinarith
    have hdiv : Real.sqrt (3/1216)/Real.sqrt ε ≤ ((H+1 : ℕ) : ℝ) :=
      (div_le_iff₀ hrootε).mpr (by nlinarith)
    calc
      _ ≤ Real.sqrt (3/1216)*(1/Real.sqrt ε) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC0
      _ = Real.sqrt (3/1216)/Real.sqrt ε := by ring
      _ ≤ ((H+1 : ℕ) : ℝ) := hdiv
      _ ≤ _ := by dsimp [H]; push_cast; linarith
  · have hdimR : (m : ℝ)+2 ≤ 2*((H : ℝ)+2) := by exact_mod_cast (show m+2 ≤ 2*(H+2) by omega)
    calc
      _ ≤ Real.sqrt (3/1216)*((m : ℝ)+2) := mul_le_mul_of_nonneg_left (min_le_left _ _) hC0
      _ ≤ (1/2)*((m : ℝ)+2) := mul_le_mul_of_nonneg_right hChalf (by positivity)
      _ ≤ _ := by dsimp [H] at hdimR; linarith

end
end SparseCompletion

/- Fixed source body: SupportRate.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem supportSize_le_dimension {m : ℕ} (q : Fin m → ℝ) : supportSize q ≤ m := by
  classical
  unfold supportSize residualSupport
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => q j ≠ 0)

theorem two_anchor_total_support_card {m : ℕ} (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (ha : ∀ h, 0 < a h) :
    (Finset.univ.filter fun v => blockWeights a q v ≠ 0).card = supportSize q+2 := by
  classical
  rw [block_support_card]
  have heq : (Finset.univ.filter fun h => a h ≠ 0) = Finset.univ := by
    ext h
    simp [ne_of_gt (ha h)]
  rw [heq]
  simp only [Finset.card_univ, Fintype.card_fin, supportSize, residualSupport]
  omega

theorem uniform_grid_support_upper (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((2+gridSize 1 (1/4) ε : ℕ) : ℝ) ≤ 3/Real.sqrt ε := by
  have hr : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hr1 : Real.sqrt ε ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hε1
  have hquarter : Real.sqrt (1/4 : ℝ) = 1/2 := by norm_num
  have hroot : Real.sqrt (1*(1/4)/ε) = 1/(2*Real.sqrt ε) := by
    rw [one_mul, Real.sqrt_div (by norm_num), hquarter]
    ring
  by_cases he : 1/4 ≤ ε
  · have hrhalf : 1/2 ≤ Real.sqrt ε := by
      have hh := Real.sqrt_le_sqrt he
      rw [hquarter] at hh
      exact hh
    have hceil : gridSize 1 (1/4) ε ≤ 1 := by
      unfold gridSize
      apply Nat.ceil_le.mpr
      rw [hroot]
      apply (div_le_iff₀ (show 0 < 2*Real.sqrt ε by positivity)).mpr
      norm_num
      linarith
    have hc : ((2+gridSize 1 (1/4) ε : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show 2+gridSize 1 (1/4) ε ≤ 3 by omega)
    exact le_trans hc ((le_div_iff₀ hr).mpr (by nlinarith))
  · have hlt : ε < 1/4 := lt_of_not_ge he
    have hrhalf : Real.sqrt ε < 1/2 := by
      have hh := Real.sqrt_lt_sqrt (le_of_lt hε) hlt
      rw [hquarter] at hh
      exact hh
    have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (1*(1/4)/ε))
    change (gridSize 1 (1/4) ε : ℝ) < Real.sqrt (1*(1/4)/ε)+1 at hc
    rw [hroot] at hc
    have hm := mul_lt_mul_of_pos_right hc hr
    have hid : (1/(2*Real.sqrt ε))*Real.sqrt ε = 1/2 := by field_simp
    rw [add_mul, hid] at hm
    apply (le_div_iff₀ hr).mpr
    push_cast
    nlinarith

/-- Matching existential support rate obtained directly from the main
    sparse-witness theorem. It does not assert the paper's explicit bin
    constructions or their exact exploitability formulas. -/
theorem uniform_sparse_upper_rate {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1/(4 : ℕ)) ∧
      IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      (∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) v ≤ ε) ∧
      (supportSize q : ℝ) ≤ 3*min (m : ℝ) (1/Real.sqrt ε) ∧
      (supportSize q : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt ε) := by
  norm_num only [Nat.cast_ofNat] at *
  let qstar := uniformTarget m (1/4)
  let K := rigidityCore qstar
  let D := rigidityCross qstar
  let p := twoShares (3/4)
  have hqstar : ∀ j, 0 ≤ qstar j := fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j)
  have hmass : ∑ j, qstar j = 1/4 := uniformTarget_mass m hm (1/4)
  have hresp0 : ∀ v, response (blockMatrix K D (orderedBlock 1)) (blockWeights p qstar) v ≤ 0 :=
    fun v => le_of_eq (two_anchor_target_feasible qstar (3/4) (1/4) (by norm_num) hmass v)
  obtain ⟨q,B,hq,hqm,_,hc,_,hB,hb,hresp⟩ := exact_game_sparse_completion 2 K D (orderedBlock 1)
    p qstar 1 (1/4) ε (by norm_num) (by norm_num) hε
    (fun _ => by norm_num [p,twoShares]) hqstar hmass (twoCore_skew _) (orderedBlock_skew 1)
    (orderedBlock_bounds 1 (by norm_num)) hresp0
  have hsupp : supportSize q ≤ 2+gridSize 1 (1/4) ε := by
    simpa only [supportSize,residualSupport] using hc
  have hdim : (supportSize q : ℝ) ≤ m := by exact_mod_cast supportSize_le_dimension q
  have hcard : (supportSize q : ℝ) ≤ 3/Real.sqrt ε :=
    le_trans (by exact_mod_cast hsupp) (uniform_grid_support_upper ε hε hε1)
  have hcard' : (supportSize q : ℝ) ≤ 3*(1/Real.sqrt ε) := by
    calc
      _ ≤ 3/Real.sqrt ε := hcard
      _ = _ := by ring
  have hr : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hr1 : Real.sqrt ε ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hε1
  have hresidual : (supportSize q : ℝ) ≤ 3*min (m : ℝ) (1/Real.sqrt ε) := by
    rcases le_total (m : ℝ) (1/Real.sqrt ε) with hh | hh
    · rw [min_eq_left hh]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    · rw [min_eq_right hh]
      nlinarith
  have htotal : (supportSize q : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt ε) := by
    rcases le_total ((m : ℝ)+2) (1/Real.sqrt ε) with hh | hh
    · rw [min_eq_left hh]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    · rw [min_eq_right hh]
      have hinv : 1 ≤ 1/Real.sqrt ε := (le_div_iff₀ hr).mpr (by nlinarith)
      nlinarith
  refine ⟨q,B,hq,hqm,hB,hb,?_,hresidual,htotal⟩
  simpa only [zero_add] using hresp

end
end SparseCompletion

/- Fixed source body: SupportMinimum.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Actual witnesses in the uniform observed game. `fixed=true` adds
    exact anchor shares; both classes retain the two minimum shares. -/
def UniformWitness (m : ℕ) (ε : ℝ) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) ∧
    (fixed=true → a=twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) ∧
    (∑ h, a h)+(∑ j, q j)=1 ∧
    IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
    ∀ v, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights a q) v ≤ ε

/-- The integer count minimized below is the actual support of the full strategy. -/
theorem uniform_witness_total_support_card {m : ℕ} {ε : ℝ} {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε fixed a q B) :
    (Finset.univ.filter fun v => blockWeights a q v ≠ 0).card = supportSize q+2 := by
  apply two_anchor_total_support_card
  intro h
  have hh := hw.2.1 h
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem uniform_witness_dense (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    UniformWitness m ε fixed (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) (uniformTarget m (1/(4 : ℕ))) (orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  unfold UniformWitness
  norm_num only [Nat.cast_ofNat]
  have hmass := uniformTarget_mass m hm (1/4)
  refine ⟨fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j),
    fun _ => by norm_num [twoShares], (by simp), ?_, orderedBlock_skew 1,
    orderedBlock_bounds 1 (by norm_num), ?_⟩
  · rw [hmass, Fin.sum_univ_two]
    norm_num [twoShares]
  · intro v
    exact le_trans (le_of_eq (two_anchor_target_feasible _ (3/4) (1/4) (by norm_num) hmass v)) hε

theorem uniform_witness_support_exists (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ s : ℕ, ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      UniformWitness m ε fixed a q B ∧ supportSize q+2=s := by
  exact ⟨supportSize (uniformTarget m (1/4))+2, twoShares (3/4),uniformTarget m (1/4),
    orderedBlock 1, uniform_witness_dense m hm ε hε fixed,rfl⟩

/-- A genuine attained integer minimum over actual completions and
    strategies. Nonemptiness is supplied by the dense exact witness. -/
def uniformMinimumTotalSupport (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) : ℕ :=
  by
    classical
    exact Nat.find (uniform_witness_support_exists m hm ε hε fixed)

theorem uniformMinimumTotalSupport_attained (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      UniformWitness m ε fixed a q B ∧
      supportSize q+2=uniformMinimumTotalSupport m hm ε hε fixed :=
  by
    classical
    exact Nat.find_spec (uniform_witness_support_exists m hm ε hε fixed)

theorem uniformMinimumTotalSupport_le (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hw : UniformWitness m ε fixed a q B) :
    uniformMinimumTotalSupport m hm ε hε fixed ≤ supportSize q+2 :=
  by
    classical
    exact Nat.find_min' (uniform_witness_support_exists m hm ε hε fixed) ⟨a,q,B,hw,rfl⟩

theorem uniformMinimumTotalSupport_zero (m : ℕ) (hm : 2 ≤ m) (fixed : Bool) :
    uniformMinimumTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 (le_refl 0) fixed = m+2 := by
  obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m (by omega) 0 (by norm_num) fixed
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  obtain ⟨hq,ha,_,hnorm,hB,hb,hresp⟩ := hw
  have hrigid := bounded_two_anchor_minimum_share_rigidity hm (uniformTarget m (1/4)) q a
    (uniformTarget_positive m (1/4) (by norm_num)) (uniformTarget_mass m (by omega) (1/4))
    ha hq hnorm B hB hb hresp
  have hcard : supportSize q=m := by
    rw [hrigid.2.1]
    exact positive_target_full_support _ (uniformTarget_positive m (1/4) (by norm_num))
  omega

/-- Sharp-order total support complexity with the paper's explicit
    constants, for both minimum-share and fixed-share commitment classes. -/
theorem uniformMinimumTotalSupport_sharp (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (fixed : Bool) :
    Real.sqrt (3/1216)*min ((m : ℝ)+2) (1/Real.sqrt ε) ≤
      (uniformMinimumTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) fixed : ℝ) ∧
    (uniformMinimumTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) fixed : ℝ) ≤
      5*min ((m : ℝ)+2) (1/Real.sqrt ε) := by
  constructor
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m (by omega) ε (le_of_lt hε) fixed
    simp only [UniformWitness,Nat.cast_ofNat] at hw
    obtain ⟨hq,ha,_,hnorm,hB,hb,hresp⟩ := hw
    have hh := uniform_total_support_lower (by omega) q a hq ha hnorm B hB
      (fun i j => (hb i j).1) ε hε hresp
    have heq : (supportSize q : ℝ)+2 = (uniformMinimumTotalSupport m (by omega) ε (le_of_lt hε) fixed : ℝ) := by
      exact_mod_cast hcount
    rw [← heq]
    exact hh
  · obtain ⟨q,B,hq,hqm,hB,hb,hresp,_,hcount⟩ := uniform_sparse_upper_rate (m := m) (by omega) ε hε hε1
    have hw : UniformWitness m ε fixed (twoShares (3/4)) q B := by
      unfold UniformWitness
      norm_num only [Nat.cast_ofNat]
      refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,hB,hb,hresp⟩
      rw [hqm,Fin.sum_univ_two]
      norm_num [twoShares]
    have hle := uniformMinimumTotalSupport_le m (by omega) ε (le_of_lt hε) fixed (twoShares (3/4)) q B hw
    have hleR : (uniformMinimumTotalSupport m (by omega) ε (le_of_lt hε) fixed : ℝ) ≤ (supportSize q : ℝ)+2 := by
      exact_mod_cast hle
    exact le_trans hleR hcount

end
end SparseCompletion

/- Fixed source body: ResidualMinimum.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem residual_rate_from_inverse_square (m H : ℕ) (hH : 1 ≤ H)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : 2*(H+1) ≤ m → 3/(1216*((H+1 : ℕ) : ℝ)^2) ≤ ε) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤ H := by
  norm_num only [Nat.cast_ofNat] at *
  have hr : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hc0 : 0 ≤ Real.sqrt (3/1216) := Real.sqrt_nonneg _
  have hc2 : (Real.sqrt (3/1216))^2 = (3/1216 : ℝ) := Real.sq_sqrt (by norm_num)
  have hc : Real.sqrt (3/1216)/2 ≤ 1/3 := by nlinarith
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  by_cases hdim : 2*(H+1) ≤ m
  · have hh := hbound hdim
    have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
    have hs : (3/1216 : ℝ) ≤ ε*((H+1 : ℕ) : ℝ)^2 := by
      have h := (div_le_iff₀ (show 0 < 1216*((H+1 : ℕ) : ℝ)^2 by positivity)).mp hh
      nlinarith
    have heq : (Real.sqrt ε*((H+1 : ℕ) : ℝ))^2 = ε*((H+1 : ℕ) : ℝ)^2 := by
      rw [mul_pow,Real.sq_sqrt (le_of_lt hε)]
    have hroot : Real.sqrt (3/1216) ≤ Real.sqrt ε*((H+1 : ℕ) : ℝ) := by
      have hnn := mul_nonneg (le_of_lt hr) (le_of_lt hN)
      nlinarith
    have hdiv : Real.sqrt (3/1216)/(2*Real.sqrt ε) ≤ (H : ℝ) := by
      apply (div_le_iff₀ (show 0 < 2*Real.sqrt ε by positivity)).mpr
      norm_num only [Nat.cast_add,Nat.cast_one] at hroot
      nlinarith
    calc
      _ ≤ (Real.sqrt (3/1216)/2)*(1/Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = Real.sqrt (3/1216)/(2*Real.sqrt ε) := by ring
      _ ≤ _ := hdiv
  · have hdimR : (m : ℝ) ≤ 3*(H : ℝ) := by
      exact_mod_cast (show m ≤ 3*H by omega)
    calc
      _ ≤ (Real.sqrt (3/1216)/2)*(m : ℝ) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ ≤ (1/3)*(m : ℝ) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ ≤ _ := by linarith

theorem uniform_witness_fixed_residual_positive {m : ℕ} {ε : ℝ}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε true a q B) : 1 ≤ supportSize q := by
  classical
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨_,_,ha,hnorm,_⟩
  have hmass : ∑ j, q j = 1/4 := by
    rw [ha trivial,Fin.sum_univ_two] at hnorm
    norm_num [twoShares] at hnorm
    linarith
  have hex : ∃ j, q j ≠ 0 := by
    by_contra hh
    push Not at hh
    simp only [hh,Finset.sum_const_zero] at hmass
    norm_num at hmass
  obtain ⟨j,hj⟩ := hex
  exact Finset.card_pos.mpr ⟨j,by simp [residualSupport,hj]⟩

theorem uniform_witness_small_residual_positive {m : ℕ} (hm : 2 ≤ m) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(1024 : ℕ)) {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε fixed a q B) : 1 ≤ supportSize q := by
  norm_num only [Nat.cast_ofNat] at *
  by_contra hh
  have hzero : supportSize q=0 := by omega
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  have hd : 2*(supportSize q+1) ≤ m := by omega
  have hbound := uniform_minimum_share_inverse_square (by omega) q a hq ha hnorm hd B hB
    (fun i j => (hb i j).1) ε hε hresp
  norm_num [hzero] at hbound
  linarith

theorem uniform_witness_residual_lower {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) {fixed : Bool} {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {B : Fin m → Fin m → ℝ} (hw : UniformWitness m ε fixed a q B)
    (hpos : 1 ≤ supportSize q) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤ supportSize q := by
  norm_num only [Nat.cast_ofNat] at *
  apply residual_rate_from_inverse_square m (supportSize q) hpos ε hε
  intro hdim
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  exact uniform_minimum_share_inverse_square hm q a hq ha hnorm hdim B hB
    (fun i j => (hb i j).1) ε (le_of_lt hε) hresp

/-- The residual count of the attained total minimum. Both anchors have
    strictly positive mass, so subtracting two gives the residual minimum. -/
def uniformMinimumResidualSupport (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) : ℕ :=
  uniformMinimumTotalSupport m hm ε hε fixed-2

theorem uniformMinimumResidualSupport_attained (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      UniformWitness m ε fixed a q B ∧ supportSize q=uniformMinimumResidualSupport m hm ε hε fixed := by
  obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m hm ε hε fixed
  exact ⟨a,q,B,hw,by rw [uniformMinimumResidualSupport,←hcount]; omega⟩

theorem uniformMinimumResidualSupport_le (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ) (hw : UniformWitness m ε fixed a q B) :
    uniformMinimumResidualSupport m hm ε hε fixed ≤ supportSize q := by
  have hh := uniformMinimumTotalSupport_le m hm ε hε fixed a q B hw
  unfold uniformMinimumResidualSupport
  omega

theorem uniformMinimumResidualSupport_zero (m : ℕ) (hm : 2 ≤ m) (fixed : Bool) :
    uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 (le_refl 0) fixed=m := by
  rw [uniformMinimumResidualSupport,uniformMinimumTotalSupport_zero m hm fixed]
  omega

theorem uniformMinimumResidualSupport_upper (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (fixed : Bool) :
    (uniformMinimumResidualSupport m hm ε (le_of_lt hε) fixed : ℝ) ≤
      3*min (m : ℝ) (1/Real.sqrt ε) := by
  obtain ⟨q,B,hq,hqm,hB,hb,hresp,hcount,_⟩ := uniform_sparse_upper_rate hm ε hε hε1
  have hw : UniformWitness m ε fixed (twoShares (3/4)) q B := by
    unfold UniformWitness
    norm_num only [Nat.cast_ofNat]
    refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,hB,hb,hresp⟩
    rw [hqm,Fin.sum_univ_two]
    norm_num [twoShares]
  have hmin := uniformMinimumResidualSupport_le m hm ε (le_of_lt hε) fixed (twoShares (3/4)) q B hw
  exact le_trans (by exact_mod_cast hmin) hcount

theorem uniformMinimumResidualSupport_fixed_sharp (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤
      (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) true : ℝ) ∧
    (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) true : ℝ) ≤
      3*min (m : ℝ) (1/Real.sqrt ε) := by
  norm_num only [Nat.cast_ofNat] at *
  constructor
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumResidualSupport_attained m (by omega) ε (le_of_lt hε) true
    have hh := uniform_witness_residual_lower (by omega) hε hw (uniform_witness_fixed_residual_positive hw)
    have heq : (supportSize q : ℝ) = (uniformMinimumResidualSupport m (by omega) ε (le_of_lt hε) true : ℝ) := by exact_mod_cast hcount
    rwa [heq] at hh
  · exact uniformMinimumResidualSupport_upper m (by omega) ε hε hε1 true

theorem uniformMinimumResidualSupport_natural_sharp (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hsmall : ε ≤ 1/(1024 : ℕ)) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤
      (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) false : ℝ) ∧
    (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) false : ℝ) ≤
      3*min (m : ℝ) (1/Real.sqrt ε) := by
  norm_num only [Nat.cast_ofNat] at *
  constructor
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumResidualSupport_attained m (by omega) ε (le_of_lt hε) false
    have hh := uniform_witness_residual_lower (by omega) hε hw
      (uniform_witness_small_residual_positive hm (le_of_lt hε) hsmall hw)
    have heq : (supportSize q : ℝ) = (uniformMinimumResidualSupport m (by omega) ε (le_of_lt hε) false : ℝ) := by exact_mod_cast hcount
    rwa [heq] at hh
  · exact uniformMinimumResidualSupport_upper m (by omega) ε hε (by linarith) false

end
end SparseCompletion

/- Fixed source body: IntervalLower.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem block_entry_perturbation {α ι : Type*}
    (K K' : α → α → ℝ) (D D' : ι → α → ℝ) (B : ι → ι → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hK : ∀ i j, |K i j-K' i j| ≤ δ)
    (hD : ∀ j i, |D j i-D' j i| ≤ δ) :
    ∀ i j, |blockMatrix K D B i j-blockMatrix K' D' B i j| ≤ δ := by
  intro i j
  cases i <;> cases j
  · exact hK _ _
  · simpa only [blockMatrix, neg_sub_neg, abs_sub_comm] using hD _ _
  · exact hD _ _
  · simpa only [blockMatrix, sub_self, abs_zero] using hδ

/-- Closed clipped observation interval about a central bounded payoff. -/
def ClippedObservation (a δ x : ℝ) : Prop := -1 ≤ x ∧ x ≤ 1 ∧ |x-a| ≤ δ

theorem clipped_observation_interval (a δ x : ℝ) :
    ClippedObservation a δ x ↔ x ∈ Set.Icc (max (-1) (a-δ)) (min 1 (a+δ)) := by
  simp only [ClippedObservation, Set.mem_Icc, max_le_iff, le_min_iff, abs_le]
  constructor
  · rintro ⟨h1,h2,hlo,hup⟩
    exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
  · rintro ⟨⟨h1,hlo⟩,h2,hup⟩
    exact ⟨h1,h2,by constructor <;> linarith⟩

/-- The residual block is free; precisely the anchor-incident entries are
    restricted to their clipped uncertainty intervals. -/
def UniformIntervalWitness (m : ℕ) (ε δ : ℝ) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ)
    (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∀ h, ((3 : ℕ) : ℝ)/(8 : ℕ) ≤ a h) ∧
    (fixed=true → a=twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) ∧
    (∑ h, a h)+(∑ j, q j)=1 ∧ IsSkew K ∧ IsSkew B ∧
    (∀ i j, ClippedObservation (rigidityCore (uniformTarget m (1/(4 : ℕ))) i j) δ (K i j)) ∧
    (∀ j h, ClippedObservation (rigidityCross (uniformTarget m (1/(4 : ℕ))) j h) δ (D j h)) ∧
    (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
    ∀ v, response (blockMatrix K D B) (blockWeights a q) v ≤ ε

theorem uniform_interval_restore {m : ℕ} {ε δ : ℝ} {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {K : Fin 2 → Fin 2 → ℝ} {D : Fin m → Fin 2 → ℝ} {B : Fin m → Fin m → ℝ}
    (hδ : 0 ≤ δ) (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    UniformWitness m (ε+δ) fixed a q B := by
  rcases hw with ⟨hq,ha,hfixed,hmass,_,hB,hK,hD,hb,hresp⟩
  unfold UniformWitness
  norm_num only [Nat.cast_ofNat]
  refine ⟨hq,ha,hfixed,hmass,hB,hb,?_⟩
  intro v
  have hp : ∀ h, 0 ≤ a h := fun h => by linarith [ha h]
  have hh := response_perturbation
    (blockMatrix (rigidityCore (uniformTarget m (1/4))) (rigidityCross (uniformTarget m (1/4))) B)
    (blockMatrix K D B) (blockWeights a q) δ 1
    (blockWeights_nonneg a q hp hq)
    (by rw [blockWeights_mass]; exact hmass)
    (block_entry_perturbation _ _ _ _ _ δ hδ
      (fun i j => by simpa only [abs_sub_comm,Nat.cast_ofNat] using (hK i j).2.2)
      (fun j h => by simpa only [abs_sub_comm,Nat.cast_ofNat] using (hD j h).2.2)) v
  have hup := (abs_le.mp hh).2
  linarith [hresp v]


theorem uniform_interval_total_support_card {m : ℕ} {ε δ : ℝ} {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {K : Fin 2 → Fin 2 → ℝ} {D : Fin m → Fin 2 → ℝ} {B : Fin m → Fin m → ℝ}
    (hδ : 0 ≤ δ) (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    (Finset.univ.filter fun v => blockWeights a q v ≠ 0).card = supportSize q+2 := by
  exact uniform_witness_total_support_card (uniform_interval_restore hδ hw)

theorem uniform_interval_total_support_lower {m : ℕ} (hm : 0 < m)
    {ε δ : ℝ} (heff : 0 < ε+δ) (hδ : 0 ≤ δ) {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {K : Fin 2 → Fin 2 → ℝ} {D : Fin m → Fin 2 → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+δ)) ≤ (supportSize q : ℝ)+2 := by
  norm_num only [Nat.cast_ofNat] at *
  have hr := uniform_interval_restore hδ hw
  simp only [UniformWitness,Nat.cast_ofNat] at hr
  rcases hr with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  exact uniform_total_support_lower hm q a hq ha hnorm B hB (fun i j => (hb i j).1)
    (ε+δ) heff hresp


theorem uniform_interval_dense (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) :
    UniformIntervalWitness m ε δ fixed (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) (uniformTarget m (1/(4 : ℕ)))
      (rigidityCore (uniformTarget m (1/(4 : ℕ)))) (rigidityCross (uniformTarget m (1/(4 : ℕ))))
      (orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  have hdense := uniform_witness_dense m hm ε hε fixed
  simp only [UniformWitness,Nat.cast_ofNat] at hdense
  rcases hdense with ⟨hq,ha,hfixed,hmass,hB,hb,hresp⟩
  have hobs := two_anchor_observed_bounds hm (uniformTarget m (1/4)) hq
    (uniformTarget_mass m hm (1/4))
  change (∀ i j, -1 ≤ rigidityCore (uniformTarget m (1/4)) i j ∧
      rigidityCore (uniformTarget m (1/4)) i j ≤ 1) ∧
    (∀ j h, -1 ≤ rigidityCross (uniformTarget m (1/4)) j h ∧
      rigidityCross (uniformTarget m (1/4)) j h ≤ 1) at hobs
  refine ⟨hq,ha,(by simp),hmass,twoCore_skew _,hB,?_,?_,hb,hresp⟩
  · intro i j
    exact ⟨(hobs.1 i j).1,(hobs.1 i j).2,by simpa using hδ⟩
  · intro j h
    exact ⟨(hobs.2 j h).1,(hobs.2 j h).2,by simpa using hδ⟩

theorem uniform_interval_support_exists (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) :
    ∃ s : ℕ, ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ)
      (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ) (B : Fin m → Fin m → ℝ),
      UniformIntervalWitness m ε δ fixed a q K D B ∧ supportSize q+2=s := by
  exact ⟨supportSize (uniformTarget m (1/4))+2,twoShares (3/4),uniformTarget m (1/4),
    rigidityCore _,rigidityCross _,orderedBlock 1,uniform_interval_dense m hm ε δ hε hδ fixed,rfl⟩

def uniformMinimumIntervalTotalSupport (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) : ℕ := by
  classical
  exact Nat.find (uniform_interval_support_exists m hm ε δ hε hδ fixed)

theorem uniformMinimumIntervalTotalSupport_attained (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool) :
    ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ)
      (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ) (B : Fin m → Fin m → ℝ),
      UniformIntervalWitness m ε δ fixed a q K D B ∧
        supportSize q+2=uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed := by
  classical
  exact Nat.find_spec (uniform_interval_support_exists m hm ε δ hε hδ fixed)

theorem uniformMinimumIntervalTotalSupport_lower (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (heff : 0 < ε+δ) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+δ)) ≤
      (uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed : ℝ) := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨a,q,K,D,B,hw,hcount⟩ :=
    uniformMinimumIntervalTotalSupport_attained m hm ε δ hε hδ fixed
  have hlower := uniform_interval_total_support_lower hm heff hδ hw
  have heq : (supportSize q : ℝ)+2 =
      (uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed : ℝ) := by exact_mod_cast hcount
  rwa [heq] at hlower


theorem uniform_exact_to_interval {m : ℕ} (hm : 0 < m) {ε δ : ℝ} (hδ : 0 ≤ δ)
    {fixed : Bool} {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε fixed a q B) :
    UniformIntervalWitness m ε δ fixed a q (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B := by
  norm_num only [Nat.cast_ofNat] at *
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨hq,ha,hfixed,hmass,hB,hb,hresp⟩
  have hobs := two_anchor_observed_bounds hm (uniformTarget m (1/4))
    (fun j => le_of_lt (uniformTarget_positive m (1/4) (by norm_num) j))
    (uniformTarget_mass m hm (1/4))
  change (∀ i j, -1 ≤ rigidityCore (uniformTarget m (1/4)) i j ∧
      rigidityCore (uniformTarget m (1/4)) i j ≤ 1) ∧
    (∀ j h, -1 ≤ rigidityCross (uniformTarget m (1/4)) j h ∧
      rigidityCross (uniformTarget m (1/4)) j h ≤ 1) at hobs
  refine ⟨hq,ha,hfixed,hmass,twoCore_skew _,hB,?_,?_,hb,hresp⟩
  · intro i j
    exact ⟨(hobs.1 i j).1,(hobs.1 i j).2,by simpa using hδ⟩
  · intro j h
    exact ⟨(hobs.2 j h).1,(hobs.2 j h).2,by simpa using hδ⟩

theorem uniformMinimumIntervalTotalSupport_le (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (fixed : Bool)
    (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (K : Fin 2 → Fin 2 → ℝ) (D : Fin m → Fin 2 → ℝ) (B : Fin m → Fin m → ℝ)
    (hw : UniformIntervalWitness m ε δ fixed a q K D B) :
    uniformMinimumIntervalTotalSupport m hm ε δ hε hδ fixed ≤ supportSize q+2 := by
  classical
  exact Nat.find_min' (uniform_interval_support_exists m hm ε δ hε hδ fixed) ⟨a,q,K,D,B,hw,rfl⟩

theorem uniformMinimumIntervalTotalSupport_radius_zero (m : ℕ) (hm : 0 < m) (ε : ℝ)
    (hε : 0 ≤ ε) (fixed : Bool) :
    uniformMinimumIntervalTotalSupport m hm ε 0 hε (le_refl 0) fixed =
      uniformMinimumTotalSupport m hm ε hε fixed := by
  apply Nat.le_antisymm
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m hm ε hε fixed
    have hle := uniformMinimumIntervalTotalSupport_le m hm ε 0 hε (by norm_num) fixed
      a q _ _ B (uniform_exact_to_interval hm (by norm_num) hw)
    rwa [hcount] at hle
  · obtain ⟨a,q,K,D,B,hw,hcount⟩ :=
      uniformMinimumIntervalTotalSupport_attained m hm ε 0 hε (by norm_num) fixed
    have hcentral : UniformWitness m ε fixed a q B := by
      simpa only [add_zero] using uniform_interval_restore (by norm_num : (0 : ℝ) ≤ 0) hw
    have hle := uniformMinimumTotalSupport_le m hm ε hε fixed a q B hcentral
    rwa [hcount] at hle

theorem uniformMinimumIntervalTotalSupport_origin (m : ℕ) (hm : 2 ≤ m) (fixed : Bool) :
    uniformMinimumIntervalTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 0 (le_refl 0) (le_refl 0) fixed = m+2 := by
  rw [uniformMinimumIntervalTotalSupport_radius_zero]
  exact uniformMinimumTotalSupport_zero m hm fixed

end
end SparseCompletion

/- Fixed source body: CoreLower.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem two_core_response_perturbation {ι : Type*} [Fintype ι]
    (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ) (q : ι → ℝ)
    (u v δ : ℝ) (hδ : 0 ≤ δ) (huv : |u-v| ≤ δ) :
    ∀ i, |response (blockMatrix (twoCore u) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) i-
      response (blockMatrix (twoCore v) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) i| ≤ (((3 : ℕ) : ℝ)/(8 : ℕ))*δ := by
  norm_num only [Nat.cast_ofNat] at *
  intro i
  cases i with
  | inl h =>
    rw [block_response_anchor,block_response_anchor]
    fin_cases h
    · change |anchorResponse (twoCore u) D (twoShares (3/4)) q 0-
        anchorResponse (twoCore v) D (twoShares (3/4)) q 0| ≤ (3/8)*δ
      have heq : anchorResponse (twoCore u) D (twoShares (3/4)) q 0-
          anchorResponse (twoCore v) D (twoShares (3/4)) q 0 = (u-v)*(3/8) := by
        simp [anchorResponse,Fin.sum_univ_two,twoCore,twoShares]
        ring
      rw [heq,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/8)]
      nlinarith
    · change |anchorResponse (twoCore u) D (twoShares (3/4)) q 1-
        anchorResponse (twoCore v) D (twoShares (3/4)) q 1| ≤ (3/8)*δ
      have heq : anchorResponse (twoCore u) D (twoShares (3/4)) q 1-
          anchorResponse (twoCore v) D (twoShares (3/4)) q 1 = -(u-v)*(3/8) := by
        simp [anchorResponse,Fin.sum_univ_two,twoCore,twoShares]
        ring
      rw [heq,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/8)]
      nlinarith
  | inr j =>
    rw [block_response_residual,block_response_residual,sub_self,abs_zero]
    positivity

/-- Exact cross observations, fixed anchor shares, and uncertainty solely
    in the single unordered anchor-core entry. -/
def UniformCoreWitness (m : ℕ) (ε δ : ℝ) (q : Fin m → ℝ) (u : ℝ)
    (B : Fin m → Fin m → ℝ) : Prop :=
  UniformIntervalWitness m ε δ true (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q (twoCore u)
    (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B

theorem uniform_core_restore {m : ℕ} {ε δ : ℝ} {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (hδ : 0 ≤ δ) (hw : UniformCoreWitness m ε δ q u B) :
    UniformWitness m (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) true (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q B := by
  norm_num only [Nat.cast_ofNat] at *
  rcases hw with ⟨hq,ha,_,hmass,_,hB,hK,_,hb,hresp⟩
  let c := (2 : ℕ)*scoreMoment (uniformTarget m (1/4))
    (exposingWeight (uniformTarget m (1/4)) (1/4))/((3 : ℕ)/(4 : ℕ))
  have hnear : |u-c| ≤ δ := by
    simpa [rigidityCore,twoCore,c] using (hK 0 1).2.2
  have hpert := two_core_response_perturbation (rigidityCross (uniformTarget m (1/4))) B q
    c u δ hδ (by simpa only [abs_sub_comm] using hnear)
  unfold UniformWitness
  norm_num only [Nat.cast_ofNat]
  refine ⟨hq,ha,(by simp),hmass,hB,hb,?_⟩
  intro v
  have hh := (abs_le.mp (hpert v)).2
  change response (blockMatrix (twoCore c) (rigidityCross (uniformTarget m (1/4))) B)
      (blockWeights (twoShares (3/4)) q) v ≤ ε+(3/8)*δ
  linarith [hresp v]

theorem uniform_core_total_support_lower {m : ℕ} (hm : 0 < m) {ε δ : ℝ}
    (heff : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) (hδ : 0 ≤ δ) {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (hw : UniformCoreWitness m ε δ q u B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) ≤ (supportSize q : ℝ)+2 := by
  norm_num only [Nat.cast_ofNat] at *
  have hr := uniform_core_restore hδ hw
  simp only [UniformWitness,Nat.cast_ofNat] at hr
  rcases hr with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  exact uniform_total_support_lower hm q (twoShares (3/4)) hq ha hnorm B hB
    (fun i j => (hb i j).1) (ε+(3/8)*δ) heff hresp


/-- The central bounded anchor-core payoff of the uniform family. -/
def uniformCoreValue (m : ℕ) : ℝ :=
  (2 : ℕ)*scoreMoment (uniformTarget m (1/(4 : ℕ)))
    (exposingWeight (uniformTarget m (1/(4 : ℕ))) (1/(4 : ℕ)))/((3 : ℕ)/(4 : ℕ))

theorem uniform_core_dense (m : ℕ) (hm : 0 < m) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    UniformCoreWitness m ε δ (uniformTarget m (1/(4 : ℕ))) (uniformCoreValue m) (orderedBlock 1) := by
  norm_num only [Nat.cast_ofNat] at *
  exact uniform_interval_dense m hm ε δ hε hδ true

theorem uniform_core_support_exists (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    ∃ s : ℕ, ∃ (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ),
      UniformCoreWitness m ε δ q u B ∧ supportSize q+2=s := by
  exact ⟨supportSize (uniformTarget m (1/4))+2,uniformTarget m (1/4),uniformCoreValue m,
    orderedBlock 1,uniform_core_dense m hm ε δ hε hδ,rfl⟩

def uniformMinimumCoreTotalSupport (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) : ℕ := by
  classical
  exact Nat.find (uniform_core_support_exists m hm ε δ hε hδ)

theorem uniformMinimumCoreTotalSupport_attained (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    ∃ (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ),
      UniformCoreWitness m ε δ q u B ∧
        supportSize q+2=uniformMinimumCoreTotalSupport m hm ε δ hε hδ := by
  classical
  exact Nat.find_spec (uniform_core_support_exists m hm ε δ hε hδ)

theorem uniformMinimumCoreTotalSupport_le (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ)
    (hw : UniformCoreWitness m ε δ q u B) :
    uniformMinimumCoreTotalSupport m hm ε δ hε hδ ≤ supportSize q+2 := by
  classical
  exact Nat.find_min' (uniform_core_support_exists m hm ε δ hε hδ) ⟨q,u,B,hw,rfl⟩

theorem uniform_core_total_support_card {m : ℕ} {ε δ : ℝ} {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (hδ : 0 ≤ δ) (hw : UniformCoreWitness m ε δ q u B) :
    (Finset.univ.filter fun v => blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q v ≠ 0).card = supportSize q+2 := by
  norm_num only [Nat.cast_ofNat] at *
  exact uniform_witness_total_support_card (uniform_core_restore hδ hw)

theorem uniformMinimumCoreTotalSupport_lower (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (heff : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+2) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) ≤
      (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨q,u,B,hw,hcount⟩ := uniformMinimumCoreTotalSupport_attained m hm ε δ hε hδ
  have hh := uniform_core_total_support_lower hm heff hδ hw
  have heq : (supportSize q : ℝ)+2 =
      (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) := by exact_mod_cast hcount
  rwa [heq] at hh

theorem uniformMinimumCoreTotalSupport_radius_zero (m : ℕ) (hm : 0 < m) (ε : ℝ)
    (hε : 0 ≤ ε) :
    uniformMinimumCoreTotalSupport m hm ε 0 hε (le_refl 0) =
      uniformMinimumTotalSupport m hm ε hε true := by
  apply Nat.le_antisymm
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m hm ε hε true
    have ha := hw.2.2.1 rfl
    subst a
    have hinterval := uniform_exact_to_interval hm (le_refl 0) hw
    have hle := uniformMinimumCoreTotalSupport_le m hm ε 0 hε (le_refl 0) q
      (uniformCoreValue m) B hinterval
    rwa [hcount] at hle
  · obtain ⟨q,u,B,hw,hcount⟩ := uniformMinimumCoreTotalSupport_attained m hm ε 0 hε (le_refl 0)
    have hcentral : UniformWitness m ε true (twoShares (3/4)) q B := by
      simpa only [mul_zero,add_zero,Nat.cast_ofNat] using uniform_core_restore (le_refl 0) hw
    have hle := uniformMinimumTotalSupport_le m hm ε hε true (twoShares (3/4)) q B hcentral
    rwa [hcount] at hle

theorem uniformMinimumCoreTotalSupport_origin (m : ℕ) (hm : 2 ≤ m) :
    uniformMinimumCoreTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 0
      (le_refl 0) (le_refl 0) = m+2 := by
  rw [uniformMinimumCoreTotalSupport_radius_zero]
  exact uniformMinimumTotalSupport_zero m hm true

end
end SparseCompletion

/- Fixed source body: BinCompression.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Moving a symmetric pair inward decreases every call payoff. -/
theorem inner_pair_call_le (a u v b z : ℝ) (hau : a ≤ u) (huv : u ≤ v)
    (hvb : v ≤ b) (hsum : a+b=u+v) :
    max (u-z) 0+max (v-z) 0 ≤ max (a-z) 0+max (b-z) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- The two central original labels, coalescing when the bin has odd size. -/
def binLower (L : ℕ) (hL : 0 < L) : Fin L := ⟨(L-1)/2,lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hL (Nat.zero_lt_succ 0))⟩
def binUpper (L : ℕ) (hL : 0 < L) : Fin L := ⟨L/2,Nat.div_lt_self hL (Nat.lt_succ_self 1)⟩

theorem bin_middle_sum (L : ℕ) (hL : 0 < L) :
    (binLower L hL).val+(binUpper L hL).val=L-1 := by
  simp only [binLower,binUpper]
  omega

theorem bin_middle_order (L : ℕ) (hL : 0 < L) : binLower L hL ≤ binUpper L hL := by
  simp only [Fin.le_def,binLower,binUpper]
  omega

theorem bin_middle_outer (L : ℕ) (hL : 0 < L) (i : Fin L) :
    min i.val (L-1-i.val) ≤ (binLower L hL).val ∧
      (binUpper L hL).val ≤ max i.val (L-1-i.val) := by
  simp only [binLower,binUpper]
  omega

theorem bin_pair_call_le (L : ℕ) (hL : 0 < L) (a d z : ℝ) (hd : 0 ≤ d) (i : Fin L) :
    max (a+d*(binLower L hL).val-z) 0+max (a+d*(binUpper L hL).val-z) 0 ≤
      max (a+d*i.val-z) 0+max (a+d*(L-1-i.val : ℕ)-z) 0 := by
  have houter := bin_middle_outer L hL i
  have hmiddle := bin_middle_order L hL
  have hsum := bin_middle_sum L hL
  have hi : i.val ≤ L-1 := by omega
  by_cases hii : i.val ≤ L-1-i.val
  · have hlo : i.val ≤ (binLower L hL).val := by simpa only [min_eq_left hii] using houter.1
    have hhi : (binUpper L hL).val ≤ L-1-i.val := by simpa only [max_eq_right hii] using houter.2
    apply inner_pair_call_le
    · have hh : (i.val : ℝ) ≤ (binLower L hL).val := by exact_mod_cast hlo
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binLower L hL).val : ℝ) ≤ (binUpper L hL).val := by exact_mod_cast hmiddle
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binUpper L hL).val : ℝ) ≤ (L-1-i.val : ℕ) := by exact_mod_cast hhi
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : (i.val : ℝ)+(L-1-i.val : ℕ) =
          (binLower L hL).val+(binUpper L hL).val := by
        exact_mod_cast (show i.val+(L-1-i.val)= (binLower L hL).val+(binUpper L hL).val by omega)
      nlinarith
  · have hii' : L-1-i.val ≤ i.val := by omega
    have hlo : L-1-i.val ≤ (binLower L hL).val := by simpa only [min_eq_right hii'] using houter.1
    have hhi : (binUpper L hL).val ≤ i.val := by simpa only [max_eq_left hii'] using houter.2
    rw [add_comm (max (a+d*(i.val : ℝ)-z) 0)]
    apply inner_pair_call_le
    · have hh : ((L-1-i.val : ℕ) : ℝ) ≤ (binLower L hL).val := by exact_mod_cast hlo
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binLower L hL).val : ℝ) ≤ (binUpper L hL).val := by exact_mod_cast hmiddle
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binUpper L hL).val : ℝ) ≤ i.val := by exact_mod_cast hhi
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : (i.val : ℝ)+(L-1-i.val : ℕ) =
          (binLower L hL).val+(binUpper L hL).val := by
        exact_mod_cast (show i.val+(L-1-i.val)= (binLower L hL).val+(binUpper L hL).val by omega)
      nlinarith


theorem bin_call_compression_nonneg (L : ℕ) (hL : 0 < L) (a d z : ℝ) (hd : 0 ≤ d) :
    (L : ℝ)*(max (a+d*(binLower L hL).val-z) 0+
      max (a+d*(binUpper L hL).val-z) 0) ≤
      (2 : ℕ)*∑ i : Fin L, max (a+d*i.val-z) 0 := by
  norm_num only [Nat.cast_ofNat] at *
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L)))
    (fun i _ => bin_pair_call_le L hL a d z hd i)
  have hrev : (∑ i : Fin L, max (a+d*(L-1-i.val : ℕ)-z) 0) =
      ∑ i : Fin L, max (a+d*i.val-z) 0 := by
    simpa only [Fin.revPerm_apply,Fin.val_rev,Nat.sub_sub,Nat.add_comm] using
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin L)) (fun i => max (a+d*i.val-z) 0))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_add_distrib,hrev] at hs
  linarith

theorem negative_call_identity (x : ℝ) : max (-x) 0=max x 0-x := by
  simp only [max_def]
  split_ifs <;> linarith

theorem bin_call_compression (L : ℕ) (hL : 0 < L) (a d z : ℝ) :
    (L : ℝ)*(max (a+d*(binLower L hL).val-z) 0+
      max (a+d*(binUpper L hL).val-z) 0) ≤
      (2 : ℕ)*∑ i : Fin L, max (a+d*i.val-z) 0 := by
  norm_num only [Nat.cast_ofNat] at *
  by_cases hd : 0 ≤ d
  · exact bin_call_compression_nonneg L hL a d z hd
  · have hh := bin_call_compression_nonneg L hL (-a) (-d) (-z) (by linarith)
    have heq : ∀ i : Fin L, max (-a+-d*i.val- -z) 0 = max (a+d*i.val-z) 0-(a+d*i.val-z) := by
      intro i
      convert negative_call_identity (a+d*i.val-z) using 1
      congr 1
      ring
    simp only [heq] at hh
    have hsum : (∑ i : Fin L, (a+d*i.val-z)) =
        (L : ℝ)*((a+d*(binLower L hL).val-z)+(a+d*(binUpper L hL).val-z))/2 := by
      have hidx : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
        rw [Fin.sum_univ_eq_sum_range]
        exact first_index_moment L
      have hmid := bin_middle_sum L hL
      have hmidR : ((binLower L hL).val : ℝ)+(binUpper L hL).val=(L : ℝ)-1 := by
        have hcast : ((L-1 : ℕ) : ℝ)=(L : ℝ)-1 := by
          have hh : ((L-1 : ℕ) : ℝ)+1=(L : ℝ) := by exact_mod_cast (show (L-1)+1=L by omega)
          linarith
        rw [←hcast]
        exact_mod_cast hmid
      simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,hidx]
      nlinarith [congrArg (fun x : ℝ => (L : ℝ)*d*x) hmidR]
    rw [Finset.sum_sub_distrib,hsum] at hh
    nlinarith


theorem bin_middle_sum_real (L : ℕ) (hL : 0 < L) :
    ((binLower L hL).val : ℝ)+(binUpper L hL).val=(L : ℝ)-1 := by
  have hh : ((L-1 : ℕ) : ℝ)+1=(L : ℝ) := by exact_mod_cast (show (L-1)+1=L by omega)
  have hs : ((binLower L hL).val : ℝ)+(binUpper L hL).val=((L-1 : ℕ) : ℝ) :=
    by exact_mod_cast bin_middle_sum L hL
  linarith

theorem bin_affine_mean (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i : Fin L, (a+d*i.val)) =
      (L : ℝ)*((a+d*(binLower L hL).val)+(a+d*(binUpper L hL).val))/(2 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hidx : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact first_index_moment L
  have hm := bin_middle_sum_real L hL
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,←Finset.mul_sum,hidx]
  nlinarith [congrArg (fun x : ℝ => (L : ℝ)*d*x) hm]

theorem bin_quadratic_loss_identity (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (L : ℝ)/(2 : ℕ)*((a+d*(binLower L hL).val)^(2 : ℕ)+(a+d*(binUpper L hL).val)^(2 : ℕ)) =
      d^(2 : ℕ)*(L : ℝ)/(12 : ℕ)*((L : ℝ)^(2 : ℕ)-1-((3 : ℕ) : ℝ)*((binLower L hL).val-(binUpper L hL).val : ℝ)^(2 : ℕ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have hidx : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact first_index_moment L
  have hsq : (∑ i : Fin L, (i.val : ℝ)^2) =
      (L : ℝ)*(((L : ℝ)-1)/2)^2+(L : ℝ)*((L : ℝ)^2-1)/12 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)^2)]
    simpa only [zero_add,one_mul,zero_sub,neg_sq,one_pow,mul_one,sub_zero] using
      constant_run_error_identity L 0 1 0
  have hm := bin_middle_sum_real L hL
  have hv : ((binUpper L hL).val : ℝ)=(L : ℝ)-1-(binLower L hL).val := by linarith
  have he : (∑ i : Fin L, (a+d*i.val)^2) =
      (L : ℝ)*a^2+2*a*d*(∑ i : Fin L, (i.val : ℝ))+d^2*(∑ i : Fin L, (i.val : ℝ)^2) := by
    simp only [add_sq,mul_pow,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
    ring
  rw [he,hidx,hsq,hv]
  ring

theorem bin_middle_gap_bound (L : ℕ) (hL : 0 < L) :
    ((binLower L hL).val-(binUpper L hL).val : ℝ)^(2 : ℕ) ≤ 1 := by
  have hh : (binLower L hL).val ≤ (binUpper L hL).val ∧
      (binUpper L hL).val ≤ (binLower L hL).val+1 := by
    simp only [binLower,binUpper]
    omega
  have h1 : ((binLower L hL).val : ℝ) ≤ (binUpper L hL).val := by exact_mod_cast hh.1
  have h2 : ((binUpper L hL).val : ℝ) ≤ (binLower L hL).val+1 := by exact_mod_cast hh.2
  nlinarith

theorem bin_quadratic_loss_bounds (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    0 ≤ (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (L : ℝ)/(2 : ℕ)*((a+d*(binLower L hL).val)^(2 : ℕ)+(a+d*(binUpper L hL).val)^(2 : ℕ)) ∧
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (L : ℝ)/(2 : ℕ)*((a+d*(binLower L hL).val)^(2 : ℕ)+(a+d*(binUpper L hL).val)^(2 : ℕ)) ≤
      d^(2 : ℕ)*(L : ℝ)^(3 : ℕ)/(12 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hid := bin_quadratic_loss_identity L hL a d
  norm_num only [Nat.cast_ofNat] at hid
  rw [hid]
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hcoef : 0 ≤ d^2*(L : ℝ)/12 := by positivity
  have hgap := bin_middle_gap_bound L hL
  constructor
  · apply mul_nonneg hcoef
    by_cases he : L=1
    · subst L
      norm_num [binLower,binUpper]
    · have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
      nlinarith
  · have hsq : 0 ≤ ((binLower L hL).val-(binUpper L hL).val : ℝ)^2 := sq_nonneg _
    have hp := mul_nonneg hcoef (show 0 ≤ 1+3*((binLower L hL).val-(binUpper L hL).val : ℝ)^2 by positivity)
    nlinarith


/-- Coalescing labels retain a single middle action in an odd bin. -/
def binCompressedLabel (L : ℕ) (hL : 0 < L) (b : Fin 2) : Fin L :=
  if b.val=0 then binLower L hL else binUpper L hL

def binCompressedWeights (L : ℕ) (hL : 0 < L) : Fin L → ℝ :=
  pushWeights (binCompressedLabel L hL) (fun _ => (L : ℝ)/(2 : ℕ))

theorem bin_compressed_nonneg (L : ℕ) (hL : 0 < L) :
    ∀ i, 0 ≤ binCompressedWeights L hL i := by
  exact pushWeights_nonneg _ _ (fun _ => by positivity)

theorem bin_compressed_mass (L : ℕ) (hL : 0 < L) :
    (∑ i, binCompressedWeights L hL i)=(L : ℝ) := by
  rw [binCompressedWeights,pushWeights_mass,Fin.sum_univ_two]
  norm_num

theorem bin_compressed_support (L : ℕ) (hL : 0 < L) :
    (Finset.univ.filter fun i => binCompressedWeights L hL i ≠ 0).card ≤ min L (2 : ℕ) := by
  classical
  apply le_min
  · exact le_trans (Finset.card_filter_le _ _) (by simp)
  · exact le_trans (pushWeights_support_card _ _) (by simp)

theorem bin_compressed_moment (L : ℕ) (hL : 0 < L) (f : Fin L → ℝ) :
    (∑ i, binCompressedWeights L hL i*f i)=
      (L : ℝ)/(2 : ℕ)*(f (binLower L hL)+f (binUpper L hL)) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [binCompressedWeights,pushWeights_moment,Fin.sum_univ_two]
  simp only [binCompressedLabel,Fin.val_zero,Fin.val_one,ite_true,one_ne_zero,ite_false,Nat.cast_ofNat]
  ring

theorem bin_compressed_affine_moment (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i, binCompressedWeights L hL i*(a+d*i.val))=∑ i : Fin L, (a+d*i.val) := by
  rw [bin_compressed_moment,bin_affine_mean L hL a d]
  ring

theorem bin_compressed_calls (L : ℕ) (hL : 0 < L) (a d z : ℝ) :
    (∑ i, binCompressedWeights L hL i*max (a+d*i.val-z) 0) ≤
      ∑ i : Fin L, max (a+d*i.val-z) 0 := by
  rw [bin_compressed_moment]
  have hh := bin_call_compression L hL a d z
  norm_num only [Nat.cast_ofNat] at *
  linarith

theorem bin_compressed_quadratic_loss (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    0 ≤ (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (∑ i, binCompressedWeights L hL i*(a+d*i.val)^(2 : ℕ)) ∧
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (∑ i, binCompressedWeights L hL i*(a+d*i.val)^(2 : ℕ)) ≤ d^(2 : ℕ)*(L : ℝ)^(3 : ℕ)/(12 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [bin_compressed_moment]
  exact bin_quadratic_loss_bounds L hL a d

end
end SparseCompletion

/- Fixed source body: BinnedWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def binIndex {h : ℕ} (L : Fin h → ℕ) (b : Fin h) (i : Fin (L b)) : Fin (∑ b, L b) :=
  finSigmaFinEquiv ⟨b,i⟩

def binStart {h : ℕ} (L : Fin h → ℕ) (b : Fin h) : ℕ :=
  ∑ i : Fin b.val, L (Fin.castLE b.isLt.le i)

theorem binIndex_val {h : ℕ} (L : Fin h → ℕ) (b : Fin h) (i : Fin (L b)) :
    (binIndex L b i).val=binStart L b+i.val := finSigmaFinEquiv_apply ⟨b,i⟩

theorem sum_bin_partition {h : ℕ} (L : Fin h → ℕ) (f : Fin (∑ b, L b) → ℝ) :
    (∑ j, f j)=∑ b, ∑ i : Fin (L b), f (binIndex L b i) := by
  simpa only [Fintype.sum_sigma,binIndex] using (Equiv.sum_comp finSigmaFinEquiv f).symm

def binnedLabel {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (b : Fin h × Fin 2) :
    Fin (∑ b, L b) := binIndex L b.1 (binCompressedLabel (L b.1) (hL b.1) b.2)

def binnedWeights {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ) :
    Fin (∑ b, L b) → ℝ :=
  pushWeights (binnedLabel L hL) (fun b => (r/((∑ b, L b : ℕ) : ℝ))*(L b.1 : ℝ)/(2 : ℕ))

theorem binned_nonneg {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ) (hr : 0 ≤ r) :
    ∀ j, 0 ≤ binnedWeights L hL r j := by
  exact pushWeights_nonneg _ _ (fun _ => by positivity)

theorem binned_support {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ) :
    supportSize (binnedWeights L hL r) ≤ min (∑ b, L b) ((2 : ℕ)*h) := by
  classical
  have hdim := supportSize_le_dimension (binnedWeights L hL r)
  have hc : supportSize (binnedWeights L hL r) ≤ 2*h := by
    unfold supportSize residualSupport binnedWeights
    exact le_trans (pushWeights_support_card _ _) (by simp [mul_comm])
  omega

theorem binned_moment {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ)
    (f : Fin (∑ b, L b) → ℝ) :
    (∑ j, binnedWeights L hL r j*f j)=
      (r/((∑ b, L b : ℕ) : ℝ))*∑ b, ∑ i : Fin (L b),
        binCompressedWeights (L b) (hL b) i*f (binIndex L b i) := by
  rw [binnedWeights,pushWeights_moment,Finset.mul_sum]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro b _
  rw [bin_compressed_moment]
  simp only [binnedLabel,binCompressedLabel,Fin.val_zero,Fin.val_one,ite_true,one_ne_zero,ite_false,Nat.cast_ofNat]
  ring

theorem binned_mass {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ)
    (hm : 0 < ∑ b, L b) : (∑ j, binnedWeights L hL r j)=r := by
  have hh := binned_moment L hL r (fun _ => 1)
  simp only [mul_one,bin_compressed_mass,←Nat.cast_sum] at hh
  have hne : ((∑ b, L b : ℕ) : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  rw [hh]
  field_simp

theorem binned_affine_moment {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r a d : ℝ) :
    (∑ j, binnedWeights L hL r j*(a+d*j.val))=
      (r/((∑ b, L b : ℕ) : ℝ))*∑ j : Fin (∑ b, L b), (a+d*j.val) := by
  rw [binned_moment,sum_bin_partition L]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val = (a+d*binStart L b)+d*i.val := by
    intro i
    rw [binIndex_val]
    push_cast
    ring
  simp only [hform]
  exact bin_compressed_affine_moment (L b) (hL b) _ _

theorem binned_call_contraction {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r : ℝ) (hr : 0 ≤ r) (a d z : ℝ) :
    call (binnedWeights L hL r) (fun j => a+d*j.val) z ≤
      call (uniformTarget (∑ b, L b) r) (fun j => a+d*j.val) z := by
  unfold call
  rw [binned_moment]
  have hright : (∑ j : Fin (∑ b, L b), uniformTarget (∑ b, L b) r j*max (a+d*j.val-z) 0) =
      (r/((∑ b, L b : ℕ) : ℝ))*∑ j : Fin (∑ b, L b), max (a+d*j.val-z) 0 := by
    simp only [uniformTarget,Finset.mul_sum]
  rw [hright,sum_bin_partition L]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro b _
  have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val-z = (a+d*binStart L b)+d*i.val-z := by
    intro i
    rw [binIndex_val]
    push_cast
    ring
  simp only [hform]
  exact bin_compressed_calls (L b) (hL b) _ _ _

end
end SparseCompletion

/- Fixed source body: BalancedBins.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def balancedLength (m h : ℕ) (b : Fin h) : ℕ :=
  m/h+if b.val<m%h then 1 else 0

theorem balancedLength_positive (m h : ℕ) (hh : 0 < h) (hhm : h ≤ m) :
    ∀ b, 0 < balancedLength m h b := by
  have hq : 0 < m/h := Nat.div_pos hhm hh
  intro b
  unfold balancedLength
  split_ifs <;> omega

theorem balancedLength_mass (m h : ℕ) (hh : 0 < h) : ∑ b, balancedLength m h b=m := by
  classical
  have hr : m%h<h := Nat.mod_lt m hh
  have hf : (Finset.univ.filter fun b : Fin h => b.val<m%h) = Finset.Iio ⟨m%h,hr⟩ := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio,Fin.lt_def]
  have hrem : (∑ b : Fin h, if b.val<m%h then (1 : ℕ) else 0)=m%h := by
    rw [←Finset.sum_filter,hf]
    simp only [Finset.sum_const,smul_eq_mul,mul_one,Fin.card_Iio]
  simp only [balancedLength,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,hrem]
  have hdiv := Nat.mod_add_div m h
  omega

theorem balancedLength_bound (m h : ℕ) (hh : 0 < h) (b : Fin h) :
    (balancedLength m h b : ℝ) ≤ (m : ℝ)/(h : ℝ)+1 := by
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hq : ((m/h : ℕ) : ℝ) ≤ (m : ℝ)/(h : ℝ) := by
    apply (le_div_iff₀ hhR).mpr
    exact_mod_cast Nat.div_mul_le_self m h
  have hb : balancedLength m h b ≤ m/h+1 := by
    unfold balancedLength
    split_ifs <;> omega
  have hbR : (balancedLength m h b : ℝ) ≤ ((m/h : ℕ) : ℝ)+1 := by exact_mod_cast hb
  linarith

theorem balancedLength_cube_sum (m h : ℕ) (hh : 0 < h) :
    (∑ b : Fin h, (balancedLength m h b : ℝ)^(3 : ℕ)) ≤
      (m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ) := by
  have hc : ∀ b : Fin h, (balancedLength m h b : ℝ)^3 ≤
      ((m : ℝ)/(h : ℝ)+1)^2*(balancedLength m h b : ℝ) := by
    intro b
    have hb := balancedLength_bound m h hh b
    have hn : (0 : ℝ) ≤ balancedLength m h b := Nat.cast_nonneg _
    have hh0 : (0 : ℝ) ≤ (m : ℝ)/(h : ℝ)+1 := by positivity
    have hs : (balancedLength m h b : ℝ)^2 ≤ ((m : ℝ)/(h : ℝ)+1)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hs hn
    nlinarith
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin h))) (fun b _ => hc b)
  rw [←Finset.mul_sum,←Nat.cast_sum,balancedLength_mass m h hh] at hs
  nlinarith

end
end SparseCompletion

/- Fixed source body: BinnedCompletion.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem uniform_score_affine (m : ℕ) (r : ℝ) :
    targetScore (uniformTarget m r) r =
      (fun j => r*(1-1/(m : ℝ))+(-((2 : ℕ) : ℝ)*r/(m : ℝ))*j.val) := by
  norm_num only [Nat.cast_ofNat] at *
  funext j
  rw [uniform_target_score]
  ring

theorem uniform_target_cuts (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    Cuts 1 r (uniformTarget m r) (targetScore (uniformTarget m r) r) := by
  have hq : ∀ j, 0 ≤ uniformTarget m r j := fun _ => div_nonneg hr (Nat.cast_nonneg _)
  have hmass := uniformTarget_mass m hm r
  have hh := completion_cuts_necessary (uniformTarget m r) (targetScore (uniformTarget m r) r)
    (orderedBlock 1) 1 r 0 hq hmass (orderedBlock_skew 1)
    (fun i j => (orderedBlock_bounds 1 (by norm_num) i j).1)
    (fun j => by rw [orderedBlock_response _ r hmass]; linarith)
  simpa only [sub_zero] using hh

theorem binned_uniform_cuts {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 ≤ r) :
    Cuts 1 r (binnedWeights L hL r) (targetScore (uniformTarget (∑ b, L b) r) r) := by
  apply call_bound_implies_cuts _ _ 1 r (by norm_num) (binned_nonneg L hL r hr)
    (binned_mass L hL r hm)
  intro z _
  have hc := binned_call_contraction L hL r hr (r*(1-1/((∑ b, L b : ℕ) : ℝ)))
    (-2*r/((∑ b, L b : ℕ) : ℝ)) z
  have hform := uniform_score_affine (∑ b, L b) r
  norm_num only [Nat.cast_ofNat] at hform
  rw [← hform] at hc
  exact le_trans hc (cuts_imply_call_bound _ _ 1 r (by norm_num)
    (uniform_target_cuts _ hm r hr) z)

theorem binned_uniform_score_mean {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) :
    scoreMoment (binnedWeights L hL r) (targetScore (uniformTarget (∑ b, L b) r) r)=0 := by
  have hh := binned_affine_moment L hL r (r*(1-1/((∑ b, L b : ℕ) : ℝ)))
    (-2*r/((∑ b, L b : ℕ) : ℝ))
  have hform := uniform_score_affine (∑ b, L b) r
  norm_num only [Nat.cast_ofNat] at hform
  rw [← hform] at hh
  change (∑ j, binnedWeights L hL r j*targetScore (uniformTarget (∑ b, L b) r) r j)=0
  rw [hform,hh]
  have ht := target_score_moment_zero (uniformTarget (∑ b, L b) r) r
    (uniformTarget_mass _ hm r)
  simpa only [scoreMoment,uniformTarget,←Finset.mul_sum] using ht

theorem binned_uniform_residual_completion {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 ≤ r) :
    ∃ B : Fin (∑ b, L b) → Fin (∑ b, L b) → ℝ,
      IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      ∀ i, targetScore (uniformTarget (∑ b, L b) r) r i+
        response B (binnedWeights L hL r) i ≤ 0 := by
  apply completion_of_cuts_and_guards _ _ 1 r 0 (by norm_num)
    (binned_nonneg L hL r hr) (binned_mass L hL r hm)
  · simpa only [sub_zero] using binned_uniform_cuts L hL hm r hr
  · intro j
    simpa only [zero_add,one_mul] using
      (targetScore_bounds (uniformTarget (∑ b, L b) r)
        (fun _ => div_nonneg hr (Nat.cast_nonneg _)) r (uniformTarget_mass _ hm r) j).2

end
end SparseCompletion

/- Fixed source body: BinnedMoments.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem binned_quadratic_loss {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r : ℝ) (hr : 0 ≤ r) (a d : ℝ) :
    let qstar := uniformTarget (∑ b, L b) r
    let q := binnedWeights L hL r
    let f := fun j : Fin (∑ b, L b) => (a+d*j.val)^(2 : ℕ)
    0 ≤ scoreMoment qstar f-scoreMoment q f ∧
    scoreMoment qstar f-scoreMoment q f ≤
      (r/((∑ b, L b : ℕ) : ℝ))*d^(2 : ℕ)/(12 : ℕ)*∑ b, (L b : ℝ)^(3 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  let Δ := fun b : Fin h =>
    (∑ i : Fin (L b), (a+d*(binIndex L b i).val)^2)-
      ∑ i : Fin (L b), binCompressedWeights (L b) (hL b) i*(a+d*(binIndex L b i).val)^2
  have hb : ∀ b, 0 ≤ Δ b ∧ Δ b ≤ d^2*(L b : ℝ)^3/12 := by
    intro b
    have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val=(a+d*binStart L b)+d*i.val := by
      intro i
      rw [binIndex_val]
      push_cast
      ring
    dsimp only [Δ]
    simp only [hform]
    have hh := bin_compressed_quadratic_loss (L b) (hL b) (a+d*binStart L b) d
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have he : scoreMoment (uniformTarget (∑ b, L b) r) (fun j => (a+d*j.val)^2)-
      scoreMoment (binnedWeights L hL r) (fun j => (a+d*j.val)^2) =
      (r/((∑ b, L b : ℕ) : ℝ))*∑ b, Δ b := by
    unfold scoreMoment
    rw [binned_moment]
    simp only [uniformTarget,←Finset.mul_sum]
    rw [sum_bin_partition L,←mul_sub,←Finset.sum_sub_distrib]
  rw [he]
  have hc : 0 ≤ r/((∑ b, L b : ℕ) : ℝ) := by positivity
  constructor
  · exact mul_nonneg hc (Finset.sum_nonneg fun b _ => (hb b).1)
  · have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin h))) (fun b _ => (hb b).2)
    have heq : (∑ b : Fin h, d^2*(L b : ℝ)^3/12)=d^2/12*∑ b, (L b : ℝ)^3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [heq] at hs
    have hh := mul_le_mul_of_nonneg_left hs hc
    nlinarith

theorem binned_exposing_loss {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 ≤ r) :
    let qstar := uniformTarget (∑ b, L b) r
    let q := binnedWeights L hL r
    let w := exposingWeight qstar r
    0 ≤ scoreMoment qstar w-scoreMoment q w ∧
    scoreMoment qstar w-scoreMoment q w ≤
      r^(2 : ℕ)/((12 : ℕ)*((∑ b, L b : ℕ) : ℝ)^(3 : ℕ))*∑ b, (L b : ℝ)^(3 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let f := fun j : Fin m => (((m : ℝ)-1)/(m : ℝ)+(-1/(m : ℝ))*j.val)^2
  have hw : exposingWeight (uniformTarget m r) r=(fun j => r*f j) := by
    funext j
    rw [uniform_exposing_weight]
    dsimp only [f]
    congr 1
    congr 1
    ring
  have he : scoreMoment (uniformTarget m r) (exposingWeight (uniformTarget m r) r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight (uniformTarget m r) r)=
      r*(scoreMoment (uniformTarget m r) f-scoreMoment (binnedWeights L hL r) f) := by
    rw [hw]
    simp only [scoreMoment,mul_left_comm _ r,←Finset.mul_sum]
    ring
  change 0 ≤ scoreMoment (uniformTarget m r) (exposingWeight (uniformTarget m r) r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight (uniformTarget m r) r) ∧ _
  rw [he]
  have hq := binned_quadratic_loss L hL r hr (((m : ℝ)-1)/(m : ℝ)) (-1/(m : ℝ))
  norm_num only [Nat.cast_ofNat] at hq
  change 0 ≤ scoreMoment (uniformTarget m r) f-scoreMoment (binnedWeights L hL r) f ∧ _ at hq
  constructor
  · exact mul_nonneg hr hq.1
  · have hh := mul_le_mul_of_nonneg_left hq.2 hr
    convert hh using 1
    dsimp only [m]
    field_simp

end
end SparseCompletion

/- Fixed source body: BinnedGame.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem binned_game_witness {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) :
    let m := ∑ b, L b
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧
      d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ))*∑ b, (L b : ℝ)^(3 : ℕ) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  let qstar := uniformTarget m (1/4)
  let q := binnedWeights L hL (1/4)
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let d := βstar-scoreMoment q w
  have hq : ∀ j, 0 ≤ q j := binned_nonneg L hL (1/4) (by norm_num)
  have hmass : ∑ j, q j=1/4 := binned_mass L hL (1/4) hm
  have hmean : scoreMoment q t=0 := binned_uniform_score_mean L hL hm (1/4)
  have hloss := binned_exposing_loss L hL hm (1/4) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hloss
  change 0 ≤ d ∧ d ≤ (1/16 : ℝ)/(12*(m : ℝ)^3)*∑ b, (L b : ℝ)^3 at hloss
  have hw : ∀ j, 0 ≤ w j := fun j =>
    (exposingWeight_bounds hm qstar (fun _ => div_nonneg (by norm_num) (Nat.cast_nonneg _)) (1/4)
      (uniformTarget_mass _ hm (1/4)) j).1
  have hβ : 0 ≤ scoreMoment q w := Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (hw j)
  obtain ⟨B,hB,hb,hrows⟩ := binned_uniform_residual_completion L hL hm (1/4) (by norm_num)
  refine ⟨q,B,d,hq,hmass,hB,hb,binned_support L hL (1/4),hloss.1,?_,hloss.2,?_,?_,?_⟩
  · dsimp only [d]
    linarith
  · rw [block_response_anchor]
    have ha := (two_anchor_responses t w q (3/4) βstar (by norm_num)).1
    change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 0=d
    rw [ha,hmean]
    dsimp only [d]
    ring
  · rw [block_response_anchor]
    have ha := (two_anchor_responses t w q (3/4) βstar (by norm_num)).2
    change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 1= -d
    rw [ha,hmean]
    dsimp only [d]
    ring
  · intro j
    rw [block_response_residual]
    have hs : score (rigidityCross qstar) (twoShares (3/4))=t :=
      two_score t w (3/4) (by norm_num)
    rw [hs]
    exact hrows j

end
end SparseCompletion

/- Fixed source body: BalancedGame.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bin_error_scale (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m) (r : ℝ) :
    (r^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ)))*(m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ) ≤ r^(2 : ℕ)/((3 : ℕ)*(h : ℝ)^(2 : ℕ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hdim : (h : ℝ) ≤ m := by exact_mod_cast hhm
  have hsq : ((m : ℝ)+(h : ℝ))^2 ≤ 4*(m : ℝ)^2 := by nlinarith
  have heq : (r^2/(12*(m : ℝ)^3))*(m : ℝ)*((m : ℝ)/(h : ℝ)+1)^2 =
      (r^2/(12*(m : ℝ)^2*(h : ℝ)^2))*((m : ℝ)+(h : ℝ))^2 := by
    field_simp
  rw [heq]
  calc
    _ ≤ (r^2/(12*(m : ℝ)^2*(h : ℝ)^2))*(4*(m : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by field_simp; ring

theorem partition_game_witness (m h : ℕ) (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hsum : ∑ b, L b=m) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m)
    (hcube : (∑ b : Fin h, (L b : ℝ)^(3 : ℕ)) ≤ (m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ)) :
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧
      d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/((3 : ℕ)*(h : ℝ)^(2 : ℕ)) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  subst m
  obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,hloss,h0,h1,hrows⟩ := binned_game_witness L hL hm
  refine ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,?_,h0,h1,hrows⟩
  norm_num only [Nat.cast_ofNat] at hloss
  have hc : 0 ≤ (1/16 : ℝ)/(12*((∑ b, L b : ℕ) : ℝ)^3) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hcube hc
  exact le_trans hloss (le_trans hbound (by
    have hh := bin_error_scale _ h hm hh hhm (1/4)
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [mul_assoc] using hh))

theorem balanced_game_witness (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m) :
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧
      d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/((3 : ℕ)*(h : ℝ)^(2 : ℕ)) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  have hc := partition_game_witness m h (balancedLength m h) (balancedLength_positive m h hh hhm)
    (balancedLength_mass m h hh) hm hh hhm (balancedLength_cube_sum m h hh)
  norm_num only [Nat.cast_ofNat] at hc
  exact hc

end
end SparseCompletion

/- Fixed source body: CoreAdjustment.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem two_core_anchor_shift {ι : Type*} [Fintype ι] (D : ι → Fin (2 : ℕ) → ℝ)
    (B : ι → ι → ℝ) (q : ι → ℝ) (u τ : ℝ) :
    response (blockMatrix (twoCore (u-(((8 : ℕ) : ℝ)/(3 : ℕ))*τ)) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=
      response (blockMatrix (twoCore u) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)-τ ∧
    response (blockMatrix (twoCore (u-(((8 : ℕ) : ℝ)/(3 : ℕ))*τ)) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)=
      response (blockMatrix (twoCore u) D B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)+τ := by
  norm_num only [Nat.cast_ofNat] at *
  constructor <;> rw [block_response_anchor,block_response_anchor] <;>
    simp only [anchorResponse,Fin.sum_univ_two,twoCore,twoShares] <;> norm_num <;> ring

theorem core_observation_adjustment (u d δ : ℝ) (hu1 : u ≤ 1)
    (hd : 0 ≤ d) (hdu : (((8 : ℕ) : ℝ)/(3 : ℕ))*d ≤ u) (hδ : 0 ≤ δ) :
    let u' := u-(((8 : ℕ) : ℝ)/(3 : ℕ))*min d ((((3 : ℕ) : ℝ)/(8 : ℕ))*δ)
    ∀ i j, ClippedObservation (twoCore u i j) δ (twoCore u' i j) := by
  norm_num only [Nat.cast_ofNat] at *
  have hτ0 : 0 ≤ min d ((3/8)*δ) := le_min hd (by positivity)
  have hτd := min_le_left d ((3/8)*δ)
  have hτδ := min_le_right d ((3/8)*δ)
  have hnew0 : 0 ≤ u-(8/3)*min d ((3/8)*δ) := by nlinarith
  have hnew1 : u-(8/3)*min d ((3/8)*δ) ≤ 1 := by nlinarith
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoCore,ClippedObservation,abs_le] <;>
    (repeat' constructor) <;> linarith [abs_of_nonneg hτ0]

/-- A nonnegative anchor error can be absorbed by moving only the bounded
    anchor-core observation inside its clipped interval. -/
theorem uniform_core_adjust {m : ℕ} (hm : 0 < m) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ) (d ε δ : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hmass : ∑ j, q j=1/(4 : ℕ)) (hB : IsSkew B)
    (hb : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) (hd : 0 ≤ d)
    (hβ : d ≤ scoreMoment (uniformTarget m (1/(4 : ℕ))) (exposingWeight (uniformTarget m (1/(4 : ℕ))) (1/(4 : ℕ))))
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (heff : d ≤ ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)
    (h0 : response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d)
    (h1 : response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d)
    (hrows : ∀ j, response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B) (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0) :
    ∃ u, UniformCoreWitness m ε δ q u B := by
  norm_num only [Nat.cast_ofNat] at *
  let qstar := uniformTarget m (1/4)
  let u := uniformCoreValue m
  let τ := min d ((3/8)*δ)
  have hobs := two_anchor_observed_bounds hm qstar
    (fun _ => div_nonneg (by norm_num) (Nat.cast_nonneg _)) (uniformTarget_mass m hm (1/4))
  have hu1 : u ≤ 1 := by simpa [u,uniformCoreValue,twoCore,qstar] using (hobs.1 0 1).2
  have hdu : (8/3)*d ≤ u := by
    dsimp [u,uniformCoreValue]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hclip := core_observation_adjustment u d δ hu1 hd hdu hδ
  norm_num only [Nat.cast_ofNat] at hclip
  refine ⟨u-(8/3)*τ,?_⟩
  unfold UniformCoreWitness UniformIntervalWitness
  norm_num only [Nat.cast_ofNat]
  refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,twoCore_skew _,hB,hclip,?_,hb,?_⟩
  · rw [hmass,Fin.sum_univ_two]
    norm_num [twoShares]
  · intro j h
    exact ⟨(hobs.2 j h).1,(hobs.2 j h).2,by simpa using hδ⟩
  · intro v
    cases v with
    | inl h =>
      have hshift := two_core_anchor_shift (rigidityCross qstar) B q u τ
      norm_num only [Nat.cast_ofNat] at hshift
      change response (blockMatrix (twoCore u) (rigidityCross qstar) B)
        (blockWeights (twoShares (3/4)) q) (.inl 0)=d at h0
      change response (blockMatrix (twoCore u) (rigidityCross qstar) B)
        (blockWeights (twoShares (3/4)) q) (.inl 1)= -d at h1
      rw [h0,h1] at hshift
      have hτd : τ ≤ d := min_le_left _ _
      have hτ : d-τ ≤ ε := by
        dsimp only [τ]
        rcases le_total d ((3/8)*δ) with hh | hh
        · rw [min_eq_left hh]
          linarith
        · rw [min_eq_right hh]
          linarith
      fin_cases h
      · exact le_of_eq_of_le hshift.1 hτ
      · exact le_of_eq_of_le hshift.2 (by linarith)
    | inr j =>
      rw [block_response_residual]
      have hh := hrows j
      rw [block_response_residual] at hh
      linarith

end
end SparseCompletion

/- Fixed source body: NoiseUpper.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem double_grid_support_upper (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    (((2 : ℕ)+(2 : ℕ)*gridSize 1 (1/(4 : ℕ)) e : ℕ) : ℝ) ≤ (5 : ℕ)/Real.sqrt e := by
  norm_num only [Nat.cast_ofNat] at *
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hs1 : Real.sqrt e ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt he1
  have hroot : Real.sqrt (1*(1/4)/e) = 1/(2*Real.sqrt e) := by
    rw [one_mul,Real.sqrt_div (by norm_num)]
    norm_num
    ring
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (1*(1/4)/e))
  change (gridSize 1 (1/4) e : ℝ) < Real.sqrt (1*(1/4)/e)+1 at hc
  rw [hroot] at hc
  have hm := mul_lt_mul_of_pos_right hc hs
  have hid : (1/(2*Real.sqrt e))*Real.sqrt e=1/2 := by field_simp
  rw [add_mul,hid] at hm
  apply (le_div_iff₀ hs).mpr
  push_cast
  nlinarith

/-- A sparse central witness with its entire error in the two anchor
    responses, ready for the single-core uncertainty adjustment. -/
theorem uniform_binned_upper (m : ℕ) (hm : 0 < m) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      (supportSize q : ℝ)+(2 : ℕ) ≤ (5 : ℕ)*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt e) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧ d ≤ e ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  let H := gridSize 1 (1/4) e
  have hgrid := gridSize_bound 1 (1/4) e (by norm_num) (by norm_num) he
  have hH : 0 < H := by
    by_contra hh
    have hz : H=0 := by omega
    change 1*(1/4 : ℝ) ≤ e*(H : ℝ)^2 at hgrid
    rw [hz] at hgrid
    norm_num at hgrid
  have hr : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hr1 : Real.sqrt e ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt he1
  by_cases hdim : m ≤ H
  · let qstar := uniformTarget m (1/4)
    have hq : ∀ j, 0 ≤ qstar j := fun _ => div_nonneg (by norm_num) (Nat.cast_nonneg _)
    have hmass : ∑ j, qstar j=1/4 := uniformTarget_mass m hm (1/4)
    have hresp := two_anchor_target_feasible qstar (3/4) (1/4) (by norm_num) hmass
    have hcard : (supportSize qstar : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt e) := by
      have hqcard : (supportSize qstar : ℝ) ≤ m := by exact_mod_cast supportSize_le_dimension qstar
      have hsmall : (supportSize qstar : ℝ)+2 ≤ 5/Real.sqrt e := by
        have hc : (supportSize qstar : ℝ)+2 ≤ ((2+2*H : ℕ) : ℝ) := by
          have hh := supportSize_le_dimension qstar
          exact_mod_cast (show supportSize qstar+2 ≤ 2+2*H by omega)
        exact le_trans hc (double_grid_support_upper e he he1)
      rcases le_total ((m : ℝ)+2) (1/Real.sqrt e) with hh | hh
      · rw [min_eq_left hh]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        linarith
      · rw [min_eq_right hh]
        calc
          _ ≤ 5/Real.sqrt e := hsmall
          _ = _ := by ring
    refine ⟨qstar,orderedBlock 1,0,hq,hmass,orderedBlock_skew 1,
      orderedBlock_bounds 1 (by norm_num),hcard,le_refl 0,?_,le_of_lt he,?_,?_,?_⟩
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hq j)
        (exposingWeight_bounds hm qstar hq (1/4) hmass j).1
    · exact hresp _
    · simpa only [neg_zero,rigidityCore,rigidityCross,qstar,Nat.cast_ofNat] using hresp (.inl 1)
    · intro j
      exact le_of_eq (hresp (.inr j))
  · have hHm : H ≤ m := by omega
    obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,herr,h0,h1,hrows⟩ := balanced_game_witness m H hm hH hHm
    norm_num only [Nat.cast_ofNat] at herr
    have hdH : d ≤ e := by
      have hHR : (0 : ℝ) < H := Nat.cast_pos.mpr hH
      have heq : (1/16 : ℝ)/(3*(H : ℝ)^2)=1/(48*(H : ℝ)^2) := by ring
      rw [heq] at herr
      have hg : (1/4 : ℝ) ≤ e*(H : ℝ)^2 := by simpa only [one_mul] using hgrid
      have hbound : 1/(48*(H : ℝ)^2) ≤ e := by
        apply (div_le_iff₀ (show 0 < 48*(H : ℝ)^2 by positivity)).mpr
        nlinarith
      exact le_trans herr hbound
    have hdimq : (supportSize q : ℝ) ≤ m := by exact_mod_cast le_trans hcard (min_le_left _ _)
    have hcount : (supportSize q : ℝ)+2 ≤ 5/Real.sqrt e := by
      have hh : (supportSize q : ℝ)+2 ≤ ((2+2*H : ℕ) : ℝ) := by
        have hc := le_trans hcard (min_le_right _ _)
        exact_mod_cast (show supportSize q+2 ≤ 2+2*H by omega)
      exact le_trans hh (double_grid_support_upper e he he1)
    have htotal : (supportSize q : ℝ)+2 ≤ 5*min ((m : ℝ)+2) (1/Real.sqrt e) := by
      rcases le_total ((m : ℝ)+2) (1/Real.sqrt e) with hh | hh
      · rw [min_eq_left hh]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        linarith
      · rw [min_eq_right hh]
        calc
          _ ≤ 5/Real.sqrt e := hcount
          _ = _ := by ring
    exact ⟨q,B,d,hq,hmass,hB,hb,htotal,hd,hβ,hdH,h0,h1,hrows⟩

theorem uniform_core_uncertainty_upper (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (he : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) (he1 : ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ ≤ 1) :
    ∃ (q : Fin m → ℝ) (u : ℝ) (B : Fin m → Fin m → ℝ),
      UniformCoreWitness m ε δ q u B ∧
      (supportSize q : ℝ)+(2 : ℕ) ≤ (5 : ℕ)*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,hde,h0,h1,hrows⟩ :=
    uniform_binned_upper m hm (ε+(3/8)*δ) he he1
  obtain ⟨u,hu⟩ := uniform_core_adjust hm q B d ε δ hq hmass hB hb hd hβ hε hδ hde h0 h1 hrows
  exact ⟨q,u,B,hu,hcard⟩

end
end SparseCompletion

/- Fixed source body: NoiseSharp.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem core_witness_interval {m : ℕ} {ε δ : ℝ} {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (fixed : Bool) (hw : UniformCoreWitness m ε δ q u B) :
    UniformIntervalWitness m ε δ fixed (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q (twoCore u)
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B := by
  norm_num only [Nat.cast_ofNat] at *
  rcases hw with ⟨hq,ha,_,hmass,hK,hB,hobsK,hobsD,hb,hresp⟩
  exact ⟨hq,ha,fun _ => rfl,hmass,hK,hB,hobsK,hobsD,hb,hresp⟩

theorem uniformMinimumCoreTotalSupport_sharp (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (he : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) (he1 : ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ ≤ 1) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) ≤
      (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) ∧
    (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) ≤
      (5 : ℕ)*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) := by
  norm_num only [Nat.cast_ofNat] at *
  refine ⟨uniformMinimumCoreTotalSupport_lower m hm ε δ hε hδ he,?_⟩
  obtain ⟨q,u,B,hw,hcount⟩ := uniform_core_uncertainty_upper m hm ε δ hε hδ he he1
  have hmin := uniformMinimumCoreTotalSupport_le m hm ε δ hε hδ q u B hw
  have hminR : (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) ≤ (supportSize q : ℝ)+2 :=
    by exact_mod_cast hmin
  exact le_trans hminR hcount

theorem uncertainty_rate_comparison (N e s : ℝ) (hN : 0 ≤ N) (he : 0 < e) (hs : 0 < s)
    (hcmp : (((3 : ℕ) : ℝ)/(8 : ℕ))*s ≤ e) :
    (5 : ℕ)*min N (1/Real.sqrt e) ≤ ((5 : ℕ)*Real.sqrt (((8 : ℕ) : ℝ)/(3 : ℕ)))*min N (1/Real.sqrt s) := by
  norm_num only [Nat.cast_ofNat] at *
  have hre : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hrs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hC : 1 ≤ Real.sqrt (8/3) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 8/3 by norm_num)
  have hC0 : 0 ≤ Real.sqrt (8/3) := Real.sqrt_nonneg _
  have hCsq : (Real.sqrt (8/3))^2=(8/3 : ℝ) := Real.sq_sqrt (by norm_num)
  have heq : (Real.sqrt (8/3)*Real.sqrt e)^2=(8/3 : ℝ)*e := by
    rw [mul_pow,hCsq,Real.sq_sqrt (le_of_lt he)]
  have hroots : Real.sqrt s ≤ Real.sqrt (8/3)*Real.sqrt e := by
    have hnn := mul_nonneg hC0 (le_of_lt hre)
    nlinarith [Real.sq_sqrt (le_of_lt hs)]
  have hfrac : 1/Real.sqrt e ≤ Real.sqrt (8/3)/Real.sqrt s :=
    (div_le_div_iff₀ hre hrs).mpr (by simpa only [one_mul] using hroots)
  rcases le_total N (1/Real.sqrt s) with hh | hh
  · rw [min_eq_left hh]
    calc
      _ ≤ 5*N := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ ≤ (5*Real.sqrt (8/3))*N := mul_le_mul_of_nonneg_right (by nlinarith) hN
  · rw [min_eq_right hh]
    calc
      _ ≤ 5*(1/Real.sqrt e) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ ≤ 5*(Real.sqrt (8/3)/Real.sqrt s) := mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = _ := by ring

/-- The paper's family-specific sharp support law under clipped interval
    uncertainty, for both fixed and minimum anchor shares. -/
theorem uniformMinimumIntervalTotalSupport_sharp (m : ℕ) (hm : (2 : ℕ) ≤ m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (he : 0 < ε+δ) (he1 : ε+δ ≤ 1) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+δ)) ≤
      (uniformMinimumIntervalTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε δ hε hδ fixed : ℝ) ∧
    (uniformMinimumIntervalTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε δ hε hδ fixed : ℝ) ≤
      ((5 : ℕ)*Real.sqrt (((8 : ℕ) : ℝ)/(3 : ℕ)))*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+δ)) := by
  norm_num only [Nat.cast_ofNat] at *
  refine ⟨uniformMinimumIntervalTotalSupport_lower m (by omega) ε δ hε hδ he fixed,?_⟩
  have heff : 0 < ε+(3/8)*δ := by nlinarith
  have heff1 : ε+(3/8)*δ ≤ 1 := by nlinarith
  obtain ⟨q,u,B,hw,hcount⟩ := uniform_core_uncertainty_upper m (by omega) ε δ hε hδ heff heff1
  have hi := core_witness_interval fixed hw
  have hmin := uniformMinimumIntervalTotalSupport_le m (by omega) ε δ hε hδ fixed
    (twoShares (3/4)) q (twoCore u) (rigidityCross (uniformTarget m (1/4))) B hi
  have hminR : (uniformMinimumIntervalTotalSupport m (by omega) ε δ hε hδ fixed : ℝ) ≤
      (supportSize q : ℝ)+2 := by exact_mod_cast hmin
  apply le_trans hminR
  exact le_trans hcount (uncertainty_rate_comparison ((m : ℝ)+2) (ε+(3/8)*δ) (ε+δ)
    (by positivity) heff he (by nlinarith))

end
end SparseCompletion

/- Fixed source body: MidpointExact.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bin_middle_even_gap (L : ℕ) (hL : 0 < L) (heven : L%(2 : ℕ)=0) :
    (binLower L hL).val+1=(binUpper L hL).val := by
  simp only [binLower,binUpper]
  omega

theorem bin_middle_odd_same (L : ℕ) (hL : 0 < L) (hodd : L%(2 : ℕ)≠0) :
    binLower L hL=binUpper L hL := by
  apply Fin.ext
  simp only [binLower,binUpper]
  omega

theorem bin_quadratic_parity_identity (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (∑ i, binCompressedWeights L hL i*(a+d*i.val)^(2 : ℕ))=
      d^(2 : ℕ)*(L : ℝ)/(12 : ℕ)*((L : ℝ)^(2 : ℕ)-(if L%(2 : ℕ)=0 then (4 : ℕ) else 1)) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [bin_compressed_moment,bin_quadratic_loss_identity]
  by_cases heven : L%2=0
  · rw [ite_eq_left heven]
    have hh : ((binUpper L hL).val : ℝ)=(binLower L hL).val+1 := by
      exact_mod_cast (bin_middle_even_gap L hL heven).symm
    rw [hh]
    ring
  · rw [ite_eq_right heven,bin_middle_odd_same L hL heven]
    ring

theorem bin_odd_support (L : ℕ) (hL : 0 < L) (hodd : L%(2 : ℕ)≠0) :
    (Finset.univ.filter fun i => binCompressedWeights L hL i ≠ 0).card ≤ 1 := by
  classical
  have hsup : (Finset.univ.filter fun i => binCompressedWeights L hL i ≠ 0) ⊆
      {binLower L hL} := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    by_contra he
    have heq : ∀ b : Fin 2, binCompressedLabel L hL b=binLower L hL := by
      intro b
      simp only [binCompressedLabel,←bin_middle_odd_same L hL hodd,ite_self]
    have hz : binCompressedWeights L hL i=0 := by
      unfold binCompressedWeights pushWeights
      apply Finset.sum_eq_zero
      intro b _
      have hne : binCompressedLabel L hL b ≠ i := by
        rw [heq]
        simpa only [Finset.mem_singleton,ne_comm] using he
      simp only [ite_eq_right hne]
    exact hn hz
  exact le_trans (Finset.card_le_card hsup) (by simp)

end
end SparseCompletion

/- Fixed source body: BinnedExact.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def binParityTerm (L : ℕ) : ℝ :=
  (L : ℝ)*((L : ℝ)^2-(if L%2=0 then ((4 : ℕ) : ℝ) else 1))

theorem binned_quadratic_loss_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r a d : ℝ) :
    scoreMoment (uniformTarget (∑ b, L b) r) (fun j => (a+d*j.val)^(2 : ℕ))-
      scoreMoment (binnedWeights L hL r) (fun j => (a+d*j.val)^(2 : ℕ)) =
      (r/((∑ b, L b : ℕ) : ℝ))*d^(2 : ℕ)/(12 : ℕ)*∑ b, binParityTerm (L b) := by
  norm_num only [Nat.cast_ofNat] at *
  let Δ := fun b : Fin h =>
    (∑ i : Fin (L b), (a+d*(binIndex L b i).val)^2)-
      ∑ i : Fin (L b), binCompressedWeights (L b) (hL b) i*(a+d*(binIndex L b i).val)^2
  have hb : ∀ b, Δ b=d^2/12*binParityTerm (L b) := by
    intro b
    have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val=(a+d*binStart L b)+d*i.val := by
      intro i
      rw [binIndex_val]
      push_cast
      ring
    dsimp only [Δ]
    simp only [hform]
    rw [bin_quadratic_parity_identity]
    unfold binParityTerm
    split_ifs <;> norm_num only [Nat.cast_ofNat] <;> ring
  have he : scoreMoment (uniformTarget (∑ b, L b) r) (fun j => (a+d*j.val)^2)-
      scoreMoment (binnedWeights L hL r) (fun j => (a+d*j.val)^2) =
      (r/((∑ b, L b : ℕ) : ℝ))*∑ b, Δ b := by
    unfold scoreMoment
    rw [binned_moment]
    simp only [uniformTarget,←Finset.mul_sum]
    rw [sum_bin_partition L,←mul_sub,←Finset.sum_sub_distrib]
  rw [he]
  simp only [hb,←Finset.mul_sum]
  ring

theorem binned_exposing_loss_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) :
    let qstar := uniformTarget (∑ b, L b) r
    let q := binnedWeights L hL r
    let w := exposingWeight qstar r
    scoreMoment qstar w-scoreMoment q w =
      r^(2 : ℕ)/((12 : ℕ)*((∑ b, L b : ℕ) : ℝ)^(3 : ℕ))*∑ b, binParityTerm (L b) := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let f := fun j : Fin m => (((m : ℝ)-1)/(m : ℝ)+(-1/(m : ℝ))*j.val)^2
  have hw : exposingWeight (uniformTarget m r) r=(fun j => r*f j) := by
    funext j
    rw [uniform_exposing_weight]
    dsimp only [f]
    congr 1
    congr 1
    ring
  have he : scoreMoment (uniformTarget m r) (exposingWeight (uniformTarget m r) r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight (uniformTarget m r) r)=
      r*(scoreMoment (uniformTarget m r) f-scoreMoment (binnedWeights L hL r) f) := by
    rw [hw]
    simp only [scoreMoment,mul_left_comm _ r,←Finset.mul_sum]
    ring
  change scoreMoment (uniformTarget m r) (exposingWeight (uniformTarget m r) r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight (uniformTarget m r) r)=_
  rw [he]
  have hq := binned_quadratic_loss_exact L hL r (((m : ℝ)-1)/(m : ℝ)) (-1/(m : ℝ))
  change scoreMoment (uniformTarget m r) f-scoreMoment (binnedWeights L hL r) f=_ at hq
  norm_num only [Nat.cast_ofNat] at hq
  rw [hq]
  dsimp only [m]
  field_simp

theorem binned_odd_support {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hodd : ∀ b, L b%(2 : ℕ)≠0) (r : ℝ) : supportSize (binnedWeights L hL r) ≤ h := by
  classical
  let s := Finset.univ.image (fun b : Fin h => binIndex L b (binLower (L b) (hL b)))
  have hs : ∀ k : Fin h × Fin 2, binnedLabel L hL k ∈ s := by
    intro k
    apply Finset.mem_image.mpr
    refine ⟨k.1,Finset.mem_univ _,?_⟩
    simp only [binnedLabel,binCompressedLabel,←bin_middle_odd_same (L k.1) (hL k.1) (hodd k.1),ite_self]
  have hsup : residualSupport (binnedWeights L hL r) ⊆ s := by
    intro i hi
    by_contra he
    have hz : binnedWeights L hL r i=0 := by
      unfold binnedWeights
      exact pushWeights_zero_outside _ _ s hs i he
    exact (Finset.mem_filter.mp hi).2 hz
  exact le_trans (Finset.card_le_card hsup)
    (le_trans (Finset.card_image_le) (by simp))


theorem binned_middle_positive {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 < r) (b : Fin h) :
    0 < binnedWeights L hL r (binIndex L b (binLower (L b) (hL b))) := by
  have hmR : (0 : ℝ) < (∑ b, L b : ℕ) := Nat.cast_pos.mpr hm
  have hLb : (0 : ℝ) < L b := Nat.cast_pos.mpr (hL b)
  have hnonneg : ∀ k : Fin h × Fin 2,
      0 ≤ (if binnedLabel L hL k=binIndex L b (binLower (L b) (hL b)) then
        (r/((∑ b, L b : ℕ) : ℝ))*(L k.1 : ℝ)/(2 : ℕ) else 0) := by
    intro k
    split_ifs <;> positivity
  have hsingle := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin h × Fin 2))) => hnonneg k)
    (Finset.mem_univ (b,(0 : Fin 2)))
  have hlab : binnedLabel L hL (b,(0 : Fin 2))=binIndex L b (binLower (L b) (hL b)) := by
    simp only [binnedLabel,binCompressedLabel,Fin.val_zero,ite_true]
  simp only [hlab,ite_true] at hsingle
  change 0 < ∑ k : Fin h × Fin 2, if binnedLabel L hL k=binIndex L b (binLower (L b) (hL b)) then
    (r/((∑ b, L b : ℕ) : ℝ))*(L k.1 : ℝ)/(2 : ℕ) else 0
  exact lt_of_lt_of_le (by positivity) hsingle

theorem binned_middle_injective {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) :
    Function.Injective (fun b => binIndex L b (binLower (L b) (hL b))) := by
  intro b c he
  change finSigmaFinEquiv ⟨b,binLower (L b) (hL b)⟩=
    finSigmaFinEquiv ⟨c,binLower (L c) (hL c)⟩ at he
  exact congrArg Sigma.fst (finSigmaFinEquiv.injective he)

theorem binned_support_lower {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 < r) : h ≤ supportSize (binnedWeights L hL r) := by
  classical
  let s := Finset.univ.image (fun b : Fin h => binIndex L b (binLower (L b) (hL b)))
  have hs : s ⊆ residualSupport (binnedWeights L hL r) := by
    intro i hi
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hi
    subst i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne_of_gt (binned_middle_positive L hL hm r hr b)⟩
  have hcard : s.card=h := by
    dsimp only [s]
    rw [Finset.card_image_of_injective _ (binned_middle_injective L hL)]
    simp
  calc
    h = s.card := hcard.symm
    _ ≤ supportSize (binnedWeights L hL r) := Finset.card_le_card hs

theorem binned_odd_support_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hodd : ∀ b, L b%(2 : ℕ)≠0) (r : ℝ) (hr : 0 < r) :
    supportSize (binnedWeights L hL r)=h := by
  exact le_antisymm (binned_odd_support L hL hodd r) (binned_support_lower L hL hm r hr)

end
end SparseCompletion

/- Fixed source body: MidpointGame.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem binned_game_completion_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) :
    let m := ∑ b, L b
    let qstar := uniformTarget m (1/(4 : ℕ))
    let q := binnedWeights L hL (1/(4 : ℕ))
    let d := scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ)))-
      scoreMoment q (exposingWeight qstar (1/(4 : ℕ)))
    ∃ B : Fin m → Fin m → ℝ, IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  let qstar := uniformTarget m (1/4)
  let q := binnedWeights L hL (1/4)
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let d := βstar-scoreMoment q w
  have hmean : scoreMoment q t=0 := binned_uniform_score_mean L hL hm (1/4)
  obtain ⟨B,hB,hb,hrows⟩ := binned_uniform_residual_completion L hL hm (1/4) (by norm_num)
  refine ⟨B,hB,hb,?_,?_,?_⟩
  · rw [block_response_anchor]
    have ha := (two_anchor_responses t w q (3/4) βstar (by norm_num)).1
    change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 0=d
    rw [ha,hmean]
    dsimp only [d]
    ring
  · rw [block_response_anchor]
    have ha := (two_anchor_responses t w q (3/4) βstar (by norm_num)).2
    change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 1= -d
    rw [ha,hmean]
    dsimp only [d]
    ring
  · intro j
    rw [block_response_residual]
    have hs : score (rigidityCross qstar) (twoShares (3/4))=t := two_score t w (3/4) (by norm_num)
    rw [hs]
    exact hrows j

theorem binned_odd_game_witness {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hodd : ∀ b, L b%(2 : ℕ)≠0) :
    let m := ∑ b, L b
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      UniformWitness m d true (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q=h ∧
      response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d ∧
      d=(1/(4 : ℕ) : ℝ)^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ))*∑ b, binParityTerm (L b) := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  let qstar := uniformTarget m (1/4)
  let q := binnedWeights L hL (1/4)
  let d := scoreMoment qstar (exposingWeight qstar (1/4))-
    scoreMoment q (exposingWeight qstar (1/4))
  have hq : ∀ j, 0 ≤ q j := binned_nonneg L hL (1/4) (by norm_num)
  have hmass : ∑ j, q j=1/4 := binned_mass L hL (1/4) hm
  have hd : 0 ≤ d := (binned_exposing_loss L hL hm (1/4) (by norm_num)).1
  obtain ⟨B,hB,hb,h0,h1,hrows⟩ := binned_game_completion_exact L hL hm
  refine ⟨q,B,d,?_,binned_odd_support_exact L hL hm hodd (1/4) (by norm_num),h0,?_⟩
  · unfold UniformWitness
    norm_num only [Nat.cast_ofNat]
    refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,hB,hb,?_⟩
    · rw [hmass,Fin.sum_univ_two]
      norm_num [twoShares]
    · intro v
      cases v with
      | inl a =>
        fin_cases a
        · exact le_of_eq h0
        · exact le_of_eq_of_le h1 (by linarith)
      | inr j => exact le_trans (hrows j) hd
  · have he := binned_exposing_loss_exact L hL hm (1/4)
    norm_num only [Nat.cast_ofNat] at he
    exact he

theorem odd_midpoint_error_identity (h s : ℕ) (hh : 0 < h) (hs : 0 < s) (r : ℝ) :
    (r^(2 : ℕ)/((12 : ℕ)*((h*s : ℕ) : ℝ)^(3 : ℕ)))*(h : ℝ)*(s : ℝ)*((s : ℝ)^(2 : ℕ)-1)=
      r^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)^(2 : ℕ)-1/((h*s : ℕ) : ℝ)^(2 : ℕ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  push_cast
  field_simp

theorem uniform_odd_midpoint_witness (h s : ℕ) (hh : 0 < h) (hs : 0 < s) (hodd : s%(2 : ℕ)≠0) :
    ∃ (q : Fin (h*s) → ℝ) (B : Fin (h*s) → Fin (h*s) → ℝ),
      UniformWitness (h*s) ((1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)^(2 : ℕ)-1/((h*s : ℕ) : ℝ)^(2 : ℕ))) true
        (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q=h ∧
      response (blockMatrix (rigidityCore (uniformTarget (h*s) (1/(4 : ℕ))))
        (rigidityCross (uniformTarget (h*s) (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=
          (1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)^(2 : ℕ)-1/((h*s : ℕ) : ℝ)^(2 : ℕ)) := by
  have hsum : (∑ _ : Fin h, s)=h*s := by simp
  have hm : 0 < ∑ _ : Fin h, s := by rw [hsum]; exact Nat.mul_pos hh hs
  obtain ⟨q,B,d,hw,hcard,hrow,hd⟩ := binned_odd_game_witness (fun _ : Fin h => s) (fun _ => hs) hm (fun _ => hodd)
  have hparity : binParityTerm s=(s : ℝ)*((s : ℝ)^2-1) := by
    simp only [binParityTerm,ite_eq_right hodd]
  have herr : d=(1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2) := by
    rw [hd,hsum]
    simp only [hparity,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    convert odd_midpoint_error_identity h s hh hs (1/4) using 1
    ring
  rw [herr] at hw hrow
  have result : ∃ (q : Fin (∑ _ : Fin h, s) → ℝ)
      (B : Fin (∑ _ : Fin h, s) → Fin (∑ _ : Fin h, s) → ℝ),
      UniformWitness (∑ _ : Fin h, s) ((1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2))
        true (twoShares (3/4)) q B ∧ supportSize q=h ∧
      response (blockMatrix (rigidityCore (uniformTarget (∑ _ : Fin h, s) (1/4)))
        (rigidityCross (uniformTarget (∑ _ : Fin h, s) (1/4))) B)
        (blockWeights (twoShares (3/4)) q) (.inl 0)=
          (1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2) := ⟨q,B,hw,hcard,hrow⟩
  exact (congrArg (fun m : ℕ => ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
    UniformWitness m ((1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2))
      true (twoShares (3/4)) q B ∧ supportSize q=h ∧
    response (blockMatrix (rigidityCore (uniformTarget m (1/4)))
      (rigidityCross (uniformTarget m (1/4))) B)
      (blockWeights (twoShares (3/4)) q) (.inl 0)=
        (1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2)) hsum).mp result

end
end SparseCompletion

/- Fixed source body: BalancedExact.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bin_error_finite_identity (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (r : ℝ) :
    (r^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ)))*(m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ) =
      r^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  field_simp

theorem binned_finite_correction {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hh : 0 < h) (r : ℝ) (hr : 0 ≤ r)
    (hcube : (∑ b : Fin h, (L b : ℝ)^(3 : ℕ)) ≤
      (∑ b, L b : ℝ)*(((∑ b, L b : ℕ) : ℝ)/(h : ℝ)+1)^(2 : ℕ)) :
    let m := ∑ b, L b
    let qstar := uniformTarget m r
    scoreMoment qstar (exposingWeight qstar r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight qstar r) ≤
        r^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hc : 0 ≤ r^2/(12*((∑ b, L b : ℕ) : ℝ)^3) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hcube hc
  have hloss := (binned_exposing_loss L hL hm r hr).2
  have hid := bin_error_finite_identity _ h hm hh r
  norm_num only [Nat.cast_ofNat] at hid
  refine le_trans hloss (le_trans ?_ (le_of_eq hid))
  norm_num only [Nat.cast_ofNat] at *
  simpa only [Nat.cast_sum,mul_assoc] using hbound


theorem binned_finite_game_witness {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hh : 0 < h)
    (hcube : (∑ b : Fin h, (L b : ℝ)^(3 : ℕ)) ≤
      (∑ b, L b : ℝ)*(((∑ b, L b : ℕ) : ℝ)/(h : ℝ)+1)^(2 : ℕ)) :
    let m := ∑ b, L b
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      UniformWitness m d true (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) ∧
      response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,_,hloss,h0,h1,hrows⟩ := binned_game_witness L hL hm
  refine ⟨q,B,d,?_,hcard,hd,?_,h0⟩
  · unfold UniformWitness
    norm_num only [Nat.cast_ofNat]
    refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,hB,hb,?_⟩
    · rw [hmass,Fin.sum_univ_two]
      norm_num [twoShares]
    · intro v
      cases v with
      | inl a =>
        fin_cases a
        · exact le_of_eq h0
        · exact le_of_eq_of_le h1 (by linarith)
      | inr j => exact le_trans (hrows j) hd
  · have hc : 0 ≤ (1/(4 : ℕ) : ℝ)^2/(12*((∑ b, L b : ℕ) : ℝ)^3) := by positivity
    have hbound := mul_le_mul_of_nonneg_left hcube hc
    have hid := bin_error_finite_identity _ h hm hh (1/4)
    norm_num only [Nat.cast_ofNat] at hid
    refine le_trans hloss (le_trans ?_ (le_of_eq hid))
    norm_num only [Nat.cast_ofNat] at *
    simpa only [Nat.cast_sum,mul_assoc] using hbound

theorem balanced_finite_game_witness (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m) :
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      UniformWitness m d true (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) ∧
      response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d := by
  have hw := binned_finite_game_witness (balancedLength m h)
    (balancedLength_positive m h hh hhm) (by rw [balancedLength_mass m h hh]; exact hm) hh
  have hcube : (∑ b : Fin h, (balancedLength m h b : ℝ)^3) ≤
      (∑ b, balancedLength m h b : ℝ)*(((∑ b, balancedLength m h b : ℕ) : ℝ)/(h : ℝ)+1)^2 := by
    simpa only [←Nat.cast_sum,balancedLength_mass m h hh] using balancedLength_cube_sum m h hh
  have result := hw hcube
  exact (congrArg (fun n : ℕ => ∃ (q : Fin n → ℝ) (B : Fin n → Fin n → ℝ) (d : ℝ),
    UniformWitness n d true (twoShares (3/4)) q B ∧ supportSize q ≤ min n (2*h) ∧
      0 ≤ d ∧ d ≤ (1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)+1/(n : ℝ))^2 ∧
      response (blockMatrix (rigidityCore (uniformTarget n (1/4)))
        (rigidityCross (uniformTarget n (1/4))) B)
        (blockWeights (twoShares (3/4)) q) (.inl 0)=d) (balancedLength_mass m h hh)).mp result

end
end SparseCompletion

/- Fixed source body: AllMassWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem nonnegative_mass_zero {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=0) : q=fun _ => 0 := by
  classical
  funext i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hq j) (Finset.mem_univ i)
  rw [hm] at hi
  exact le_antisymm hi (hq i)

theorem normalized_sparse_witness_all_mass {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q hq (by simpa only [hz] using hqmass)
    have hc : (Finset.univ.filter fun i => q i ≠ 0).card=0 := by simp [hzero]
    have ha : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨q,B,blockWeights_nonneg p q hp hq,?_,fun _ => rfl,fun _ hi => hi,?_,?_,
      fun _ => rfl,blockMatrix_skew K D B hK hB,blockMatrix_bounds K D B M hKb hDb hBb,?_⟩
    · rw [blockWeights_mass,hqmass]
      exact hpmass
    · rw [hc]
      exact Nat.zero_le _
    · rw [block_support_card,hc]
      omega
    · intro a
      exact le_trans (hresp a) (by linarith)
  · obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hmo,hsk,hb,hrows⟩ :=
      normalized_sparse_witness k K D B p q M r ρ η hM (lt_of_le_of_ne hr (Ne.symm hz)) hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
    refine ⟨q',B',hn,hm,ha,hs,Nat.le_min.mpr ⟨?_,hc⟩,Nat.le_min.mpr ⟨?_,ht⟩,hmo,hsk,hb,hrows⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (Finset.card_filter_le _ _) (by simp)

theorem normalized_exact_sparse_witness_all_mass {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q hq (by simpa only [hz] using hqmass)
    have hc : (Finset.univ.filter fun i => q i ≠ 0).card=0 := by simp [hzero]
    have ha : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨q,B,blockWeights_nonneg p q hp hq,?_,fun _ => rfl,fun _ hi => hi,?_,?_,
      fun _ => rfl,blockMatrix_skew K D B hK hB,blockMatrix_bounds K D B M hKb hDb hBb,?_⟩
    · rw [blockWeights_mass,hqmass]
      exact hpmass
    · rw [hc]
      exact Nat.zero_le _
    · rw [block_support_card,hc]
      omega
    · intro a
      exact le_trans (hresp a) (by linarith)
  · obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hmo,hsk,hb,hrows⟩ :=
      normalized_exact_sparse_witness k K D B p q M r η hM (lt_of_le_of_ne hr (Ne.symm hz)) hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
    refine ⟨q',B',hn,hm,ha,hs,Nat.le_min.mpr ⟨?_,hc⟩,Nat.le_min.mpr ⟨?_,ht⟩,hmo,hsk,hb,hrows⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (Finset.card_filter_le _ _) (by simp)

end
end SparseCompletion

/- Fixed source body: ExtraMomentCuts.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def extraSparseFeatures {ι : Type*} (k d H : ℕ) (D : ι → Fin k → ℝ)
    (F : ι → Fin d → ℝ) (v : ι → ℝ) (M r η : ℝ) (i : ι) :
    ((Fin k ⊕ Fin d) ⊕ Fin H) → ℝ :=
  Sum.elim (Sum.elim (D i) (F i))
    (fun l => max (v i-(M*r-gridNode M r η (l.val+1))) 0)

theorem sparse_cut_witness_extra_moments {ι : Type*} [Fintype ι]
    (k d H : ℕ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hH : M*r ≤ η*(H:ℝ)^2) (hq : ∀ i, 0 ≤ q i)
    (hmass : ∑ i, q i = r) (hcuts : Cuts M r q v) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+1+H ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      Cuts M r q' (fun i => v i-η) := by
  classical
  obtain ⟨q', hq', hmass', hsupp, hcard, hmom⟩ :=
    finite_feature_compression ((Fin k ⊕ Fin d) ⊕ Fin H) q (extraSparseFeatures k d H D F v M r η) r hq hmass hr
  refine ⟨q', hq', hmass', hsupp, ?_, ?_, (fun g => hmom (Sum.inl (Sum.inr g))), ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_right_comm (k+d) H 1] using hcard
  · intro h
    exact hmom (Sum.inl (Sum.inl h))
  · apply call_bound_implies_cuts q' (fun i => v i-η) M r hM hq' hmass'
    apply finite_grid_implication q' v M r η H hM (le_of_lt hr) hη hH hq'
    · intro i hi
      exact supported_score_cap q v M r hM hq hcuts i (fun hzero => hi (hsupp i hzero))
    · intro l hl hlH
      let j : Fin H := ⟨l-1, by omega⟩
      have hj : j.val+1 = l := by dsimp [j]; omega
      have hm := hmom (Sum.inr j)
      change (∑ i, q' i*max (v i-(M*r-gridNode M r η (j.val+1))) 0) =
        ∑ i, q i*max (v i-(M*r-gridNode M r η (j.val+1))) 0 at hm
      rw [hj] at hm
      change (∑ i, q' i*max (v i-(M*r-gridNode M r η l)) 0) ≤ _
      rw [hm]
      exact cuts_imply_call_bound q v M r hM hcuts _

theorem exact_sparse_cut_witness_extra_moments {ι : Type*} [Fintype ι]
    (k d H : ℕ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (p : Fin k → ℝ) (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hH : M*r ≤ η*(H:ℝ)^2) (hq : ∀ i, 0 ≤ q i)
    (hmass : ∑ i, q i = r) (hcuts : Cuts M r q v)
    (hv : ∀ i, v i = ∑ h, D i h*p h) (hmean : ∑ i, q i*v i = 0)
    (hlow : ∀ i, q i ≠ 0 → -M*r ≤ v i) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+H ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      Cuts M r q' (fun i => v i-η) := by
  classical
  have hHpos : 0 < H := by
    by_contra hn
    have hzero : H = 0 := by omega
    subst H
    norm_num at hH
    nlinarith [mul_pos hM hr]
  obtain ⟨q', hq', hmass', hsupp, hcard, hmom⟩ :=
    finite_feature_compression ((Fin k ⊕ Fin d) ⊕ Fin (H-1)) q (extraSparseFeatures k d (H-1) D F v M r η) r hq hmass hr
  have hanchor : ∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h := fun h => hmom (Sum.inl (Sum.inl h))
  refine ⟨q', hq', hmass', hsupp, ?_, hanchor, (fun g => hmom (Sum.inl (Sum.inr g))), ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  · apply call_bound_implies_cuts q' (fun i => v i-η) M r hM hq' hmass'
    apply finite_grid_implication q' v M r η H hM (le_of_lt hr) hη hH hq'
    · intro i hi
      exact supported_score_cap q v M r hM hq hcuts i (fun hzero => hi (hsupp i hzero))
    · intro l hl hlH
      by_cases hlast : l = H
      · subst l
        have hnode : gridNode M r η H = 2*M*r := min_eq_right (by nlinarith)
        rw [hnode]
        have harg : M*r-2*M*r = -M*r := by ring
        rw [harg]
        have hmean' : ∑ i, q' i*v i = 0 :=
          (linear_score_moment_preserved k D p q q' v hv hanchor).trans hmean
        rw [bottom_call_of_zero_mean q' v M r hmass' hmean'
          (fun i hi => hlow i (fun hzero => hi (hsupp i hzero)))]
        have heq : envelope M r (-M*r) = M*r^2 := by
          unfold envelope
          field_simp
          ring
        rw [heq]
      · have hlt : l < H := lt_of_le_of_ne hlH hlast
        let j : Fin (H-1) := ⟨l-1, by omega⟩
        have hj : j.val+1 = l := by dsimp [j]; omega
        have hm := hmom (Sum.inr j)
        change (∑ i, q' i*max (v i-(M*r-gridNode M r η (j.val+1))) 0) =
          ∑ i, q i*max (v i-(M*r-gridNode M r η (j.val+1))) 0 at hm
        rw [hj] at hm
        change (∑ i, q' i*max (v i-(M*r-gridNode M r η l)) 0) ≤ _
        rw [hm]
        exact cuts_imply_call_bound q v M r hM hcuts _

end
end SparseCompletion

/- Fixed source body: ExtraMomentGameCertificates.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem game_sparse_cut_certificate_extra_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+1+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      (∀ i, score D p i ≤ (ρ+η)+M*r) ∧
      Cuts M r q' (fun i => score D p i-(ρ+η)) := by
  classical
  have hres := ((block_response_bounds_iff K D B p q ρ).mp hresp).2
  have hcuts := completion_cuts_necessary q (score D p) B M r ρ hq hmass hB hbound hres
  obtain ⟨q', hq', hmass', hsupp, hcard, hfeatures, hextra, hc⟩ :=
    sparse_cut_witness_extra_moments k d (gridSize M r η) D F q (fun i => score D p i-ρ) M r η hM hr hη (gridSize_bound M r η hM (le_of_lt hr) hη) hq hmass hcuts
  refine ⟨q', hq', hmass', hsupp, hcard, anchor_response_of_moments k K D p q q' hfeatures, hextra, ?_, ?_⟩
  · intro i
    have hg := response_guard q (score D p) B M r ρ hq hmass hbound hres i
    linarith
  · convert hc using 1
    funext i
    ring

theorem exact_game_sparse_cut_certificate_extra_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      (∀ i, score D p i ≤ η+M*r) ∧
      Cuts M r q' (fun i => score D p i-η) := by
  classical
  have hres := ((block_response_bounds_iff K D B p q 0).mp hresp).2
  have hcuts0 := completion_cuts_necessary q (score D p) B M r 0 hq hmass hB
    (fun i j => (hbound i j).1) hres
  have hcuts : Cuts M r q (score D p) := by simpa only [sub_zero] using hcuts0
  have hmean := exact_score_mean_zero K D B p q hp hq hK hB hresp
  have hlow : ∀ i, q i ≠ 0 → -M*r ≤ score D p i := by
    intro i hi
    simpa only [neg_mul] using
      (abs_le.mp (exact_score_bounds K D B p q M r hp hq hmass hK hB hbound hresp i hi)).1
  obtain ⟨q', hq', hmass', hsupp, hcard, hfeatures, hextra, hc⟩ :=
    exact_sparse_cut_witness_extra_moments k d (gridSize M r η) D F p q (score D p) M r η hM hr hη
      (gridSize_bound M r η hM (le_of_lt hr) hη) hq hmass hcuts (fun _ => rfl) hmean hlow
  refine ⟨q', hq', hmass', hsupp, hcard, anchor_response_of_moments k K D p q q' hfeatures, hextra, ?_, hc⟩
  intro i
  have hg := response_guard q (score D p) B M r 0 hq hmass
    (fun i j => (hbound i j).1) hres i
  linarith

end
end SparseCompletion

/- Fixed source body: ExtraMomentCompletion.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem game_sparse_completion_extra_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+1+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  obtain ⟨q', hq', hm', hs, hn, ha, hextra, hg, hc⟩ :=
    game_sparse_cut_certificate_extra_moments k d K D F B p q M r ρ η hM hr hη hq hmass hB hbound hresp
  obtain ⟨B', hsk', hb', hres'⟩ := completion_of_cuts_and_guards q' (score D p)
    M r (ρ+η) (le_of_lt hM) hq' hm' hc hg
  refine ⟨q', B', hq', hm', hs, hn, ha, hextra, hsk', hb', ?_⟩
  apply (block_response_bounds_iff K D B' p q' (ρ+η)).mpr
  refine ⟨?_, hres'⟩
  intro h
  rw [ha h]
  have hh := ((block_response_bounds_iff K D B p q ρ).mp hresp).1 h
  linarith

/-- Exact equilibria save the bottom hinge constraint, hence one support
    point, while still producing an actual completion on all original rows. -/
theorem exact_game_sparse_completion_extra_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  obtain ⟨q', hq', hm', hs, hn, ha, hextra, hg, hc⟩ :=
    exact_game_sparse_cut_certificate_extra_moments k d K D F B p q M r η hM hr hη hp hq hmass hK hB hbound hresp
  obtain ⟨B', hsk', hb', hres'⟩ := completion_of_cuts_and_guards q' (score D p)
    M r η (le_of_lt hM) hq' hm' hc hg
  refine ⟨q', B', hq', hm', hs, hn, ha, hextra, hsk', hb', ?_⟩
  apply (block_response_bounds_iff K D B' p q' η).mpr
  refine ⟨?_, hres'⟩
  intro h
  rw [ha h]
  have hh := ((block_response_bounds_iff K D B p q 0).mp hresp).1 h
  linarith

end
end SparseCompletion

/- Fixed source body: ExtraMomentWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_sparse_witness_extra_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+1+gridSize M r η ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ (2 : ℕ)*k+d+1+gridSize M r η ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  obtain ⟨q', B', hn, hm, hs, hc, ha, hextra, hsk, hb, he⟩ :=
    game_sparse_completion_extra_moments k d K D F B p q M r ρ η hM hr hη hq hqmass hB
      (fun i j => (hBb i j).1) hresp
  refine ⟨q', B', blockWeights_nonneg p q' hp hn, ?_, fun _ => rfl, hs, hc, ?_, ?_, hextra,
    blockMatrix_skew K D B' hK hsk, blockMatrix_bounds K D B' M hKb hDb hb, he⟩
  · rw [blockWeights_mass, hm]
    exact hpmass
  · rw [block_support_card]
    have hanchor : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  · intro h
    have hh := ha h
    unfold anchorResponse at hh
    have hsums : (∑ i, D i h*q' i) = ∑ i, D i h*q i := by linarith
    simpa only [mul_comm] using hsums
/-- Normalized, bounded whole-game specialization of the sparse witness.
    The conclusion preserves the prescribed anchor shares literally. -/
theorem normalized_exact_sparse_witness_extra_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+gridSize M r η ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ (2 : ℕ)*k+d+gridSize M r η ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  obtain ⟨q', B', hn, hm, hs, hc, ha, hextra, hsk, hb, he⟩ :=
    exact_game_sparse_completion_extra_moments k d K D F B p q M r η hM hr hη hp hq hqmass hK hB hBb hresp
  refine ⟨q', B', blockWeights_nonneg p q' hp hn, ?_, fun _ => rfl, hs, hc, ?_, ?_, hextra,
    blockMatrix_skew K D B' hK hsk, blockMatrix_bounds K D B' M hKb hDb hb, he⟩
  · rw [blockWeights_mass, hm]
    exact hpmass
  · rw [block_support_card]
    have hanchor : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  · intro h
    have hh := ha h
    unfold anchorResponse at hh
    have hsums : (∑ i, D i h*q' i) = ∑ i, D i h*q i := by linarith
    simpa only [mul_comm] using hsums

end
end SparseCompletion

/- Fixed source body: ExtraMomentAllMass.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_sparse_witness_extra_moments_all_mass {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q hq (by simpa only [hz] using hqmass)
    have hc : (Finset.univ.filter fun i => q i ≠ 0).card=0 := by simp [hzero]
    have ha : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨q,B,blockWeights_nonneg p q hp hq,?_,fun _ => rfl,fun _ hi => hi,?_,?_,
      fun _ => rfl,fun _ => rfl,blockMatrix_skew K D B hK hB,blockMatrix_bounds K D B M hKb hDb hBb,?_⟩
    · rw [blockWeights_mass,hqmass]
      exact hpmass
    · rw [hc]
      exact Nat.zero_le _
    · rw [block_support_card,hc]
      omega
    · intro a
      exact le_trans (hresp a) (by linarith)
  · obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hmo,hf,hsk,hb,hrows⟩ :=
      normalized_sparse_witness_extra_moments k d K D F B p q M r ρ η hM (lt_of_le_of_ne hr (Ne.symm hz)) hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
    refine ⟨q',B',hn,hm,ha,hs,Nat.le_min.mpr ⟨?_,hc⟩,Nat.le_min.mpr ⟨?_,ht⟩,hmo,hf,hsk,hb,hrows⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (Finset.card_filter_le _ _) (by simp)

theorem normalized_exact_sparse_witness_extra_moments_all_mass {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q hq (by simpa only [hz] using hqmass)
    have hc : (Finset.univ.filter fun i => q i ≠ 0).card=0 := by simp [hzero]
    have ha : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨q,B,blockWeights_nonneg p q hp hq,?_,fun _ => rfl,fun _ hi => hi,?_,?_,
      fun _ => rfl,fun _ => rfl,blockMatrix_skew K D B hK hB,blockMatrix_bounds K D B M hKb hDb hBb,?_⟩
    · rw [blockWeights_mass,hqmass]
      exact hpmass
    · rw [hc]
      exact Nat.zero_le _
    · rw [block_support_card,hc]
      omega
    · intro a
      exact le_trans (hresp a) (by linarith)
  · obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hmo,hf,hsk,hb,hrows⟩ :=
      normalized_exact_sparse_witness_extra_moments k d K D F B p q M r η hM (lt_of_le_of_ne hr (Ne.symm hz)) hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
    refine ⟨q',B',hn,hm,ha,hs,Nat.le_min.mpr ⟨?_,hc⟩,Nat.le_min.mpr ⟨?_,ht⟩,hmo,hf,hsk,hb,hrows⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (Finset.card_filter_le _ _) (by simp)

end
end SparseCompletion

/- Fixed source body: ScorePrefixes.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def scorePrefix (m l : ℕ) : Finset (Fin m) := Finset.univ.filter fun i => i.val<l

theorem threshold_is_score_prefix {m : ℕ} (v : Fin m → ℝ) (hv : Antitone v) (z : ℝ) :
    ∃ l : ℕ, l ≤ m ∧ (Finset.univ.filter fun i => 0 < v i-z)=scorePrefix m l := by
  classical
  let s := Finset.univ.filter fun i => 0 < v i-z
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hjv : 0 < v j-z := (Finset.mem_filter.mp hj).2
    refine ⟨j.val+1,by omega,?_⟩
    ext i
    change i ∈ s ↔ i ∈ scorePrefix m (j.val+1)
    simp only [scorePrefix,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hi
      have hle : i ≤ j := Finset.le_max' s i hi
      exact Nat.lt_succ_iff.mpr (show i.val ≤ j.val from hle)
    · intro hi
      have hle : i ≤ j := show i.val ≤ j.val from Nat.lt_succ_iff.mp hi
      have hvi := hv hle
      change i ∈ Finset.univ.filter fun i => 0 < v i-z
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith⟩
  · refine ⟨0,Nat.zero_le _,?_⟩
    have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa only [scorePrefix,Nat.not_lt_zero,Finset.filter_false] using he

theorem cuts_iff_score_prefixes {m : ℕ} (q v : Fin m → ℝ) (M r : ℝ)
    (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i=r) (hv : Antitone v) :
    Cuts M r q v ↔ ∀ l : ℕ, l ≤ m →
      (∑ i ∈ scorePrefix m l, q i*v i) ≤
        M*mass (scorePrefix m l) q*(r-mass (scorePrefix m l) q) := by
  constructor
  · intro hc l _
    exact hc _
  · intro hp
    apply call_bound_implies_cuts q v M r hM hq hmass
    intro z _
    classical
    let s := Finset.univ.filter fun i => 0 < v i-z
    let Q := mass s q
    have heq : call q v z = (∑ i ∈ s, q i*v i)-z*Q := by
      have hh : call q v z = ∑ i ∈ s, q i*(v i-z) := by
        unfold call
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => 0 < v i-z)]
        have hz : (∑ i ∈ Finset.univ.filter (fun i => ¬0 < v i-z), q i*max (v i-z) 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have := (Finset.mem_filter.mp hi).2
          rw [max_eq_right (le_of_not_gt this), mul_zero]
        rw [hz, add_zero]
        exact Finset.sum_congr rfl fun i hi => by rw [max_eq_left (le_of_lt (Finset.mem_filter.mp hi).2)]
      rw [hh]
      simp only [Q, mass, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      simp only [mul_comm]
    obtain ⟨l,hl,he⟩ := threshold_is_score_prefix v hv z
    have hc : (∑ i ∈ s, q i*v i) ≤ M*Q*(r-Q) := by
      dsimp only [Q,s]
      rw [he]
      exact hp l hl
    have hs := sq_nonneg (2*M*Q - (M*r-z))
    have he : 4*M*envelope M r z = (M*r-z)^2 := by
      unfold envelope
      field_simp
    rw [heq]
    apply (mul_le_mul_iff_right₀ (show 0 < 4*M by positivity)).mp
    nlinarith

end
end SparseCompletion

/- Fixed source body: ConicCompletion.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def rotatedLorentz (u v w : ℝ) : Prop := 0 ≤ u ∧ 0 ≤ v ∧ w^2 ≤ (2 : ℕ)*u*v

theorem prefix_cut_quadratic {m : ℕ} (q t : Fin m → ℝ) (M r ε : ℝ) (l : ℕ) :
    (∑ i ∈ scorePrefix m l, q i*(t i-ε)) ≤
      M*mass (scorePrefix m l) q*(r-mass (scorePrefix m l) q) ↔
    M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
      (∑ i ∈ scorePrefix m l, q i*(t i-ε)) ≤ 0 := by
  constructor <;> intro h <;> nlinarith

theorem quadratic_rotated_cone (M r Q a : ℝ) (hM : 0 < M) :
    M*Q^2-M*r*Q+a ≤ 0 ↔ rotatedLorentz (r*Q-a/M) (1/(2 : ℕ)) Q := by
  have hscale : M*(r*Q-a/M-Q^2)= -(M*Q^2-M*r*Q+a) := by
    field_simp
    ring
  unfold rotatedLorentz
  norm_num only [Nat.cast_ofNat]
  constructor
  · intro h
    have hh : 0 ≤ r*Q-a/M-Q^2 := nonneg_of_mul_nonneg_right (by linarith) hM
    refine ⟨?_,by norm_num,?_⟩ <;> nlinarith [sq_nonneg Q]
  · rintro ⟨_,_,h⟩
    have hh : 0 ≤ M*(r*Q-a/M-Q^2) := mul_nonneg (le_of_lt hM) (by nlinarith)
    linarith

theorem weighted_completion_prefix_quadratic_iff {m : ℕ} (q t : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (ht : Antitone t) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ε) ↔
    (∀ i, t i ≤ ε+M*r) ∧ ∀ l : ℕ, l ≤ m →
      M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
        (∑ i ∈ scorePrefix m l, q i*(t i-ε)) ≤ 0 := by
  rw [weighted_completion_iff q t M r ε (le_of_lt hM) hq hr]
  have hs : Antitone (fun i => t i-ε) := fun _ _ hij => sub_le_sub_right (ht hij) ε
  rw [cuts_iff_score_prefixes q (fun i => t i-ε) M r hM hq hr hs]
  constructor
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (prefix_cut_quadratic q t M r ε l).mp (hp l hl)⟩
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (prefix_cut_quadratic q t M r ε l).mpr (hp l hl)⟩

theorem weighted_completion_rotated_cones_iff {m : ℕ} (q t : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (ht : Antitone t) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ε) ↔
    (∀ i, t i ≤ ε+M*r) ∧ ∀ l : ℕ, l ≤ m →
      rotatedLorentz (r*mass (scorePrefix m l) q-
        (∑ i ∈ scorePrefix m l, q i*(t i-ε))/M) (1/(2 : ℕ)) (mass (scorePrefix m l) q) := by
  rw [weighted_completion_prefix_quadratic_iff q t M r ε hM hq hr ht]
  constructor
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (quadratic_rotated_cone M r _ _ hM).mp (hp l hl)⟩
  · rintro ⟨hg,hp⟩
    exact ⟨hg,fun l hl => (quadratic_rotated_cone M r _ _ hM).mpr (hp l hl)⟩

theorem known_anchor_prefix_characterization {m k : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ) (q : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (ht : Antitone (score D p)) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    (∀ h, anchorResponse K D p q h ≤ ε) ∧ (∀ i, score D p i ≤ ε+M*r) ∧
      ∀ l : ℕ, l ≤ m →
        rotatedLorentz (r*mass (scorePrefix m l) q-
          (∑ i ∈ scorePrefix m l, q i*(score D p i-ε))/M) (1/(2 : ℕ)) (mass (scorePrefix m l) q) := by
  constructor
  · rintro ⟨B,hB,hb,hrows⟩
    have hh := (block_response_bounds_iff K D B p q ε).mp hrows
    have hc := (weighted_completion_rotated_cones_iff q (score D p) M r ε hM hq hr ht).mp
      ⟨B,hB,hb,hh.2⟩
    exact ⟨hh.1,hc⟩
  · rintro ⟨ha,hg,hp⟩
    obtain ⟨B,hB,hb,hrows⟩ :=
      (weighted_completion_rotated_cones_iff q (score D p) M r ε hM hq hr ht).mpr ⟨hg,hp⟩
    exact ⟨B,hB,hb,(block_response_bounds_iff K D B p q ε).mpr ⟨ha,hrows⟩⟩

theorem normalized_known_anchor_conic_iff {m k : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ) (q : Fin m → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hr : ∑ i, q i=r) (hpmass : (∑ h, p h)+r=1)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M) (ht : Antitone (score D p)) :
    (∃ B, (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
      IsSkew (blockMatrix K D B) ∧
      (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    (∀ h, anchorResponse K D p q h ≤ ε) ∧ (∀ i, score D p i ≤ ε+M*r) ∧
      ∀ l : ℕ, l ≤ m →
        rotatedLorentz (r*mass (scorePrefix m l) q-
          (∑ i ∈ scorePrefix m l, q i*(score D p i-ε))/M) (1/(2 : ℕ)) (mass (scorePrefix m l) q) := by
  constructor
  · rintro ⟨B,_,_,hsk,hb,hrows⟩
    apply (known_anchor_prefix_characterization K D p q M r ε hM hq hr ht).mp
    refine ⟨B,?_,?_,hrows⟩
    · intro i j
      exact hsk (.inr i) (.inr j)
    · intro i j
      exact hb (.inr i) (.inr j)
  · intro h
    obtain ⟨B,hB,hb,hrows⟩ :=
      (known_anchor_prefix_characterization K D p q M r ε hM hq hr ht).mpr h
    refine ⟨B,blockWeights_nonneg p q hp hq,?_,blockMatrix_skew K D B hK hB,
      blockMatrix_bounds K D B M hKb hDb hb,hrows⟩
    rw [blockWeights_mass,hr]
    exact hpmass

end
end SparseCompletion

/- Fixed source body: ConicConvexity.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def prefixQuadratic {m : ℕ} (t : Fin m → ℝ) (M r ε : ℝ) (l : ℕ) (q : Fin m → ℝ) : ℝ :=
  M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
    ∑ i ∈ scorePrefix m l, q i*(t i-ε)

theorem finite_linear_mix {ι : Type*} (s : Finset ι) (q q' f : ι → ℝ) (a b : ℝ) :
    (∑ i ∈ s, (a*q i+b*q' i)*f i)=a*(∑ i ∈ s, q i*f i)+b*(∑ i ∈ s, q' i*f i) := by
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,←Finset.mul_sum]

theorem finite_mass_mix {ι : Type*} (s : Finset ι) (q q' : ι → ℝ) (a b : ℝ) :
    mass s (a • q+b • q')=a*mass s q+b*mass s q' := by
  unfold mass
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_one] using finite_linear_mix s q q' (fun _ => 1) a b

theorem prefix_quadratic_mix {m : ℕ} (t q q' : Fin m → ℝ) (M r ε a b : ℝ)
    (l : ℕ) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    prefixQuadratic t M r ε l (a • q+b • q') ≤
      a*prefixQuadratic t M r ε l q+b*prefixQuadratic t M r ε l q' := by
  unfold prefixQuadratic
  rw [finite_mass_mix]
  have he := finite_linear_mix (scorePrefix m l) q q' (fun i => t i-ε) a b
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [he]
  have hid : M*(a*mass (scorePrefix m l) q+b*mass (scorePrefix m l) q')^2-
      M*r*(a*mass (scorePrefix m l) q+b*mass (scorePrefix m l) q')+
      (a*(∑ i ∈ scorePrefix m l, q i*(t i-ε))+b*(∑ i ∈ scorePrefix m l, q' i*(t i-ε))) =
      a*(M*(mass (scorePrefix m l) q)^2-M*r*mass (scorePrefix m l) q+
        ∑ i ∈ scorePrefix m l, q i*(t i-ε))+
      b*(M*(mass (scorePrefix m l) q')^2-M*r*mass (scorePrefix m l) q'+
        ∑ i ∈ scorePrefix m l, q' i*(t i-ε))-
      M*a*b*(mass (scorePrefix m l) q-mass (scorePrefix m l) q')^2 := by
    have hb' : b=1-a := by linarith
    rw [hb']
    ring
  rw [hid]
  exact sub_le_self _ (by positivity)

theorem prefix_system_convex {m : ℕ} (t : Fin m → ℝ) (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {q : Fin m → ℝ | ∀ l : ℕ, l ≤ m → prefixQuadratic t M r ε l q ≤ 0} := by
  intro q hq q' hq' a b ha hb hab l hl
  have hm := prefix_quadratic_mix t q q' M r ε a b l hM ha hb hab
  have h1 := mul_nonpos_of_nonneg_of_nonpos ha (hq l hl)
  have h2 := mul_nonpos_of_nonneg_of_nonpos hb (hq' l hl)
  exact le_trans hm (by linarith)


theorem anchor_response_mix {m k : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ) (q q' : Fin m → ℝ)
    (a b : ℝ) (hab : a+b=1) (h : Fin k) :
    anchorResponse K D p (a • q+b • q') h=
      a*anchorResponse K D p q h+b*anchorResponse K D p q' h := by
  have hs := finite_linear_mix Finset.univ q q' (fun i => D i h) a b
  have hs' : (∑ i, D i h*(a • q+b • q') i)=
      a*(∑ i, D i h*q i)+b*(∑ i, D i h*q' i) := by
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hs
  unfold anchorResponse
  rw [hs']
  have hb : b=1-a := by linarith
  rw [hb]
  ring

def knownAnchorConicFeasible {m k : ℕ} (R : Set (Fin m → ℝ))
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ)
    (M r ε : ℝ) : Set (Fin m → ℝ) :=
  {q | q ∈ R ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
    (∀ h, anchorResponse K D p q h ≤ ε) ∧ (∀ i, score D p i ≤ ε+M*r) ∧
    ∀ l : ℕ, l ≤ m → prefixQuadratic (score D p) M r ε l q ≤ 0}

theorem known_anchor_conic_system_convex {m k : ℕ} (R : Set (Fin m → ℝ))
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ)
    (M r ε : ℝ) (hM : 0 ≤ M) (hR : Convex ℝ R) :
    Convex ℝ (knownAnchorConicFeasible R K D p M r ε) := by
  intro q hq q' hq' a b ha hb hab
  rcases hq with ⟨hqR,hqn,hqm,hqa,hqg,hqp⟩
  rcases hq' with ⟨hqR',hqn',hqm',hqa',_,hqp'⟩
  refine ⟨hR hqR hqR' ha hb hab,?_,?_,?_,hqg,?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hqn i)) (mul_nonneg hb (hqn' i))
  · have hm := finite_mass_mix Finset.univ q q' a b
    unfold mass at hm
    rw [hm,hqm,hqm',←add_mul,hab,one_mul]
  · intro h
    rw [anchor_response_mix K D p q q' a b hab h]
    have h0 := mul_le_mul_of_nonneg_left (hqa h) ha
    have h1 := mul_le_mul_of_nonneg_left (hqa' h) hb
    calc
      _ ≤ a*ε+b*ε := add_le_add h0 h1
      _ = ε := by rw [←add_mul,hab,one_mul]
  · exact prefix_system_convex (score D p) M r ε hM hqp hqp' ha hb hab

theorem known_anchor_conic_system_iff {m k : ℕ} (R : Set (Fin m → ℝ))
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ) (p : Fin k → ℝ)
    (q : Fin m → ℝ) (M r ε : ℝ) (hM : 0 < M) (ht : Antitone (score D p)) :
    q ∈ knownAnchorConicFeasible R K D p M r ε ↔
      q ∈ R ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
      ∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
        ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε := by
  constructor
  · rintro ⟨hqR,hq,hm,ha,hg,hp⟩
    refine ⟨hqR,hq,hm,?_⟩
    apply (known_anchor_prefix_characterization K D p q M r ε hM hq hm ht).mpr
    refine ⟨ha,hg,?_⟩
    intro l hl
    exact (quadratic_rotated_cone M r _ _ hM).mp (hp l hl)
  · rintro ⟨hqR,hq,hm,hB⟩
    obtain ⟨ha,hg,hp⟩ := (known_anchor_prefix_characterization K D p q M r ε hM hq hm ht).mp hB
    refine ⟨hqR,hq,hm,ha,hg,?_⟩
    intro l hl
    exact (quadratic_rotated_cone M r _ _ hM).mpr (hp l hl)


theorem linear_repertoire_convex {m : ℕ} {β : Type*} (F : Fin m → β → ℝ) (c : β → ℝ) :
    Convex ℝ {q : Fin m → ℝ | ∀ j, (∑ i, q i*F i j) ≤ c j} := by
  intro q hq q' hq' a b ha hb hab j
  have hs := finite_linear_mix Finset.univ q q' (fun i => F i j) a b
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [hs]
  calc
    _ ≤ a*c j+b*c j := add_le_add
      (mul_le_mul_of_nonneg_left (hq j) ha) (mul_le_mul_of_nonneg_left (hq' j) hb)
    _ = c j := by rw [←add_mul,hab,one_mul]

end
end SparseCompletion

/- Fixed source body: IntervalPerspective.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def perspectiveRecover (lo V q : ℝ) : ℝ := if q=0 then lo else V/q

theorem perspective_zero (lo hi V q : ℝ) (hq : q=0)
    (hlo : lo*q ≤ V) (hhi : V ≤ hi*q) : V=0 := by
  subst q
  simp only [mul_zero] at hlo hhi
  exact le_antisymm hhi hlo

theorem perspective_recover_bounds (lo hi V q : ℝ) (hq : 0 ≤ q) (hlu : lo ≤ hi)
    (hlo : lo*q ≤ V) (hhi : V ≤ hi*q) :
    lo ≤ perspectiveRecover lo V q ∧ perspectiveRecover lo V q ≤ hi ∧
      q*perspectiveRecover lo V q=V := by
  by_cases hz : q=0
  · have hv := perspective_zero lo hi V q hz hlo hhi
    simp only [perspectiveRecover,hz,ite_true,zero_mul]
    exact ⟨le_refl _,hlu,hv.symm⟩
  · have hp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    simp only [perspectiveRecover,ite_eq_right hz]
    refine ⟨(le_div_iff₀ hp).mpr hlo,(div_le_iff₀ hp).mpr hhi,?_⟩
    field_simp

def intervalCrossRecover {ι α : Type*} (lo V : ι → α → ℝ) (q : ι → ℝ) : ι → α → ℝ :=
  fun i h => perspectiveRecover (lo i h) (V i h) (q i)

def intervalMomentScore {ι α : Type*} [Fintype α] (p : α → ℝ) (V : ι → α → ℝ) : ι → ℝ :=
  fun i => ∑ h, p h*V i h

theorem interval_recovered_cross_bounds {ι α : Type*} (lo hi V : ι → α → ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hlu : ∀ i h, lo i h ≤ hi i h)
    (hlo : ∀ i h, lo i h*q i ≤ V i h) (hhi : ∀ i h, V i h ≤ hi i h*q i) :
    (∀ i h, lo i h ≤ intervalCrossRecover lo V q i h ∧ intervalCrossRecover lo V q i h ≤ hi i h) ∧
      ∀ i h, q i*intervalCrossRecover lo V q i h=V i h := by
  constructor
  · intro i h
    exact ⟨(perspective_recover_bounds _ _ _ _ (hq i) (hlu i h) (hlo i h) (hhi i h)).1,
      (perspective_recover_bounds _ _ _ _ (hq i) (hlu i h) (hlo i h) (hhi i h)).2.1⟩
  · intro i h
    exact (perspective_recover_bounds _ _ _ _ (hq i) (hlu i h) (hlo i h) (hhi i h)).2.2

theorem interval_recovered_score_moment {ι α : Type*} [Fintype α]
    (lo V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (hm : ∀ i h, q i*intervalCrossRecover lo V q i h=V i h) (i : ι) :
    q i*score (intervalCrossRecover lo V q) p i=intervalMomentScore p V i := by
  unfold score intervalMomentScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = p h*(q i*intervalCrossRecover lo V q i h) := by ring
    _ = _ := by rw [hm i h]

end
end SparseCompletion

/- Fixed source body: IntervalConic.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def perspectiveCuts {ι : Type*} [Fintype ι] (q H : ι → ℝ) (M r ε : ℝ) : Prop :=
  ∀ S : Finset ι, M*(mass S q)^2-M*r*mass S q+(∑ i ∈ S, (H i-ε*q i)) ≤ 0

theorem perspective_cuts_iff {ι : Type*} [Fintype ι] (q t H : ι → ℝ) (M r ε : ℝ)
    (hH : ∀ i, q i*t i=H i) :
    Cuts M r q (fun i => t i-ε) ↔ perspectiveCuts q H M r ε := by
  have he : ∀ S : Finset ι, (∑ i ∈ S, q i*(t i-ε))=∑ i ∈ S, (H i-ε*q i) := by
    intro S
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_sub,hH i,mul_comm (q i) ε]
  constructor <;> intro h S
  · have hc := h S
    rw [he] at hc
    nlinarith
  · have hc := h S
    rw [he]
    nlinarith

theorem anchor_response_of_perspective {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (hV : ∀ i h, q i*D i h=V i h) (h : α) :
    anchorResponse K D p q h=(∑ a, K h a*p a)-∑ i, V i h := by
  unfold anchorResponse
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, hV i h]

theorem score_lower_from_intervals {ι α : Type*} [Fintype α]
    (lo D : ι → α → ℝ) (p : α → ℝ) (hp : ∀ h, 0 ≤ p h)
    (hD : ∀ i h, lo i h ≤ D i h) (i : ι) : score lo p i ≤ score D p i := by
  unfold score
  exact Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hD i h) (hp h)

theorem interval_perspective_completion_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hr : ∑ i, q i=r) (hlu : ∀ i h, lo i h ≤ hi i h) :
    (∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧ IsSkew B ∧
      (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ V : ι → α → ℝ,
      (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
      (∀ h, (∑ a, K h a*p a)-(∑ i, V i h) ≤ ε) ∧
      (∀ i, score lo p i ≤ ε+M*r) ∧ perspectiveCuts q (intervalMomentScore p V) M r ε := by
  classical
  constructor
  · rintro ⟨D,B,hD,hB,hb,hrows⟩
    let V := fun i h => q i*D i h
    have hV : ∀ i h, q i*D i h=V i h := fun _ _ => rfl
    have hh := (block_response_bounds_iff K D B p q ε).mp hrows
    have hc := (weighted_completion_iff q (score D p) M r ε (le_of_lt hM) hq hr).mp
      ⟨B,hB,hb,hh.2⟩
    refine ⟨V,?_,?_,?_,?_⟩
    · intro i h
      exact ⟨by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).1) (hq i)],
        by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).2) (hq i)]⟩
    · intro h
      rw [←anchor_response_of_perspective K D V p q hV h]
      exact hh.1 h
    · intro i
      exact le_trans (score_lower_from_intervals lo D p hp (fun i h => (hD i h).1) i) (hc.1 i)
    · apply (perspective_cuts_iff q (score D p) (intervalMomentScore p V) M r ε ?_).mp hc.2
      intro i
      unfold score intervalMomentScore
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by dsimp only [V]; ring
  · rintro ⟨V,hV,ha,hg,hcuts⟩
    let D := intervalCrossRecover lo V q
    obtain ⟨hD,hprod⟩ := interval_recovered_cross_bounds lo hi V q hq hlu
      (fun i h => (hV i h).1) (fun i h => (hV i h).2)
    have hc : Cuts M r q (fun i => score D p i-ε) :=
      (perspective_cuts_iff q (score D p) (intervalMomentScore p V) M r ε
        (fun i => interval_recovered_score_moment lo V p q hprod i)).mpr hcuts
    have hguard : ∀ i, score D p i ≤ ε+M*r := by
      intro i
      by_cases hz : q i=0
      · have he : score D p i=score lo p i := by
          simp only [D,score,intervalCrossRecover,perspectiveRecover,hz,ite_true]
        rw [he]
        exact hg i
      · have ht := supported_score_cap q (fun i => score D p i-ε) M r hM hq hc i hz
        linarith
    obtain ⟨B,hB,hb,hrows⟩ :=
      (weighted_completion_iff q (score D p) M r ε (le_of_lt hM) hq hr).mpr ⟨hguard,hc⟩
    refine ⟨D,B,hD,hB,hb,?_⟩
    apply (block_response_bounds_iff K D B p q ε).mpr
    refine ⟨?_,hrows⟩
    intro h
    rw [anchor_response_of_perspective K D V p q hprod h]
    exact ha h

theorem normalized_interval_perspective_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hr : ∑ i, q i=r) (hpmass : (∑ h, p h)+r=1) (hK : IsSkew K)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) :
    (∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
      (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
      IsSkew (blockMatrix K D B) ∧
      (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ V : ι → α → ℝ,
      (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
      (∀ h, (∑ a, K h a*p a)-(∑ i, V i h) ≤ ε) ∧
      (∀ i, score lo p i ≤ ε+M*r) ∧ perspectiveCuts q (intervalMomentScore p V) M r ε := by
  constructor
  · rintro ⟨D,B,hD,_,_,hsk,hb,hrows⟩
    apply (interval_perspective_completion_iff K lo hi p q M r ε hM hp hq hr hlu).mp
    refine ⟨D,B,hD,?_,?_,hrows⟩
    · intro i j
      exact hsk (.inr i) (.inr j)
    · intro i j
      exact hb (.inr i) (.inr j)
  · intro h
    obtain ⟨D,B,hD,hB,hb,hrows⟩ :=
      (interval_perspective_completion_iff K lo hi p q M r ε hM hp hq hr hlu).mpr h
    have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun i h =>
      ⟨le_trans (hlo i h) (hD i h).1,le_trans (hD i h).2 (hhi i h)⟩
    refine ⟨D,B,hD,blockWeights_nonneg p q hp hq,?_,blockMatrix_skew K D B hK hB,
      blockMatrix_bounds K D B M hKb hDb hb,hrows⟩
    rw [blockWeights_mass,hr]
    exact hpmass

end
end SparseCompletion

/- Fixed source body: ObservationCover.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def offDiagonalIntervals {ν : Type*} (lo hi A : ν → ν → ℝ) : Prop :=
  ∀ a b, a ≠ b → lo a b ≤ A a b ∧ A a b ≤ hi a b

def freeResidualIntervals {ι α : Type*} (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M : ℝ) : Prop :=
  ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -M ∧ hi (.inr i) (.inr j)=M

def intervalConstraintEdge {ν : Type*} (lo hi : ν → ν → ℝ) (M : ℝ) (a b : ν) : Prop :=
  a ≠ b ∧ (lo a b ≠ -M ∨ hi a b ≠ M)

theorem free_residual_iff_anchor_cover {ι α : Type*}
    (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M : ℝ) :
    freeResidualIntervals lo hi M ↔
      ∀ a b, intervalConstraintEdge lo hi M a b →
        (∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h := by
  constructor
  · intro hc a b he
    cases a with
    | inl h => exact Or.inl ⟨h,rfl⟩
    | inr i =>
      cases b with
      | inl h => exact Or.inr ⟨h,rfl⟩
      | inr j =>
        have hij : i ≠ j := fun hij => he.1 (congrArg Sum.inr hij)
        have hh := hc i j hij
        exact False.elim (he.2.elim (fun hn => hn hh.1) (fun hn => hn hh.2))
  · intro hc i j hij
    have he : Sum.inr i ≠ (Sum.inr j : α ⊕ ι) := fun he => hij (Sum.inr.inj he)
    by_contra hn
    have hbad : lo (.inr i) (.inr j) ≠ -M ∨ hi (.inr i) (.inr j) ≠ M := by
      tauto
    obtain (⟨h,hh⟩ | ⟨h,hh⟩) := hc (.inr i) (.inr j) ⟨he,hbad⟩ <;> cases hh

theorem cover_intervals_preserved {ι α : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B B' : ι → ι → ℝ) (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M : ℝ)
    (hc : freeResidualIntervals lo hi M) (hI : offDiagonalIntervals lo hi (blockMatrix K D B))
    (hB' : ∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) :
    offDiagonalIntervals lo hi (blockMatrix K D B') := by
  intro a b hab
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact hI (.inl h) (.inl h') hab
    | inr j => exact hI (.inl h) (.inr j) hab
  | inr i =>
    cases b with
    | inl h => exact hI (.inr i) (.inl h) hab
    | inr j =>
      have hij : i ≠ j := fun he => hab (congrArg Sum.inr he)
      have hh := hc i j hij
      change lo (.inr i) (.inr j) ≤ B' i j ∧ B' i j ≤ hi (.inr i) (.inr j)
      rw [hh.1,hh.2]
      exact hB' i j

theorem anchor_incident_entries_preserved {ι α : Type*} (K : α → α → ℝ)
    (D : ι → α → ℝ) (B B' : ι → ι → ℝ) (a b : α ⊕ ι)
    (hc : (∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) :
    blockMatrix K D B' a b=blockMatrix K D B a b := by
  rcases hc with ⟨h,rfl⟩ | ⟨h,rfl⟩
  · cases b <;> rfl
  · cases a <;> rfl

end
end SparseCompletion

/- Fixed source body: CoveredWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hcover : freeResidualIntervals lo hi M)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_sparse_witness_extra_moments_all_mass k d K D F B p q M r ρ η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  refine ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows,?_,?_,?_⟩
  · exact cover_intervals_preserved K D B B' lo hi M hcover hI (fun i j => hb (.inr i) (.inr j))
  · intro a b hab
    exact anchor_incident_entries_preserved K D B B' a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

theorem normalized_exact_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hcover : freeResidualIntervals lo hi M)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_exact_sparse_witness_extra_moments_all_mass k d K D F B p q M r η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  refine ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows,?_,?_,?_⟩
  · exact cover_intervals_preserved K D B B' lo hi M hcover hI (fun i j => hb (.inr i) (.inr j))
  · intro a b hab
    exact anchor_incident_entries_preserved K D B B' a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

end
end SparseCompletion

/- Fixed source body: IntervalProjection.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def intervalClip (lo hi x : ℝ) : ℝ := max lo (min hi x)

def intervalLoss (M lo hi : ℝ) : ℝ := max (M+lo) (M-hi)

theorem interval_clip_bounds (lo hi x : ℝ) (hlu : lo ≤ hi) :
    lo ≤ intervalClip lo hi x ∧ intervalClip lo hi x ≤ hi := by
  unfold intervalClip
  exact ⟨le_max_left _ _,max_le hlu (min_le_left _ _)⟩

theorem interval_clip_neg (lo hi x : ℝ) (hlu : lo ≤ hi) :
    intervalClip (-hi) (-lo) (-x)= -intervalClip lo hi x := by
  unfold intervalClip
  by_cases hxl : x ≤ lo
  · rw [min_eq_left (neg_le_neg hxl),max_eq_right (neg_le_neg hlu),
      min_eq_right (le_trans hxl hlu),max_eq_left hxl]
  · by_cases hxu : hi ≤ x
    · rw [min_eq_right (neg_le_neg (le_trans hlu hxu)),max_eq_left (neg_le_neg hxu),
        min_eq_left hxu,max_eq_right hlu]
    · have hlx : lo ≤ x := le_of_not_ge hxl
      have hxh : x ≤ hi := le_of_not_ge hxu
      rw [min_eq_right (neg_le_neg hlx),max_eq_right (neg_le_neg hxh),
        min_eq_right hxh,max_eq_right hlx]

theorem interval_loss_nonnegative (M lo hi : ℝ) (hlo : -M ≤ lo) :
    0 ≤ intervalLoss M lo hi := by
  exact le_trans (by linarith) (le_max_left _ _)

theorem interval_clip_distance (M lo hi x : ℝ) (hx : -M ≤ x ∧ x ≤ M) (hlu : lo ≤ hi) (hlo : -M ≤ lo) :
    |intervalClip lo hi x-x| ≤ intervalLoss M lo hi := by
  unfold intervalClip intervalLoss
  by_cases hxl : x < lo
  · rw [min_eq_right (le_trans (le_of_lt hxl) hlu),max_eq_left (le_of_lt hxl),abs_of_nonneg (by linarith)]
    exact le_trans (by linarith [hx.1]) (le_max_left _ _)
  · by_cases hxu : hi < x
    · rw [min_eq_left (le_of_lt hxu),max_eq_right hlu,abs_of_nonpos (by linarith)]
      exact le_trans (by linarith [hx.2]) (le_max_right _ _)
    · rw [min_eq_right (le_of_not_gt hxu),max_eq_right (le_of_not_gt hxl),sub_self,abs_zero]
      have h0 : 0 ≤ M+lo := by linarith
      exact le_trans h0 (le_max_left _ _)

def projectedResidual {ι : Type*} (lo hi B : ι → ι → ℝ) : ι → ι → ℝ := by
  classical
  exact fun i j => if i=j then 0 else intervalClip (lo i j) (hi i j) (B i j)

theorem projected_residual_skew {ι : Type*} (lo hi B : ι → ι → ℝ)
    (hB : IsSkew B) (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j) (hrev : ∀ i j, i ≠ j → lo i j= -hi j i ∧ hi i j= -lo j i) :
    IsSkew (projectedResidual lo hi B) := by
  intro i j
  by_cases he : i=j
  · subst j
    simp only [projectedResidual,ite_true,neg_zero]
  · simp only [projectedResidual,ite_eq_right he,ite_eq_right (Ne.symm he)]
    rw [(hrev i j he).1,(hrev i j he).2,hB i j,interval_clip_neg _ _ _ (hlu j i (Ne.symm he))]

theorem projected_residual_interval {ι : Type*} (lo hi B : ι → ι → ℝ)
    (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j) :
    offDiagonalIntervals lo hi (projectedResidual lo hi B) := by
  intro i j he
  simp only [projectedResidual,ite_eq_right he]
  exact interval_clip_bounds _ _ _ (hlu i j he)

theorem projected_residual_bounds {ι : Type*} (lo hi B : ι → ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j) (hhi : ∀ i j, i ≠ j → hi i j ≤ M) :
    ∀ i j, -M ≤ projectedResidual lo hi B i j ∧ projectedResidual lo hi B i j ≤ M := by
  intro i j
  by_cases he : i=j
  · simp only [projectedResidual,ite_eq_left he]
    exact ⟨by linarith,hM⟩
  · have hh := interval_clip_bounds (lo i j) (hi i j) (B i j) (hlu i j he)
    simp only [projectedResidual,ite_eq_right he]
    exact ⟨le_trans (hlo i j he) hh.1,le_trans hh.2 (hhi i j he)⟩

theorem projected_residual_distance {ι : Type*} (lo hi B : ι → ι → ℝ) (M β : ℝ)
    (hβ : 0 ≤ β) (hB : IsSkew B) (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j)
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo i j) (hi i j) ≤ β) :
    ∀ i j, |projectedResidual lo hi B i j-B i j| ≤ β := by
  intro i j
  by_cases he : i=j
  · subst j
    have hz : B i i=0 := by linarith [hB i i]
    simp only [projectedResidual,ite_true,hz,sub_self,abs_zero]
    exact hβ
  · simp only [projectedResidual,ite_eq_right he]
    exact le_trans (interval_clip_distance M _ _ _ (hb i j) (hlu i j he) (hlo i j he)) (hloss i j he)

end
end SparseCompletion

/- Fixed source body: WeakCover.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem projected_block_intervals {ι α : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B B' : ι → ι → ℝ) (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B))
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j)) :
    offDiagonalIntervals lo hi (blockMatrix K D
      (projectedResidual (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) B')) := by
  intro a b hab
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact hI (.inl h) (.inl h') hab
    | inr j => exact hI (.inl h) (.inr j) hab
  | inr i =>
    cases b with
    | inl h => exact hI (.inr i) (.inl h) hab
    | inr j =>
      have hij : i ≠ j := fun he => hab (congrArg Sum.inr he)
      exact projected_residual_interval _ _ B' hlu i j hij

theorem residual_projection_response_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B lo hi : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M β r τ : ℝ)
    (hβ : 0 ≤ β) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hB : IsSkew B) (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j)
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo i j) (hi i j) ≤ β)
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ τ) :
    ∀ a, response (blockMatrix K D (projectedResidual lo hi B)) (blockWeights p q) a ≤ τ+β*r := by
  have hr : 0 ≤ r := by rw [←hm]; exact Finset.sum_nonneg fun i _ => hq i
  intro a
  cases a with
  | inl h =>
    rw [block_response_anchor]
    have ha := hrows (.inl h)
    rw [block_response_anchor] at ha
    exact le_trans ha (by nlinarith)
  | inr i =>
    rw [block_response_residual]
    have ha := hrows (.inr i)
    rw [block_response_residual] at ha
    have hp := response_perturbation (projectedResidual lo hi B) B q β r hq hm
      (projected_residual_distance lo hi B M β hβ hB hb hlu hlo hloss) i
    have hh := (abs_le.mp hp).2
    linarith

end
end SparseCompletion

/- Fixed source body: WeakCoverWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_weak_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η β : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hβ : 0 ≤ β)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo (.inr i) (.inr j)) (hi (.inr i) (.inr j)) ≤ β)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η+β*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_sparse_witness_extra_moments_all_mass k d K D F B p q M r ρ η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  let loR := fun i j => lo (Sum.inr i) (Sum.inr j)
  let hiR := fun i j => hi (Sum.inr i) (Sum.inr j)
  let C := projectedResidual loR hiR B'
  have hB' : IsSkew B' := fun i j => hsk (.inr i) (.inr j)
  have hb' : ∀ i j, -M ≤ B' i j ∧ B' i j ≤ M := fun i j => hb (.inr i) (.inr j)
  have hq'n : ∀ i, 0 ≤ q' i := fun i => hn (.inr i)
  have hq'm : ∑ i, q' i=r := by
    have hmass := blockWeights_mass p q'
    rw [hm] at hmass
    linarith
  have hC : IsSkew C := projected_residual_skew loR hiR B' hB' hlu hrev
  have hCb : ∀ i j, -M ≤ C i j ∧ C i j ≤ M :=
    projected_residual_bounds loR hiR B' M (le_of_lt hM) hlu hlo hhi
  have hCrows := residual_projection_response_bound K D B' loR hiR p q' M β r (ρ+η)
    hβ hq'n hq'm hB' hb' hlu hlo hloss hrows
  refine ⟨q',C,hn,hm,ha,hs,hc,ht,hD,hF,blockMatrix_skew K D C hK hC,
    blockMatrix_bounds K D C M hKb hDb hCb,hCrows,?_,?_,?_⟩
  · exact projected_block_intervals K D B B' lo hi hI hlu
  · intro a b hab
    exact anchor_incident_entries_preserved K D B C a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

theorem normalized_exact_weak_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η β : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hβ : 0 ≤ β)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo (.inr i) (.inr j)) (hi (.inr i) (.inr j)) ≤ β)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η+β*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_exact_sparse_witness_extra_moments_all_mass k d K D F B p q M r η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  let loR := fun i j => lo (Sum.inr i) (Sum.inr j)
  let hiR := fun i j => hi (Sum.inr i) (Sum.inr j)
  let C := projectedResidual loR hiR B'
  have hB' : IsSkew B' := fun i j => hsk (.inr i) (.inr j)
  have hb' : ∀ i j, -M ≤ B' i j ∧ B' i j ≤ M := fun i j => hb (.inr i) (.inr j)
  have hq'n : ∀ i, 0 ≤ q' i := fun i => hn (.inr i)
  have hq'm : ∑ i, q' i=r := by
    have hmass := blockWeights_mass p q'
    rw [hm] at hmass
    linarith
  have hC : IsSkew C := projected_residual_skew loR hiR B' hB' hlu hrev
  have hCb : ∀ i j, -M ≤ C i j ∧ C i j ≤ M :=
    projected_residual_bounds loR hiR B' M (le_of_lt hM) hlu hlo hhi
  have hCrows := residual_projection_response_bound K D B' loR hiR p q' M β r η
    hβ hq'n hq'm hB' hb' hlu hlo hloss hrows
  refine ⟨q',C,hn,hm,ha,hs,hc,ht,hD,hF,blockMatrix_skew K D C hK hC,
    blockMatrix_bounds K D C M hKb hDb hCb,hCrows,?_,?_,?_⟩
  · exact projected_block_intervals K D B B' lo hi hI hlu
  · intro a b hab
    exact anchor_incident_entries_preserved K D B C a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

end
end SparseCompletion

/- Fixed source body: IntervalLossMaximum.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_loss_bounds (M lo hi : ℝ) (hlo : -M ≤ lo) (hhi : hi ≤ M) (hlu : lo ≤ hi) :
    0 ≤ intervalLoss M lo hi ∧ intervalLoss M lo hi ≤ (2 : ℕ)*M := by
  refine ⟨interval_loss_nonnegative M lo hi hlo,?_⟩
  unfold intervalLoss
  norm_num only [Nat.cast_ofNat]
  exact max_le (by nlinarith) (by nlinarith)

theorem interval_loss_zero_iff (M lo hi : ℝ) (hlo : -M ≤ lo) (hhi : hi ≤ M) :
    intervalLoss M lo hi=0 ↔ lo= -M ∧ hi=M := by
  constructor
  · intro h
    have h0 : M+lo ≤ 0 := by rw [←h]; exact le_max_left _ _
    have h1 : M-hi ≤ 0 := by rw [←h]; exact le_max_right _ _
    constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    simp only [intervalLoss,add_neg_cancel,sub_self,max_self]

def residualLossValues {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) : Finset ℝ := by
  classical
  exact insert 0 ((Finset.univ.filter fun ij : ι × ι => ij.1 ≠ ij.2).image
    fun ij => intervalLoss M (lo ij.1 ij.2) (hi ij.1 ij.2))

theorem residual_loss_values_nonempty {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) :
    (residualLossValues lo hi M).Nonempty := by
  classical
  unfold residualLossValues
  exact ⟨0,Finset.mem_insert_self _ _⟩

def residualLossBound {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) : ℝ :=
  (residualLossValues lo hi M).max' (residual_loss_values_nonempty lo hi M)

theorem residual_loss_bound_nonnegative {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) :
    0 ≤ residualLossBound lo hi M := by
  classical
  unfold residualLossBound
  apply Finset.le_max'
  unfold residualLossValues
  exact Finset.mem_insert_self _ _

theorem residual_loss_le_bound {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ)
    (i j : ι) (hij : i ≠ j) : intervalLoss M (lo i j) (hi i j) ≤ residualLossBound lo hi M := by
  classical
  unfold residualLossBound
  apply Finset.le_max'
  unfold residualLossValues
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,rfl⟩

theorem residual_loss_bound_le {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hlo : ∀ i j, i ≠ j → -M ≤ lo i j)
    (hhi : ∀ i j, i ≠ j → hi i j ≤ M) (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j) :
    residualLossBound lo hi M ≤ (2 : ℕ)*M := by
  classical
  unfold residualLossBound
  apply Finset.max'_le
  intro x hx
  unfold residualLossValues at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · positivity
  · obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hx
    have he := (Finset.mem_filter.mp hij).2
    exact (interval_loss_bounds M (lo i j) (hi i j) (hlo i j he) (hhi i j he) (hlu i j he)).2

theorem residual_loss_bound_le_iff {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M β : ℝ) :
    residualLossBound lo hi M ≤ β ↔ 0 ≤ β ∧
      ∀ i j, i ≠ j → intervalLoss M (lo i j) (hi i j) ≤ β := by
  classical
  constructor
  · intro h
    exact ⟨le_trans (residual_loss_bound_nonnegative lo hi M) h,
      fun i j hij => le_trans (residual_loss_le_bound lo hi M i j hij) h⟩
  · rintro ⟨hβ,h⟩
    unfold residualLossBound
    apply Finset.max'_le
    intro x hx
    unfold residualLossValues at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hβ
    · obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hx
      exact h i j (Finset.mem_filter.mp hij).2

theorem residual_loss_bound_zero_iff {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j) (hhi : ∀ i j, i ≠ j → hi i j ≤ M) :
    residualLossBound lo hi M=0 ↔ ∀ i j, i ≠ j → lo i j= -M ∧ hi i j=M := by
  constructor
  · intro h i j hij
    apply (interval_loss_zero_iff M _ _ (hlo i j hij) (hhi i j hij)).mp
    apply le_antisymm
    · rw [←h]
      exact residual_loss_le_bound lo hi M i j hij
    · exact interval_loss_nonnegative M _ _ (hlo i j hij)
  · intro h
    apply le_antisymm
    · apply (residual_loss_bound_le_iff lo hi M 0).mpr
      refine ⟨le_refl _,?_⟩
      intro i j hij
      have hz := (interval_loss_zero_iff M _ _ (hlo i j hij) (hhi i j hij)).mpr (h i j hij)
      exact le_of_eq hz
    · exact residual_loss_bound_nonnegative lo hi M

end
end SparseCompletion

/- Fixed source body: WeakCoverMaximum.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_weak_cover_maximum {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η+(residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M)*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  exact normalized_weak_cover_witness k d K D F B p q M r ρ η
    (residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M) hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp lo hi
    (residual_loss_bound_nonnegative _ _ M) hlu hlo hhi hrev
    (fun i j hij => residual_loss_le_bound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M i j hij) hI

theorem normalized_exact_weak_cover_maximum {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η+(residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M)*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  exact normalized_exact_weak_cover_witness k d K D F B p q M r η
    (residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M) hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp lo hi
    (residual_loss_bound_nonnegative _ _ M) hlu hlo hhi hrev
    (fun i j hij => residual_loss_le_bound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M i j hij) hI

end
end SparseCompletion

/- Fixed source body: CoverRelabel.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def relabelWeights {ν μ : Type*} (e : ν ≃ μ) (q : ν → ℝ) : μ → ℝ := fun i => q (e.symm i)

def relabelMatrix {ν μ : Type*} (e : ν ≃ μ) (A : ν → ν → ℝ) : μ → μ → ℝ :=
  fun i j => A (e.symm i) (e.symm j)

theorem relabel_mass {ν μ : Type*} [Fintype ν] [Fintype μ] (e : ν ≃ μ) (q : ν → ℝ) :
    (∑ i, relabelWeights e q i)=∑ i, q i := Equiv.sum_comp e.symm q

theorem relabel_response {ν μ : Type*} [Fintype ν] [Fintype μ] (e : ν ≃ μ)
    (A : ν → ν → ℝ) (q : ν → ℝ) (i : μ) :
    response (relabelMatrix e A) (relabelWeights e q) i=response A q (e.symm i) := by
  exact Equiv.sum_comp e.symm (fun j => A (e.symm i) j*q j)

theorem relabel_support_card {ν μ : Type*} [Fintype ν] [Fintype μ] (e : ν ≃ μ) (q : ν → ℝ) :
    (Finset.univ.filter fun i => relabelWeights e q i ≠ 0).card=
      (Finset.univ.filter fun i => q i ≠ 0).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Equiv.sum_comp e.symm (fun j => if q j ≠ 0 then (1 : ℕ) else 0)

theorem relabel_skew {ν μ : Type*} (e : ν ≃ μ) (A : ν → ν → ℝ) (hA : IsSkew A) :
    IsSkew (relabelMatrix e A) := fun i j => hA (e.symm i) (e.symm j)

theorem relabel_intervals {ν μ : Type*} (e : ν ≃ μ) (lo hi A : ν → ν → ℝ) :
    offDiagonalIntervals (relabelMatrix e lo) (relabelMatrix e hi) (relabelMatrix e A) ↔
      offDiagonalIntervals lo hi A := by
  constructor
  · intro h i j hij
    have hne : e i ≠ e j := fun he => hij (e.injective he)
    simpa only [relabelMatrix,e.symm_apply_apply] using h (e i) (e j) hne
  · intro h i j hij
    exact h (e.symm i) (e.symm j) (fun he => hij (e.symm.injective he))

def coverEquiv {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] :
    (Fin (Fintype.card C) ⊕ (Cᶜ : Set ν)) ≃ ν :=
   (Equiv.sumCongr (Fintype.equivFin C).symm (Equiv.refl _)).trans (Equiv.Set.sumCompl C)

theorem cover_equiv_anchor {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] (h : Fin (Fintype.card C)) :
    coverEquiv C (.inl h) ∈ C := by
  change ((Fintype.equivFin C).symm h).val ∈ C
  exact ((Fintype.equivFin C).symm h).property

theorem cover_equiv_residual {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] (i : (Cᶜ : Set ν)) :
    coverEquiv C (.inr i)=i.val := rfl

theorem cover_equiv_inverse_anchor {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] (v : ν) (hv : v ∈ C) :
    ∃ h, (coverEquiv C).symm v=Sum.inl h := by
  classical
  cases he : (coverEquiv C).symm v with
  | inl h => exact ⟨h,rfl⟩
  | inr i =>
    have hh : v=i.val := by
      have h0 := congrArg (coverEquiv C) he
      simpa only [Equiv.apply_symm_apply,cover_equiv_residual] using h0
    exact False.elim (i.property (hh ▸ hv))

def intervalVertexCover {ν : Type*} (C : Set ν) (lo hi : ν → ν → ℝ) (M : ℝ) : Prop :=
  ∀ i j, intervalConstraintEdge lo hi M i j → i ∈ C ∨ j ∈ C

theorem arbitrary_cover_free_residual {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (lo hi : ν → ν → ℝ) (M : ℝ) (hc : intervalVertexCover C lo hi M) :
    freeResidualIntervals (relabelMatrix (coverEquiv C).symm lo)
      (relabelMatrix (coverEquiv C).symm hi) M := by
  intro i j hij
  have hv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  by_contra hn
  have hbad : lo i.val j.val ≠ -M ∨ hi i.val j.val ≠ M := by
    change ¬(lo i.val j.val= -M ∧ hi i.val j.val=M) at hn
    tauto
  rcases hc i.val j.val ⟨hv,hbad⟩ with h | h
  · exact i.property h
  · exact j.property h

theorem split_weights {ν α ι : Type*} (e : (α ⊕ ι) ≃ ν) (x : ν → ℝ) :
    relabelWeights e.symm x=blockWeights (fun h => x (e (.inl h))) (fun i => x (e (.inr i))) := by
  funext a
  cases a <;> rfl

theorem split_skew_matrix {ν α ι : Type*} (e : (α ⊕ ι) ≃ ν) (A : ν → ν → ℝ) (hA : IsSkew A) :
    relabelMatrix e.symm A=blockMatrix (fun h h' => A (e (.inl h)) (e (.inl h')))
      (fun i h => A (e (.inr i)) (e (.inl h))) (fun i j => A (e (.inr i)) (e (.inr j))) := by
  funext a b
  cases a with
  | inl h =>
    cases b with
    | inl h' => rfl
    | inr j => exact hA _ _
  | inr i => cases b <;> rfl

theorem cover_relabel_on_residual {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (p : Fin (Fintype.card C) → ℝ) (q : (Cᶜ : Set ν) → ℝ) (i : (Cᶜ : Set ν)) :
    relabelWeights (coverEquiv C) (blockWeights p q) i.val=q i := by
  rw [←cover_equiv_residual C i]
  simp only [relabelWeights,Equiv.symm_apply_apply,blockWeights,Sum.elim_inr]

theorem cover_relabel_on_anchor {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (x : ν → ℝ) (q : (Cᶜ : Set ν) → ℝ) (v : ν) (hv : v ∈ C) :
    relabelWeights (coverEquiv C)
      (blockWeights (fun h => x (coverEquiv C (.inl h))) q) v=x v := by
  obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
  have hv' : v=coverEquiv C (.inl h) := by
    have hh := congrArg (coverEquiv C) he
    simpa only [Equiv.apply_symm_apply] using hh
  rw [hv']
  simp only [relabelWeights,Equiv.symm_apply_apply,blockWeights,Sum.elim_inl]

end
end SparseCompletion

/- Fixed source body: ArbitraryCover.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem arbitrary_vertex_cover_sparse {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hcover : intervalVertexCover C lo hi M) (hresp : ∀ i, response A x i ≤ ρ) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ ρ+η) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  let e := coverEquiv C
  let k := Fintype.card C
  let p := fun h : Fin k => x (e (.inl h))
  let q := fun i : (Cᶜ : Set ν) => x (e (.inr i))
  let r := ∑ i, q i
  let K := fun h h' : Fin k => A (e (.inl h)) (e (.inl h'))
  let D := fun (i : (Cᶜ : Set ν)) (h : Fin k) => A (e (.inr i)) (e (.inl h))
  let B := fun i j : (Cᶜ : Set ν) => A (e (.inr i)) (e (.inr j))
  let lo' := relabelMatrix e.symm lo
  let hi' := relabelMatrix e.symm hi
  have hxsplit : relabelWeights e.symm x=blockWeights p q := split_weights e x
  have hAsplit : relabelMatrix e.symm A=blockMatrix K D B := split_skew_matrix e A hA
  have hp : ∀ h, 0 ≤ p h := fun h => hn _
  have hq : ∀ i, 0 ≤ q i := fun i => hn _
  have hr : 0 ≤ r := Finset.sum_nonneg fun i _ => hq i
  have hpm : (∑ h, p h)+r=1 := by
    change (∑ h, p h)+(∑ i, q i)=1
    rw [←blockWeights_mass,←hxsplit,relabel_mass]
    exact hm
  have hK : IsSkew K := fun h h' => hA _ _
  have hB : IsSkew B := fun i j => hA _ _
  have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun _ _ => hb _ _
  have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun _ _ => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun _ _ => hb _ _
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ := by
    intro a
    rw [←hAsplit,←hxsplit,relabel_response]
    exact hresp _
  have hIv : offDiagonalIntervals lo' hi' (blockMatrix K D B) := by
    rw [←hAsplit]
    exact (relabel_intervals e.symm lo hi A).mpr hI
  obtain ⟨q',B',hqn,hqm,hpa,hs,hc,ht,_,hF,hsk,hbb,hresponse,hInt,hentries,hanchors⟩ :=
    normalized_cover_witness k d K D (fun i g => F i.val g) B p q M r ρ η hM hr hη hp hq hpm rfl
      hK hB hKb hDb hBb hrows lo' hi' (arbitrary_cover_free_residual C lo hi M hcover) hIv
  let A' := relabelMatrix e (blockMatrix K D B')
  let x' := relabelWeights e (blockWeights p q')
  have hres : ∀ i : (Cᶜ : Set ν), x' i.val=q' i := cover_relabel_on_residual C p q'
  have hdim : Fintype.card ν=k+Fintype.card (Cᶜ : Set ν) := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_sum,Fintype.card_fin] using hh.symm
  have hrform : r=∑ i : (Cᶜ : Set ν), x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg x (cover_equiv_residual C i)
  refine ⟨A',x',?_,?_,relabel_skew e _ hsk,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun i => hqn (e.symm i)
  · rw [relabel_mass]
    exact hqm
  · exact fun i j => hbb (e.symm i) (e.symm j)
  · intro i j hij
    have he : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simpa only [A',lo',hi',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hInt _ _ he
  · intro i
    rw [relabel_response]
    exact hresponse _
  · exact cover_relabel_on_anchor C x q'
  · intro v hv hz
    let i : (Cᶜ : Set ν) := ⟨v,hv⟩
    have hqi : q i=0 := by change x (e (.inr i))=0; rw [cover_equiv_residual]; exact hz
    exact (hres i).trans (hs i hqi)
  · have hcard : (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i.val ≠ 0)=
        Finset.univ.filter (fun i => q' i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hres]
    rw [hcard]
    simpa only [←hrform] using hc
  · rw [relabel_support_card]
    simpa only [←hrform,hdim] using ht
  · intro a b hab
    have he : (∃ h, e.symm a=Sum.inl h) ∨ ∃ h, e.symm b=Sum.inl h := by
      rcases hab with h | h
      · exact Or.inl (cover_equiv_inverse_anchor C a h)
      · exact Or.inr (cover_equiv_inverse_anchor C b h)
    have hh := hentries (e.symm a) (e.symm b) he
    rw [←hAsplit] at hh
    simpa only [A',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hh
  · intro v hv
    obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
    have hh := hanchors h
    rw [←hAsplit,←hxsplit,relabel_response] at hh
    change response A' x' v=response A x v
    rw [relabel_response,he]
    have hv' : e (.inl h)=v := by rw [←he]; exact e.apply_symm_apply v
    simpa only [Equiv.symm_symm,hv'] using hh
  · intro g
    simpa only [hres,q,e,cover_equiv_residual] using hF g

theorem arbitrary_vertex_cover_exact {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hcover : intervalVertexCover C lo hi M) (hresp : ∀ i, response A x i ≤ 0) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ η) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  let e := coverEquiv C
  let k := Fintype.card C
  let p := fun h : Fin k => x (e (.inl h))
  let q := fun i : (Cᶜ : Set ν) => x (e (.inr i))
  let r := ∑ i, q i
  let K := fun h h' : Fin k => A (e (.inl h)) (e (.inl h'))
  let D := fun (i : (Cᶜ : Set ν)) (h : Fin k) => A (e (.inr i)) (e (.inl h))
  let B := fun i j : (Cᶜ : Set ν) => A (e (.inr i)) (e (.inr j))
  let lo' := relabelMatrix e.symm lo
  let hi' := relabelMatrix e.symm hi
  have hxsplit : relabelWeights e.symm x=blockWeights p q := split_weights e x
  have hAsplit : relabelMatrix e.symm A=blockMatrix K D B := split_skew_matrix e A hA
  have hp : ∀ h, 0 ≤ p h := fun h => hn _
  have hq : ∀ i, 0 ≤ q i := fun i => hn _
  have hr : 0 ≤ r := Finset.sum_nonneg fun i _ => hq i
  have hpm : (∑ h, p h)+r=1 := by
    change (∑ h, p h)+(∑ i, q i)=1
    rw [←blockWeights_mass,←hxsplit,relabel_mass]
    exact hm
  have hK : IsSkew K := fun h h' => hA _ _
  have hB : IsSkew B := fun i j => hA _ _
  have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun _ _ => hb _ _
  have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun _ _ => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun _ _ => hb _ _
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0 := by
    intro a
    rw [←hAsplit,←hxsplit,relabel_response]
    exact hresp _
  have hIv : offDiagonalIntervals lo' hi' (blockMatrix K D B) := by
    rw [←hAsplit]
    exact (relabel_intervals e.symm lo hi A).mpr hI
  obtain ⟨q',B',hqn,hqm,hpa,hs,hc,ht,_,hF,hsk,hbb,hresponse,hInt,hentries,hanchors⟩ :=
    normalized_exact_cover_witness k d K D (fun i g => F i.val g) B p q M r η hM hr hη hp hq hpm rfl
      hK hB hKb hDb hBb hrows lo' hi' (arbitrary_cover_free_residual C lo hi M hcover) hIv
  let A' := relabelMatrix e (blockMatrix K D B')
  let x' := relabelWeights e (blockWeights p q')
  have hres : ∀ i : (Cᶜ : Set ν), x' i.val=q' i := cover_relabel_on_residual C p q'
  have hdim : Fintype.card ν=k+Fintype.card (Cᶜ : Set ν) := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_sum,Fintype.card_fin] using hh.symm
  have hrform : r=∑ i : (Cᶜ : Set ν), x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg x (cover_equiv_residual C i)
  refine ⟨A',x',?_,?_,relabel_skew e _ hsk,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun i => hqn (e.symm i)
  · rw [relabel_mass]
    exact hqm
  · exact fun i j => hbb (e.symm i) (e.symm j)
  · intro i j hij
    have he : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simpa only [A',lo',hi',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hInt _ _ he
  · intro i
    rw [relabel_response]
    exact hresponse _
  · exact cover_relabel_on_anchor C x q'
  · intro v hv hz
    let i : (Cᶜ : Set ν) := ⟨v,hv⟩
    have hqi : q i=0 := by change x (e (.inr i))=0; rw [cover_equiv_residual]; exact hz
    exact (hres i).trans (hs i hqi)
  · have hcard : (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i.val ≠ 0)=
        Finset.univ.filter (fun i => q' i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hres]
    rw [hcard]
    simpa only [←hrform] using hc
  · rw [relabel_support_card]
    simpa only [←hrform,hdim] using ht
  · intro a b hab
    have he : (∃ h, e.symm a=Sum.inl h) ∨ ∃ h, e.symm b=Sum.inl h := by
      rcases hab with h | h
      · exact Or.inl (cover_equiv_inverse_anchor C a h)
      · exact Or.inr (cover_equiv_inverse_anchor C b h)
    have hh := hentries (e.symm a) (e.symm b) he
    rw [←hAsplit] at hh
    simpa only [A',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hh
  · intro v hv
    obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
    have hh := hanchors h
    rw [←hAsplit,←hxsplit,relabel_response] at hh
    change response A' x' v=response A x v
    rw [relabel_response,he]
    have hv' : e (.inl h)=v := by rw [←he]; exact e.apply_symm_apply v
    simpa only [Equiv.symm_symm,hv'] using hh
  · intro g
    simpa only [hres,q,e,cover_equiv_residual] using hF g

end
end SparseCompletion

/- Fixed source body: ArbitraryWeakCover.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem arbitrary_vertex_subset_weak_sparse {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hlo : ∀ a b, a ≠ b → -M ≤ lo a b) (hhi : ∀ a b, a ≠ b → hi a b ≤ M)
    (hlu : ∀ a b, a ≠ b → lo a b ≤ hi a b)
    (hrev : ∀ a b, a ≠ b → lo a b= -hi b a ∧ hi a b= -lo b a) (hresp : ∀ i, response A x i ≤ ρ) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    let β := residualLossBound (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
      (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ ρ+η+β*r) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  let e := coverEquiv C
  let k := Fintype.card C
  let p := fun h : Fin k => x (e (.inl h))
  let q := fun i : (Cᶜ : Set ν) => x (e (.inr i))
  let r := ∑ i, q i
  let K := fun h h' : Fin k => A (e (.inl h)) (e (.inl h'))
  let D := fun (i : (Cᶜ : Set ν)) (h : Fin k) => A (e (.inr i)) (e (.inl h))
  let B := fun i j : (Cᶜ : Set ν) => A (e (.inr i)) (e (.inr j))
  let lo' := relabelMatrix e.symm lo
  let hi' := relabelMatrix e.symm hi
  have hxsplit : relabelWeights e.symm x=blockWeights p q := split_weights e x
  have hAsplit : relabelMatrix e.symm A=blockMatrix K D B := split_skew_matrix e A hA
  have hp : ∀ h, 0 ≤ p h := fun h => hn _
  have hq : ∀ i, 0 ≤ q i := fun i => hn _
  have hr : 0 ≤ r := Finset.sum_nonneg fun i _ => hq i
  have hpm : (∑ h, p h)+r=1 := by
    change (∑ h, p h)+(∑ i, q i)=1
    rw [←blockWeights_mass,←hxsplit,relabel_mass]
    exact hm
  have hK : IsSkew K := fun h h' => hA _ _
  have hB : IsSkew B := fun i j => hA _ _
  have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun _ _ => hb _ _
  have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun _ _ => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun _ _ => hb _ _
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ := by
    intro a
    rw [←hAsplit,←hxsplit,relabel_response]
    exact hresp _
  have hIv : offDiagonalIntervals lo' hi' (blockMatrix K D B) := by
    rw [←hAsplit]
    exact (relabel_intervals e.symm lo hi A).mpr hI
  have heinj : ∀ i j : (Cᶜ : Set ν), i ≠ j → e (.inr i) ≠ e (.inr j) :=
    fun i j hij he => hij (Sum.inr.inj (e.injective he))
  have hrlu : ∀ i j, i ≠ j → lo' (.inr i) (.inr j) ≤ hi' (.inr i) (.inr j) :=
    fun i j hij => hlu _ _ (heinj i j hij)
  have hrlo : ∀ i j, i ≠ j → -M ≤ lo' (.inr i) (.inr j) :=
    fun i j hij => hlo _ _ (heinj i j hij)
  have hrhi : ∀ i j, i ≠ j → hi' (.inr i) (.inr j) ≤ M :=
    fun i j hij => hhi _ _ (heinj i j hij)
  have hrrev : ∀ i j, i ≠ j → lo' (.inr i) (.inr j)= -hi' (.inr j) (.inr i) ∧
      hi' (.inr i) (.inr j)= -lo' (.inr j) (.inr i) :=
    fun i j hij => hrev _ _ (heinj i j hij)
  obtain ⟨q',B',hqn,hqm,hpa,hs,hc,ht,_,hF,hsk,hbb,hresponse,hInt,hentries,hanchors⟩ :=
    normalized_weak_cover_maximum k d K D (fun i g => F i.val g) B p q M r ρ η hM hr hη hp hq hpm rfl
      hK hB hKb hDb hBb hrows lo' hi' hrlu hrlo hrhi hrrev hIv
  let A' := relabelMatrix e (blockMatrix K D B')
  let x' := relabelWeights e (blockWeights p q')
  have hres : ∀ i : (Cᶜ : Set ν), x' i.val=q' i := cover_relabel_on_residual C p q'
  have hdim : Fintype.card ν=k+Fintype.card (Cᶜ : Set ν) := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_sum,Fintype.card_fin] using hh.symm
  have hrform : r=∑ i : (Cᶜ : Set ν), x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg x (cover_equiv_residual C i)
  refine ⟨A',x',?_,?_,relabel_skew e _ hsk,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun i => hqn (e.symm i)
  · rw [relabel_mass]
    exact hqm
  · exact fun i j => hbb (e.symm i) (e.symm j)
  · intro i j hij
    have he : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simpa only [A',lo',hi',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hInt _ _ he
  · intro i
    rw [relabel_response]
    exact hresponse _
  · exact cover_relabel_on_anchor C x q'
  · intro v hv hz
    let i : (Cᶜ : Set ν) := ⟨v,hv⟩
    have hqi : q i=0 := by change x (e (.inr i))=0; rw [cover_equiv_residual]; exact hz
    exact (hres i).trans (hs i hqi)
  · have hcard : (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i.val ≠ 0)=
        Finset.univ.filter (fun i => q' i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hres]
    rw [hcard]
    simpa only [←hrform] using hc
  · rw [relabel_support_card]
    simpa only [←hrform,hdim] using ht
  · intro a b hab
    have he : (∃ h, e.symm a=Sum.inl h) ∨ ∃ h, e.symm b=Sum.inl h := by
      rcases hab with h | h
      · exact Or.inl (cover_equiv_inverse_anchor C a h)
      · exact Or.inr (cover_equiv_inverse_anchor C b h)
    have hh := hentries (e.symm a) (e.symm b) he
    rw [←hAsplit] at hh
    simpa only [A',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hh
  · intro v hv
    obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
    have hh := hanchors h
    rw [←hAsplit,←hxsplit,relabel_response] at hh
    change response A' x' v=response A x v
    rw [relabel_response,he]
    have hv' : e (.inl h)=v := by rw [←he]; exact e.apply_symm_apply v
    simpa only [Equiv.symm_symm,hv'] using hh
  · intro g
    simpa only [hres,q,e,cover_equiv_residual] using hF g

theorem arbitrary_vertex_subset_weak_exact {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hlo : ∀ a b, a ≠ b → -M ≤ lo a b) (hhi : ∀ a b, a ≠ b → hi a b ≤ M)
    (hlu : ∀ a b, a ≠ b → lo a b ≤ hi a b)
    (hrev : ∀ a b, a ≠ b → lo a b= -hi b a ∧ hi a b= -lo b a) (hresp : ∀ i, response A x i ≤ 0) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    let β := residualLossBound (fun i j : (Cᶜ : Set ν) => lo i.val j.val)
      (fun i j : (Cᶜ : Set ν) => hi i.val j.val) M
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ η+β*r) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  let e := coverEquiv C
  let k := Fintype.card C
  let p := fun h : Fin k => x (e (.inl h))
  let q := fun i : (Cᶜ : Set ν) => x (e (.inr i))
  let r := ∑ i, q i
  let K := fun h h' : Fin k => A (e (.inl h)) (e (.inl h'))
  let D := fun (i : (Cᶜ : Set ν)) (h : Fin k) => A (e (.inr i)) (e (.inl h))
  let B := fun i j : (Cᶜ : Set ν) => A (e (.inr i)) (e (.inr j))
  let lo' := relabelMatrix e.symm lo
  let hi' := relabelMatrix e.symm hi
  have hxsplit : relabelWeights e.symm x=blockWeights p q := split_weights e x
  have hAsplit : relabelMatrix e.symm A=blockMatrix K D B := split_skew_matrix e A hA
  have hp : ∀ h, 0 ≤ p h := fun h => hn _
  have hq : ∀ i, 0 ≤ q i := fun i => hn _
  have hr : 0 ≤ r := Finset.sum_nonneg fun i _ => hq i
  have hpm : (∑ h, p h)+r=1 := by
    change (∑ h, p h)+(∑ i, q i)=1
    rw [←blockWeights_mass,←hxsplit,relabel_mass]
    exact hm
  have hK : IsSkew K := fun h h' => hA _ _
  have hB : IsSkew B := fun i j => hA _ _
  have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun _ _ => hb _ _
  have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun _ _ => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun _ _ => hb _ _
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0 := by
    intro a
    rw [←hAsplit,←hxsplit,relabel_response]
    exact hresp _
  have hIv : offDiagonalIntervals lo' hi' (blockMatrix K D B) := by
    rw [←hAsplit]
    exact (relabel_intervals e.symm lo hi A).mpr hI
  have heinj : ∀ i j : (Cᶜ : Set ν), i ≠ j → e (.inr i) ≠ e (.inr j) :=
    fun i j hij he => hij (Sum.inr.inj (e.injective he))
  have hrlu : ∀ i j, i ≠ j → lo' (.inr i) (.inr j) ≤ hi' (.inr i) (.inr j) :=
    fun i j hij => hlu _ _ (heinj i j hij)
  have hrlo : ∀ i j, i ≠ j → -M ≤ lo' (.inr i) (.inr j) :=
    fun i j hij => hlo _ _ (heinj i j hij)
  have hrhi : ∀ i j, i ≠ j → hi' (.inr i) (.inr j) ≤ M :=
    fun i j hij => hhi _ _ (heinj i j hij)
  have hrrev : ∀ i j, i ≠ j → lo' (.inr i) (.inr j)= -hi' (.inr j) (.inr i) ∧
      hi' (.inr i) (.inr j)= -lo' (.inr j) (.inr i) :=
    fun i j hij => hrev _ _ (heinj i j hij)
  obtain ⟨q',B',hqn,hqm,hpa,hs,hc,ht,_,hF,hsk,hbb,hresponse,hInt,hentries,hanchors⟩ :=
    normalized_exact_weak_cover_maximum k d K D (fun i g => F i.val g) B p q M r η hM hr hη hp hq hpm rfl
      hK hB hKb hDb hBb hrows lo' hi' hrlu hrlo hrhi hrrev hIv
  let A' := relabelMatrix e (blockMatrix K D B')
  let x' := relabelWeights e (blockWeights p q')
  have hres : ∀ i : (Cᶜ : Set ν), x' i.val=q' i := cover_relabel_on_residual C p q'
  have hdim : Fintype.card ν=k+Fintype.card (Cᶜ : Set ν) := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_sum,Fintype.card_fin] using hh.symm
  have hrform : r=∑ i : (Cᶜ : Set ν), x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg x (cover_equiv_residual C i)
  refine ⟨A',x',?_,?_,relabel_skew e _ hsk,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun i => hqn (e.symm i)
  · rw [relabel_mass]
    exact hqm
  · exact fun i j => hbb (e.symm i) (e.symm j)
  · intro i j hij
    have he : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simpa only [A',lo',hi',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hInt _ _ he
  · intro i
    rw [relabel_response]
    exact hresponse _
  · exact cover_relabel_on_anchor C x q'
  · intro v hv hz
    let i : (Cᶜ : Set ν) := ⟨v,hv⟩
    have hqi : q i=0 := by change x (e (.inr i))=0; rw [cover_equiv_residual]; exact hz
    exact (hres i).trans (hs i hqi)
  · have hcard : (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i.val ≠ 0)=
        Finset.univ.filter (fun i => q' i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hres]
    rw [hcard]
    simpa only [←hrform] using hc
  · rw [relabel_support_card]
    simpa only [←hrform,hdim] using ht
  · intro a b hab
    have he : (∃ h, e.symm a=Sum.inl h) ∨ ∃ h, e.symm b=Sum.inl h := by
      rcases hab with h | h
      · exact Or.inl (cover_equiv_inverse_anchor C a h)
      · exact Or.inr (cover_equiv_inverse_anchor C b h)
    have hh := hentries (e.symm a) (e.symm b) he
    rw [←hAsplit] at hh
    simpa only [A',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hh
  · intro v hv
    obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
    have hh := hanchors h
    rw [←hAsplit,←hxsplit,relabel_response] at hh
    change response A' x' v=response A x v
    rw [relabel_response,he]
    have hv' : e (.inl h)=v := by rw [←he]; exact e.apply_symm_apply v
    simpa only [Equiv.symm_symm,hv'] using hh
  · intro g
    simpa only [hres,q,e,cover_equiv_residual] using hF g

end
end SparseCompletion

/- Fixed source body: IntervalLossOrder.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_loss_reverse (M lo hi : ℝ) :
    intervalLoss M (-hi) (-lo)=intervalLoss M lo hi := by
  unfold intervalLoss
  have h1 : M- -lo=M+lo := by ring
  have h2 : M+ -hi=M-hi := by ring
  rw [h1,h2]
  exact max_comm _ _

def orderedResidualLossValues {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ) : Finset ℝ := by
  classical
  exact insert 0 ((Finset.univ.filter fun ij : ι × ι => ij.1 < ij.2).image
    fun ij => intervalLoss M (lo ij.1 ij.2) (hi ij.1 ij.2))

theorem ordered_loss_values_nonempty {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ) : (orderedResidualLossValues lo hi M).Nonempty := by
  classical
  unfold orderedResidualLossValues
  exact ⟨0,Finset.mem_insert_self _ _⟩

def orderedResidualLossBound {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ) : ℝ :=
  (orderedResidualLossValues lo hi M).max' (ordered_loss_values_nonempty lo hi M)

theorem residual_loss_values_ordered {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ)
    (hrev : ∀ i j, i ≠ j → lo i j= -hi j i ∧ hi i j= -lo j i) :
    residualLossValues lo hi M=orderedResidualLossValues lo hi M := by
  classical
  ext z
  simp only [residualLossValues,orderedResidualLossValues,Finset.mem_insert,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ⟨⟨i,j⟩,hij,hz⟩)
    · exact Or.inl rfl
    · apply Or.inr
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨(i,j),h,hz⟩
      · refine ⟨(j,i),h,?_⟩
        have hs : intervalLoss M (lo i j) (hi i j)=intervalLoss M (lo j i) (hi j i) := by
          rw [(hrev i j hij).1,(hrev i j hij).2,interval_loss_reverse]
        exact hs.symm.trans hz
  · rintro (rfl | ⟨⟨i,j⟩,hij,hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨(i,j),ne_of_lt hij,hz⟩

theorem residual_loss_bound_ordered {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ)
    (hrev : ∀ i j, i ≠ j → lo i j= -hi j i ∧ hi i j= -lo j i) :
    residualLossBound lo hi M=orderedResidualLossBound lo hi M := by
  unfold residualLossBound orderedResidualLossBound
  have hs := residual_loss_values_ordered lo hi M hrev
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    exact Finset.le_max' _ _ (hs ▸ hx)
  · apply Finset.max'_le
    intro x hx
    exact Finset.le_max' _ _ (hs.symm ▸ hx)

end
end SparseCompletion

/- Fixed source body: IntervalConvexity.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem perspective_quadratic_mix {ι : Type*} (S : Finset ι)
    (q q' H H' : ι → ℝ) (M r ε a b : ℝ)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    M*(mass S (a • q+b • q'))^2-M*r*mass S (a • q+b • q')+
      (∑ i ∈ S, ((a*H i+b*H' i)-ε*(a*q i+b*q' i))) ≤
      a*(M*(mass S q)^2-M*r*mass S q+(∑ i ∈ S, (H i-ε*q i)))+
      b*(M*(mass S q')^2-M*r*mass S q'+(∑ i ∈ S, (H' i-ε*q' i))) := by
  rw [finite_mass_mix]
  have he : (∑ i ∈ S, ((a*H i+b*H' i)-ε*(a*q i+b*q' i)))=
      a*(∑ i ∈ S, (H i-ε*q i))+b*(∑ i ∈ S, (H' i-ε*q' i)) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  have hid : M*(a*mass S q+b*mass S q')^2-M*r*(a*mass S q+b*mass S q')+
      (a*(∑ i ∈ S, (H i-ε*q i))+b*(∑ i ∈ S, (H' i-ε*q' i)))=
      a*(M*(mass S q)^2-M*r*mass S q+(∑ i ∈ S, (H i-ε*q i)))+
      b*(M*(mass S q')^2-M*r*mass S q'+(∑ i ∈ S, (H' i-ε*q' i)))-
      M*a*b*(mass S q-mass S q')^2 := by
    have hb' : b=1-a := by linarith
    rw [hb']
    ring
  rw [hid]
  exact sub_le_self _ (by positivity)

theorem perspective_cuts_mix {ι : Type*} [Fintype ι]
    (q q' H H' : ι → ℝ) (M r ε a b : ℝ)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (h : perspectiveCuts q H M r ε) (h' : perspectiveCuts q' H' M r ε) :
    perspectiveCuts (a • q+b • q') (a • H+b • H') M r ε := by
  intro S
  have hm := perspective_quadratic_mix S q q' H H' M r ε a b hM ha hb hab
  have h1 := mul_nonpos_of_nonneg_of_nonpos ha (h S)
  have h2 := mul_nonpos_of_nonneg_of_nonpos hb (h' S)
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using le_trans hm (by linarith)

theorem perspective_cut_system_convex {ι : Type*} [Fintype ι]
    (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {z : (ι → ℝ) × (ι → ℝ) | perspectiveCuts z.1 z.2 M r ε} := by
  intro z hz z' hz' a b ha hb hab
  exact perspective_cuts_mix z.1 z'.1 z.2 z'.2 M r ε a b hM ha hb hab hz hz'

theorem interval_moment_mix {ι α : Type*} [Fintype α]
    (p : α → ℝ) (V V' : ι → α → ℝ) (a b : ℝ) :
    intervalMomentScore p (a • V+b • V')=
      a • intervalMomentScore p V+b • intervalMomentScore p V' := by
  funext i
  unfold intervalMomentScore
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem interval_perspective_cut_system_convex {ι α : Type*} [Fintype ι] [Fintype α]
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {z : (ι → ℝ) × (ι → α → ℝ) |
      perspectiveCuts z.1 (intervalMomentScore p z.2) M r ε} := by
  intro z hz z' hz' a b ha hb hab
  change perspectiveCuts (a • z.1+b • z'.1)
    (intervalMomentScore p (a • z.2+b • z'.2)) M r ε
  rw [interval_moment_mix]
  exact perspective_cuts_mix z.1 z'.1 (intervalMomentScore p z.2)
    (intervalMomentScore p z'.2) M r ε a b hM ha hb hab hz hz'

def intervalPerspectiveSystem {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ)
    (z : (ι → ℝ) × (ι → α → ℝ) × (α → α → ℝ)) : Prop :=
  (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i)=r ∧
  (∀ i h, lo i h*z.1 i ≤ z.2.1 i h ∧ z.2.1 i h ≤ hi i h*z.1 i) ∧
  (∀ h, (∑ a, z.2.2 h a*p a)-(∑ i, z.2.1 i h) ≤ ε) ∧
  IsSkew z.2.2 ∧ (∀ h h', coreLo h h' ≤ z.2.2 h h' ∧ z.2.2 h h' ≤ coreHi h h') ∧
  (∀ i, score lo p i ≤ ε+M*r) ∧ perspectiveCuts z.1 (intervalMomentScore p z.2.1) M r ε

theorem interval_perspective_system_convex {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {z | intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z} := by
  intro z hz z' hz' a b ha hb hab
  rcases hz with ⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩
  rcases hz' with ⟨hq',hr',hV',hA',hK',hC',_,hcuts'⟩
  change intervalPerspectiveSystem lo hi coreLo coreHi p M r ε
    (a • z.1+b • z'.1, a • z.2.1+b • z'.2.1, a • z.2.2+b • z'.2.2)
  refine ⟨?_,?_,?_,?_,?_,?_,hg,?_⟩
  · intro i
    change 0 ≤ a*z.1 i+b*z'.1 i
    exact add_nonneg (mul_nonneg ha (hq i)) (mul_nonneg hb (hq' i))
  · change (∑ i, (a*z.1 i+b*z'.1 i))=r
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hr,hr',←add_mul,hab,one_mul]
  · intro i h
    change lo i h*(a*z.1 i+b*z'.1 i) ≤ a*z.2.1 i h+b*z'.2.1 i h ∧
      a*z.2.1 i h+b*z'.2.1 i h ≤ hi i h*(a*z.1 i+b*z'.1 i)
    have h1 := mul_le_mul_of_nonneg_left (hV i h).1 ha
    have h2 := mul_le_mul_of_nonneg_left (hV' i h).1 hb
    have h3 := mul_le_mul_of_nonneg_left (hV i h).2 ha
    have h4 := mul_le_mul_of_nonneg_left (hV' i h).2 hb
    constructor <;> nlinarith
  · intro h
    change (∑ c, (a*z.2.2 h c+b*z'.2.2 h c)*p c)-(∑ i, (a*z.2.1 i h+b*z'.2.1 i h)) ≤ ε
    rw [finite_linear_mix]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hA h) ha
    have h2 := mul_le_mul_of_nonneg_left (hA' h) hb
    have he : a*ε+b*ε=ε := by rw [←add_mul,hab,one_mul]
    nlinarith
  · intro h h'
    change a*z.2.2 h h'+b*z'.2.2 h h'= -(a*z.2.2 h' h+b*z'.2.2 h' h)
    rw [hK h h',hK' h h']
    ring
  · intro h h'
    change coreLo h h' ≤ a*z.2.2 h h'+b*z'.2.2 h h' ∧
      a*z.2.2 h h'+b*z'.2.2 h h' ≤ coreHi h h'
    have h1 := mul_le_mul_of_nonneg_left (hC h h').1 ha
    have h2 := mul_le_mul_of_nonneg_left (hC' h h').1 hb
    have h3 := mul_le_mul_of_nonneg_left (hC h h').2 ha
    have h4 := mul_le_mul_of_nonneg_left (hC' h h').2 hb
    have hlo : a*coreLo h h'+b*coreLo h h'=coreLo h h' := by rw [←add_mul,hab,one_mul]
    have hhi : a*coreHi h h'+b*coreHi h h'=coreHi h h' := by rw [←add_mul,hab,one_mul]
    constructor <;> linarith
  · rw [interval_moment_mix]
    exact perspective_cuts_mix z.1 z'.1 (intervalMomentScore p z.2.1)
      (intervalMomentScore p z'.2.1) M r ε a b hM ha hb hab hcuts hcuts'

theorem variable_core_interval_completion_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h)
    (hpmass : (∑ h, p h)+r=1)
    (hclo : ∀ h h', -M ≤ coreLo h h') (hchi : ∀ h h', coreHi h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) :
    (∃ (q : ι → ℝ) (K : α → α → ℝ),
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧ IsSkew K ∧
      (∀ h h', coreLo h h' ≤ K h h' ∧ K h h' ≤ coreHi h h') ∧
      ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
        (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
        (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
        IsSkew (blockMatrix K D B) ∧
        (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
        ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ z, intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z := by
  constructor
  · rintro ⟨q,K,hq,hr,hK,hC,hgame⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    obtain ⟨V,hV,hA,hg,hcuts⟩ :=
      (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
        hK hKb hlo hhi hlu).mp hgame
    exact ⟨(q,V,K),hq,hr,hV,hA,hK,hC,hg,hcuts⟩
  · rintro ⟨⟨q,V,K⟩,hq,hr,hV,hA,hK,hC,hg,hcuts⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    refine ⟨q,K,hq,hr,hK,hC,?_⟩
    exact (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
      hK hKb hlo hhi hlu).mpr ⟨V,hV,hA,hg,hcuts⟩

theorem interval_system_repertoire_convex {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 ≤ M)
    (R : Set (ι → ℝ)) (hR : Convex ℝ R) :
    Convex ℝ {z | intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z ∧ z.1 ∈ R} := by
  intro z hz z' hz' a b ha hb hab
  exact ⟨interval_perspective_system_convex lo hi coreLo coreHi p M r ε hM
    hz.1 hz'.1 ha hb hab,hR hz.2 hz'.2 ha hb hab⟩

theorem residual_linear_repertoire_convex {ι κ : Type*} [Fintype ι]
    (F : κ → ι → ℝ) (b : κ → ℝ) :
    Convex ℝ {q : ι → ℝ | ∀ c, (∑ i, q i*F c i) ≤ b c} := by
  intro q hq q' hq' a d ha hd had c
  change (∑ i, (a*q i+d*q' i)*F c i) ≤ b c
  rw [finite_linear_mix]
  have h1 := mul_le_mul_of_nonneg_left (hq c) ha
  have h2 := mul_le_mul_of_nonneg_left (hq' c) hd
  have he : a*b c+d*b c=b c := by rw [←add_mul,had,one_mul]
  linarith

end
end SparseCompletion

/- Fixed source body: GapCertificates.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def fixedAnchorGapPoint {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i, score D p i ≤ ρ+M*r) ∧ (∀ h, anchorResponse K D p q h ≤ ρ) ∧
  ∀ l : ℕ, 1 ≤ l → l ≤ gridSize M r η →
    call q (fun i => score D p i-ρ) (M*r-gridNode M r η l) ≤
      envelope M r (M*r-gridNode M r η l)

theorem exact_completion_gap_point {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r ρ η : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r) (hB : IsSkew B)
    (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    fixedAnchorGapPoint K D p q M r ρ η := by
  have hh := (block_response_bounds_iff K D B p q ρ).mp hrows
  have hc := (weighted_completion_iff q (score D p) M r ρ (le_of_lt hM) hq hr).mp
    ⟨B,hB,hb,hh.2⟩
  refine ⟨hq,hr,hc.1,hh.1,?_⟩
  intro l _ _
  exact cuts_imply_call_bound q (fun i => score D p i-ρ) M r hM hc.2 _

theorem gap_point_completed_witness {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ B : ι → ι → ℝ, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ+η := by
  rcases h with ⟨hq,hm,hg,ha,hgrid⟩
  have hcap : ∀ i, q i ≠ 0 → score D p i-ρ ≤ M*r := fun i _ => by linarith [hg i]
  have hc := canonical_grid_implication q (fun i => score D p i-ρ) M r η hM hr hη hq hcap hgrid
  have hcuts := call_bound_implies_cuts q (fun i => (score D p i-ρ)-η) M r hM hq hm hc
  have he : (fun i => (score D p i-ρ)-η)=(fun i => score D p i-(ρ+η)) := by
    funext i
    ring
  rw [he] at hcuts
  obtain ⟨B,hB,hb,hres⟩ :=
    (weighted_completion_iff q (score D p) M r (ρ+η) (le_of_lt hM) hq hm).mpr
      ⟨fun i => by linarith [hg i],hcuts⟩
  refine ⟨B,hB,hb,?_⟩
  apply (block_response_bounds_iff K D B p q (ρ+η)).mpr
  exact ⟨fun h => le_trans (ha h) (by linarith),hres⟩

theorem shifted_call_antitone {ι : Type*} [Fintype ι]
    (q t : ι → ℝ) (ρ ρ' z : ℝ) (hq : ∀ i, 0 ≤ q i) (hρ : ρ ≤ ρ') :
    call q (fun i => t i-ρ') z ≤ call q (fun i => t i-ρ) z := by
  unfold call
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hq i)
  exact max_le_max (by linarith) (le_refl 0)

theorem fixed_anchor_gap_monotone {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ ρ' η : ℝ) (hρ : ρ ≤ ρ')
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    fixedAnchorGapPoint K D p q M r ρ' η := by
  rcases h with ⟨hq,hm,hg,ha,hgrid⟩
  refine ⟨hq,hm,fun i => by linarith [hg i],fun h => le_trans (ha h) hρ,?_⟩
  intro l hl hH
  exact le_trans (shifted_call_antitone q (score D p) ρ ρ' _ hq hρ) (hgrid l hl hH)

end
end SparseCompletion

/- Fixed source body: GapFeasibility.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def fixedAnchorFeasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ : ℝ) : Prop :=
  ∃ q ∈ R, (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
    ∃ B : ι → ι → ℝ, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ

def fixedAnchorGapFeasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) : Prop :=
  ∃ q ∈ R, fixedAnchorGapPoint K D p q M r ρ η

theorem feasible_implies_gap_feasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) (hM : 0 < M)
    (h : fixedAnchorFeasible R K D p M r ρ) :
    fixedAnchorGapFeasible R K D p M r ρ η := by
  rcases h with ⟨q,hR,hq,hr,B,hB,hb,hrows⟩
  exact ⟨q,hR,exact_completion_gap_point K D B p q M r ρ η hM hq hr hB hb hrows⟩

theorem gap_feasible_implies_relaxed_feasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (h : fixedAnchorGapFeasible R K D p M r ρ η) :
    fixedAnchorFeasible R K D p M r (ρ+η) := by
  rcases h with ⟨q,hR,hpoint⟩
  exact ⟨q,hR,hpoint.1,hpoint.2.1,gap_point_completed_witness K D p q M r ρ η hM hr hη hpoint⟩

theorem gap_infeasible_excludes_completion {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) (hM : 0 < M)
    (h : ¬fixedAnchorGapFeasible R K D p M r ρ η) :
    ¬fixedAnchorFeasible R K D p M r ρ :=
  fun hf => h (feasible_implies_gap_feasible R K D p M r ρ η hM hf)

theorem gap_feasibility_monotone {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ ρ' η : ℝ) (hρ : ρ ≤ ρ')
    (h : fixedAnchorGapFeasible R K D p M r ρ η) :
    fixedAnchorGapFeasible R K D p M r ρ' η := by
  rcases h with ⟨q,hR,hpoint⟩
  exact ⟨q,hR,fixed_anchor_gap_monotone K D p q M r ρ ρ' η hρ hpoint⟩

end
end SparseCompletion

/- Fixed source body: IntervalRepertoire.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem repertoire_interval_completion_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h)
    (hpmass : (∑ h, p h)+r=1)
    (hclo : ∀ h h', -M ≤ coreLo h h') (hchi : ∀ h h', coreHi h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) (R : Set (ι → ℝ)) :
    (∃ (q : ι → ℝ) (K : α → α → ℝ),
      q ∈ R ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧ IsSkew K ∧
      (∀ h h', coreLo h h' ≤ K h h' ∧ K h h' ≤ coreHi h h') ∧
      ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
        (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
        (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
        IsSkew (blockMatrix K D B) ∧
        (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
        ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ z, intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z ∧ z.1 ∈ R := by
  constructor
  · rintro ⟨q,K,hR,hq,hr,hK,hC,hgame⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    obtain ⟨V,hV,hA,hg,hcuts⟩ :=
      (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
        hK hKb hlo hhi hlu).mp hgame
    exact ⟨(q,V,K),⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩,hR⟩
  · rintro ⟨⟨q,V,K⟩,⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩,hR⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    refine ⟨q,K,hR,hq,hr,hK,hC,?_⟩
    exact (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
      hK hKb hlo hhi hlu).mpr ⟨V,hV,hA,hg,hcuts⟩

end
end SparseCompletion

/- Fixed source body: IntervalStability.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_clip_endpoint_distance (lo hi lo' hi' x δ : ℝ)
    (hx : lo ≤ x ∧ x ≤ hi) (hlu' : lo' ≤ hi') (hδ : 0 ≤ δ)
    (hl : |lo-lo'| ≤ δ) (hu : |hi-hi'| ≤ δ) :
    |intervalClip lo' hi' x-x| ≤ δ := by
  obtain ⟨hl1,hl2⟩ := abs_le.mp hl
  obtain ⟨hu1,hu2⟩ := abs_le.mp hu
  unfold intervalClip
  by_cases hxl : x < lo'
  · rw [min_eq_right (le_trans (le_of_lt hxl) hlu'),max_eq_left (le_of_lt hxl),
      abs_of_nonneg (by linarith)]
    linarith [hx.1]
  · by_cases hxu : hi' < x
    · rw [min_eq_left (le_of_lt hxu),max_eq_right hlu',abs_of_nonpos (by linarith)]
      linarith [hx.2]
    · rw [min_eq_right (le_of_not_gt hxu),max_eq_right (le_of_not_gt hxl),sub_self,abs_zero]
      exact hδ

theorem interval_system_projection_distance {ν : Type*} (lo hi lo' hi' A : ν → ν → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hA : IsSkew A) (hI : offDiagonalIntervals lo hi A)
    (hlu' : ∀ i j, i ≠ j → lo' i j ≤ hi' i j)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    ∀ i j, |A i j-projectedResidual lo' hi' A i j| ≤ δ := by
  intro i j
  by_cases he : i=j
  · subst j
    have hz : A i i=0 := by have h := hA i i; linarith
    simp only [projectedResidual,ite_true,hz,sub_self,abs_zero]
    exact hδ
  · simp only [projectedResidual,ite_eq_right he]
    rw [abs_sub_comm]
    exact interval_clip_endpoint_distance _ _ _ _ _ _ (hI i j he) (hlu' i j he) hδ
      (hd i j he).1 (hd i j he).2

def exploitability {ν : Type*} [Fintype ν] [Nonempty ν] (A : ν → ν → ℝ) (x : ν → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (response A x)

theorem exploitability_le_iff {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (v : ℝ) :
    exploitability A x ≤ v ↔ ∀ i, response A x i ≤ v := by
  unfold exploitability
  simp only [Finset.sup'_le_iff,Finset.mem_univ,true_implies]

theorem response_le_exploitability {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (i : ν) : response A x i ≤ exploitability A x :=
  Finset.le_sup' (response A x) (Finset.mem_univ i)

theorem exploitability_perturbation {ν : Type*} [Fintype ν] [Nonempty ν]
    (A B : ν → ν → ℝ) (x : ν → ℝ) (δ r : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=r) (hAB : ∀ i j, |A i j-B i j| ≤ δ) :
    |exploitability A x-exploitability B x| ≤ δ*r := by
  apply abs_le.mpr
  constructor
  · have h : exploitability B x ≤ exploitability A x+δ*r := by
      apply (exploitability_le_iff B x _).mpr
      intro i
      have hp := (abs_le.mp (response_perturbation A B x δ r hx hm hAB i)).1
      linarith [response_le_exploitability A x i]
    linarith
  · have h : exploitability A x ≤ exploitability B x+δ*r := by
      apply (exploitability_le_iff A x _).mpr
      intro i
      have hp := (abs_le.mp (response_perturbation A B x δ r hx hm hAB i)).2
      linarith [response_le_exploitability B x i]
    linarith

theorem exploitability_continuous {ν : Type*} [Fintype ν] [Nonempty ν] :
    Continuous (fun z : (ν → ν → ℝ) × (ν → ℝ) => exploitability z.1 z.2) := by
  unfold exploitability
  apply Continuous.finset_sup'_apply
  intro i _
  unfold response
  fun_prop

end
end SparseCompletion

/- Fixed source body: OptimisticValue.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def ValidIntervalSystem {ν : Type*} (lo hi : ν → ν → ℝ) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ i j, i ≠ j → -M ≤ lo i j ∧ lo i j ≤ hi i j ∧ hi i j ≤ M ∧
    lo i j= -hi j i ∧ hi i j= -lo j i

def intervalMatrices {ν : Type*} (lo hi : ν → ν → ℝ) (M : ℝ) : Set (ν → ν → ℝ) :=
  skewBox M ∩ {A | offDiagonalIntervals lo hi A}

theorem interval_matrices_compact {ν : Type*} [Fintype ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) : IsCompact (intervalMatrices lo hi M) := by
  apply (skewBox_compact M).inter_right
  have he : {A : ν → ν → ℝ | offDiagonalIntervals lo hi A}=
      ⋂ i, ⋂ j, ⋂ (_h : i ≠ j), {A | lo i j ≤ A i j ∧ A i j ≤ hi i j} := by
    ext A
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,offDiagonalIntervals]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  change IsClosed ({A : ν → ν → ℝ | lo i j ≤ A i j} ∩ {A | A i j ≤ hi i j})
  exact (isClosed_le continuous_const
    (show Continuous (fun A : ν → ν → ℝ => A i j) by fun_prop)).inter
    (isClosed_le (show Continuous (fun A : ν → ν → ℝ => A i j) by fun_prop) continuous_const)

theorem interval_matrices_nonempty {ν : Type*}
    (lo hi : ν → ν → ℝ) (M : ℝ) (h : ValidIntervalSystem lo hi M) :
    (intervalMatrices lo hi M).Nonempty := by
  let A := projectedResidual lo hi (fun _ _ => 0)
  have hzero : IsSkew (fun _ _ : ν => (0 : ℝ)) := by intro _ _; exact neg_zero.symm
  have hlu := fun i j he => (h.2 i j he).2.1
  have hlo := fun i j he => (h.2 i j he).1
  have hhi := fun i j he => (h.2 i j he).2.2.1
  have hrev := fun i j he => (h.2 i j he).2.2.2
  exact ⟨A,⟨projected_residual_skew lo hi _ hzero hlu hrev,
    projected_residual_bounds lo hi _ M h.1 hlu hlo hhi⟩,
    projected_residual_interval lo hi _ hlu⟩

def optimisticValue {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ)) : ℝ :=
  sInf ((fun z : (ν → ν → ℝ) × (ν → ℝ) => exploitability z.1 z.2) ''
    (intervalMatrices lo hi M ×ˢ X))

theorem optimistic_value_attained {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hX : IsCompact X) (hne : X.Nonempty) :
    ∃ A ∈ intervalMatrices lo hi M, ∃ x ∈ X, exploitability A x=optimisticValue lo hi M X := by
  have hc := ((interval_matrices_compact lo hi M).prod hX).image exploitability_continuous
  have hn := ((interval_matrices_nonempty lo hi M hI).prod hne).image
    (fun z : (ν → ν → ℝ) × (ν → ℝ) => exploitability z.1 z.2)
  obtain ⟨⟨A,x⟩,⟨hA,hx⟩,he⟩ := hc.sInf_mem hn
  exact ⟨A,hA,x,hx,he⟩

theorem optimistic_value_le_witness {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ)) (hX : IsCompact X)
    (A : ν → ν → ℝ) (x : ν → ℝ) (hA : A ∈ intervalMatrices lo hi M) (hx : x ∈ X) :
    optimisticValue lo hi M X ≤ exploitability A x := by
  apply csInf_le (((interval_matrices_compact lo hi M).prod hX).image exploitability_continuous).bddBelow
  exact ⟨(A,x),⟨hA,hx⟩,rfl⟩

end
end SparseCompletion

/- Fixed source body: ValueStability.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_matrices_projection {ν : Type*}
    (lo hi lo' hi' A : ν → ν → ℝ) (M : ℝ)
    (hI' : ValidIntervalSystem lo' hi' M) (hA : A ∈ intervalMatrices lo hi M) :
    projectedResidual lo' hi' A ∈ intervalMatrices lo' hi' M := by
  have hlu := fun i j he => (hI'.2 i j he).2.1
  have hlo := fun i j he => (hI'.2 i j he).1
  have hhi := fun i j he => (hI'.2 i j he).2.2.1
  have hrev := fun i j he => (hI'.2 i j he).2.2.2
  exact ⟨⟨projected_residual_skew lo' hi' A hA.1.1 hlu hrev,
    projected_residual_bounds lo' hi' A M hI'.1 hlu hlo hhi⟩,
    projected_residual_interval lo' hi' A hlu⟩

theorem optimistic_value_projection_bound {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : X.Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    optimisticValue lo' hi' M X ≤ optimisticValue lo hi M X+δ := by
  obtain ⟨A,hA,x,hx,he⟩ := optimistic_value_attained lo hi M X hI hX hne
  let A' := projectedResidual lo' hi' A
  have hA' : A' ∈ intervalMatrices lo' hi' M := interval_matrices_projection lo hi lo' hi' A M hI' hA
  have hdist := interval_system_projection_distance lo hi lo' hi' A δ hδ hA.1.1 hA.2
    (fun i j hij => (hI'.2 i j hij).2.1) hd
  have hp := exploitability_perturbation A A' x δ 1 (hprob x hx).1 (hprob x hx).2 hdist
  have hv := optimistic_value_le_witness lo' hi' M X hX A' x hA' hx
  have hb := (abs_le.mp hp).1
  rw [he] at hb
  nlinarith

theorem optimistic_value_interval_stability {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : X.Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M X-optimisticValue lo' hi' M X| ≤ δ := by
  have h1 := optimistic_value_projection_bound lo hi lo' hi' M δ X hI hI' hδ hX hne hprob hd
  have hd' : ∀ i j, i ≠ j → |lo' i j-lo i j| ≤ δ ∧ |hi' i j-hi i j| ≤ δ := by
    intro i j hij
    constructor
    · rw [abs_sub_comm]; exact (hd i j hij).1
    · rw [abs_sub_comm]; exact (hd i j hij).2
  have h2 := optimistic_value_projection_bound lo' hi' lo hi M δ X hI' hI hδ hX hne hprob hd'
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end SparseCompletion

/- Fixed source body: SupportCompact.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def supportBudget {ν : Type*} [Fintype ν] (s : ℕ) : Set (ν → ℝ) := by
  classical
  exact {x | (Finset.univ.filter fun i => x i ≠ 0).card ≤ s}

theorem support_budget_closed {ν : Type*} [Fintype ν] (s : ℕ) :
    IsClosed (supportBudget (ν := ν) s) := by
  classical
  have he : supportBudget (ν := ν) s=
      ⋃ S : {S : Finset ν // S.card ≤ s}, {x : ν → ℝ | ∀ i, i ∉ S.val → x i=0} := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨⟨Finset.univ.filter (fun i => x i ≠ 0),h⟩,?_⟩
      intro i hi
      by_contra hx
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩)
    · rintro ⟨S,hS⟩
      apply le_trans (Finset.card_le_card ?_) S.property
      intro i hi
      by_contra hn
      exact (Finset.mem_filter.mp hi).2 (hS i hn)
  rw [he]
  apply isClosed_iUnion_of_finite
  intro S
  have hz : {x : ν → ℝ | ∀ i, i ∉ S.val → x i=0}=
      ⋂ i, ⋂ (_hi : i ∉ S.val), {x : ν → ℝ | x i=0} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
  rw [hz]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i) continuous_const

theorem support_restricted_compact {ν : Type*} [Fintype ν]
    (X : Set (ν → ℝ)) (hX : IsCompact X) (s : ℕ) : IsCompact (X ∩ supportBudget s) :=
  hX.inter_right (support_budget_closed s)

theorem optimistic_support_value_attained {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ)) (s : ℕ)
    (hI : ValidIntervalSystem lo hi M) (hX : IsCompact X)
    (hne : (X ∩ supportBudget s).Nonempty) :
    ∃ A ∈ intervalMatrices lo hi M, ∃ x ∈ X ∩ supportBudget s,
      exploitability A x=optimisticValue lo hi M (X ∩ supportBudget s) :=
  optimistic_value_attained lo hi M _ hI (support_restricted_compact X hX s) hne

theorem optimistic_support_value_stability {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ)) (s : ℕ)
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : (X ∩ supportBudget s).Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M (X ∩ supportBudget s)-optimisticValue lo' hi' M (X ∩ supportBudget s)| ≤ δ :=
  optimistic_value_interval_stability lo hi lo' hi' M δ _ hI hI' hδ
    (support_restricted_compact X hX s) hne (fun x hx => hprob x hx.1) hd

end
end SparseCompletion

/- Fixed source body: OrderedStability.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem endpoint_bounds_from_order {ν : Type*} [LinearOrder ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ)
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hd : ∀ i j, i < j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hd i j h
  · have hh := hd j i h
    have h1 := (hI.2 i j hij).2.2.2
    have h2 := (hI'.2 i j hij).2.2.2
    rw [h1.1,h1.2,h2.1,h2.2]
    constructor
    · simpa only [neg_sub_neg,abs_sub_comm] using hh.2
    · simpa only [neg_sub_neg,abs_sub_comm] using hh.1

theorem optimistic_value_ordered_interval_stability {ν : Type*}
    [Fintype ν] [Nonempty ν] [LinearOrder ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : X.Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i < j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M X-optimisticValue lo' hi' M X| ≤ δ :=
  optimistic_value_interval_stability lo hi lo' hi' M δ X hI hI' hδ hX hne hprob
    (endpoint_bounds_from_order lo hi lo' hi' M δ hI hI' hd)

theorem optimistic_support_value_ordered_stability {ν : Type*}
    [Fintype ν] [Nonempty ν] [LinearOrder ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ)) (s : ℕ)
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : (X ∩ supportBudget s).Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i < j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M (X ∩ supportBudget s)-optimisticValue lo' hi' M (X ∩ supportBudget s)| ≤ δ :=
  optimistic_support_value_stability lo hi lo' hi' M δ X s hI hI' hδ hX hne hprob
    (endpoint_bounds_from_order lo hi lo' hi' M δ hI hI' hd)

end
end SparseCompletion

/- Fixed source body: ThresholdSeparation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def positiveScoreSet {ι : Type*} [Fintype ι] (q v : ι → ℝ) (z : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => q i ≠ 0 ∧ 0 < v i-z

def weightedUpperSet {ι : Type*} [Fintype ι] (q v : ι → ℝ) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun j => q j ≠ 0 ∧ v i ≤ v j

theorem positive_score_threshold {ι : Type*} [Fintype ι] (q v : ι → ℝ) (z : ℝ)
    (hs : (positiveScoreSet q v z).Nonempty) :
    ∃ i, q i ≠ 0 ∧ positiveScoreSet q v z=weightedUpperSet q v i := by
  classical
  let s := positiveScoreSet q v z
  obtain ⟨i,hi,hmin⟩ := Set.exists_min_image (s : Set ι) v s.finite_toSet hs
  have hip := (Finset.mem_filter.mp hi).2
  refine ⟨i,hip.1,?_⟩
  ext j
  simp only [positiveScoreSet,weightedUpperSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hq,hv⟩
    exact ⟨hq,hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hv⟩)⟩
  · rintro ⟨hq,hv⟩
    exact ⟨hq,by linarith [hip.2]⟩

theorem positive_score_call_identity {ι : Type*} [Fintype ι] (q v : ι → ℝ) (z : ℝ) :
    call q v z=(∑ i ∈ positiveScoreSet q v z, q i*v i)-z*mass (positiveScoreSet q v z) q := by
  classical
  have hh : call q v z=∑ i ∈ positiveScoreSet q v z, q i*(v i-z) := by
    unfold call positiveScoreSet
    rw [←Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i => q i ≠ 0 ∧ 0 < v i-z)]
    have hz : (∑ i ∈ Finset.univ.filter (fun i => ¬(q i ≠ 0 ∧ 0 < v i-z)),
        q i*max (v i-z) 0)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hn := (Finset.mem_filter.mp hi).2
      by_cases hq : q i=0
      · rw [hq,zero_mul]
      · have hv : ¬0 < v i-z := fun hv => hn ⟨hq,hv⟩
        rw [max_eq_right (le_of_not_gt hv),mul_zero]
    rw [hz,add_zero]
    exact Finset.sum_congr rfl fun i hi => by
      rw [max_eq_left (le_of_lt (Finset.mem_filter.mp hi).2.2)]
  rw [hh]
  simp only [mass,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  simp only [mul_comm]

theorem cuts_iff_positive_thresholds {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i=r) :
    Cuts M r q v ↔ ∀ i, q i ≠ 0 →
      (∑ j ∈ weightedUpperSet q v i, q j*v j) ≤
        M*mass (weightedUpperSet q v i) q*(r-mass (weightedUpperSet q v i) q) := by
  constructor
  · intro h i _
    exact h _
  · intro hp
    apply call_bound_implies_cuts q v M r hM hq hmass
    intro z _
    classical
    let s := positiveScoreSet q v z
    let Q := mass s q
    have hc : (∑ i ∈ s, q i*v i) ≤ M*Q*(r-Q) := by
      by_cases hs : s.Nonempty
      · obtain ⟨i,hi,he⟩ := positive_score_threshold q v z hs
        dsimp only [Q,s]
        rw [he]
        exact hp i hi
      · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        dsimp only [Q]
        simp only [he,mass,Finset.sum_empty,mul_zero,zero_mul,sub_zero,le_refl]
    have hsq := sq_nonneg ((2 : ℕ)*M*Q-(M*r-z))
    have he : (4 : ℕ)*M*envelope M r z=(M*r-z)^2 := by
      unfold envelope
      norm_num only [Nat.cast_ofNat]
      field_simp
    rw [positive_score_call_identity]
    apply (mul_le_mul_iff_right₀ (show 0 < (4 : ℕ)*M by positivity)).mp
    dsimp only [Q,s] at hc hsq
    rw [he]
    norm_num only [Nat.cast_ofNat] at *
    nlinarith

def effectiveScore {ι : Type*} (q H : ι → ℝ) (i : ι) : ℝ :=
  if q i=0 then 0 else H i/q i

theorem effective_score_product {ι : Type*} (q H : ι → ℝ)
    (hzero : ∀ i, q i=0 → H i=0) (i : ι) : q i*effectiveScore q H i=H i := by
  unfold effectiveScore
  split_ifs with h
  · rw [hzero i h,mul_zero]
  · field_simp

theorem perspective_cuts_iff_candidate_thresholds {ι : Type*} [Fintype ι]
    (q H : ι → ℝ) (M r ε : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i=r) (hzero : ∀ i, q i=0 → H i=0) :
    perspectiveCuts q H M r ε ↔ ∀ i : ι, q i ≠ 0 →
      M*(mass (weightedUpperSet q (effectiveScore q H) i) q)^2-
        M*r*mass (weightedUpperSet q (effectiveScore q H) i) q+
        (∑ j ∈ (weightedUpperSet q (effectiveScore q H) i : Finset ι), (H j-ε*q j : ℝ)) ≤ 0 := by
  have hprod := effective_score_product q H hzero
  rw [←perspective_cuts_iff q (effectiveScore q H) H M r ε hprod,
    cuts_iff_positive_thresholds q (fun i : ι => effectiveScore q H i-ε) M r hM hq hmass]
  have he : ∀ i, weightedUpperSet q (fun j : ι => effectiveScore q H j-ε) i=
      weightedUpperSet q (effectiveScore q H) i := by
    intro i
    classical
    ext j
    simp only [weightedUpperSet,Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_congr_right fun _ => sub_le_sub_iff_right ε
  simp_rw [he]
  have hs : ∀ S : Finset ι, (∑ j ∈ S, q j*(effectiveScore q H j-ε))=
      ∑ j ∈ S, (H j-ε*q j) := by
    intro S
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_sub,hprod j,mul_comm (q j) ε]
  simp_rw [hs]
  constructor <;> intro h i hi <;> have hc := h i hi <;> nlinarith

end
end SparseCompletion

/- Fixed source body: IntervalSeparation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem perspective_moment_zero {ι α : Type*} [Fintype α]
    (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (hb : ∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) :
    ∀ i, q i=0 → intervalMomentScore p V i=0 := by
  intro i hiq
  unfold intervalMomentScore
  apply Finset.sum_eq_zero
  intro h _
  rw [perspective_zero (lo i h) (hi i h) (V i h) (q i) hiq (hb i h).1 (hb i h).2,mul_zero]

def intervalThresholdSystem {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ)
    (z : (ι → ℝ) × (ι → α → ℝ) × (α → α → ℝ)) : Prop :=
  (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i)=r ∧
  (∀ i h, lo i h*z.1 i ≤ z.2.1 i h ∧ z.2.1 i h ≤ hi i h*z.1 i) ∧
  (∀ h, (∑ a, z.2.2 h a*p a)-(∑ i, z.2.1 i h) ≤ ε) ∧
  IsSkew z.2.2 ∧ (∀ h h', coreLo h h' ≤ z.2.2 h h' ∧ z.2.2 h h' ≤ coreHi h h') ∧
  (∀ i, score lo p i ≤ ε+M*r) ∧ ∀ i : ι, z.1 i ≠ 0 →
    M*(mass (weightedUpperSet z.1 (effectiveScore z.1 (intervalMomentScore p z.2.1)) i) z.1)^2-
      M*r*mass (weightedUpperSet z.1 (effectiveScore z.1 (intervalMomentScore p z.2.1)) i) z.1+
      (∑ j ∈ weightedUpperSet z.1 (effectiveScore z.1 (intervalMomentScore p z.2.1)) i,
        (intervalMomentScore p z.2.1 j-ε*z.1 j)) ≤ 0

theorem interval_system_iff_threshold_system {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 < M)
    (z : (ι → ℝ) × (ι → α → ℝ) × (α → α → ℝ)) :
    intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z ↔
      intervalThresholdSystem lo hi coreLo coreHi p M r ε z := by
  constructor
  · rintro ⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩
    exact ⟨hq,hr,hV,hA,hK,hC,hg,
      (perspective_cuts_iff_candidate_thresholds z.1 (intervalMomentScore p z.2.1) M r ε hM hq hr
        (perspective_moment_zero lo hi z.2.1 p z.1 hV)).mp hcuts⟩
  · rintro ⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩
    exact ⟨hq,hr,hV,hA,hK,hC,hg,
      (perspective_cuts_iff_candidate_thresholds z.1 (intervalMomentScore p z.2.1) M r ε hM hq hr
        (perspective_moment_zero lo hi z.2.1 p z.1 hV)).mpr hcuts⟩

end
end SparseCompletion

/- Fixed source body: JointSupportFoundation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

abbrev CloneAnchors (n : ℕ) := Fin (n+1) ⊕ Unit

def cloneClass {n : ℕ} : CloneAnchors n → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

def aggregateClones {n : ℕ} (p : CloneAnchors n → ℝ) : Fin 2 → ℝ :=
  fun h => if h.val=0 then ∑ i : Fin (n+1), p (.inl i) else p (.inr ())

def clonedCore {n : ℕ} (K : Fin 2 → Fin 2 → ℝ) : CloneAnchors n → CloneAnchors n → ℝ :=
  fun h h' => K (cloneClass h) (cloneClass h')

def clonedCross {ι : Type*} {n : ℕ} (D : ι → Fin 2 → ℝ) : ι → CloneAnchors n → ℝ :=
  fun i h => D i (cloneClass h)

theorem aggregate_clones_mass {n : ℕ} (p : CloneAnchors n → ℝ) :
    (∑ h, aggregateClones p h)=∑ h, p h := by
  simp [aggregateClones,Fin.sum_univ_two,Fintype.sum_sum_type]

theorem aggregate_clones_nonnegative {n : ℕ} (p : CloneAnchors n → ℝ)
    (hp : ∀ h, 0 ≤ p h) : ∀ h, 0 ≤ aggregateClones p h := by
  intro h
  unfold aggregateClones
  split_ifs
  · exact Finset.sum_nonneg fun i _ => hp _
  · exact hp _

theorem aggregate_clones_mono {n : ℕ} (p p' : CloneAnchors n → ℝ)
    (hp : ∀ h, p h ≤ p' h) : ∀ h, aggregateClones p h ≤ aggregateClones p' h := by
  intro h
  unfold aggregateClones
  split_ifs
  · exact Finset.sum_le_sum fun i _ => hp _
  · exact hp _

theorem cloned_core_skew {n : ℕ} (K : Fin 2 → Fin 2 → ℝ) (hK : IsSkew K) :
    IsSkew (clonedCore (n := n) K) := fun _ _ => hK _ _

theorem cloned_anchor_response {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (h : CloneAnchors n) :
    anchorResponse (clonedCore K) (clonedCross D) p q h=
      anchorResponse K D (aggregateClones p) q (cloneClass h) := by
  cases h <;>
    simp [anchorResponse,clonedCore,clonedCross,cloneClass,aggregateClones,
      Fintype.sum_sum_type,Fin.sum_univ_two,←Finset.mul_sum]

theorem cloned_score {ι : Type*} {n : ℕ} (D : ι → Fin 2 → ℝ)
    (p : CloneAnchors n → ℝ) (i : ι) :
    score (clonedCross D) p i=score D (aggregateClones p) i := by
  simp [score,clonedCross,cloneClass,aggregateClones,Fintype.sum_sum_type,
    Fin.sum_univ_two,←Finset.mul_sum]

theorem cloned_response_anchor {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (h : CloneAnchors n) :
    response (blockMatrix (clonedCore K) (clonedCross D) B) (blockWeights p q) (.inl h)=
      response (blockMatrix K D B) (blockWeights (aggregateClones p) q) (.inl (cloneClass h)) := by
  rw [block_response_anchor,block_response_anchor,cloned_anchor_response]

theorem cloned_response_residual {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (i : ι) :
    response (blockMatrix (clonedCore K) (clonedCross D) B) (blockWeights p q) (.inr i)=
      response (blockMatrix K D B) (blockWeights (aggregateClones p) q) (.inr i) := by
  rw [block_response_residual,block_response_residual,cloned_score]

theorem cloned_response_bounds_iff {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (ε : ℝ) :
    (∀ v, response (blockMatrix (clonedCore K) (clonedCross D) B) (blockWeights p q) v ≤ ε) ↔
      ∀ v, response (blockMatrix K D B) (blockWeights (aggregateClones p) q) v ≤ ε := by
  constructor
  · intro h v
    cases v with
    | inl a =>
      fin_cases a
      · simpa [cloned_response_anchor,cloneClass] using h (.inl (.inl (0 : Fin (n+1))))
      · simpa [cloned_response_anchor,cloneClass] using h (.inl (.inr ()))
    | inr i => simpa only [cloned_response_residual] using h (.inr i)
  · intro h v
    cases v with
    | inl a => rw [cloned_response_anchor]; exact h _
    | inr i => rw [cloned_response_residual]; exact h _

def cloneShares (n : ℕ) : CloneAnchors n → ℝ :=
  Sum.elim (fun _ => ((3 : ℕ) : ℝ)/((8 : ℕ)*((n+1 : ℕ) : ℝ))) (fun _ => ((3 : ℕ) : ℝ)/(8 : ℕ))

theorem clone_shares_positive (n : ℕ) : ∀ h, 0 < cloneShares n h := by
  intro h
  cases h <;> simp only [cloneShares,Sum.elim_inl,Sum.elim_inr] <;> positivity

theorem aggregate_clone_shares (n : ℕ) : aggregateClones (cloneShares n)=twoShares (((3 : ℕ) : ℝ)/(4 : ℕ)) := by
  funext h
  fin_cases h
  · have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [aggregateClones,ite_true,cloneShares,Sum.elim_inl,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,twoShares]
    field_simp
    norm_num
  · norm_num [aggregateClones,cloneShares,twoShares]

theorem aggregate_clone_lower {n : ℕ} (p : CloneAnchors n → ℝ)
    (hp : ∀ h, cloneShares n h ≤ p h) : ∀ h, (((3 : ℕ) : ℝ)/(8 : ℕ) : ℝ) ≤ aggregateClones p h := by
  have hh := aggregate_clones_mono (cloneShares n) p hp
  rw [aggregate_clone_shares] at hh
  intro h
  have hx := hh h
  norm_num [twoShares] at hx
  exact hx

theorem clone_support_card {m n : ℕ}
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (hp : ∀ h, cloneShares n h ≤ p h) :
    (Finset.univ.filter fun v => blockWeights p q v ≠ 0).card=n+2+supportSize q := by
  classical
  have hpa : (Finset.univ.filter fun h => p h ≠ 0)=(Finset.univ : Finset (CloneAnchors n)) := by
    ext h
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact ne_of_gt (lt_of_lt_of_le (clone_shares_positive n h) (hp h))
  rw [block_support_card,hpa]
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
  rfl

end
end SparseCompletion

/- Fixed source body: JointSupportLower.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def ClonedUniformWitness (n m : ℕ) (ε : ℝ) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∀ h, cloneShares n h ≤ p h) ∧
  (fixed=true → p=cloneShares n) ∧
  (∑ h, p h)+(∑ j, q j)=1 ∧ IsSkew B ∧
  (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
  ∀ v, response (blockMatrix (clonedCore (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
    (clonedCross (rigidityCross (uniformTarget m (1/(4 : ℕ))))) B) (blockWeights p q) v ≤ ε

theorem cloned_witness_aggregates {n m : ℕ} (ε : ℝ) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (h : ClonedUniformWitness n m ε fixed p q B) :
    UniformWitness m ε fixed (aggregateClones p) q B := by
  rcases h with ⟨hq,hp,hfix,hm,hB,hb,hr⟩
  refine ⟨hq,?_,?_,?_,hB,hb,?_⟩
  · simpa only [Nat.cast_ofNat] using aggregate_clone_lower p hp
  · intro hf
    rw [hfix hf,aggregate_clone_shares]
  · rw [aggregate_clones_mass]
    exact hm
  · exact (cloned_response_bounds_iff _ _ _ _ _ _).mp hr

theorem cloned_uniform_dense (n m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ClonedUniformWitness n m ε fixed (cloneShares n) (uniformTarget m (1/(4 : ℕ))) (orderedBlock 1) := by
  have h := uniform_witness_dense m hm ε hε fixed
  rcases h with ⟨hq,ha,hfix,hn,hB,hb,hr⟩
  refine ⟨hq,fun _ => le_refl _,fun _ => rfl,?_,hB,hb,?_⟩
  · rw [←aggregate_clones_mass,aggregate_clone_shares]
    exact hn
  · apply (cloned_response_bounds_iff _ _ _ _ _ _).mpr
    rw [aggregate_clone_shares]
    exact hr

theorem cloned_uniform_observations_bounded (n m : ℕ) (hm : 0 < m) :
    IsSkew (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ))))) ∧
    (∀ h h', -1 ≤ clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ∧
      clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ≤ 1) ∧
    (∀ i h, -1 ≤ clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ∧
      clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ≤ 1) := by
  have hb := two_anchor_observed_bounds hm (uniformTarget m (1/(4 : ℕ)))
    (fun j => le_of_lt (uniformTarget_positive m (1/(4 : ℕ)) (by norm_num) j))
    (uniformTarget_mass m hm (1/(4 : ℕ)))
  norm_num only [Nat.cast_ofNat] at hb
  refine ⟨cloned_core_skew _ (twoCore_skew _),?_,?_⟩
  · intro h h'
    simpa only [clonedCore,rigidityCore,Nat.cast_ofNat] using hb.1 (cloneClass h) (cloneClass h')
  · intro i h
    simpa only [clonedCross,rigidityCross,Nat.cast_ofNat] using hb.2 i (cloneClass h)

theorem cloned_uniform_dense_full_game (n m : ℕ) (hm : 0 < m) :
    (∀ v, 0 ≤ blockWeights (cloneShares n) (uniformTarget m (1/(4 : ℕ))) v) ∧
    (∑ v, blockWeights (cloneShares n) (uniformTarget m (1/(4 : ℕ))) v)=1 ∧
    IsSkew (blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1)) ∧
    (∀ v w, -1 ≤ blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1) v w ∧
      blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1) v w ≤ 1) ∧
    ∀ v, response (blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1))
      (blockWeights (cloneShares n) (uniformTarget m (1/(4 : ℕ)))) v ≤ 0 := by
  have hw := cloned_uniform_dense n m hm 0 (le_refl 0) true
  have hb := cloned_uniform_observations_bounded n m hm
  refine ⟨blockWeights_nonneg _ _ (fun h => le_of_lt (clone_shares_positive n h)) hw.1,?_,
    blockMatrix_skew _ _ _ hb.1 hw.2.2.2.2.1,
    blockMatrix_bounds _ _ _ 1 hb.2.1 hb.2.2 hw.2.2.2.2.2.1,hw.2.2.2.2.2.2⟩
  rw [blockWeights_mass]
  exact hw.2.2.2.1

theorem joint_support_scalar_lower (k m H Q c : ℝ) (hk : 2 ≤ k)
    (hH : 0 ≤ H) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hbase : c*min (m+2) Q ≤ H+2) :
    c/(2 : ℕ)*min (k+m) (k+Q) ≤ k+H := by
  have hsmall : c*min m Q ≤ k+H := by
    have hm : min m Q ≤ min (m+2) Q := min_le_min (by linarith) (le_refl _)
    have := mul_le_mul_of_nonneg_left hm hc
    linarith
  have hident : min (k+m) (k+Q) = k+min m Q := by rw [min_add_add_left]
  rw [hident]
  have hk0 : 0 ≤ k := by linarith
  have hck := mul_le_mul_of_nonneg_right hc1 hk0
  nlinarith

theorem cloned_uniform_total_support_lower {n m : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (h : ClonedUniformWitness n m ε fixed p q B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) * min ((n+2 : ℕ)+ (m : ℝ))
      ((n+2 : ℕ)+1/Real.sqrt ε) ≤
      ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ) := by
  classical
  have ha := cloned_witness_aggregates ε fixed p q B h
  have hlow := uniform_total_support_lower hm q (aggregateClones p)
    ha.1 ha.2.1 ha.2.2.2.1 B ha.2.2.2.2.1 (fun i j => (ha.2.2.2.2.2.1 i j).1)
    ε hε ha.2.2.2.2.2.2
  rw [clone_support_card p q h.2.1]
  push_cast
  have hc0 := Real.sqrt_nonneg (((3 : ℕ) : ℝ)/(1216 : ℕ) : ℝ)
  have hc1 : Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ) : ℝ) ≤ 1 := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ ((3 : ℕ) : ℝ)/(1216 : ℕ) by norm_num)
    nlinarith
  have hb := joint_support_scalar_lower ((n : ℝ)+2) m (supportSize q) (1/Real.sqrt ε)
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by positivity) hc0 hc1 hlow
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hb

end
end SparseCompletion

/- Fixed source body: JointSupportUpper.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem unit_mass_grid_bound (r η : ℝ) (hr : r ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    (gridSize 1 r η : ℝ) ≤ (2 : ℕ)*(1/Real.sqrt η) := by
  norm_num only [Nat.cast_ofNat] at *
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hs1 : Real.sqrt η ≤ 1 := by simpa using Real.sqrt_le_sqrt hη1
  have hQ : 1 ≤ 1/Real.sqrt η := (le_div_iff₀ hs).mpr (by simpa using hs1)
  have hroot : Real.sqrt (1*r/η) ≤ 1/Real.sqrt η := by
    calc
      _ ≤ Real.sqrt (1/η) := Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right hη).mpr (by simpa using hr))
      _ = _ := by rw [Real.sqrt_div (by norm_num),Real.sqrt_one]
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (1*r/η))
  change (gridSize 1 r η : ℝ) < Real.sqrt (1*r/η)+1 at hc
  linarith

theorem joint_support_scalar_upper (k m T Q : ℝ) (hm : 0 ≤ m) (hk : 0 ≤ k)
    (h1 : T ≤ k+m) (h2 : T ≤ (2 : ℕ)*k+(2 : ℕ)*Q) :
    T ≤ (2 : ℕ)*min (k+m) (k+Q) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact le_min (by linarith) (by linarith)

theorem normalized_joint_support_upper {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (r η : ℝ)
    (hr : 0 ≤ r) (hη : 0 < η) (hη1 : η ≤ 1)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r=1) (hqmass : ∑ i, q i=r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -1 ≤ K h h' ∧ K h h' ≤ 1)
    (hDb : ∀ i h, -1 ≤ D i h ∧ D i h ≤ 1)
    (hBb : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ i, q i=0 → q' i=0) ∧
      (∀ h, (∑ i, q' i*D i h)=∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -1 ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ 1) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) ∧
      ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤
        (2 : ℕ)*min ((k : ℝ)+Fintype.card ι) ((k : ℝ)+1/Real.sqrt η) := by
  norm_num only [Nat.cast_ofNat] at *
  classical
  obtain ⟨q',B',hn,hm,_ha,hs,_hc,ht,hmo,hsk,hb,hrows⟩ :=
    normalized_exact_sparse_witness_all_mass k K D B p q 1 r η (by norm_num) hr hη
      hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  refine ⟨q',B',hn,hm,hs,hmo,hsk,hb,hrows,?_⟩
  have hr1 : r ≤ 1 := by
    have hsp := Finset.sum_nonneg (fun h (_ : h ∈ Finset.univ) => hp h)
    linarith
  have hgrid := unit_mass_grid_bound r η hr1 hη hη1
  norm_num only [Nat.cast_ofNat] at hgrid
  have hdim := le_trans ht (min_le_left _ _)
  have hgridnat := le_trans ht (min_le_right _ _)
  have hdimR : ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤ k+Fintype.card ι := by exact_mod_cast hdim
  have hgridR : ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤ (2 : ℕ)*(k : ℝ)+(gridSize 1 r η : ℝ) := by exact_mod_cast hgridnat
  exact joint_support_scalar_upper k (Fintype.card ι) _ (1/Real.sqrt η)
    (by positivity) (by positivity) hdimR (by
      norm_num only [Nat.cast_ofNat] at hgridR ⊢
      linarith)

end
end SparseCompletion

/- Fixed source body: JointSupportTheorem.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- An actual bounded normalized exact game, with supplied anchor allocation. -/
structure ExactAnchorInstance (k m : ℕ) where
  K : Fin k → Fin k → ℝ
  D : Fin m → Fin k → ℝ
  B : Fin m → Fin m → ℝ
  p : Fin k → ℝ
  q : Fin m → ℝ
  r : ℝ
  residual_nonnegative : 0 ≤ r
  anchors_nonnegative : ∀ h, 0 ≤ p h
  residual_weights_nonnegative : ∀ i, 0 ≤ q i
  normalized : (∑ h, p h)+r=1
  residual_mass : ∑ i, q i=r
  core_skew : IsSkew K
  residual_skew : IsSkew B
  core_bounds : ∀ h h', -1 ≤ K h h' ∧ K h h' ≤ 1
  cross_bounds : ∀ i h, -1 ≤ D i h ∧ D i h ≤ 1
  residual_bounds : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1
  exact_responses : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0

/-- The supplied allocation p is held fixed literally, so any originally satisfied
    coordinatewise anchor floors remain satisfied as well. -/
def JointUpperWitness {k m : ℕ} (I : ExactAnchorInstance k m) (η : ℝ)
    (q' : Fin m → ℝ) (B' : Fin m → Fin m → ℝ) : Prop :=
  (∀ a, 0 ≤ blockWeights I.p q' a) ∧ (∑ a, blockWeights I.p q' a)=1 ∧
  (∀ i, I.q i=0 → q' i=0) ∧
  (∀ h, (∑ i, q' i*I.D i h)=∑ i, I.q i*I.D i h) ∧
  IsSkew (blockMatrix I.K I.D B') ∧
  (∀ a b, -1 ≤ blockMatrix I.K I.D B' a b ∧ blockMatrix I.K I.D B' a b ≤ 1) ∧
  (∀ a, response (blockMatrix I.K I.D B') (blockWeights I.p q') a ≤ η) ∧
  ((Finset.univ.filter fun a => blockWeights I.p q' a ≠ 0).card : ℝ) ≤
    (2 : ℕ)*min ((k : ℝ)+m) ((k : ℝ)+1/Real.sqrt η)

/-- Quantified sharp joint order: every actual exact instance has the universal
    upper witness, while the actual bounded clone family is exactly feasible and
    forces the lower bound in both commitment classes. No worst-case operator or
    supremum is asserted or assumed. Here the number of anchors is k=n+2. -/
theorem joint_anchor_support_order (n m : ℕ) (hm : 0 < m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (∀ I : ExactAnchorInstance (n+2) m,
      ∃ q' B', JointUpperWitness I η q' B') ∧
    (∀ fixed : Bool,
      (∃ p q B, ClonedUniformWitness n m 0 fixed p q B) ∧
      ∀ p q B, ClonedUniformWitness n m η fixed p q B →
        Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) * min ((n+2 : ℕ)+(m : ℝ))
          ((n+2 : ℕ)+1/Real.sqrt η) ≤
          ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ)) ∧
    (IsSkew (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ))))) ∧
      (∀ h h', -1 ≤ clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ∧
        clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ≤ 1) ∧
      (∀ i h, -1 ≤ clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ∧
        clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ≤ 1)) := by
  refine ⟨?_,?_,cloned_uniform_observations_bounded n m hm⟩
  · intro I
    simpa only [JointUpperWitness,Fintype.card_fin] using normalized_joint_support_upper
      (n+2) I.K I.D I.B I.p I.q I.r η I.residual_nonnegative hη hη1
      I.anchors_nonnegative I.residual_weights_nonnegative I.normalized I.residual_mass
      I.core_skew I.residual_skew I.core_bounds I.cross_bounds I.residual_bounds I.exact_responses
  · intro fixed
    refine ⟨⟨cloneShares n,uniformTarget m (1/(4 : ℕ)),orderedBlock 1,
      cloned_uniform_dense n m hm 0 (le_refl 0) fixed⟩,?_⟩
    intro p q B hw
    exact cloned_uniform_total_support_lower hm η hη fixed p q B hw

end
end SparseCompletion

/- Fixed source body: JointSupportGeneral.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem joint_anchor_support_order_general (k m : ℕ) (hk : (2 : ℕ) ≤ k) (hm : 0 < m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (∀ I : ExactAnchorInstance k m,
      ∃ q' B', JointUpperWitness I η q' B') ∧
    (∀ fixed : Bool,
      (∃ p q B, ClonedUniformWitness (k-2) m 0 fixed p q B) ∧
      ∀ p q B, ClonedUniformWitness (k-2) m η fixed p q B →
        Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) * min (k+(m : ℝ))
          (k+1/Real.sqrt η) ≤
          ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ)) ∧
    (IsSkew (clonedCore (n := k-2) (rigidityCore (uniformTarget m (1/(4 : ℕ))))) ∧
      (∀ h h', -1 ≤ clonedCore (n := k-2) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ∧
        clonedCore (n := k-2) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ≤ 1) ∧
      (∀ i h, -1 ≤ clonedCross (n := k-2) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ∧
        clonedCross (n := k-2) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ≤ 1)) := by
  have he : k-2+2=k := Nat.sub_add_cancel hk
  generalize hn : k-2=n at *
  subst k
  exact joint_anchor_support_order n m hm η hη hη1

end
end SparseCompletion

/- Fixed source body: RationalCertificate.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
structure RationalCertificate (k m : ℕ) where
  support : Finset (Fin m)
  anchors : Fin k → ℚ
  weights : support → ℚ
  residual : support → support → ℚ

namespace RationalCertificate

def q {k m : ℕ} (c : RationalCertificate k m) (i : Fin m) : ℚ :=
  if h : i ∈ c.support then c.weights ⟨i,h⟩ else 0

def b {k m : ℕ} (c : RationalCertificate k m) (i j : Fin m) : ℚ :=
  if hi : i ∈ c.support then
    if hj : j ∈ c.support then c.residual ⟨i,hi⟩ ⟨j,hj⟩ else 0
  else 0

def Rows {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) : Prop :=
  (∀ h, (∑ h', K h h'*c.anchors h')-∑ i, D i h*c.q i ≤ σ) ∧
  (∀ i ∈ c.support, (∑ h, D i h*c.anchors h)+(∑ j ∈ c.support, c.b i j*c.q j) ≤ σ) ∧
  (∀ i, i ∉ c.support → (∑ h, D i h*c.anchors h)-M*(∑ j, c.q j) ≤ σ)

def Conditions {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) : Prop :=
  0 ≤ M ∧
  (∀ h, 0 ≤ c.anchors h) ∧ (∀ i, 0 ≤ c.q i) ∧
  (∑ h, c.anchors h)+(∑ i, c.q i)=1 ∧
  (∀ h h', K h h' = -K h' h) ∧
  (∀ h h', -M ≤ K h h' ∧ K h h' ≤ M) ∧
  (∀ i h, -M ≤ D i h ∧ D i h ≤ M) ∧
  (∀ i ∈ c.support, ∀ j ∈ c.support, c.b i j = -c.b j i) ∧
  (∀ i ∈ c.support, ∀ j ∈ c.support, -M ≤ c.b i j ∧ c.b i j ≤ M) ∧
  c.Rows K D M σ

instance {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) :
    Decidable (c.Conditions K D M σ) := by
  unfold RationalCertificate.Conditions RationalCertificate.Rows
  infer_instance

/-- Computable finite rational checker, including every omitted row. -/
def check {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) : Bool :=
  decide (c.Conditions K D M σ)

theorem check_iff {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) :
    c.check K D M σ=true ↔ c.Conditions K D M σ := by
  exact decide_eq_true_iff

theorem q_on {k m : ℕ} (c : RationalCertificate k m) (i : c.support) :
    c.q i=c.weights i := by simp [q]

theorem b_on {k m : ℕ} (c : RationalCertificate k m) (i j : c.support) :
    c.b i j=c.residual i j := by simp [b]

theorem reject_omitted_violation {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ)
    (i : Fin m) (hi : i ∉ c.support)
    (hv : σ < (∑ h, D i h*c.anchors h)-M*(∑ j, c.q j)) :
    c.check K D M σ=false := by
  cases he : c.check K D M σ
  · rfl
  · have hc := (c.check_iff K D M σ).mp he
    exact False.elim (not_le_of_gt hv (hc.2.2.2.2.2.2.2.2.2.2.2 i hi))

noncomputable section

def realQ {k m : ℕ} (c : RationalCertificate k m) : Fin m → ℝ :=
  fun i => (c.q i : ℝ)

def realB {k m : ℕ} (c : RationalCertificate k m) (M : ℚ) : Fin m → Fin m → ℝ :=
  compactCompletion c.support (M : ℝ) (fun i j => (c.b i j : ℝ))

theorem realQ_off {k m : ℕ} (c : RationalCertificate k m)
    (i : Fin m) (hi : i ∉ c.support) : c.realQ i=0 := by
  simp [realQ,q,hi]

theorem support_card_le {k m : ℕ} (c : RationalCertificate k m) :
    (Finset.univ.filter fun i => c.realQ i ≠ 0).card ≤ c.support.card := by
  classical
  apply Finset.card_le_card
  intro i hi
  by_contra hs
  exact (Finset.mem_filter.mp hi).2 (c.realQ_off i hs)

theorem realB_stored {k m : ℕ} (c : RationalCertificate k m)
    (M : ℚ) (i j : c.support) : c.realB M i j=(c.residual i j : ℝ) := by
  simp [realB,compactCompletion,b]

theorem realB_omitted {k m : ℕ} (c : RationalCertificate k m)
    (M : ℚ) (i j : Fin m) (hi : i ∉ c.support) :
    c.realB M i j=if j ∈ c.support then -(M : ℝ) else 0 := by
  simp [realB,compactCompletion,hi]

theorem rows_iff {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ) :
    (∀ a, response (blockMatrix (fun h h' => (K h h' : ℝ))
      (fun i h => (D i h : ℝ)) (c.realB M))
      (blockWeights (fun h => (c.anchors h : ℝ)) c.realQ) a ≤ (σ : ℝ)) ↔
      c.Rows K D M σ := by
  rw [realB,compact_block_certificate_iff c.support _ _ _ _ c.realQ (M : ℝ)
    (∑ i, c.realQ i) (σ : ℝ) c.realQ_off rfl]
  simp only [anchorResponse,score,realQ,Rows]
  norm_cast
end
end RationalCertificate
end SparseCompletion

/- Fixed source body: RationalCertificateSoundness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
namespace RationalCertificate
noncomputable section

/-- Acceptance produces this actual explicit completion, not merely an
    existential response vector or assumed feasibility certificate. -/
theorem accepted_full_game {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ)
    (hc : c.check K D M σ=true) :
    (∀ a, 0 ≤ blockWeights (fun h => (c.anchors h : ℝ)) c.realQ a) ∧
    (∑ a, blockWeights (fun h => (c.anchors h : ℝ)) c.realQ a)=1 ∧
    IsSkew (blockMatrix (fun h h' => (K h h' : ℝ)) (fun i h => (D i h : ℝ)) (c.realB M)) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun h h' => (K h h' : ℝ))
      (fun i h => (D i h : ℝ)) (c.realB M) a b ∧
      blockMatrix (fun h h' => (K h h' : ℝ)) (fun i h => (D i h : ℝ)) (c.realB M) a b ≤ (M : ℝ)) ∧
    (∀ a, response (blockMatrix (fun h h' => (K h h' : ℝ)) (fun i h => (D i h : ℝ)) (c.realB M))
      (blockWeights (fun h => (c.anchors h : ℝ)) c.realQ) a ≤ (σ : ℝ)) := by
  obtain ⟨hM,hp,hq,hm,hK,hKb,hD,hB,hBb,hrows⟩ := c.check_iff K D M σ |>.mp hc
  have hpR : ∀ h, 0 ≤ (c.anchors h : ℝ) := by intro h; exact_mod_cast hp h
  have hqR : ∀ i, 0 ≤ c.realQ i := by
    intro i
    change 0 ≤ (c.q i : ℝ)
    exact_mod_cast hq i
  have hKR : IsSkew (fun h h' => (K h h' : ℝ)) := by
    intro h h'
    change (K h h' : ℝ) = -(K h' h : ℝ)
    exact_mod_cast hK h h'
  have hBR : IsSkew (c.realB M) := by
    apply compactCompletion_skew
    intro i hi j hj
    exact_mod_cast hB i hi j hj
  have hKbR : ∀ h h', -(M : ℝ) ≤ (K h h' : ℝ) ∧ (K h h' : ℝ) ≤ (M : ℝ) := by
    intro h h'; exact_mod_cast hKb h h'
  have hDR : ∀ i h, -(M : ℝ) ≤ (D i h : ℝ) ∧ (D i h : ℝ) ≤ (M : ℝ) := by
    intro i h; exact_mod_cast hD i h
  have hBbR : ∀ i j, -(M : ℝ) ≤ c.realB M i j ∧ c.realB M i j ≤ (M : ℝ) := by
    apply compactCompletion_bounds
    · exact_mod_cast hM
    · intro i hi j hj; exact_mod_cast hBb i hi j hj
  refine ⟨blockWeights_nonneg _ _ hpR hqR,?_,blockMatrix_skew _ _ _ hKR hBR,
    blockMatrix_bounds _ _ _ _ hKbR hDR hBbR,(c.rows_iff K D M σ).mpr hrows⟩
  rw [blockWeights_mass]
  simp only [realQ]
  exact_mod_cast hm

/-- With probability and bounded-skew data validated, acceptance is equivalent
    to all rows of the explicit omitted-row real completion passing. -/
theorem check_iff_full_rows {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ)
    (hg : 0 ≤ M ∧ (∀ h, 0 ≤ c.anchors h) ∧ (∀ i, 0 ≤ c.q i) ∧
      (∑ h, c.anchors h)+(∑ i, c.q i)=1 ∧
      (∀ h h', K h h' = -K h' h) ∧
      (∀ h h', -M ≤ K h h' ∧ K h h' ≤ M) ∧
      (∀ i h, -M ≤ D i h ∧ D i h ≤ M) ∧
      (∀ i ∈ c.support, ∀ j ∈ c.support, c.b i j = -c.b j i) ∧
      (∀ i ∈ c.support, ∀ j ∈ c.support, -M ≤ c.b i j ∧ c.b i j ≤ M)) :
    c.check K D M σ=true ↔
      ∀ a, response (blockMatrix (fun h h' => (K h h' : ℝ))
        (fun i h => (D i h : ℝ)) (c.realB M))
        (blockWeights (fun h => (c.anchors h : ℝ)) c.realQ) a ≤ (σ : ℝ) := by
  rw [c.check_iff,c.rows_iff]
  obtain ⟨hM,hp,hq,hm,hK,hKb,hD,hB,hBb⟩ := hg
  exact ⟨fun h => h.2.2.2.2.2.2.2.2.2,
    fun hr => ⟨hM,hp,hq,hm,hK,hKb,hD,hB,hBb,hr⟩⟩
end
end RationalCertificate
end SparseCompletion

/- Fixed source body: FixedValue.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def fixedGameValue {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty (α ⊕ ι)]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (M : ℝ) (R : Set (ι → ℝ)) : ℝ :=
  sInf ((fun z : (ι → ι → ℝ) × (ι → ℝ) =>
    exploitability (blockMatrix K D z.1) (blockWeights p z.2)) '' (skewBox M ×ˢ R))

theorem fixed_game_exploitability_continuous {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) :
    Continuous (fun z : (ι → ι → ℝ) × (ι → ℝ) =>
      exploitability (blockMatrix K D z.1) (blockWeights p z.2)) := by
  unfold exploitability
  apply Continuous.finset_sup'_apply
  intro a _
  cases a with
  | inl h =>
    simp only [block_response_anchor,anchorResponse]
    fun_prop
  | inr i =>
    simp only [response,Fintype.sum_sum_type,blockMatrix,blockWeights,Sum.elim_inl,Sum.elim_inr]
    fun_prop

theorem fixed_game_value_attained {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M : ℝ) (R : Set (ι → ℝ)) (hM : 0 ≤ M) (hR : IsCompact R) (hne : R.Nonempty) :
    ∃ B ∈ skewBox M, ∃ q ∈ R,
      exploitability (blockMatrix K D B) (blockWeights p q)=fixedGameValue K D p M R := by
  have hc := ((skewBox_compact M).prod hR).image (fixed_game_exploitability_continuous K D p)
  have hn := ((show (skewBox (ι := ι) M).Nonempty from ⟨0,skewBox_zero M hM⟩).prod hne).image
    (fun z : (ι → ι → ℝ) × (ι → ℝ) => exploitability (blockMatrix K D z.1) (blockWeights p z.2))
  obtain ⟨⟨B,q⟩,⟨hB,hq⟩,he⟩ := hc.sInf_mem hn
  exact ⟨B,hB,q,hq,he⟩

theorem fixed_game_value_le_witness {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M : ℝ) (R : Set (ι → ℝ)) (hR : IsCompact R)
    (B : ι → ι → ℝ) (q : ι → ℝ) (hB : B ∈ skewBox M) (hq : q ∈ R) :
    fixedGameValue K D p M R ≤ exploitability (blockMatrix K D B) (blockWeights p q) := by
  apply csInf_le (((skewBox_compact M).prod hR).image (fixed_game_exploitability_continuous K D p)).bddBelow
  exact ⟨(B,q),⟨hB,hq⟩,rfl⟩

end
end SparseCompletion

/- Fixed source body: GapCompact.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem gap_points_closed {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (M r η : ℝ) :
    IsClosed {z : (ι → ℝ) × ℝ | fixedAnchorGapPoint K D p z.1 M r z.2 η} := by
  change IsClosed ({z : ((ι → ℝ) × ℝ) | ∀ i, 0 ≤ z.1 i} ∩
    ({z : ((ι → ℝ) × ℝ) | (∑ i, z.1 i)=r} ∩
    ({z : ((ι → ℝ) × ℝ) | ∀ i, score D p i ≤ z.2+M*r} ∩
    ({z : ((ι → ℝ) × ℝ) | ∀ h, anchorResponse K D p z.1 h ≤ z.2} ∩
    {z : ((ι → ℝ) × ℝ) | ∀ l : ℕ, 1 ≤ l → l ≤ gridSize M r η →
      call z.1 (fun i => score D p i-z.2) (M*r-gridNode M r η l) ≤
        envelope M r (M*r-gridNode M r η l)}))))
  simp only [Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (show Continuous (fun z : ((ι → ℝ) × ℝ) => z.1 i) by fun_prop)
  · apply IsClosed.inter
    · exact isClosed_eq (show Continuous (fun z : ((ι → ℝ) × ℝ) => ∑ i, z.1 i) by fun_prop) continuous_const
    · apply IsClosed.inter
      · apply isClosed_iInter
        intro i
        exact isClosed_le continuous_const (show Continuous (fun z : ((ι → ℝ) × ℝ) => z.2+M*r) by fun_prop)
      · apply IsClosed.inter
        · apply isClosed_iInter
          intro h
          exact isClosed_le (show Continuous (fun z : ((ι → ℝ) × ℝ) => anchorResponse K D p z.1 h) by
            unfold anchorResponse; fun_prop) continuous_snd
        · apply isClosed_iInter
          intro l
          apply isClosed_iInter
          intro _
          apply isClosed_iInter
          intro _
          exact isClosed_le (show Continuous (fun z : ((ι → ℝ) × ℝ) =>
            call z.1 (fun i => score D p i-z.2) (M*r-gridNode M r η l)) by
              unfold call; fun_prop) continuous_const

def gapPairs {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) : Set ((ι → ℝ) × ℝ) :=
  (R ×ˢ Set.Icc 0 M) ∩ {z | fixedAnchorGapPoint K D p z.1 M r z.2 η}

theorem gap_pairs_compact {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (hR : IsCompact R) : IsCompact (gapPairs R K D p M r η) :=
  (hR.prod isCompact_Icc).inter_right (gap_points_closed K D p M r η)

def gapThresholdValue {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (M r η : ℝ) : ℝ :=
  sInf (Prod.snd '' gapPairs R K D p M r η)

theorem gap_threshold_attained {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (hR : IsCompact R) (hne : (gapPairs R K D p M r η).Nonempty) :
    ∃ q ∈ R, fixedAnchorGapPoint K D p q M r (gapThresholdValue R K D p M r η) η ∧
      0 ≤ gapThresholdValue R K D p M r η ∧ gapThresholdValue R K D p M r η ≤ M := by
  have hc := (gap_pairs_compact R K D p M r η hR).image continuous_snd
  obtain ⟨⟨q,ρ⟩,⟨⟨hq,hρ⟩,hpoint⟩,he⟩ := hc.sInf_mem (hne.image Prod.snd)
  change ρ=gapThresholdValue R K D p M r η at he
  rw [←he]
  exact ⟨q,hq,hpoint,hρ⟩

theorem gap_threshold_le {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η ρ : ℝ) (hR : IsCompact R)
    (q : ι → ℝ) (hq : q ∈ R) (hρ : 0 ≤ ρ ∧ ρ ≤ M)
    (hpoint : fixedAnchorGapPoint K D p q M r ρ η) : gapThresholdValue R K D p M r η ≤ ρ := by
  apply csInf_le ((gap_pairs_compact R K D p M r η hR).image continuous_snd).bddBelow
  exact ⟨(q,ρ),⟨⟨hq,hρ⟩,hpoint⟩,rfl⟩

end
end SparseCompletion

/- Fixed source body: ValueBounds.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem exploitability_nonnegative {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (hA : IsSkew A)
    (hx : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) : 0 ≤ exploitability A x := by
  have hz : (∑ i, x i*response A x i)=0 := by
    simpa only [response,Finset.mul_sum,mul_assoc] using skew_weighted_sum Finset.univ x A hA
  calc
    0 = ∑ i, x i*response A x i := hz.symm
    _ ≤ ∑ i, x i*exploitability A x := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (response_le_exploitability A x i) (hx i)
    _ = _ := by rw [←Finset.sum_mul,hm,one_mul]

theorem exploitability_bounded_above {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (M : ℝ)
    (hA : ∀ i j, A i j ≤ M) (hx : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) :
    exploitability A x ≤ M := by
  apply (exploitability_le_iff A x M).mpr
  intro i
  unfold response
  calc
    (∑ j, A i j*x j) ≤ ∑ j, M*x j := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hA i j) (hx j)
    _ = M := by rw [←Finset.mul_sum,hm,mul_one]

theorem fixed_game_value_bounds {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r : ℝ) (R : Set (ι → ℝ)) (hM : 0 ≤ M) (hR : IsCompact R) (hne : R.Nonempty)
    (hp : ∀ h, 0 ≤ p h) (hpm : (∑ h, p h)+r=1)
    (hprob : ∀ q ∈ R, (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M) :
    0 ≤ fixedGameValue K D p M R ∧ fixedGameValue K D p M R ≤ M ∧
      fixedAnchorFeasible R K D p M r (fixedGameValue K D p M R) := by
  obtain ⟨B,hB,q,hq,he⟩ := fixed_game_value_attained K D p M R hM hR hne
  have hsk := blockMatrix_skew K D B hK hB.1
  have hb := blockMatrix_bounds K D B M hKb hDb hB.2
  have hn := blockWeights_nonneg p q hp (hprob q hq).1
  have hm : (∑ a, blockWeights p q a)=1 := by rw [blockWeights_mass,(hprob q hq).2,hpm]
  have h0 := exploitability_nonnegative _ _ hsk hn hm
  have hu := exploitability_bounded_above _ _ M (fun i j => (hb i j).2) hn hm
  rw [he] at h0 hu
  refine ⟨h0,hu,q,hq,(hprob q hq).1,(hprob q hq).2,B,hB.1,hB.2,?_⟩
  intro a
  rw [←he]
  exact response_le_exploitability _ _ a

end
end SparseCompletion

/- Fixed source body: GapValue.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem gap_threshold_minimal_nonnegative {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η ρ : ℝ) (hR : IsCompact R) (hne : (gapPairs R K D p M r η).Nonempty)
    (hρ : 0 ≤ ρ) (hgap : fixedAnchorGapFeasible R K D p M r ρ η) :
    gapThresholdValue R K D p M r η ≤ ρ := by
  obtain ⟨q,hq,hpoint,_,hW⟩ := gap_threshold_attained R K D p M r η hR hne
  by_cases hρM : ρ ≤ M
  · obtain ⟨q',hq',hp'⟩ := hgap
    exact gap_threshold_le R K D p M r η ρ hR q' hq' ⟨hρ,hρM⟩ hp'
  · exact le_trans hW (le_of_lt (lt_of_not_ge hρM))

theorem gap_original_infimum_eq {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (hR : IsCompact R) (hne : (gapPairs R K D p M r η).Nonempty) :
    sInf {ρ : ℝ | 0 ≤ ρ ∧ fixedAnchorGapFeasible R K D p M r ρ η}=
      gapThresholdValue R K D p M r η := by
  obtain ⟨q,hq,hpoint,hW0,_⟩ := gap_threshold_attained R K D p M r η hR hne
  have hmem : gapThresholdValue R K D p M r η ∈
      {ρ : ℝ | 0 ≤ ρ ∧ fixedAnchorGapFeasible R K D p M r ρ η} := ⟨hW0,q,hq,hpoint⟩
  apply le_antisymm
  · exact csInf_le ⟨0,fun _ h => h.1⟩ hmem
  · exact le_csInf ⟨_,hmem⟩ fun ρ h => gap_threshold_minimal_nonnegative R K D p M r η ρ hR hne h.1 h.2

theorem fixed_anchor_additive_value_enclosure {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (R : Set (ι → ℝ)) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hR : IsCompact R) (hne : R.Nonempty)
    (hp : ∀ h, 0 ≤ p h) (hpm : (∑ h, p h)+r=1)
    (hprob : ∀ q ∈ R, (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M) :
    0 ≤ gapThresholdValue R K D p M r η ∧ gapThresholdValue R K D p M r η ≤ M ∧
    gapThresholdValue R K D p M r η ≤ fixedGameValue K D p M R ∧
    fixedGameValue K D p M R ≤ gapThresholdValue R K D p M r η+η ∧
    ∃ q ∈ R, ∃ B : ι → ι → ℝ, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ gapThresholdValue R K D p M r η+η := by
  obtain ⟨hV0,hVM,hfeas⟩ := fixed_game_value_bounds K D p M r R (le_of_lt hM) hR hne hp hpm hprob hK hKb hDb
  obtain ⟨q,hq,hpoint⟩ := feasible_implies_gap_feasible R K D p M r (fixedGameValue K D p M R) η hM hfeas
  have hpair : (gapPairs R K D p M r η).Nonempty :=
    ⟨(q,fixedGameValue K D p M R),⟨⟨hq,hV0,hVM⟩,hpoint⟩⟩
  have hWV := gap_threshold_le R K D p M r η _ hR q hq ⟨hV0,hVM⟩ hpoint
  obtain ⟨q',hq',hpoint',hW0,hWM⟩ := gap_threshold_attained R K D p M r η hR hpair
  obtain ⟨B,hB,hb,hrows⟩ := gap_point_completed_witness K D p q' M r _ η hM hr hη hpoint'
  have hV := fixed_game_value_le_witness K D p M R hR B q' ⟨hB,hb⟩ hq'
  have hu := (exploitability_le_iff _ _ _).mpr hrows
  exact ⟨hW0,hWM,hWV,le_trans hV hu,q',hq',B,hB,hb,hrows⟩

end
end SparseCompletion

/- Fixed source body: AllocationRounding.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def roundedAnchor (s p δ : ℝ) : ℝ := s+δ*(Nat.floor ((p-s)/δ) : ℝ)

theorem rounded_anchor_bounds (s p δ : ℝ) (hsp : s ≤ p) (hδ : 0 < δ) :
    s ≤ roundedAnchor s p δ ∧ roundedAnchor s p δ ≤ p ∧ p-roundedAnchor s p δ < δ := by
  have hx : 0 ≤ (p-s)/δ := div_nonneg (sub_nonneg.mpr hsp) (le_of_lt hδ)
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one ((p-s)/δ)
  have h3 := (le_div_iff₀ hδ).mp h1
  have h4 := (div_lt_iff₀ hδ).mp h2
  unfold roundedAnchor
  exact ⟨le_add_of_nonneg_right (mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)),by nlinarith,by nlinarith⟩

def roundedAllocation {α : Type*} (s p : α → ℝ) (δ : ℝ) (i : α) : ℝ := roundedAnchor (s i) (p i) δ

def removedAnchorMass {α : Type*} [Fintype α] (s p : α → ℝ) (δ : ℝ) : ℝ :=
  ∑ i, (p i-roundedAllocation s p δ i)

theorem removed_anchor_mass_bounds {α : Type*} [Fintype α] (s p : α → ℝ) (δ : ℝ)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    0 ≤ removedAnchorMass s p δ ∧ removedAnchorMass s p δ ≤ (Fintype.card α : ℝ)*δ := by
  constructor
  · exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.1
  · calc
      removedAnchorMass s p δ ≤ ∑ _i : α, δ := Finset.sum_le_sum fun i _ =>
        le_of_lt (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.2
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

def transferredResidual {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (d : ℝ) (j : ι) (i : ι) : ℝ :=
  q i+if i=j then d else 0

theorem transferred_residual_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (d : ℝ) (j : ι) : (∑ i, transferredResidual q d j i)=(∑ i, q i)+d := by
  simp only [transferredResidual,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem allocation_rounding_mass {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s p : α → ℝ) (q : ι → ℝ) (δ : ℝ) (j : ι) :
    (∑ i, roundedAllocation s p δ i)+(∑ i, transferredResidual q (removedAnchorMass s p δ) j i)=
      (∑ i, p i)+(∑ i, q i) := by
  rw [transferred_residual_mass]
  unfold removedAnchorMass
  rw [Finset.sum_sub_distrib]
  ring

theorem transferred_residual_distance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (d : ℝ) (j : ι) (hd : 0 ≤ d) :
    (∑ i, |q i-transferredResidual q d j i|)=d := by
  have he : ∀ i, |q i-transferredResidual q d j i|=if i=j then d else 0 := by
    intro i
    by_cases h : i=j
    · simp only [transferredResidual,h,ite_true,sub_add_cancel_left,abs_neg,abs_of_nonneg hd]
    · simp only [transferredResidual,h,ite_false,add_zero,sub_self,abs_zero]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem allocation_rounding_distance {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s p : α → ℝ) (q : ι → ℝ) (δ : ℝ) (j : ι)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    (∑ a, |blockWeights p q a-
      blockWeights (roundedAllocation s p δ) (transferredResidual q (removedAnchorMass s p δ) j) a|) ≤
        (2 : ℕ)*(Fintype.card α : ℝ)*δ := by
  have hd := removed_anchor_mass_bounds s p δ hsp hδ
  have ha : (∑ i, |p i-roundedAllocation s p δ i|)=removedAnchorMass s p δ := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (sub_nonneg.mpr (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.1)
  rw [Fintype.sum_sum_type]
  simp only [blockWeights,Sum.elim_inl,Sum.elim_inr]
  rw [ha,transferred_residual_distance q _ j hd.1]
  norm_num only [Nat.cast_ofNat]
  linarith

end
end SparseCompletion

/- Fixed source body: AllocationGrid.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rounded_anchor_grid_index (s p δ : ℝ) (hs : 0 ≤ s) (hp : p ≤ 1) (hδ : 0 < δ) :
    Nat.floor ((p-s)/δ) < 1+Nat.floor (1/δ) := by
  have h : (p-s)/δ ≤ 1/δ := div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ)
  have hm := Nat.floor_mono h
  omega

theorem rounded_allocation_finite_grid {α : Type*} (s p : α → ℝ) (δ : ℝ)
    (hs : ∀ i, 0 ≤ s i) (hp : ∀ i, p i ≤ 1) (hδ : 0 < δ) :
    ∃ z : α → Fin (1+Nat.floor (1/δ)),
      ∀ i, roundedAllocation s p δ i=s i+δ*(z i : ℕ) := by
  exact ⟨fun i => ⟨Nat.floor ((p i-s i)/δ),rounded_anchor_grid_index _ _ _ (hs i) (hp i) hδ⟩,
    fun _ => rfl⟩

theorem allocation_grid_card {α : Type*} [Fintype α] [DecidableEq α] (δ : ℝ) :
    Fintype.card (α → Fin (1+Nat.floor (1/δ)))=(1+Nat.floor (1/δ))^Fintype.card α := by
  simp only [Fintype.card_fun,Fintype.card_fin]

theorem allocation_rounding_preserves_floors {α ι : Type*} [Fintype α] [DecidableEq ι]
    (s p : α → ℝ) (t q : ι → ℝ) (δ : ℝ) (j : ι)
    (hsp : ∀ i, s i ≤ p i) (htq : ∀ i, t i ≤ q i) (hδ : 0 < δ) :
    (∀ i, s i ≤ roundedAllocation s p δ i) ∧
      (∀ i, t i ≤ transferredResidual q (removedAnchorMass s p δ) j i) := by
  refine ⟨fun i => (rounded_anchor_bounds _ _ _ (hsp i) hδ).1,?_⟩
  intro i
  apply le_trans (htq i)
  apply le_add_of_nonneg_right
  split_ifs
  · exact (removed_anchor_mass_bounds s p δ hsp hδ).1
  · exact le_refl 0

end
end SparseCompletion

/- Fixed source body: AllocationResponse.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem response_strategy_distance {ν : Type*} [Fintype ν]
    (A : ν → ν → ℝ) (x y : ν → ℝ) (M : ℝ)
    (hA : ∀ i j, |A i j| ≤ M) (i : ν) :
    |response A x i-response A y i| ≤ M*(∑ j, |x j-y j|) := by
  calc
    |response A x i-response A y i| = |∑ j, A i j*(x j-y j)| := by
      simp only [response,mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ j, |A i j*(x j-y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, M*|x j-y j| := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem exploitability_strategy_distance {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x y : ν → ℝ) (M : ℝ)
    (hA : ∀ i j, |A i j| ≤ M) :
    |exploitability A x-exploitability A y| ≤ M*(∑ j, |x j-y j|) := by
  have hone : ∀ x y : ν → ℝ, exploitability A x ≤ exploitability A y+M*(∑ j, |x j-y j|) := by
    intro x y
    apply (exploitability_le_iff A x _).mpr
    intro i
    have h := (abs_le.mp (response_strategy_distance A x y M hA i)).2
    linarith [response_le_exploitability A y i]
  apply abs_le.mpr
  constructor
  · have hh := hone y x
    simp_rw [abs_sub_comm (y _) (x _)] at hh
    linarith
  · linarith [hone x y]

theorem allocation_rounding_value_bound {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty (α ⊕ ι)]
    (s p : α → ℝ) (q : ι → ℝ) (δ M : ℝ) (j : ι)
    (A : (α ⊕ ι) → (α ⊕ ι) → ℝ)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) :
    exploitability A (blockWeights (roundedAllocation s p δ)
      (transferredResidual q (removedAnchorMass s p δ) j)) ≤
      exploitability A (blockWeights p q)+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  have h := (abs_le.mp (exploitability_strategy_distance A (blockWeights p q)
    (blockWeights (roundedAllocation s p δ) (transferredResidual q (removedAnchorMass s p δ) j)) M hA)).1
  have hd := mul_le_mul_of_nonneg_left (allocation_rounding_distance s p q δ j hsp hδ) hM
  norm_num only [Nat.cast_ofNat] at hd ⊢
  nlinarith

end
end SparseCompletion

/- Fixed source body: AllocationValue.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def floorStrategies {ν : Type*} [Fintype ν] (s : ν → ℝ) : Set (ν → ℝ) :=
  {x | (∀ i, s i ≤ x i) ∧ (∑ i, x i)=1}

theorem floor_strategy_coordinate_bounds {ν : Type*} [Fintype ν]
    (s x : ν → ℝ) (hs : ∀ i, 0 ≤ s i) (hx : x ∈ floorStrategies s) (i : ν) :
    0 ≤ x i ∧ x i ≤ 1 := by
  have hn : ∀ j, 0 ≤ x j := fun j => le_trans (hs j) (hx.1 j)
  refine ⟨hn i,?_⟩
  rw [←hx.2]
  exact Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)

theorem floor_strategies_compact {ν : Type*} [Fintype ν]
    (s : ν → ℝ) (hs : ∀ i, 0 ≤ s i) : IsCompact (floorStrategies s) := by
  have hc : IsClosed (floorStrategies s) := by
    have he : floorStrategies s=
        (⋂ i, {x : ν → ℝ | s i ≤ x i}) ∩ {x | (∑ i, x i)=1} := by
      ext x
      simp only [floorStrategies,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    rw [he]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  exact isCompact_Icc.of_isClosed_subset hc (fun x hx =>
    ⟨fun i => (floor_strategy_coordinate_bounds s x hs hx i).1,
      fun i => (floor_strategy_coordinate_bounds s x hs hx i).2⟩)

def allocationGridStrategies {α ι : Type*} [Fintype α] [Fintype ι]
    (s : (α ⊕ ι) → ℝ) (δ : ℝ) : Set ((α ⊕ ι) → ℝ) :=
  floorStrategies s ∩ {x | ∃ z : α → Fin (1+Nat.floor (1/δ)),
    ∀ i, x (Sum.inl i)=s (Sum.inl i)+δ*(z i : ℕ)}

theorem allocation_grid_strategies_compact {α ι : Type*} [Fintype α] [Fintype ι]
    (s : (α ⊕ ι) → ℝ) (δ : ℝ) (hs : ∀ i, 0 ≤ s i) :
    IsCompact (allocationGridStrategies s δ) := by
  classical
  apply (floor_strategies_compact s hs).inter_right
  have he : {x : (α ⊕ ι) → ℝ | ∃ z : α → Fin (1+Nat.floor (1/δ)),
      ∀ i, x (Sum.inl i)=s (Sum.inl i)+δ*(z i : ℕ)}=
      ⋃ z : α → Fin (1+Nat.floor (1/δ)),
        ⋂ i, {x | x (Sum.inl i)=s (Sum.inl i)+δ*(z i : ℕ)} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_iInter]
  rw [he]
  exact isClosed_iUnion_of_finite fun z => isClosed_iInter fun i =>
    isClosed_eq (continuous_apply _) continuous_const

theorem allocation_rounding_in_grid {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s : (α ⊕ ι) → ℝ) (x : (α ⊕ ι) → ℝ) (δ : ℝ) (j : ι)
    (hs : ∀ i, 0 ≤ s i) (hx : x ∈ floorStrategies s) (hδ : 0 < δ) :
    blockWeights (roundedAllocation (fun i => s (Sum.inl i)) (fun i => x (Sum.inl i)) δ)
      (transferredResidual (fun i => x (Sum.inr i))
        (removedAnchorMass (fun i => s (Sum.inl i)) (fun i => x (Sum.inl i)) δ) j) ∈
      allocationGridStrategies s δ := by
  have hsp := fun i => hx.1 (Sum.inl i)
  have htq := fun i => hx.1 (Sum.inr i)
  have hf := allocation_rounding_preserves_floors _ _ _ _ δ j hsp htq hδ
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    cases i with
    | inl i => exact hf.1 i
    | inr i => exact hf.2 i
  · rw [blockWeights_mass,allocation_rounding_mass]
    exact (Fintype.sum_sum_type x).symm.trans hx.2
  · obtain ⟨z,hz⟩ := rounded_allocation_finite_grid
      (fun i => s (Sum.inl i)) (fun i => x (Sum.inl i)) δ
      (fun i => hs (Sum.inl i))
      (fun i => (floor_strategy_coordinate_bounds s x hs hx (Sum.inl i)).2) hδ
    exact ⟨z,hz⟩

end
end SparseCompletion

/- Fixed source body: AllocationApproximation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem floor_strategies_nonempty {ν : Type*} [Fintype ν] [DecidableEq ν]
    (s : ν → ℝ) (j : ν) (hm : (∑ i, s i) ≤ 1) : (floorStrategies s).Nonempty := by
  refine ⟨transferredResidual s (1-∑ i, s i) j,?_,?_⟩
  · intro i
    apply le_add_of_nonneg_right
    split_ifs
    · linarith
    · exact le_refl 0
  · rw [transferred_residual_mass]
    ring

theorem allocation_grid_nonempty {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s : (α ⊕ ι) → ℝ) (δ : ℝ) (j : ι)
    (hs : ∀ i, 0 ≤ s i) (hne : (floorStrategies s).Nonempty) (hδ : 0 < δ) :
    (allocationGridStrategies s δ).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨_,allocation_rounding_in_grid s x δ j hs hx hδ⟩

theorem optimistic_allocation_grid_bounds {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] [Nonempty (α ⊕ ι)]
    (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M δ : ℝ) (s : (α ⊕ ι) → ℝ) (j : ι)
    (hI : ValidIntervalSystem lo hi M) (hs : ∀ i, 0 ≤ s i)
    (hne : (floorStrategies s).Nonempty) (hδ : 0 < δ) :
    optimisticValue lo hi M (floorStrategies s) ≤
        optimisticValue lo hi M (allocationGridStrategies s δ) ∧
    optimisticValue lo hi M (allocationGridStrategies s δ) ≤
        optimisticValue lo hi M (floorStrategies s)+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  have hc := floor_strategies_compact s hs
  have hg := allocation_grid_strategies_compact s δ hs
  have hgn := allocation_grid_nonempty s δ j hs hne hδ
  constructor
  · obtain ⟨A,hA,x,hx,he⟩ := optimistic_value_attained lo hi M _ hI hg hgn
    have hh := optimistic_value_le_witness lo hi M _ hc A x hA hx.1
    rwa [he] at hh
  · obtain ⟨A,hA,x,hx,he⟩ := optimistic_value_attained lo hi M _ hI hc hne
    let p := fun i => x (Sum.inl i)
    let q := fun i => x (Sum.inr i)
    let t := fun i => s (Sum.inl i)
    have hxdec : blockWeights p q=x := by ext i; cases i <;> rfl
    let x' := blockWeights (roundedAllocation t p δ)
      (transferredResidual q (removedAnchorMass t p δ) j)
    have hx' : x' ∈ allocationGridStrategies s δ := allocation_rounding_in_grid s x δ j hs hx hδ
    have hv := optimistic_value_le_witness lo hi M _ hg A x' hA hx'
    have hb : ∀ i j, |A i j| ≤ M := fun i j => abs_le.mpr (hA.1.2 i j)
    have hh := allocation_rounding_value_bound t p q δ M j A
      (fun i => hx.1 (Sum.inl i)) hδ hI.1 hb
    rw [hxdec,he] at hh
    exact le_trans hv hh

end
end SparseCompletion

/- Fixed source body: IntervalGap.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def perspectiveCall {ι : Type*} [Fintype ι] (q H : ι → ℝ) (ρ z : ℝ) : ℝ :=
  ∑ i, max (H i-(ρ+z)*q i) 0

theorem perspective_call_identity {ι : Type*} [Fintype ι]
    (q t H : ι → ℝ) (ρ z : ℝ) (hq : ∀ i, 0 ≤ q i) (hH : ∀ i, q i*t i=H i) :
    call q (fun i => t i-ρ) z=perspectiveCall q H ρ z := by
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ (hq i),mul_zero]
  congr 1
  linear_combination hH i

theorem perspective_call_epigraph_iff {ι : Type*} [Fintype ι]
    (q H : ι → ℝ) (ρ z C : ℝ) :
    perspectiveCall q H ρ z ≤ C ↔
      ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, H i-(ρ+z)*q i ≤ a i) ∧ (∑ i, a i) ≤ C := by
  constructor
  · intro h
    exact ⟨fun i => max (H i-(ρ+z)*q i) 0,fun i => le_max_right _ _,
      fun i => le_max_left _ _,h⟩
  · rintro ⟨a,ha,hb,hc⟩
    exact le_trans (Finset.sum_le_sum fun i _ => max_le (hb i) (ha i)) hc

def intervalGapPoint {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
  (∀ h, (∑ a, K h a*p a)-(∑ i, V i h) ≤ ρ) ∧
  (∀ i, score lo p i ≤ ρ+M*r) ∧
  (∀ i, intervalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : ℕ, 1 ≤ l → l ≤ gridSize M r η →
    perspectiveCall q (intervalMomentScore p V) ρ (M*r-gridNode M r η l) ≤
      envelope M r (M*r-gridNode M r η l)

theorem interval_gap_recovered_exact_point {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hlu : ∀ i h, lo i h ≤ hi i h)
    (h : intervalGapPoint K lo hi V p q M r ρ η) :
    (∀ i h, lo i h ≤ intervalCrossRecover lo V q i h ∧ intervalCrossRecover lo V q i h ≤ hi i h) ∧
      fixedAnchorGapPoint K (intervalCrossRecover lo V q) p q M r ρ η := by
  rcases h with ⟨hq,hm,hV,ha,hlo,hcap,hgrid⟩
  obtain ⟨hD,hprod⟩ := interval_recovered_cross_bounds lo hi V q hq hlu
    (fun i h => (hV i h).1) (fun i h => (hV i h).2)
  have hH := fun i => interval_recovered_score_moment lo V p q hprod i
  refine ⟨hD,hq,hm,?_,?_,?_⟩
  · intro i
    by_cases hz : q i=0
    · simpa only [score,intervalCrossRecover,perspectiveRecover,hz,ite_true] using hlo i
    · have hp : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
      have hc := hcap i
      rw [←hH i] at hc
      exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [mul_comm] using hc)
  · intro a
    rw [anchor_response_of_perspective K _ V p q hprod a]
    exact ha a
  · intro l hl hL
    rw [perspective_call_identity q _ _ ρ _ hq hH]
    exact hgrid l hl hL

theorem interval_gap_completed_witness {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hlu : ∀ i h, lo i h ≤ hi i h) (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧ IsSkew B ∧
      (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ+η := by
  obtain ⟨hD,hg⟩ := interval_gap_recovered_exact_point K lo hi V p q M r ρ η hlu h
  obtain ⟨B,hB,hb,hrows⟩ := gap_point_completed_witness K _ p q M r ρ η hM hr hη hg
  exact ⟨intervalCrossRecover lo V q,B,hD,hB,hb,hrows⟩

end
end SparseCompletion

/- Fixed source body: IntervalGapGame.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem exact_interval_completion_gap_point {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (hD : ∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h)
    (hB : IsSkew B) (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ V, intervalGapPoint K lo hi V p q M r ρ η := by
  have hg := exact_completion_gap_point K D B p q M r ρ η hM hq hr hB hb hrows
  let V := fun i h => q i*D i h
  have hprod : ∀ i h, q i*D i h=V i h := fun _ _ => rfl
  have hH : ∀ i, q i*score D p i=intervalMomentScore p V i := by
    intro i
    unfold score intervalMomentScore
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by dsimp only [V]; ring
  refine ⟨V,hq,hr,?_,?_,?_,?_,?_⟩
  · intro i h
    exact ⟨by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).1) (hq i)],
      by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).2) (hq i)]⟩
  · intro h
    rw [←anchor_response_of_perspective K D V p q hprod h]
    exact hg.2.2.2.1 h
  · intro i
    exact le_trans (score_lower_from_intervals lo D p hp (fun i h => (hD i h).1) i) (hg.2.2.1 i)
  · intro i
    rw [←hH i,mul_comm (q i)]
    exact mul_le_mul_of_nonneg_right (hg.2.2.1 i) (hq i)
  · intro l hl hL
    rw [←perspective_call_identity q (score D p) _ ρ _ hq hH]
    exact hg.2.2.2.2 l hl hL

theorem normalized_interval_gap_completed_witness {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hm : (∑ h, p h)+r=1)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
      (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
      IsSkew (blockMatrix K D B) ∧
      (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ+η := by
  obtain ⟨D,B,hD,hB,hb,hrows⟩ := interval_gap_completed_witness K lo hi V p q M r ρ η hM hr hη hlu h
  have hDb := fun i a => And.intro (le_trans (hlo i a) (hD i a).1) (le_trans (hD i a).2 (hhi i a))
  refine ⟨D,B,hD,blockWeights_nonneg p q hp h.1,?_,blockMatrix_skew K D B hK hB,
    blockMatrix_bounds K D B M hKb hDb hb,hrows⟩
  rw [blockWeights_mass,h.2.1]
  exact hm

end
end SparseCompletion

/- Fixed source body: Bisection.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
namespace RationalBisection

/-- Conditional rational bisection: the caller supplies genuine decidable
    feasibility. This definition does not implement an LP feasibility oracle. -/
def run (P : ℚ → Prop) [DecidablePred P] : ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, lo, hi => (lo,hi)
  | n+1, lo, hi =>
    let z := run P n lo hi
    let mid := (z.1+z.2)/((2 : ℕ) : ℚ)
    if P mid then (z.1,mid) else (mid,z.2)

/-- A feasible upper endpoint and infeasible lower endpoint are retained. -/
theorem endpoint_invariant (P : ℚ → Prop) [DecidablePred P]
    (lo hi : ℚ) (hn : ¬P lo) (hy : P hi) (n : ℕ) :
    ¬P (run P n lo hi).1 ∧ P (run P n lo hi).2 := by
  induction n with
  | zero => exact ⟨hn,hy⟩
  | succ n ih =>
    simp only [run]
    split_ifs with hm
    · exact ⟨ih.1,hm⟩
    · exact ⟨hm,ih.2⟩

theorem nested_bracket (P : ℚ → Prop) [DecidablePred P]
    (lo hi : ℚ) (hlh : lo ≤ hi) (n : ℕ) :
    lo ≤ (run P n lo hi).1 ∧ (run P n lo hi).1 ≤ (run P n lo hi).2 ∧
      (run P n lo hi).2 ≤ hi := by
  induction n with
  | zero => exact ⟨le_refl _,hlh,le_refl _⟩
  | succ n ih =>
    simp only [run]
    split_ifs <;> dsimp only
    · exact ⟨ih.1,by linarith [ih.2.1],by linarith [ih.2.1,ih.2.2]⟩
    · exact ⟨by linarith [ih.1,ih.2.1],by linarith [ih.2.1],ih.2.2⟩

theorem width_exact (P : ℚ → Prop) [DecidablePred P]
    (lo hi : ℚ) (n : ℕ) :
    (run P n lo hi).2-(run P n lo hi).1=(hi-lo)/((2 : ℕ) : ℚ)^n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hh : ((run P n lo hi).2-(run P n lo hi).1)/((2 : ℕ) : ℚ)=
        (hi-lo)/((2 : ℕ) : ℚ)^(n+1) := by
      rw [ih,pow_succ,div_div]
    simp only [run]
    split_ifs <;> dsimp only <;> linarith

/-- Monotonicity turns an infeasible endpoint into an excluded lower region. -/
theorem excludes_below (P : ℚ → Prop) [DecidablePred P] (hmono : Monotone P)
    (lo hi : ℚ) (hn : ¬P lo) (hy : P hi) (n : ℕ) (ρ : ℚ)
    (hρ : ρ ≤ (run P n lo hi).1) : ¬P ρ := by
  intro hp
  exact (endpoint_invariant P lo hi hn hy n).1 (hmono hρ hp)

/-- Finite iteration certificate: once the explicit halved width is at most ζ,
    the returned upper endpoint is feasible and the bracket has width at most ζ. -/
theorem certified_bracket (P : ℚ → Prop) [DecidablePred P]
    (lo hi ζ : ℚ) (hlh : lo ≤ hi) (hn : ¬P lo) (hy : P hi)
    (n : ℕ) (hwidth : (hi-lo)/((2 : ℕ) : ℚ)^n ≤ ζ) :
    let z := run P n lo hi
    lo ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ hi ∧ ¬P z.1 ∧ P z.2 ∧ z.2-z.1 ≤ ζ := by
  obtain ⟨hlo,horder,hhi⟩ := nested_bracket P lo hi hlh n
  obtain ⟨hl,hu⟩ := endpoint_invariant P lo hi hn hy n
  exact ⟨hlo,horder,hhi,hl,hu,(width_exact P lo hi n).symm ▸ hwidth⟩

theorem nat_le_two_pow (n : ℕ) : (n : ℚ) ≤ ((2 : ℕ) : ℚ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    have hp : (1 : ℚ) ≤ ((2 : ℕ) : ℚ)^n := one_le_pow₀ (by norm_num)
    norm_num only [Nat.cast_ofNat] at *
    linarith

/-- Positive requested width is reached after a finite number of iterations.
    This is an existence theorem, not an operation-count or bit-cost claim. -/
theorem exists_finite_width (P : ℚ → Prop) [DecidablePred P]
    (lo hi ζ : ℚ) (hζ : 0 < ζ) :
    ∃ n : ℕ, (run P n lo hi).2-(run P n lo hi).1 ≤ ζ := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((hi-lo)/ζ)
  refine ⟨n,?_⟩
  rw [width_exact]
  have hh : (hi-lo)/ζ < ((2 : ℕ) : ℚ)^n := lt_of_lt_of_le hn (nat_le_two_pow n)
  have hb := (div_lt_iff₀ hζ).mp hh
  norm_num only [Nat.cast_ofNat] at *
  exact (div_le_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) n)).mpr (by linarith)

/-- The lower endpoint may already be feasible; return it immediately in that
    case. This permits the paper's initial nonnegative bracket [0,M]. -/
def search (P : ℚ → Prop) [DecidablePred P] (n : ℕ) (lo hi : ℚ) : ℚ × ℚ :=
  if P lo then (lo,lo) else run P n lo hi

theorem search_spec (P : ℚ → Prop) [DecidablePred P] (n : ℕ)
    (lo hi : ℚ) (hlh : lo ≤ hi) (hy : P hi) :
    let z := search P n lo hi
    lo ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ hi ∧ P z.2 ∧
      (z.1=lo ∨ ¬P z.1) ∧ z.2-z.1 ≤ (hi-lo)/((2 : ℕ) : ℚ)^n := by
  unfold search
  split_ifs with hn
  · refine ⟨le_refl _,le_refl _,hlh,hn,Or.inl rfl,?_⟩
    dsimp only
    exact sub_self lo ▸ div_nonneg (sub_nonneg.mpr hlh) (le_of_lt (pow_pos (by norm_num) n))
  · obtain ⟨hl,ho,hu⟩ := nested_bracket P lo hi hlh n
    obtain ⟨hno,hyes⟩ := endpoint_invariant P lo hi hn hy n
    exact ⟨hl,ho,hu,hyes,Or.inr hno,(width_exact P lo hi n).le⟩

/-- Conditional extraction of a feasible upper-end witness and a real value
    interval. The caller supplies feasibility soundness and lower exclusion;
    neither a rational LP oracle nor a reconstruction algorithm is invented. -/
theorem value_certificate {β : Type*} (P : ℚ → Prop) [DecidablePred P]
    (Witness : ℚ → β → Prop) (V η : ℝ) (M ζ : ℚ) (n : ℕ)
    (hM : 0 ≤ M) (hupper : P M) (hV : 0 ≤ V)
    (hlower : ∀ ρ : ℚ, ¬P ρ → (ρ : ℝ) ≤ V)
    (hsound : ∀ ρ : ℚ, P ρ → ∃ w, Witness ρ w ∧ V ≤ (ρ : ℝ)+η)
    (hwidth : M/((2 : ℕ) : ℚ)^n ≤ ζ) :
    let z := search P n 0 M
    (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+η ∧
      (z.2 : ℝ)+η-(z.1 : ℝ) ≤ η+(ζ : ℝ) ∧ ∃ w, Witness z.2 w := by
  obtain ⟨_,_,_,hu,hl,hw⟩ := search_spec P n 0 M hM hupper
  obtain ⟨w,hW,hv⟩ := hsound _ hu
  have hlow : ((search P n 0 M).1 : ℝ) ≤ V := by
    rcases hl with he | hn
    · rw [he]; exact_mod_cast hV
    · exact hlower _ hn
  have hh : (search P n 0 M).2-(search P n 0 M).1 ≤ ζ := by
    exact le_trans hw (by simpa only [sub_zero] using hwidth)
  have hhR : ((search P n 0 M).2 : ℝ)-((search P n 0 M).1 : ℝ) ≤ (ζ : ℝ) := by
    exact_mod_cast hh
  exact ⟨hlow,hv,by linarith,w,hW⟩

end RationalBisection
end SparseCompletion

/- Fixed source body: IntervalGapEpigraph.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def intervalGapEpigraphPoint {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (a : Fin (gridSize M r η) → ι → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
  (∀ h, (∑ b, K h b*p b)-(∑ i, V i h) ≤ ρ) ∧
  (∀ i, score lo p i ≤ ρ+M*r) ∧
  (∀ i, intervalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : Fin (gridSize M r η),
    (∀ i, 0 ≤ a l i) ∧
    (∀ i, intervalMomentScore p V i-(ρ+(M*r-gridNode M r η (l.val+1)))*q i ≤ a l i) ∧
    (∑ i, a l i) ≤ envelope M r (M*r-gridNode M r η (l.val+1))

theorem interval_gap_epigraph_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) :
    intervalGapPoint K lo hi V p q M r ρ η ↔ ∃ a, intervalGapEpigraphPoint K lo hi V p q M r ρ η a := by
  constructor
  · rintro ⟨hq,hm,hV,ha,hg,hcap,hcalls⟩
    let a := fun (l : Fin (gridSize M r η)) i =>
      max (intervalMomentScore p V i-(ρ+(M*r-gridNode M r η (l.val+1)))*q i) 0
    refine ⟨a,hq,hm,hV,ha,hg,hcap,?_⟩
    intro l
    exact ⟨fun i => le_max_right _ _,fun i => le_max_left _ _,
      hcalls (l.val+1) (by omega) (by omega)⟩
  · rintro ⟨a,hq,hm,hV,ha,hg,hcap,hcalls⟩
    refine ⟨hq,hm,hV,ha,hg,hcap,?_⟩
    intro l hl hL
    let u : Fin (gridSize M r η) := ⟨l-1,by omega⟩
    have he : u.val+1=l := by dsimp only [u]; omega
    have hh := (perspective_call_epigraph_iff q (intervalMomentScore p V) ρ
      (M*r-gridNode M r η (u.val+1)) (envelope M r (M*r-gridNode M r η (u.val+1)))).mpr
        ⟨a u,hcalls u⟩
    simpa only [he] using hh

end
end SparseCompletion

/- Fixed source body: GapSparse.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Compression of a supplied finite-gap point preserves the original grid
    exactly. No second slack is introduced and no vertex algorithm is assumed. -/
theorem gap_sparse_point_positive {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ) (hr : 0 < r)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ q' : ι → ℝ, fixedAnchorGapPoint K D p q' M r ρ η ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      ∀ a, anchorResponse K D p q' a=anchorResponse K D p q a := by
  classical
  let H := gridSize M r η
  obtain ⟨q',hq',hm',hs,hc,hfeatures⟩ := finite_feature_compression (Fin k ⊕ Fin H)
    q (sparseFeatures k H D (fun i => score D p i-ρ) M r η) r h.1 h.2.1 hr
  have hmom : ∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a := fun a => hfeatures (.inl a)
  have hanchor := anchor_response_of_moments k K D p q q' hmom
  refine ⟨q',⟨hq',hm',h.2.2.1,?_,?_⟩,hs,?_,hmom,hanchor⟩
  · intro a
    rw [hanchor]
    exact h.2.2.2.1 a
  · intro l hl hlH
    let j : Fin H := ⟨l-1,by dsimp only [H]; omega⟩
    have hj : j.val+1=l := by dsimp only [j]; omega
    have he := hfeatures (.inr j)
    change (∑ i, q' i*max ((score D p i-ρ)-(M*r-gridNode M r η (j.val+1))) 0)=
      ∑ i, q i*max ((score D p i-ρ)-(M*r-gridNode M r η (j.val+1))) 0 at he
    rw [hj] at he
    change (∑ i, q' i*max ((score D p i-ρ)-(M*r-gridNode M r η l)) 0) ≤ _
    rw [he]
    exact h.2.2.2.2 l hl hlH
  · apply Nat.le_min.mpr
    constructor
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_right_comm k H 1,H] using hc

theorem gap_sparse_point {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ q' : ι → ℝ, fixedAnchorGapPoint K D p q' M r ρ η ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      ∀ a, anchorResponse K D p q' a=anchorResponse K D p q a := by
  classical
  have hr : 0 ≤ r := by rw [←h.2.1]; exact Finset.sum_nonneg fun i _ => h.1 i
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q h.1 (by simpa only [hz] using h.2.1)
    refine ⟨q,h,fun _ hi => hi,?_,fun _ => rfl,fun _ => rfl⟩
    simp [hzero]
  · exact gap_sparse_point_positive k K D p q M r ρ η (lt_of_le_of_ne hr (Ne.symm hz)) h

theorem gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, anchorResponse K D p q' a=anchorResponse K D p q a) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η := by
  obtain ⟨q',hg,hs,hc,hm,hanchor⟩ := gap_sparse_point k K D p q M r ρ η h
  have hr : 0 ≤ r := by rw [←h.2.1]; exact Finset.sum_nonneg fun i _ => h.1 i
  obtain ⟨B',hB,hb,hrows⟩ := gap_point_completed_witness K D p q' M r ρ η hM hr hη hg
  exact ⟨q',B',hg.1,hg.2.1,hs,hc,hm,hanchor,hB,hb,hrows⟩

/-- Full normalized-game sparse gap witness, still at the original single slack. -/
theorem normalized_gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a)
    (hnorm : (∑ a, p a)+r=1) (hK : IsSkew K)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤
        min (k+Fintype.card ι) ((2 : ℕ)*k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, anchorResponse K D p q' a=anchorResponse K D p q a) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η := by
  classical
  obtain ⟨q',B',hq',hm,hs,hc,hmo,ha,hB,hb,hrows⟩ :=
    gap_sparse_completed_witness k K D p q M r ρ η hM hη h
  refine ⟨q',B',blockWeights_nonneg p q' hp hq',?_,hs,hc,?_,hmo,ha,
    blockMatrix_skew K D B' hK hB,blockMatrix_bounds K D B' M hKb hDb hb,hrows⟩
  · rw [blockWeights_mass,hm]
    exact hnorm
  · rw [block_support_card]
    have hpa : (Finset.univ.filter fun a => p a ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    have h1 := le_trans hc (min_le_left _ _)
    have h2 := le_trans hc (min_le_right _ _)
    exact Nat.le_min.mpr ⟨by omega,by omega⟩

end
end SparseCompletion

/- Fixed source body: IntervalGapSparse.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Recover compatible cross data once and hold it fixed during compression. -/
theorem interval_gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (lo hi V : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i a, lo i a ≤ intervalCrossRecover lo V q i a ∧
        intervalCrossRecover lo V q i a ≤ hi i a) ∧
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*intervalCrossRecover lo V q i a)=
        ∑ i, q i*intervalCrossRecover lo V q i a) ∧
      (∀ a, anchorResponse K (intervalCrossRecover lo V q) p q' a=
        anchorResponse K (intervalCrossRecover lo V q) p q a) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      ∀ a, response (blockMatrix K (intervalCrossRecover lo V q) B')
        (blockWeights p q') a ≤ ρ+η := by
  obtain ⟨hD,hg⟩ := interval_gap_recovered_exact_point K lo hi V p q M r ρ η hlu h
  obtain ⟨q',B',hq',hm,hs,hc,hmo,ha,hB,hb,hrows⟩ :=
    gap_sparse_completed_witness k K (intervalCrossRecover lo V q) p q M r ρ η hM hη hg
  exact ⟨q',B',hD,hq',hm,hs,hc,hmo,ha,hB,hb,hrows⟩

theorem normalized_interval_gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (lo hi V : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a)
    (hnorm : (∑ a, p a)+r=1) (hK : IsSkew K)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hlo : ∀ i a, -M ≤ lo i a) (hhi : ∀ i a, hi i a ≤ M)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i a, lo i a ≤ intervalCrossRecover lo V q i a ∧
        intervalCrossRecover lo V q i a ≤ hi i a) ∧
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤
        min (k+Fintype.card ι) ((2 : ℕ)*k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*intervalCrossRecover lo V q i a)=
        ∑ i, q i*intervalCrossRecover lo V q i a) ∧
      (∀ a, anchorResponse K (intervalCrossRecover lo V q) p q' a=
        anchorResponse K (intervalCrossRecover lo V q) p q a) ∧
      IsSkew (blockMatrix K (intervalCrossRecover lo V q) B') ∧
      (∀ a b, -M ≤ blockMatrix K (intervalCrossRecover lo V q) B' a b ∧
        blockMatrix K (intervalCrossRecover lo V q) B' a b ≤ M) ∧
      ∀ a, response (blockMatrix K (intervalCrossRecover lo V q) B')
        (blockWeights p q') a ≤ ρ+η := by
  obtain ⟨hD,hg⟩ := interval_gap_recovered_exact_point K lo hi V p q M r ρ η hlu h
  have hDb : ∀ i a, -M ≤ intervalCrossRecover lo V q i a ∧ intervalCrossRecover lo V q i a ≤ M :=
    fun i a => ⟨le_trans (hlo i a) (hD i a).1,le_trans (hD i a).2 (hhi i a)⟩
  obtain ⟨q',B',hn,hm,hs,hc,ht,hmo,ha,hB,hb,hrows⟩ :=
    normalized_gap_sparse_completed_witness k K (intervalCrossRecover lo V q) p q M r ρ η
      hM hη hp hnorm hK hKb hDb hg
  exact ⟨q',B',hD,hn,hm,hs,hc,ht,hmo,ha,hB,hb,hrows⟩

end
end SparseCompletion

/- Fixed source body: RationalGrid.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalGridSize (M r η : ℚ) : ℕ := Nat.sqrt (Nat.ceil (M*r/η))+1

def rationalGridNode (M r η : ℚ) (l : ℕ) : ℚ :=
  min ((2 : ℕ)*η*(l : ℚ)^2) ((2 : ℕ)*M*r)


theorem rational_grid_size_bound (M r η : ℚ) (hη : 0 < η) :
    M*r ≤ η*(rationalGridSize M r η : ℚ)^2 := by
  have h1 := Nat.le_ceil (M*r/η)
  have h2 : (Nat.ceil (M*r/η) : ℚ) < (rationalGridSize M r η : ℚ)^2 := by
    unfold rationalGridSize
    exact_mod_cast Nat.lt_succ_sqrt' (Nat.ceil (M*r/η))
  have hh := (div_lt_iff₀ hη).mp (lt_of_le_of_lt h1 h2)
  nlinarith

theorem rational_grid_size_real_bound (M r η : ℚ) (hη : 0 < η) :
    (M : ℝ)*(r : ℝ) ≤ (η : ℝ)*(rationalGridSize M r η : ℝ)^2 := by
  exact_mod_cast rational_grid_size_bound M r η hη

theorem rational_grid_node_real (M r η : ℚ) (l : ℕ) :
    (rationalGridNode M r η l : ℝ)=gridNode (M : ℝ) (r : ℝ) (η : ℝ) l := by
  unfold rationalGridNode gridNode
  push_cast
  rfl

def rationalCall {ι : Type*} [Fintype ι] (q v : ι → ℚ) (z : ℚ) : ℚ :=
  ∑ i, q i*max (v i-z) 0

def rationalEnvelope (M r z : ℚ) : ℚ := (M*r-z)^2/((4 : ℕ)*M)

theorem rational_call_real {ι : Type*} [Fintype ι] (q v : ι → ℚ) (z : ℚ) :
    (rationalCall q v z : ℝ)=call (fun i => (q i : ℝ)) (fun i => (v i : ℝ)) (z : ℝ) := by
  unfold rationalCall call
  push_cast
  rfl

theorem rational_envelope_real (M r z : ℚ) :
    (rationalEnvelope M r z : ℝ)=envelope (M : ℝ) (r : ℝ) (z : ℝ) := by
  unfold rationalEnvelope envelope
  push_cast
  rfl


theorem rational_finite_grid_implication {ι : Type*} [Fintype ι]
    (q v : ι → ℚ) (M r η : ℚ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hcap : ∀ i, q i ≠ 0 → v i ≤ M*r)
    (hgrid : ∀ l : ℕ, 1 ≤ l → l ≤ rationalGridSize M r η →
      rationalCall q v (M*r-rationalGridNode M r η l) ≤
        rationalEnvelope M r (M*r-rationalGridNode M r η l)) :
    ∀ z ∈ Set.Icc (-(M : ℝ)*(r : ℝ)) ((M : ℝ)*(r : ℝ)),
      call (fun i => (q i : ℝ)) (fun i => (v i : ℝ)-(η : ℝ)) z ≤
        envelope (M : ℝ) (r : ℝ) z := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hrR : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  apply finite_grid_implication (fun i => (q i : ℝ)) (fun i => (v i : ℝ))
    (M : ℝ) (r : ℝ) (η : ℝ) (rationalGridSize M r η) hMR hrR hηR
    (rational_grid_size_real_bound M r η hη)
    (fun i => by exact_mod_cast hq i)
  · intro i hi
    have hqi : q i ≠ 0 := by intro h; simp only [h,Rat.cast_zero] at hi; exact hi rfl
    exact_mod_cast hcap i hqi
  · intro l hl hL
    have hh : (rationalCall q v (M*r-rationalGridNode M r η l) : ℝ) ≤
        (rationalEnvelope M r (M*r-rationalGridNode M r η l) : ℝ) := by
      exact_mod_cast hgrid l hl hL
    simpa only [rational_call_real,rational_envelope_real,Rat.cast_sub,Rat.cast_mul,
      rational_grid_node_real] using hh

end SparseCompletion

/- Fixed source body: RationalGridSizeBounds.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

theorem rational_grid_size_positive (M r η : ℚ) : 0 < rationalGridSize M r η := by
  unfold rationalGridSize
  omega

theorem rational_grid_size_linear_bound (M r η : ℚ) :
    rationalGridSize M r η ≤ Nat.ceil (M*r/η)+1 :=
  Nat.add_le_add_right (Nat.sqrt_le_self _) 1

theorem rational_grid_size_sqrt_bound (M r η : ℚ)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hη : 0 < η) :
    (rationalGridSize M r η : ℝ) ≤
      Real.sqrt ((M : ℝ)*(r : ℝ)/(η : ℝ))+(2 : ℕ) := by
  let a := M*r/η
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hM hr) (le_of_lt hη)
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hceil : (Nat.ceil a : ℝ) < (a : ℝ)+1 := by exact_mod_cast Nat.ceil_lt_add_one ha
  have hs : (Nat.sqrt (Nat.ceil a) : ℝ)^2 ≤ (Nat.ceil a : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (Nat.ceil a)
  have hroot := Real.sq_sqrt haR
  have hroot0 := Real.sqrt_nonneg (a : ℝ)
  have hn : (0 : ℝ) ≤ (Nat.sqrt (Nat.ceil a) : ℝ) := Nat.cast_nonneg _
  have hh : (Nat.sqrt (Nat.ceil a) : ℝ) ≤ Real.sqrt (a : ℝ)+1 := by nlinarith
  have he : (a : ℝ)=(M : ℝ)*(r : ℝ)/(η : ℝ) := by dsimp only [a]; push_cast; rfl
  unfold rationalGridSize
  change ((Nat.sqrt (Nat.ceil a)+1 : ℕ) : ℝ) ≤ _
  rw [Nat.cast_add,Nat.cast_one,←he]
  norm_num only [Nat.cast_ofNat]
  linarith

end SparseCompletion

/- Fixed source body: RationalGap.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalScore {α ι : Type*} [Fintype α] (D : ι → α → ℚ) (p : α → ℚ) (i : ι) : ℚ :=
  ∑ h, D i h*p h

def rationalAnchorResponse {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℚ) (D : ι → α → ℚ) (p : α → ℚ) (q : ι → ℚ) (h : α) : ℚ :=
  (∑ a, K h a*p a)-∑ i, D i h*q i

def RationalGapConditions {k m : ℕ} (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i, rationalScore D p i ≤ ρ+M*r) ∧
  (∀ h, rationalAnchorResponse K D p q h ≤ ρ) ∧
  ∀ l : Fin (rationalGridSize M r η),
    rationalCall q (fun i => rationalScore D p i-ρ) (M*r-rationalGridNode M r η (l.val+1)) ≤
      rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))

instance rationalGapConditionsDecidable {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    Decidable (RationalGapConditions K D p q M r ρ η) := by
  unfold RationalGapConditions
  infer_instance

def checkRationalGap {k m : ℕ} (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) : Bool :=
  decide (RationalGapConditions K D p q M r ρ η)

theorem rational_gap_check_iff {k m : ℕ} (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    checkRationalGap K D p q M r ρ η=true ↔ RationalGapConditions K D p q M r ρ η := by
  simp only [checkRationalGap,decide_eq_true_eq]

theorem rational_score_real {α ι : Type*} [Fintype α] (D : ι → α → ℚ) (p : α → ℚ) (i : ι) :
    (rationalScore D p i : ℝ)=score (fun i h => (D i h : ℝ)) (fun h => (p h : ℝ)) i := by
  unfold rationalScore score
  push_cast
  rfl

theorem rational_anchor_response_real {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℚ) (D : ι → α → ℚ) (p : α → ℚ) (q : ι → ℚ) (h : α) :
    (rationalAnchorResponse K D p q h : ℝ)=
      anchorResponse (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
        (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) h := by
  unfold rationalAnchorResponse anchorResponse
  push_cast
  rfl


theorem rational_gap_completed_witness {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hcheck : checkRationalGap K D p q M r ρ η=true) :
    ∃ B : Fin m → Fin m → ℝ, IsSkew B ∧
      (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  have h := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  have hr : 0 ≤ r := by rw [←h.2.1]; exact Finset.sum_nonneg fun i _ => h.1 i
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hqr : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := fun i => by exact_mod_cast h.1 i
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast h.2.1
  have hg : ∀ i, score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i ≤
      (ρ : ℝ)+(M : ℝ)*(r : ℝ) := by
    intro i
    have hh : (rationalScore D p i : ℝ) ≤ ((ρ+M*r : ℚ) : ℝ) := by exact_mod_cast h.2.2.1 i
    simpa only [rational_score_real,Rat.cast_add,Rat.cast_mul] using hh
  have hc := rational_finite_grid_implication q (fun i => rationalScore D p i-ρ) M r η hM hr hη h.1
    (fun i _ => by linarith [h.2.2.1 i]) (by
      intro l hl hL
      let u : Fin (rationalGridSize M r η) := ⟨l-1,by omega⟩
      have he : u.val+1=l := by dsimp only [u]; omega
      simpa only [he] using h.2.2.2.2 u)
  have hcuts := call_bound_implies_cuts (fun i => (q i : ℝ))
    (fun i => ((rationalScore D p i-ρ : ℚ) : ℝ)-(η : ℝ)) (M : ℝ) (r : ℝ) hMR hqr hm hc
  have he : (fun i => ((rationalScore D p i-ρ : ℚ) : ℝ)-(η : ℝ))=
      (fun i => score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i-((ρ : ℝ)+(η : ℝ))) := by
    funext i
    rw [Rat.cast_sub,rational_score_real]
    ring
  rw [he] at hcuts
  obtain ⟨B,hB,hb,hrows⟩ := (weighted_completion_iff (fun i => (q i : ℝ))
    (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))) (M : ℝ) (r : ℝ)
    ((ρ : ℝ)+(η : ℝ)) (le_of_lt hMR) hqr hm).mpr
      ⟨fun i => by
        have hh : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
        linarith [hg i],hcuts⟩
  refine ⟨B,hB,hb,?_⟩
  apply (block_response_bounds_iff _ _ B _ _ _).mpr
  refine ⟨?_,hrows⟩
  intro a
  have hh : (rationalAnchorResponse K D p q a : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h.2.2.2.1 a
  rw [rational_anchor_response_real] at hh
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  linarith


theorem rational_gap_normalized_full_game {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hK : ∀ a b, K a b= -K b a)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hcheck : checkRationalGap K D p q M r ρ η=true) :
    ∃ B : Fin m → Fin m → ℝ,
      (∀ a, 0 ≤ blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a) ∧
      (∑ a, blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
      IsSkew (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B) ∧
      (∀ a b, -(M : ℝ) ≤ blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B a b ∧
        blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B a b ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  have h := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  obtain ⟨B,hB,hb,hrows⟩ := rational_gap_completed_witness K D p q M r ρ η hM hη hcheck
  have hKR : IsSkew (fun h a => (K h a : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    rw [hK a b,Rat.cast_neg]
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  refine ⟨B,blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a)
    (fun i => by exact_mod_cast h.1 i),?_,blockMatrix_skew _ _ B hKR hB,
    blockMatrix_bounds _ _ B (M : ℝ) hKbR hDbR hb,hrows⟩
  rw [blockWeights_mass]
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast h.2.1
  rw [hm]
  exact_mod_cast hnorm

end SparseCompletion

/- Fixed source body: RationalGapEncoding.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

abbrev RationalGapRow (k m H : ℕ) := Fin m ⊕ (Fin 2 ⊕ (Fin m ⊕ (Fin k ⊕ Fin H)))

def rationalGapCoefficient {k m : ℕ}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalGapRow k m (rationalGridSize M r η) → Fin m → ℚ :=
  Sum.elim (fun j i => if i=j then -1 else 0)
    (Sum.elim (fun a _ => if a.val=0 then 1 else -1)
      (Sum.elim (fun _ _ => 0)
        (Sum.elim (fun h i => -D i h) (fun l i =>
          max (rationalScore D p i-ρ-(M*r-rationalGridNode M r η (l.val+1))) 0))))

def rationalGapRightSide {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalGapRow k m (rationalGridSize M r η) → ℚ :=
  Sum.elim (fun _ => 0)
    (Sum.elim (fun a => if a.val=0 then r else -r)
      (Sum.elim (fun i => ρ+M*r-rationalScore D p i)
        (Sum.elim (fun h => ρ-∑ a, K h a*p a)
          (fun l => rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))))))

theorem rational_gap_encoding_rows (k m H : ℕ) :
    Fintype.card (RationalGapRow k m H)=(2 : ℕ)*m+2+k+H := by
  simp only [RationalGapRow,Fintype.card_sum,Fintype.card_fin]
  omega


theorem rational_gap_conditions_iff_linear {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    RationalGapConditions K D p q M r ρ η ↔
      ∀ a, (∑ i, rationalGapCoefficient D p M r ρ η a i*q i) ≤
        rationalGapRightSide K D p M r ρ η a := by
  constructor
  · rintro ⟨hq,hm,hg,ha,hc⟩ a
    rcases a with i | a
    · simp only [rationalGapCoefficient,Sum.elim_inl,ite_mul,neg_one_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true,rationalGapRightSide]
      linarith [hq i]
    · rcases a with a | a
      · by_cases hz : a=0
        · simpa [rationalGapCoefficient,rationalGapRightSide,hz] using le_of_eq hm
        · simpa [rationalGapCoefficient,rationalGapRightSide,hz] using neg_le_neg (le_of_eq hm.symm)
      · rcases a with i | a
        · simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
            zero_mul,Finset.sum_const_zero]
          linarith [hg i]
        · rcases a with a | l
          · have hh := ha a
            unfold rationalAnchorResponse at hh
            simpa only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
              neg_mul,Finset.sum_neg_distrib] using (by linarith :
                -(∑ i, D i a*q i) ≤ ρ-∑ b, K a b*p b)
          · have hh := hc l
            unfold rationalCall at hh
            simpa only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,mul_comm] using hh
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i
      have hh := h (.inl i)
      simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inl,ite_mul,
        neg_one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
      linarith
    · have h1 := h (.inr (.inl 0))
      have h2 := h (.inr (.inl 1))
      simp [rationalGapCoefficient,rationalGapRightSide] at h1 h2
      linarith
    · intro i
      have hh := h (.inr (.inr (.inl i)))
      simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
        zero_mul,Finset.sum_const_zero] at hh
      linarith
    · intro a
      have hh := h (.inr (.inr (.inr (.inl a))))
      simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
        neg_mul,Finset.sum_neg_distrib] at hh
      unfold rationalAnchorResponse
      linarith
    · intro l
      have hh := h (.inr (.inr (.inr (.inr l))))
      simpa only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,rationalCall,mul_comm] using hh


theorem rational_gap_linear_acceptance_iff {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    checkRationalGap K D p q M r ρ η=true ↔
      ∀ a, (∑ i, rationalGapCoefficient D p M r ρ η a i*q i) ≤
        rationalGapRightSide K D p M r ρ η a :=
  (rational_gap_check_iff K D p q M r ρ η).trans
    (rational_gap_conditions_iff_linear K D p q M r ρ η)

theorem rational_gap_nontrivial_rows (k H : ℕ) : Fintype.card (Fin k ⊕ Fin H)=k+H := by
  simp only [Fintype.card_sum,Fintype.card_fin]

end SparseCompletion

/- Fixed source body: RationalOneVariable.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion.RationalElimination

/-- Computable maximum, with none exactly for an empty list. -/
def maximum? : List ℚ → Option ℚ
  | [] => none
  | x :: xs => match maximum? xs with
    | none => some x
    | some y => some (max x y)

/-- Computable minimum, with none exactly for an empty list. -/
def minimum? : List ℚ → Option ℚ
  | [] => none
  | x :: xs => match minimum? xs with
    | none => some x
    | some y => some (min x y)

theorem maximum_none_iff (xs : List ℚ) : maximum? xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [maximum?]
  | cons x xs =>
    simp only [maximum?, List.cons_ne_nil, iff_false]
    cases maximum? xs <;> simp

theorem minimum_none_iff (xs : List ℚ) : minimum? xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [minimum?]
  | cons x xs =>
    simp only [minimum?, List.cons_ne_nil, iff_false]
    cases minimum? xs <;> simp

theorem maximum_spec {xs : List ℚ} {u : ℚ} (h : maximum? xs = some u) :
    u ∈ xs ∧ ∀ x ∈ xs, x ≤ u := by
  induction xs generalizing u with
  | nil => simp [maximum?] at h
  | cons x xs ih =>
    cases he : maximum? xs with
    | none =>
      have hempty := (maximum_none_iff xs).mp he
      subst xs
      have heq : x = u := by simpa [maximum?] using h
      subst u
      simp
    | some y =>
      have hxy : max x y = u := by simpa [maximum?, he] using h
      subst u
      obtain ⟨hy, hall⟩ := ih he
      constructor
      · rcases le_total x y with hxy | hyx
        · simp only [max_eq_right hxy]; exact List.mem_cons_of_mem x hy
        · simp only [max_eq_left hyx]; exact List.mem_cons_self
      · intro z hz
        rcases List.mem_cons.mp hz with hz | hz
        · rw [hz]; exact le_max_left x y
        · exact le_trans (hall z hz) (le_max_right x y)

theorem minimum_spec {xs : List ℚ} {u : ℚ} (h : minimum? xs = some u) :
    u ∈ xs ∧ ∀ x ∈ xs, u ≤ x := by
  induction xs generalizing u with
  | nil => simp [minimum?] at h
  | cons x xs ih =>
    cases he : minimum? xs with
    | none =>
      have hempty := (minimum_none_iff xs).mp he
      subst xs
      have heq : x = u := by simpa [minimum?] using h
      subst u
      simp
    | some y =>
      have hxy : min x y = u := by simpa [minimum?, he] using h
      subst u
      obtain ⟨hy, hall⟩ := ih he
      constructor
      · rcases le_total x y with hxy | hyx
        · simp only [min_eq_left hxy]; exact List.mem_cons_self
        · simp only [min_eq_right hyx]; exact List.mem_cons_of_mem x hy
      · intro z hz
        rcases List.mem_cons.mp hz with hz | hz
        · rw [hz]; exact min_le_left x y
        · exact le_trans (min_le_right x y) (hall z hz)

/-- Prefer the greatest lower bound; if absent use the least upper bound;
if both lists are empty use zero. This is an executable rational value. -/
def select (lower upper : List ℚ) : ℚ :=
  match maximum? lower, minimum? upper with
  | some l, _ => l
  | none, some u => u
  | none, none => 0

theorem select_bounds (lower upper : List ℚ)
    (hpairs : ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u) :
    (∀ l ∈ lower, l ≤ select lower upper) ∧
    (∀ u ∈ upper, select lower upper ≤ u) := by
  cases hl : maximum? lower with
  | some l =>
    obtain ⟨hmem, hall⟩ := maximum_spec hl
    constructor
    · simpa only [select, hl] using hall
    · intro u hu
      simpa only [select, hl] using hpairs l hmem u hu
  | none =>
    have hempty := (maximum_none_iff lower).mp hl
    subst lower
    cases hu : minimum? upper with
    | none =>
      have hempty := (minimum_none_iff upper).mp hu
      subst upper
      simp
    | some u =>
      obtain ⟨_, hall⟩ := minimum_spec hu
      constructor
      · simp
      · simpa only [select, maximum?, hu] using hall

/-- A row denotes a*x+b<=c. -/
structure Row where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq, Repr

def Row.Holds (r : Row) (x : ℚ) : Prop := r.a*x+r.b ≤ r.c

def Row.endpoint (r : Row) : ℚ := (r.c-r.b)/r.a

def lowerBounds (rows : List Row) : List ℚ :=
  (rows.filter (fun r => r.a < 0)).map Row.endpoint

def upperBounds (rows : List Row) : List ℚ :=
  (rows.filter (fun r => 0 < r.a)).map Row.endpoint

def candidate (rows : List Row) : ℚ := select (lowerBounds rows) (upperBounds rows)

/-- Precisely the one-variable Fourier--Motzkin residual conditions. -/
def Eliminated (rows : List Row) : Prop :=
  (∀ r ∈ rows, r.a = 0 → r.b ≤ r.c) ∧
  ∀ l ∈ rows, l.a < 0 → ∀ u ∈ rows, 0 < u.a → l.endpoint ≤ u.endpoint

theorem row_positive_iff (r : Row) (ha : 0 < r.a) (x : ℚ) :
    r.Holds x ↔ x ≤ r.endpoint := by
  unfold Row.Holds Row.endpoint
  rw [le_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

theorem row_negative_iff (r : Row) (ha : r.a < 0) (x : ℚ) :
    r.Holds x ↔ r.endpoint ≤ x := by
  unfold Row.Holds Row.endpoint
  rw [div_le_iff_of_neg ha]
  constructor <;> intro h <;> nlinarith

theorem feasible_implies_eliminated (rows : List Row) (x : ℚ)
    (hx : ∀ r ∈ rows, r.Holds x) : Eliminated rows := by
  constructor
  · intro r hr ha
    have hh := hx r hr
    simpa only [Row.Holds,ha,zero_mul,zero_add] using hh
  · intro l hl hla u hu hua
    exact le_trans ((row_negative_iff l hla x).mp (hx l hl))
      ((row_positive_iff u hua x).mp (hx u hu))

theorem candidate_feasible (rows : List Row) (h : Eliminated rows) :
    ∀ r ∈ rows, r.Holds (candidate rows) := by
  have hpairs : ∀ l ∈ lowerBounds rows, ∀ u ∈ upperBounds rows, l ≤ u := by
    intro l hl u hu
    obtain ⟨rl, hrl, rfl⟩ := List.mem_map.mp hl
    obtain ⟨ru, hru, rfl⟩ := List.mem_map.mp hu
    have hrl' := List.mem_filter.mp hrl
    have hru' := List.mem_filter.mp hru
    exact h.2 rl hrl'.1 (by simpa using hrl'.2) ru hru'.1 (by simpa using hru'.2)
  have hb := select_bounds (lowerBounds rows) (upperBounds rows) hpairs
  intro r hr
  rcases lt_trichotomy r.a 0 with ha | ha | ha
  · apply (row_negative_iff r ha _).mpr
    exact hb.1 r.endpoint (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,by simpa⟩,rfl⟩)
  · have hh := h.1 r hr ha
    simpa only [Row.Holds,ha,zero_mul,zero_add] using hh
  · apply (row_positive_iff r ha _).mpr
    exact hb.2 r.endpoint (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,by simpa⟩,rfl⟩)

theorem eliminated_iff_exists (rows : List Row) :
    Eliminated rows ↔ ∃ x : ℚ, ∀ r ∈ rows, r.Holds x :=
  ⟨fun h => ⟨candidate rows,candidate_feasible rows h⟩,
   fun ⟨x,hx⟩ => feasible_implies_eliminated rows x hx⟩

end SparseCompletion.RationalElimination

/- Fixed source body: RationalOneVariableFinite.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion.RationalElimination

instance eliminatedDecidable (rows : List Row) : Decidable (Eliminated rows) := by
  unfold Eliminated
  infer_instance

/-- Finite exact rational decision and reconstruction; no feasibility oracle. -/
def solve (rows : List Row) : Option ℚ :=
  if Eliminated rows then some (candidate rows) else none

theorem solve_some_sound {rows : List Row} {x : ℚ} (h : solve rows = some x) :
    ∀ r ∈ rows, r.Holds x := by
  unfold solve at h
  split at h
  next he =>
    have hx : candidate rows = x := Option.some.inj h
    rw [←hx]
    exact candidate_feasible rows he
  next he => simp at h

theorem solve_none_iff (rows : List Row) :
    solve rows = none ↔ ¬ ∃ x : ℚ, ∀ r ∈ rows, r.Holds x := by
  simp only [solve, ite_eq_right_iff, Option.some_ne_none, imp_false]
  exact not_congr (eliminated_iff_exists rows)

/-- Literal finite coefficient arrays are enumerated by List.ofFn. -/
def finiteRows {n : ℕ} (a b c : Fin n → ℚ) : List Row :=
  List.ofFn fun i => ⟨a i,b i,c i⟩

def finiteCandidate {n : ℕ} (a b c : Fin n → ℚ) : ℚ := candidate (finiteRows a b c)

def FiniteEliminated {n : ℕ} (a b c : Fin n → ℚ) : Prop :=
  (∀ i, a i = 0 → b i ≤ c i) ∧
  ∀ i, a i < 0 → ∀ j, 0 < a j → (c i-b i)/a i ≤ (c j-b j)/a j

theorem finite_eliminated_iff {n : ℕ} (a b c : Fin n → ℚ) :
    FiniteEliminated a b c ↔ Eliminated (finiteRows a b c) := by
  unfold FiniteEliminated Eliminated finiteRows
  constructor
  · intro h
    constructor
    · intro r hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      exact h.1 i
    · intro l hl hla u hu hua
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
      exact h.2 i hla j hua
  · intro h
    constructor
    · intro i hi
      exact h.1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩) hi
    · intro i hi j hj
      exact h.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩) hi _ (List.mem_ofFn.mpr ⟨j,rfl⟩) hj

theorem finite_candidate_feasible {n : ℕ} (a b c : Fin n → ℚ)
    (h : FiniteEliminated a b c) :
    ∀ i, a i*finiteCandidate a b c+b i ≤ c i := by
  intro i
  exact candidate_feasible _ ((finite_eliminated_iff a b c).mp h) _
    (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem finite_eliminated_iff_exists {n : ℕ} (a b c : Fin n → ℚ) :
    FiniteEliminated a b c ↔ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  constructor
  · intro h
    exact ⟨finiteCandidate a b c,finite_candidate_feasible a b c h⟩
  · rintro ⟨x,hx⟩
    apply (finite_eliminated_iff a b c).mpr
    apply feasible_implies_eliminated _ x
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hx i

instance finiteEliminatedDecidable {n : ℕ} (a b c : Fin n → ℚ) :
    Decidable (FiniteEliminated a b c) := by
  unfold FiniteEliminated
  infer_instance

def solveFinite {n : ℕ} (a b c : Fin n → ℚ) : Option ℚ :=
  if FiniteEliminated a b c then some (finiteCandidate a b c) else none

theorem solve_finite_some_sound {n : ℕ} {a b c : Fin n → ℚ} {x : ℚ}
    (h : solveFinite a b c = some x) : ∀ i, a i*x+b i ≤ c i := by
  unfold solveFinite at h
  split at h
  next he =>
    have hx : finiteCandidate a b c = x := Option.some.inj h
    rw [←hx]
    exact finite_candidate_feasible a b c he
  next he => simp at h

theorem solve_finite_none_iff {n : ℕ} (a b c : Fin n → ℚ) :
    solveFinite a b c = none ↔ ¬ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  simp only [solveFinite, ite_eq_right_iff, Option.some_ne_none, imp_false]
  exact not_congr (finite_eliminated_iff_exists a b c)

end SparseCompletion.RationalElimination

/- Fixed source body: RationalOneVariableFintype.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion.RationalElimination

/-- Endpoint sets use invariant finite-set operations, without choosing a list
or a noncomputable equivalence to a finite ordinal. -/
def indexedLower {I : Type*} [Fintype I] (a b c : I → ℚ) : Finset ℚ :=
  (Finset.univ.filter fun i => a i < 0).image fun i => (c i-b i)/a i

def indexedUpper {I : Type*} [Fintype I] (a b c : I → ℚ) : Finset ℚ :=
  (Finset.univ.filter fun i => 0 < a i).image fun i => (c i-b i)/a i

/-- Actual computable rational extraction for arbitrary finite row types. -/
def generalCandidate {I : Type*} [Fintype I] (a b c : I → ℚ) : ℚ :=
  if hl : (indexedLower a b c).Nonempty then (indexedLower a b c).max' hl
  else if hu : (indexedUpper a b c).Nonempty then (indexedUpper a b c).min' hu
  else 0

def FintypeEliminated {I : Type*} [Fintype I] (a b c : I → ℚ) : Prop :=
  (∀ i, a i = 0 → b i ≤ c i) ∧
  ∀ i, a i < 0 → ∀ j, 0 < a j → (c i-b i)/a i ≤ (c j-b j)/a j

theorem indexed_lower_mem {I : Type*} [Fintype I] (a b c : I → ℚ) (x : ℚ) :
    x ∈ indexedLower a b c ↔ ∃ i, a i < 0 ∧ (c i-b i)/a i=x := by
  simp only [indexedLower,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

theorem indexed_upper_mem {I : Type*} [Fintype I] (a b c : I → ℚ) (x : ℚ) :
    x ∈ indexedUpper a b c ↔ ∃ i, 0 < a i ∧ (c i-b i)/a i=x := by
  simp only [indexedUpper,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

theorem indexed_candidate_bounds {I : Type*} [Fintype I] (a b c : I → ℚ)
    (hpairs : ∀ i, a i < 0 → ∀ j, 0 < a j → (c i-b i)/a i ≤ (c j-b j)/a j) :
    (∀ i, a i < 0 → (c i-b i)/a i ≤ generalCandidate a b c) ∧
    (∀ j, 0 < a j → generalCandidate a b c ≤ (c j-b j)/a j) := by
  by_cases hl : (indexedLower a b c).Nonempty
  · have hmem := Finset.max'_mem (indexedLower a b c) hl
    obtain ⟨i,hi,heq⟩ := (indexed_lower_mem a b c _).mp hmem
    constructor
    · intro j hj
      simpa only [generalCandidate,dite_eq_left hl] using
        Finset.le_max' (indexedLower a b c) ((c j-b j)/a j)
          ((indexed_lower_mem a b c _).mpr ⟨j,hj,rfl⟩)
    · intro j hj
      simpa only [generalCandidate,dite_eq_left hl,←heq] using hpairs i hi j hj
  · constructor
    · intro i hi
      exact (hl ⟨_,(indexed_lower_mem a b c _).mpr ⟨i,hi,rfl⟩⟩).elim
    · intro j hj
      have hu : (indexedUpper a b c).Nonempty :=
        ⟨_,(indexed_upper_mem a b c _).mpr ⟨j,hj,rfl⟩⟩
      simpa only [generalCandidate,dite_eq_right hl,dite_eq_left hu] using
        Finset.min'_le (indexedUpper a b c) ((c j-b j)/a j)
          ((indexed_upper_mem a b c _).mpr ⟨j,hj,rfl⟩)

theorem fintype_candidate_feasible {I : Type*} [Fintype I] (a b c : I → ℚ)
    (h : FintypeEliminated a b c) :
    ∀ i, a i*generalCandidate a b c+b i ≤ c i := by
  have hb := indexed_candidate_bounds a b c h.2
  intro i
  rcases lt_trichotomy (a i) 0 with ha | ha | ha
  · exact (row_negative_iff ⟨a i,b i,c i⟩ ha _).mpr (hb.1 i ha)
  · simpa only [ha,zero_mul,zero_add] using h.1 i ha
  · exact (row_positive_iff ⟨a i,b i,c i⟩ ha _).mpr (hb.2 i ha)

theorem fintype_eliminated_iff_exists {I : Type*} [Fintype I] (a b c : I → ℚ) :
    FintypeEliminated a b c ↔ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  constructor
  · intro h
    exact ⟨generalCandidate a b c,fintype_candidate_feasible a b c h⟩
  · rintro ⟨x,hx⟩
    constructor
    · intro i hi
      simpa only [hi,zero_mul,zero_add] using hx i
    · intro i hi j hj
      exact le_trans ((row_negative_iff ⟨a i,b i,c i⟩ hi x).mp (hx i))
        ((row_positive_iff ⟨a j,b j,c j⟩ hj x).mp (hx j))

instance fintypeEliminatedDecidable {I : Type*} [Fintype I] (a b c : I → ℚ) :
    Decidable (FintypeEliminated a b c) := by
  unfold FintypeEliminated
  infer_instance

def solveFintype {I : Type*} [Fintype I] (a b c : I → ℚ) : Option ℚ :=
  if FintypeEliminated a b c then some (generalCandidate a b c) else none

theorem solve_fintype_some_sound {I : Type*} [Fintype I] {a b c : I → ℚ} {x : ℚ}
    (h : solveFintype a b c = some x) : ∀ i, a i*x+b i ≤ c i := by
  unfold solveFintype at h
  split at h
  next he =>
    have hx : generalCandidate a b c = x := Option.some.inj h
    rw [←hx]
    exact fintype_candidate_feasible a b c he
  next he => simp at h

theorem solve_fintype_none_iff {I : Type*} [Fintype I] (a b c : I → ℚ) :
    solveFintype a b c = none ↔ ¬ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  simp only [solveFintype,ite_eq_right_iff,Option.some_ne_none,imp_false]
  exact not_congr (fintype_eliminated_iff_exists a b c)

end SparseCompletion.RationalElimination

/- Fixed source body: RationalLinearSystem.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Classical Fourier–Motzkin elimination; no polynomial complexity claim. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure RationalLinearSystem (I : Type*) (n : ℕ) where
  coefficient : I → Fin n → ℚ
  rightSide : I → ℚ

def RationalLinearSystem.Satisfies {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) : Prop :=
  ∀ i, (∑ j, S.coefficient i j*q j) ≤ S.rightSide i

instance rationalLinearSatisfiesDecidable {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) : Decidable (S.Satisfies q) := by
  unfold RationalLinearSystem.Satisfies
  infer_instance

def RationalLinearSystem.slope {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (i : I) : ℚ := S.coefficient i 0

def RationalLinearSystem.rest {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : I) : ℚ :=
  ∑ j, S.coefficient i j.succ*q j

theorem rational_linear_cons_response {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (x : ℚ) (i : I) :
    (∑ j, S.coefficient i j*Fin.cons (α := fun _ => ℚ) x q j)=S.slope i*x+S.rest q i := by
  rw [Fin.sum_univ_succ]
  rfl

theorem rational_linear_cons_iff {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (x : ℚ) :
    S.Satisfies (Fin.cons (α := fun _ => ℚ) x q) ↔ ∀ i, S.slope i*x+S.rest q i ≤ S.rightSide i := by
  simp only [RationalLinearSystem.Satisfies,rational_linear_cons_response]

abbrev RationalLinearSystem.ZeroRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  {i : I // S.slope i=0}

abbrev RationalLinearSystem.LowerRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  {i : I // S.slope i < 0}

abbrev RationalLinearSystem.UpperRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  {i : I // 0 < S.slope i}

abbrev RationalLinearSystem.ReducedRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  S.ZeroRows ⊕ (S.LowerRows × S.UpperRows)

def RationalLinearSystem.reduce {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) : RationalLinearSystem S.ReducedRows n where
  coefficient := Sum.elim (fun i j => S.coefficient i.val j.succ)
    (fun a j => S.coefficient a.1.val j.succ/(-S.slope a.1.val)+
      S.coefficient a.2.val j.succ/S.slope a.2.val)
  rightSide := Sum.elim (fun i => S.rightSide i.val)
    (fun a => S.rightSide a.1.val/(-S.slope a.1.val)+S.rightSide a.2.val/S.slope a.2.val)

theorem rational_linear_reduced_zero {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : S.ZeroRows) :
    (∑ j, S.reduce.coefficient (.inl i) j*q j)=S.rest q i.val := rfl

theorem rational_linear_reduced_pair {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : S.LowerRows) (h : S.UpperRows) :
    (∑ j, S.reduce.coefficient (.inr (i,h)) j*q j)=
      S.rest q i.val/(-S.slope i.val)+S.rest q h.val/S.slope h.val := by
  change (∑ j, (S.coefficient i.val j.succ/(-S.slope i.val)+
      S.coefficient h.val j.succ/S.slope h.val)*q j)=_
  simp only [add_mul,Finset.sum_add_distrib,div_mul_eq_mul_div,←Finset.sum_div,
    RationalLinearSystem.rest]


def RationalLinearSystem.Eliminated {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) : Prop :=
  (∀ i, S.slope i=0 → S.rest q i ≤ S.rightSide i) ∧
    ∀ i, S.slope i < 0 → ∀ h, 0 < S.slope h →
      (S.rightSide i-S.rest q i)/S.slope i ≤ (S.rightSide h-S.rest q h)/S.slope h

theorem rational_linear_pair_inequality {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : S.LowerRows) (h : S.UpperRows) :
    (∑ j, S.reduce.coefficient (.inr (i,h)) j*q j) ≤ S.reduce.rightSide (.inr (i,h)) ↔
      (S.rightSide i.val-S.rest q i.val)/S.slope i.val ≤
        (S.rightSide h.val-S.rest q h.val)/S.slope h.val := by
  rw [rational_linear_reduced_pair]
  change S.rest q i.val/(-S.slope i.val)+S.rest q h.val/S.slope h.val ≤
    S.rightSide i.val/(-S.slope i.val)+S.rightSide h.val/S.slope h.val ↔ _
  have he : (S.rightSide i.val-S.rest q i.val)/S.slope i.val-
      (S.rightSide h.val-S.rest q h.val)/S.slope h.val=
      S.rest q i.val/(-S.slope i.val)+S.rest q h.val/S.slope h.val-
      (S.rightSide i.val/(-S.slope i.val)+S.rightSide h.val/S.slope h.val) := by
    simp only [div_neg]
    ring
  constructor <;> intro hh <;> linarith

theorem rational_linear_reduce_iff {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) :
    S.reduce.Satisfies q ↔ S.Eliminated q := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact h (.inl ⟨i,hi⟩)
    · intro i hi j hj
      exact (rational_linear_pair_inequality S q ⟨i,hi⟩ ⟨j,hj⟩).mp
        (h (.inr (⟨i,hi⟩,⟨j,hj⟩)))
  · rintro ⟨hz,hp⟩ a
    rcases a with i | ⟨i,h⟩
    · exact hz i.val i.property
    · exact (rational_linear_pair_inequality S q i h).mpr (hp i.val i.property h.val h.property)

end SparseCompletion

/- Fixed source body: RationalLinearSolver.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Classical Fourier–Motzkin elimination; this can have exponential size. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
universe u

/-- Exact rational feasibility by dimension recursion and genuine finite elimination.
This is not a polynomial-time LP theorem. -/
def rationalLPSolve : (n : ℕ) → {I : Type u} → [Fintype I] →
    RationalLinearSystem I n → Option (Fin n → ℚ)
  | 0, _, _, S => if ∀ i, 0 ≤ S.rightSide i then some Fin.elim0 else none
  | n+1, _, _, S => match rationalLPSolve n S.reduce with
    | none => none
    | some q => some (Fin.cons (α := fun _ => ℚ)
        (RationalElimination.generalCandidate S.slope (S.rest q) S.rightSide) q)

theorem rational_linear_eliminated_exists {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) :
    S.Eliminated q ↔ ∃ x : ℚ, S.Satisfies (Fin.cons (α := fun _ => ℚ) x q) := by
  have he : S.Eliminated q ↔
      RationalElimination.FintypeEliminated S.slope (S.rest q) S.rightSide := Iff.rfl
  rw [he,RationalElimination.fintype_eliminated_iff_exists]
  simp only [rational_linear_cons_iff]

theorem rational_lp_solve_sound (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) (h : rationalLPSolve n S=some q) :
    S.Satisfies q := by
  induction n generalizing I with
  | zero =>
    unfold rationalLPSolve at h
    split at h
    next hh =>
      intro i
      simpa using hh i
    next hh => simp at h
  | succ n ih =>
    cases he : rationalLPSolve n S.reduce with
    | none => simp [rationalLPSolve,he] at h
    | some y =>
      have hy := ih S.reduce y he
      have hel := (rational_linear_reduce_iff S y).mp hy
      have hx := RationalElimination.fintype_candidate_feasible S.slope (S.rest y) S.rightSide hel
      have hq : Fin.cons (α := fun _ => ℚ)
          (RationalElimination.generalCandidate S.slope (S.rest y) S.rightSide) y=q := by
        exact Option.some.inj (by simpa only [rationalLPSolve,he] using h)
      rw [←hq]
      exact (rational_linear_cons_iff S y _).mpr hx


theorem rational_linear_decomposition {n : ℕ} (q : Fin (n+1) → ℚ) :
    Fin.cons (α := fun _ => ℚ) (q 0) (fun j => q j.succ)=q := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem rational_lp_solve_complete (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) (h : ∃ q, S.Satisfies q) :
    ∃ q, rationalLPSolve n S=some q := by
  induction n generalizing I with
  | zero =>
    obtain ⟨q,hq⟩ := h
    have hr : ∀ i, 0 ≤ S.rightSide i := by
      intro i
      simpa using hq i
    exact ⟨Fin.elim0,by simp [rationalLPSolve,hr]⟩
  | succ n ih =>
    obtain ⟨q,hq⟩ := h
    have hc : S.Satisfies (Fin.cons (α := fun _ => ℚ) (q 0) (fun j => q j.succ)) := by
      rw [rational_linear_decomposition]
      exact hq
    have hel := (rational_linear_eliminated_exists S (fun j => q j.succ)).mpr ⟨q 0,hc⟩
    have hr := (rational_linear_reduce_iff S (fun j => q j.succ)).mpr hel
    obtain ⟨y,hy⟩ := ih S.reduce ⟨fun j => q j.succ,hr⟩
    exact ⟨Fin.cons (α := fun _ => ℚ)
      (RationalElimination.generalCandidate S.slope (S.rest y) S.rightSide) y,
      by simp only [rationalLPSolve,hy]⟩

theorem rational_lp_solve_none_iff (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) :
    rationalLPSolve n S=none ↔ ¬∃ q, S.Satisfies q := by
  constructor
  · intro hn hf
    obtain ⟨q,hq⟩ := rational_lp_solve_complete n S hf
    rw [hn] at hq
    cases hq
  · intro hn
    cases he : rationalLPSolve n S with
    | none => rfl
    | some q => exact False.elim (hn ⟨q,rational_lp_solve_sound n S q he⟩)

/-- Genuine decidability proved from the total rational elimination algorithm. -/
def rationalLPFeasibleDecidable (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) : Decidable (∃ q, S.Satisfies q) :=
  match he : rationalLPSolve n S with
  | none => isFalse ((rational_lp_solve_none_iff n S).mp he)
  | some q => isTrue ⟨q,rational_lp_solve_sound n S q he⟩

end SparseCompletion

/- Fixed source body: RationalLinearReal.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Real soundness of rational Fourier--Motzkin reduction; no complexity claim. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalLinearSystem.RealSatisfies {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (∑ j, (S.coefficient i j : ℝ)*x j) ≤ (S.rightSide i : ℝ)

def RationalLinearSystem.realRest {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin n → ℝ) (i : I) : ℝ :=
  ∑ j, (S.coefficient i j.succ : ℝ)*x j

theorem rational_linear_real_split {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin (n+1) → ℝ) (i : I) :
    (∑ j, (S.coefficient i j : ℝ)*x j) =
      (S.slope i : ℝ)*x 0+S.realRest (fun j => x j.succ) i := by
  rw [Fin.sum_univ_succ]
  rfl

theorem rational_linear_real_reduced_zero {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin n → ℝ) (i : S.ZeroRows) :
    (∑ j, (S.reduce.coefficient (.inl i) j : ℝ)*x j)=S.realRest x i.val := rfl

theorem rational_linear_real_reduced_pair {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin n → ℝ)
    (i : S.LowerRows) (h : S.UpperRows) :
    (∑ j, (S.reduce.coefficient (.inr (i,h)) j : ℝ)*x j)=
      S.realRest x i.val/(-(S.slope i.val : ℝ))+
      S.realRest x h.val/(S.slope h.val : ℝ) := by
  change (∑ j, ((S.coefficient i.val j.succ/(-S.slope i.val)+
    S.coefficient h.val j.succ/S.slope h.val : ℚ) : ℝ)*x j)=_
  push_cast
  simp only [add_mul,Finset.sum_add_distrib,div_mul_eq_mul_div,←Finset.sum_div,
    RationalLinearSystem.realRest]

theorem rational_linear_real_reduce_feasible {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin (n+1) → ℝ)
    (hx : S.RealSatisfies x) :
    S.reduce.RealSatisfies (fun j => x j.succ) := by
  intro row
  rcases row with i | ⟨i,h⟩
  · have hi := hx i.val
    rw [rational_linear_real_split] at hi
    have hz : (S.slope i.val : ℝ)=0 := by exact_mod_cast i.property
    rw [hz,zero_mul,zero_add] at hi
    rw [rational_linear_real_reduced_zero]
    exact hi
  · have hi := hx i.val
    have hh := hx h.val
    rw [rational_linear_real_split] at hi hh
    have hil : (S.slope i.val : ℝ)<0 := by exact_mod_cast i.property
    have hhu : (0 : ℝ)<(S.slope h.val : ℝ) := by exact_mod_cast h.property
    have hden : (0 : ℝ)< -(S.slope i.val : ℝ) := neg_pos.mpr hil
    have hli := div_le_div_of_nonneg_right hi (le_of_lt hden)
    have hhi := div_le_div_of_nonneg_right hh (le_of_lt hhu)
    have hel : ((S.slope i.val : ℝ)*x 0+S.realRest (fun j => x j.succ) i.val)/
        (-(S.slope i.val : ℝ)) =
        -x 0+S.realRest (fun j => x j.succ) i.val/(-(S.slope i.val : ℝ)) := by
      field_simp [ne_of_lt hil]
      ring
    have heu : ((S.slope h.val : ℝ)*x 0+S.realRest (fun j => x j.succ) h.val)/
        (S.slope h.val : ℝ) =
        x 0+S.realRest (fun j => x j.succ) h.val/(S.slope h.val : ℝ) := by
      field_simp [ne_of_gt hhu]
    rw [hel] at hli
    rw [heu] at hhi
    rw [rational_linear_real_reduced_pair]
    change _ ≤ ((S.rightSide i.val/(-S.slope i.val)+S.rightSide h.val/S.slope h.val : ℚ) : ℝ)
    push_cast
    linarith

theorem rational_linear_real_cast_iff {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) :
    S.RealSatisfies (fun j => (q j : ℝ)) ↔ S.Satisfies q := by
  constructor
  · intro h i
    have hi : ((∑ j, S.coefficient i j*q j : ℚ) : ℝ) ≤ (S.rightSide i : ℝ) := by
      simpa only [Rat.cast_sum,Rat.cast_mul] using h i
    exact_mod_cast hi
  · intro h i
    have hi := h i
    have hR : ((∑ j, S.coefficient i j*q j : ℚ) : ℝ) ≤ (S.rightSide i : ℝ) := by
      exact_mod_cast hi
    simpa only [Rat.cast_sum,Rat.cast_mul] using hR

theorem rational_linear_real_zero_iff {I : Type*}
    (S : RationalLinearSystem I 0) (x : Fin 0 → ℝ) :
    S.RealSatisfies x ↔ ∀ i, (0 : ℚ) ≤ S.rightSide i := by
  simp only [RationalLinearSystem.RealSatisfies,Finset.univ_eq_empty,Finset.sum_empty,
    Rat.cast_nonneg]

end SparseCompletion

/- Fixed source body: RationalLinearTransfer.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Rational Fourier–Motzkin completeness across the rational-to-real embedding. -/
@[expose] public section
namespace SparseCompletion
universe u

theorem rational_lp_real_complete (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) (h : ∃ x, S.RealSatisfies x) :
    ∃ q, rationalLPSolve n S=some q := by
  induction n generalizing I with
  | zero =>
    obtain ⟨x,hx⟩ := h
    have hr := (rational_linear_real_zero_iff S x).mp hx
    exact ⟨Fin.elim0,by simp [rationalLPSolve,hr]⟩
  | succ n ih =>
    obtain ⟨x,hx⟩ := h
    have hr := rational_linear_real_reduce_feasible S x hx
    obtain ⟨y,hy⟩ := ih S.reduce ⟨fun j => x j.succ,hr⟩
    exact ⟨Fin.cons (α := fun _ => ℚ)
      (RationalElimination.generalCandidate S.slope (S.rest y) S.rightSide) y,
      by simp only [rationalLPSolve,hy]⟩

theorem rational_linear_real_feasible_iff {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) :
    (∃ x, S.RealSatisfies x) ↔ ∃ q, S.Satisfies q := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := rational_lp_real_complete n S h
    exact ⟨q,rational_lp_solve_sound n S q hq⟩
  · rintro ⟨q,hq⟩
    exact ⟨fun j => (q j : ℝ),(rational_linear_real_cast_iff S q).mpr hq⟩

theorem rational_lp_solve_none_iff_real (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) :
    rationalLPSolve n S=none ↔ ¬∃ x, S.RealSatisfies x := by
  rw [rational_lp_solve_none_iff]
  exact not_congr (rational_linear_real_feasible_iff S).symm

/-- Computed from rational coefficients and the verified rational algorithm;
no decision procedure for arbitrary real comparisons is assumed. -/
def rationalLPRealFeasibleDecidable (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) : Decidable (∃ x, S.RealSatisfies x) :=
  match he : rationalLPSolve n S with
  | none => isFalse ((rational_lp_solve_none_iff_real n S).mp he)
  | some q => isTrue ⟨fun j => (q j : ℝ),(rational_linear_real_cast_iff S q).mpr
      (rational_lp_solve_sound n S q he)⟩

end SparseCompletion

/- Fixed source body: RationalGapDecision.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
The exact rational solver uses Fourier–Motzkin elimination; no polynomial cost. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalLinearSystem.append {I J : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (T : RationalLinearSystem J n) : RationalLinearSystem (I ⊕ J) n :=
  ⟨Sum.elim S.coefficient T.coefficient,Sum.elim S.rightSide T.rightSide⟩

theorem rational_linear_append_iff {I J : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (T : RationalLinearSystem J n) (q : Fin n → ℚ) :
    (S.append T).Satisfies q ↔ S.Satisfies q ∧ T.Satisfies q := by
  constructor
  · intro h
    exact ⟨fun i => h (.inl i),fun j => h (.inr j)⟩
  · rintro ⟨hS,hT⟩ a
    rcases a with i | j
    · exact hS i
    · exact hT j

def rationalGapSystem {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalLinearSystem (RationalGapRow k m (rationalGridSize M r η)) m :=
  ⟨rationalGapCoefficient D p M r ρ η,rationalGapRightSide K D p M r ρ η⟩

def rationalGapSolve {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) : Option (Fin m → ℚ) :=
  rationalLPSolve m ((rationalGapSystem K D p M r ρ η).append R)

theorem rational_gap_solve_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (q : Fin m → ℚ)
    (h : rationalGapSolve K D p M r ρ η R=some q) :
    checkRationalGap K D p q M r ρ η=true ∧ R.Satisfies q := by
  have hh := (rational_linear_append_iff (rationalGapSystem K D p M r ρ η) R q).mp
    (rational_lp_solve_sound m _ q h)
  exact ⟨(rational_gap_linear_acceptance_iff K D p q M r ρ η).mpr hh.1,hh.2⟩

theorem rational_gap_solve_none_iff {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) :
    rationalGapSolve K D p M r ρ η R=none ↔
      ¬∃ q, RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q := by
  rw [rationalGapSolve,rational_lp_solve_none_iff]
  apply not_congr
  apply exists_congr
  intro q
  rw [rational_linear_append_iff]
  exact and_congr (rational_gap_conditions_iff_linear K D p q M r ρ η).symm Iff.rfl

theorem rational_gap_solve_completed_witness {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (q : Fin m → ℚ) (hM : 0 < M) (hη : 0 < η)
    (h : rationalGapSolve K D p M r ρ η R=some q) :
    R.Satisfies q ∧ ∃ B : Fin m → Fin m → ℝ, IsSkew B ∧
      (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  have hs := rational_gap_solve_sound K D p M r ρ η R q h
  exact ⟨hs.2,rational_gap_completed_witness K D p q M r ρ η hM hη hs.1⟩

end SparseCompletion

/- Fixed source body: RationalGapSearch.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Uses verified rational elimination; no polynomial-time or bit-cost assertion. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_shifted_call_antitone {I : Type*} [Fintype I]
    (q t : I → ℚ) (ρ ρ' z : ℚ) (hq : ∀ i, 0 ≤ q i) (hρ : ρ ≤ ρ') :
    rationalCall q (fun i => t i-ρ') z ≤ rationalCall q (fun i => t i-ρ) z := by
  unfold rationalCall
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) (le_refl 0)) (hq i)

theorem rational_gap_conditions_monotone {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ ρ' η : ℚ) (hρ : ρ ≤ ρ') (h : RationalGapConditions K D p q M r ρ η) :
    RationalGapConditions K D p q M r ρ' η := by
  rcases h with ⟨hq,hm,hg,ha,hc⟩
  refine ⟨hq,hm,fun i => by linarith [hg i],fun a => le_trans (ha a) hρ,?_⟩
  intro l
  exact le_trans (rational_shifted_call_antitone q (rationalScore D p) ρ ρ' _ hq hρ) (hc l)

def RationalGapExists {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) : Prop :=
  ∃ q, RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q

instance rationalGapExistsDecidable {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) : Decidable (RationalGapExists K D p M r ρ η R) :=
  (Option.rec
    (motive := fun o => rationalGapSolve K D p M r ρ η R=o →
      Decidable (RationalGapExists K D p M r ρ η R))
    (fun he => isFalse ((rational_gap_solve_none_iff K D p M r ρ η R).mp he))
    (fun q he => isTrue ⟨q,(rational_gap_check_iff K D p q M r ρ η).mp
      (rational_gap_solve_sound K D p M r ρ η R q he).1,
      (rational_gap_solve_sound K D p M r ρ η R q he).2⟩)
    (rationalGapSolve K D p M r ρ η R)) rfl

theorem rational_gap_exists_monotone {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r η : ℚ)
    (R : RationalLinearSystem I m) : Monotone (fun ρ => RationalGapExists K D p M r ρ η R) := by
  intro ρ ρ' hρ
  rintro ⟨q,hq,hR⟩
  exact ⟨q,rational_gap_conditions_monotone K D p q M r ρ ρ' η hρ hq,hR⟩

def rationalGapSearch {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I m) (n : ℕ) : ℚ × ℚ :=
  RationalBisection.search (fun ρ => RationalGapExists K D p M r ρ η R) n 0 M

theorem rational_gap_search_bracket {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I m) (n : ℕ) (hM : 0 ≤ M)
    (hupper : RationalGapExists K D p M r M η R) :
    let z := rationalGapSearch K D p M r η R n
    0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ M ∧ RationalGapExists K D p M r z.2 η R ∧
      (z.1=0 ∨ ¬RationalGapExists K D p M r z.1 η R) ∧
      z.2-z.1 ≤ M/((2 : ℕ) : ℚ)^n := by
  simpa only [rationalGapSearch,sub_zero] using
    RationalBisection.search_spec (fun ρ => RationalGapExists K D p M r ρ η R) n 0 M hM hupper

end SparseCompletion

/- Fixed source body: RationalGapRealDecision.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Exact rational elimination links real game feasibility to the supplied linear program. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_linear_real_append_iff {I J : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (T : RationalLinearSystem J n) (x : Fin n → ℝ) :
    (S.append T).RealSatisfies x ↔ S.RealSatisfies x ∧ T.RealSatisfies x := by
  constructor
  · intro h
    exact ⟨fun i => h (.inl i),fun j => h (.inr j)⟩
  · rintro ⟨hS,hT⟩ a
    rcases a with i | j
    · exact hS i
    · exact hT j

theorem exact_game_rational_gap_system_real {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (x : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (M r ρ η : ℚ)
    (hM : 0 < M) (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
      (blockWeights (fun h => (p h : ℝ)) x) a ≤ (ρ : ℝ)) :
    (rationalGapSystem K D p M r ρ η).RealSatisfies x := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hh := (block_response_bounds_iff _ _ B _ x (ρ : ℝ)).mp hrows
  have hc := (weighted_completion_iff x (score (fun i h => (D i h : ℝ)) (fun h => (p h : ℝ)))
    (M : ℝ) (r : ℝ) (ρ : ℝ) (le_of_lt hMR) hq hm).mp ⟨B,hB,hb,hh.2⟩
  have hcall := cuts_imply_call_bound x
    (fun i => score (fun i h => (D i h : ℝ)) (fun h => (p h : ℝ)) i-(ρ : ℝ))
    (M : ℝ) (r : ℝ) hMR hc.2
  intro a
  rcases a with i | a
  · change (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*x j) ≤ ((0 : ℚ) : ℝ)
    have he : (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*x j)= -x i := by
      calc
        _ = ∑ j, if j=i then -x j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j=i <;> simp [hj]
        _ = _ := by simp
    rw [he,Rat.cast_zero]
    exact neg_nonpos.mpr (hq i)
  · rcases a with a | a
    · by_cases hz : a=0
      · subst a
        change (∑ j, ((1 : ℚ) : ℝ)*x j) ≤ (r : ℝ)
        simpa using le_of_eq hm
      · change (∑ j, ((if a.val=0 then (1 : ℚ) else -1 : ℚ) : ℝ)*x j) ≤
          ((if a.val=0 then r else -r : ℚ) : ℝ)
        simpa [hz] using neg_le_neg (le_of_eq hm.symm)
    · rcases a with i | a
      · change (∑ j, ((0 : ℚ) : ℝ)*x j) ≤ ((ρ+M*r-rationalScore D p i : ℚ) : ℝ)
        simp only [Rat.cast_zero,zero_mul,Finset.sum_const_zero]
        push_cast
        rw [rational_score_real]
        linarith [hc.1 i]
      · rcases a with a | l
        · change (∑ i, ((-D i a : ℚ) : ℝ)*x i) ≤ ((ρ-∑ b, K a b*p b : ℚ) : ℝ)
          push_cast
          simp_rw [neg_mul,Finset.sum_neg_distrib]
          have ha := hh.1 a
          unfold anchorResponse at ha
          linarith
        · change (∑ i, ((max (rationalScore D p i-ρ-
            (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ)*x i) ≤
            (rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1)) : ℝ)
          have ht := hcall ((M*r-rationalGridNode M r η (l.val+1) : ℚ) : ℝ)
          rw [←rational_envelope_real M r (M*r-rationalGridNode M r η (l.val+1))] at ht
          simpa only [call,Rat.cast_max,Rat.cast_sub,Rat.cast_zero,rational_score_real,mul_comm] using ht


theorem exact_game_rational_gap_solve {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (x : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (hR : R.RealSatisfies x)
    (hM : 0 < M) (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
      (blockWeights (fun h => (p h : ℝ)) x) a ≤ (ρ : ℝ)) :
    ∃ q, rationalGapSolve K D p M r ρ η R=some q := by
  apply rational_lp_real_complete m ((rationalGapSystem K D p M r ρ η).append R)
  exact ⟨x,(rational_linear_real_append_iff _ R x).mpr
    ⟨exact_game_rational_gap_system_real K D p x B M r ρ η hM hq hm hB hb hrows,hR⟩⟩

theorem rational_gap_solve_none_excludes_real_completion {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (hM : 0 < M)
    (hn : rationalGapSolve K D p M r ρ η R=none) :
    ¬∃ (x : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      R.RealSatisfies x ∧ (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=(r : ℝ) ∧ IsSkew B ∧
      (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) x) a ≤ (ρ : ℝ) := by
  rintro ⟨x,B,hR,hq,hm,hB,hb,hrows⟩
  obtain ⟨q,hsol⟩ := exact_game_rational_gap_solve K D p x B M r ρ η R hR hM hq hm hB hb hrows
  rw [hn] at hsol
  cases hsol

end SparseCompletion

/- Fixed source body: RationalResidualCompletion.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Executable rational residual completion through finite Fourier--Motzkin LP;
no polynomial complexity claim. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

abbrev ResidualCompletionRows (m : ℕ) := (Fin 4 × (Fin m × Fin m)) ⊕ Fin m

def residualDecode {α : Type*} {m : ℕ} (x : Fin (m*m) → α) (i j : Fin m) : α :=
  x (finProdFinEquiv (i,j))

def residualEncode {α : Type*} {m : ℕ} (B : Fin m → Fin m → α)
    (u : Fin (m*m)) : α := B (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2

theorem residual_decode_encode {α : Type*} {m : ℕ} (B : Fin m → Fin m → α) :
    residualDecode (residualEncode B) = B := by
  funext i j
  simp only [residualDecode,residualEncode,Equiv.symm_apply_apply]

def residualBasis {m : ℕ} (i j : Fin m) (u : Fin (m*m)) : ℚ :=
  if u=finProdFinEquiv (i,j) then 1 else 0

/-- Tags 0,1 impose upper/lower entry bounds; tags 2,3 impose both
inequalities of skew symmetry. The remaining rows impose actual responses. -/
def residualCompletionSystem {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    RationalLinearSystem (ResidualCompletionRows m) (m*m) where
  coefficient := Sum.elim
    (fun row u => if row.1.val=0 then residualBasis row.2.1 row.2.2 u
      else if row.1.val=1 then -residualBasis row.2.1 row.2.2 u
      else if row.1.val=2 then residualBasis row.2.1 row.2.2 u+residualBasis row.2.2 row.2.1 u
      else -(residualBasis row.2.1 row.2.2 u+residualBasis row.2.2 row.2.1 u))
    (fun i u => ∑ j, residualBasis i j u*q j)
  rightSide := Sum.elim (fun row => if row.1.val=0 ∨ row.1.val=1 then M else 0)
    (fun i => σ-t i)

def ResidualRealConditions {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℝ) : Prop :=
  IsSkew B ∧ (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
    ∀ i, (t i : ℝ)+∑ j, B i j*(q j : ℝ) ≤ (σ : ℝ)

def ResidualRatConditions {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) : Prop :=
  (∀ i j, B i j= -B j i) ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
    ∀ i, t i+∑ j, B i j*q j ≤ σ

theorem residual_basis_real_sum {m : ℕ} (x : Fin (m*m) → ℝ) (i j : Fin m) :
    (∑ u, (residualBasis i j u : ℝ)*x u)=residualDecode x i j := by
  simp [residualBasis,residualDecode,apply_ite]

theorem residual_response_real_sum {m : ℕ} (q : Fin m → ℚ)
    (x : Fin (m*m) → ℝ) (i : Fin m) :
    (∑ u, ((∑ j, residualBasis i j u*q j : ℚ) : ℝ)*x u)=
      ∑ j, residualDecode x i j*(q j : ℝ) := by
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [mul_right_comm,mul_comm (q j : ℝ),←Finset.sum_mul] using
    congrArg (fun z => z*(q j : ℝ)) (residual_basis_real_sum x i j)

theorem residual_completion_real_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (x : Fin (m*m) → ℝ) :
    (residualCompletionSystem q t M σ).RealSatisfies x ↔
      ResidualRealConditions q t M σ (residualDecode x) := by
  have h0 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (0,i,j)) u : ℝ)*x u)=
        residualDecode x i j := by
    change (∑ u, (residualBasis i j u : ℝ)*x u)=_
    exact residual_basis_real_sum x i j
  have h1 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (1,i,j)) u : ℝ)*x u)=
        -residualDecode x i j := by
    change (∑ u, ((-residualBasis i j u : ℚ) : ℝ)*x u)=_
    simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib,residual_basis_real_sum]
  have h2 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (2,i,j)) u : ℝ)*x u)=
        residualDecode x i j+residualDecode x j i := by
    change (∑ u, ((residualBasis i j u+residualBasis j i u : ℚ) : ℝ)*x u)=_
    simp only [Rat.cast_add,add_mul,Finset.sum_add_distrib,residual_basis_real_sum]
  have h3 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (3,i,j)) u : ℝ)*x u)=
        -(residualDecode x i j+residualDecode x j i) := by
    change (∑ u, ((-(residualBasis i j u+residualBasis j i u) : ℚ) : ℝ)*x u)=_
    simp only [Rat.cast_neg,Rat.cast_add,neg_mul,add_mul,Finset.sum_neg_distrib,
      Finset.sum_add_distrib,residual_basis_real_sum]
  constructor
  · intro h
    have hub (i j : Fin m) : residualDecode x i j ≤ (M : ℝ) := by
      have hh := h (.inl (0,i,j))
      rw [h0] at hh
      exact hh
    have hlb (i j : Fin m) : -residualDecode x i j ≤ (M : ℝ) := by
      have hh := h (.inl (1,i,j))
      rw [h1] at hh
      exact hh
    have hsk1 (i j : Fin m) : residualDecode x i j+residualDecode x j i ≤ (0 : ℝ) := by
      have hh := h (.inl (2,i,j))
      rw [h2] at hh
      simpa [residualCompletionSystem] using hh
    have hsk2 (i j : Fin m) : -(residualDecode x i j+residualDecode x j i) ≤ (0 : ℝ) := by
      have hh := h (.inl (3,i,j))
      rw [h3] at hh
      simpa [residualCompletionSystem] using hh
    refine ⟨?_,?_,?_⟩
    · intro i j
      linarith [hsk1 i j,hsk2 i j]
    · intro i j
      exact ⟨by linarith [hlb i j],hub i j⟩
    · intro i
      have hi := h (.inr i)
      change (∑ u, ((∑ j, residualBasis i j u*q j : ℚ) : ℝ)*x u) ≤ ((σ-t i : ℚ) : ℝ) at hi
      rw [residual_response_real_sum,Rat.cast_sub] at hi
      linarith
  · rintro ⟨hsk,hb,hr⟩ row
    rcases row with ⟨tag,i,j⟩ | i
    · fin_cases tag
      · change (∑ u, (residualBasis i j u : ℝ)*x u) ≤ (M : ℝ)
        rw [residual_basis_real_sum]
        exact (hb i j).2
      · change (∑ u, ((-residualBasis i j u : ℚ) : ℝ)*x u) ≤ (M : ℝ)
        simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib,residual_basis_real_sum]
        linarith [(hb i j).1]
      · change (∑ u, ((residualBasis i j u+residualBasis j i u : ℚ) : ℝ)*x u) ≤ ((0 : ℚ) : ℝ)
        simp only [Rat.cast_add,add_mul,Finset.sum_add_distrib,residual_basis_real_sum,Rat.cast_zero]
        rw [hsk i j]
        linarith
      · change (∑ u, ((-(residualBasis i j u+residualBasis j i u) : ℚ) : ℝ)*x u) ≤ ((0 : ℚ) : ℝ)
        simp only [Rat.cast_neg,Rat.cast_add,neg_mul,add_mul,Finset.sum_neg_distrib,
          Finset.sum_add_distrib,residual_basis_real_sum,Rat.cast_zero]
        rw [hsk i j]
        linarith
    · change (∑ u, ((∑ j, residualBasis i j u*q j : ℚ) : ℝ)*x u) ≤ ((σ-t i : ℚ) : ℝ)
      rw [residual_response_real_sum,Rat.cast_sub]
      linarith [hr i]

end SparseCompletion

/- Fixed source body: RationalResidualSolver.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Executable rational residual completion through finite Fourier--Motzkin LP;
no polynomial complexity claim. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem residual_completion_row_count (m : ℕ) :
    Fintype.card (ResidualCompletionRows m)=4*m*m+m := by
  simp only [ResidualCompletionRows,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

theorem residual_rat_real_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) :
    ResidualRatConditions q t M σ B ↔
      ResidualRealConditions q t M σ (fun i j => (B i j : ℝ)) := by
  constructor
  · rintro ⟨hsk,hb,hr⟩
    refine ⟨?_,?_,?_⟩
    · intro i j
      change (B i j : ℝ)= -(B j i : ℝ)
      exact_mod_cast hsk i j
    · intro i j
      change -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ)
      exact_mod_cast hb i j
    · intro i
      have hi : ((t i+∑ j, B i j*q j : ℚ) : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hr i
      simpa only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul] using hi
  · rintro ⟨hsk,hb,hr⟩
    refine ⟨?_,?_,?_⟩
    · intro i j
      have hi := hsk i j
      change (B i j : ℝ)= -(B j i : ℝ) at hi
      exact_mod_cast hi
    · intro i j
      have hi := hb i j
      change -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ) at hi
      exact_mod_cast hi
    · intro i
      have hi : ((t i+∑ j, B i j*q j : ℚ) : ℝ) ≤ (σ : ℝ) := by
        simpa only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul] using hr i
      exact_mod_cast hi

theorem residual_completion_real_exists_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    (∃ x, (residualCompletionSystem q t M σ).RealSatisfies x) ↔
      ∃ B, ResidualRealConditions q t M σ B := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨residualDecode x,(residual_completion_real_iff q t M σ x).mp hx⟩
  · rintro ⟨B,hB⟩
    refine ⟨residualEncode B,(residual_completion_real_iff q t M σ _).mpr ?_⟩
    simpa only [residual_decode_encode] using hB

/-- Total computable rational matrix reconstruction; none is genuine infeasibility.
It uses the dimension-recursive rational solver, not a flow feasibility oracle. -/
def rationalResidualCompletion {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    Option (Fin m → Fin m → ℚ) :=
  (rationalLPSolve (m*m) (residualCompletionSystem q t M σ)).map residualDecode

theorem rational_residual_completion_complete {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (h : ∃ B, ResidualRealConditions q t M σ B) :
    ∃ B, rationalResidualCompletion q t M σ=some B := by
  obtain ⟨x,hx⟩ := rational_lp_real_complete (m*m) (residualCompletionSystem q t M σ)
    ((residual_completion_real_exists_iff q t M σ).mpr h)
  exact ⟨residualDecode x,by simp only [rationalResidualCompletion,hx,Option.map_some]⟩

theorem rational_residual_completion_real_sound {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) (h : rationalResidualCompletion q t M σ=some B) :
    ResidualRealConditions q t M σ (fun i j => (B i j : ℝ)) := by
  cases hx : rationalLPSolve (m*m) (residualCompletionSystem q t M σ) with
  | none =>
    simp only [rationalResidualCompletion,hx,Option.map_none] at h
    cases h
  | some x =>
    have hB : residualDecode x=B := by
      simpa only [rationalResidualCompletion,hx,Option.map_some,Option.some.injEq] using h
    subst B
    have hr := (rational_linear_real_cast_iff (residualCompletionSystem q t M σ) x).mpr
      (rational_lp_solve_sound (m*m) (residualCompletionSystem q t M σ) x hx)
    exact (residual_completion_real_iff q t M σ (fun u => (x u : ℝ))).mp hr

theorem rational_residual_completion_rat_sound {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) (h : rationalResidualCompletion q t M σ=some B) :
    ResidualRatConditions q t M σ B :=
  (residual_rat_real_iff q t M σ B).mpr (rational_residual_completion_real_sound q t M σ B h)

theorem rational_residual_completion_none_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    rationalResidualCompletion q t M σ=none ↔ ¬∃ B, ResidualRealConditions q t M σ B := by
  rw [rationalResidualCompletion,Option.map_eq_none_iff,rational_lp_solve_none_iff_real]
  exact not_congr (residual_completion_real_exists_iff q t M σ)

theorem rational_residual_completion_rat_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    (∃ B, ResidualRatConditions q t M σ B) ↔ ∃ B, ResidualRealConditions q t M σ B := by
  constructor
  · rintro ⟨B,hB⟩
    exact ⟨fun i j => (B i j : ℝ),(residual_rat_real_iff q t M σ B).mp hB⟩
  · intro h
    obtain ⟨B,hB⟩ := rational_residual_completion_complete q t M σ h
    exact ⟨B,rational_residual_completion_rat_sound q t M σ B hB⟩

end SparseCompletion

/- Fixed source body: RationalResidualGap.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Actual rational residual reconstruction for an accepted rational gap point;
no polynomial complexity claim. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def reconstructRationalGap {k m : ℕ} (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (q : Fin m → ℚ) (M ρ η : ℚ) : Option (Fin m → Fin m → ℚ) :=
  rationalResidualCompletion q (rationalScore D p) M (ρ+η)

theorem rational_gap_reconstruction_complete {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hcheck : checkRationalGap K D p q M r ρ η=true) :
    ∃ B, reconstructRationalGap D p q M ρ η=some B := by
  obtain ⟨B,hsk,hb,hr⟩ := rational_gap_completed_witness K D p q M r ρ η hM hη hcheck
  apply rational_residual_completion_complete q (rationalScore D p) M (ρ+η)
  refine ⟨B,hsk,hb,?_⟩
  intro i
  have hi := hr (.inr i)
  rw [block_response_residual] at hi
  simpa only [response,←rational_score_real,Rat.cast_add] using hi

theorem rational_gap_reconstruction_residual_sound {k m : ℕ}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M ρ η : ℚ) (B : Fin m → Fin m → ℚ)
    (h : reconstructRationalGap D p q M ρ η=some B) :
    ResidualRatConditions q (rationalScore D p) M (ρ+η) B :=
  rational_residual_completion_rat_sound q (rationalScore D p) M (ρ+η) B h

theorem rational_gap_reconstruction_full_rows {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hη : 0 < η) (hcheck : checkRationalGap K D p q M r ρ η=true)
    (B : Fin m → Fin m → ℚ) (h : reconstructRationalGap D p q M ρ η=some B) :
    ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  have hc := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  have hB := rational_residual_completion_real_sound q (rationalScore D p) M (ρ+η) B h
  apply (block_response_bounds_iff _ _ _ _ _ _).mpr
  constructor
  · intro a
    have hh : (rationalAnchorResponse K D p q a : ℝ) ≤ (ρ : ℝ) := by
      exact_mod_cast hc.2.2.2.1 a
    rw [rational_anchor_response_real] at hh
    have hηR : (0 : ℝ)<(η : ℝ) := by exact_mod_cast hη
    linarith
  · intro i
    have hi := hB.2.2 i
    simpa only [response,←rational_score_real,Rat.cast_add] using hi

theorem rational_gap_reconstruction_normalized_full_game {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hK : ∀ a b, K a b= -K b a)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hcheck : checkRationalGap K D p q M r ρ η=true)
    (B : Fin m → Fin m → ℚ) (h : reconstructRationalGap D p q M ρ η=some B) :
    (∀ a, 0 ≤ blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a) ∧
    (∑ a, blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
    IsSkew (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ)) a b ∧
      blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
        (fun i j => (B i j : ℝ)) a b ≤ (M : ℝ)) ∧
    ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  have hc := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  have hB := rational_residual_completion_real_sound q (rationalScore D p) M (ρ+η) B h
  have hKR : IsSkew (fun h a => (K h a : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a)
    (fun i => by exact_mod_cast hc.1 i),?_,blockMatrix_skew _ _ _ hKR hB.1,
    blockMatrix_bounds _ _ _ _ hKbR hDbR hB.2.1,
    rational_gap_reconstruction_full_rows K D p q M r ρ η hη hcheck B h⟩
  rw [blockWeights_mass]
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast hc.2.1
  rw [hm]
  exact_mod_cast hnorm

end SparseCompletion

/- Fixed source body: RationalRepertoire.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalRealRepertoire {I : Type*} {m : ℕ} (R : RationalLinearSystem I m) (r : ℚ) :
    Set (Fin m → ℝ) := {x | R.RealSatisfies x ∧ (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=(r : ℝ)}

theorem rational_real_repertoire_closed {I : Type*} {m : ℕ}
    (R : RationalLinearSystem I m) (r : ℚ) : IsClosed (rationalRealRepertoire R r) := by
  have he : rationalRealRepertoire R r=
      (⋂ i, {x : Fin m → ℝ | (∑ j, (R.coefficient i j : ℝ)*x j) ≤ (R.rightSide i : ℝ)}) ∩
      ((⋂ j, {x | (0 : ℝ) ≤ x j}) ∩ {x | (∑ j, x j)=(r : ℝ)}) := by
    ext x
    simp only [rationalRealRepertoire,RationalLinearSystem.RealSatisfies,Set.mem_ofPred_eq,
      Set.mem_inter_iff,Set.mem_iInter]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_eq (by fun_prop) continuous_const))

theorem rational_real_repertoire_compact {I : Type*} {m : ℕ}
    (R : RationalLinearSystem I m) (r : ℚ) : IsCompact (rationalRealRepertoire R r) := by
  have hc := rational_real_repertoire_closed R r
  apply (show IsCompact (Set.Icc (fun _ : Fin m => (0 : ℝ)) (fun _ => (r : ℝ))) from isCompact_Icc).of_isClosed_subset hc
  intro x hx
  refine ⟨hx.2.1,?_⟩
  intro i
  have hh := Finset.single_le_sum (fun j (_h : j ∈ (Finset.univ : Finset (Fin m))) => hx.2.1 j)
    (Finset.mem_univ i)
  rwa [hx.2.2] at hh

end SparseCompletion

/- Fixed source body: RationalGapAlgorithm.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Returns actual rational strategy/payoff data; Fourier–Motzkin cost may be exponential. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalGapAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) :
    Option ((Fin m → ℚ) × (Fin m → Fin m → ℚ)) :=
  (rationalGapSolve K D p M r ρ η R).bind (fun q =>
    (rationalResidualCompletion q (rationalScore D p) M (ρ+η)).map (fun B => (q,B)))

theorem rational_gap_algorithm_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapAlgorithm K D p M r ρ η R=some (q,B)) :
    R.Satisfies q ∧ RationalGapConditions K D p q M r ρ η ∧
      ResidualRatConditions q (rationalScore D p) M (ρ+η) B := by
  cases hq : rationalGapSolve K D p M r ρ η R with
  | none => simp only [rationalGapAlgorithm,hq,Option.bind_none] at h; cases h
  | some y =>
    cases hB : rationalResidualCompletion y (rationalScore D p) M (ρ+η) with
    | none => simp only [rationalGapAlgorithm,hq,Option.bind_some,hB,Option.map_none] at h; cases h
    | some C =>
      have hp : (y,C)=(q,B) := Option.some.inj (by
        simpa only [rationalGapAlgorithm,hq,Option.bind_some,hB,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
      have hh := rational_gap_solve_sound K D p M r ρ η R y hq
      exact ⟨hh.2,(rational_gap_check_iff K D p y M r ρ η).mp hh.1,
        rational_residual_completion_rat_sound y (rationalScore D p) M (ρ+η) C hB⟩

theorem rational_gap_algorithm_complete {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (hM : 0 < M) (hη : 0 < η)
    (h : RationalGapExists K D p M r ρ η R) :
    ∃ q B, rationalGapAlgorithm K D p M r ρ η R=some (q,B) := by
  cases hq : rationalGapSolve K D p M r ρ η R with
  | none => exact False.elim ((rational_gap_solve_none_iff K D p M r ρ η R).mp hq h)
  | some q =>
    have hc := (rational_gap_solve_sound K D p M r ρ η R q hq).1
    obtain ⟨B,hB⟩ := rational_gap_reconstruction_complete K D p q M r ρ η hM hη hc
    change rationalResidualCompletion q (rationalScore D p) M (ρ+η)=some B at hB
    exact ⟨q,B,by simp only [rationalGapAlgorithm,hq,Option.bind_some,hB,Option.map_some]⟩

end SparseCompletion

/- Fixed source body: RationalGapValue.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Executable exact rational elimination, with no polynomial bit-cost assertion. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure RationalGapModel (k m : ℕ) (I : Type*) where
  K : Fin k → Fin k → ℚ
  D : Fin m → Fin k → ℚ
  p : Fin k → ℚ
  M : ℚ
  r : ℚ
  η : ℚ
  R : RationalLinearSystem I m
  positiveBound : 0 < M
  positiveSlack : 0 < η
  anchorNonneg : ∀ a, 0 ≤ p a
  normalized : (∑ a, p a)+r=1
  anchorSkew : ∀ a b, K a b= -K b a
  anchorBounds : ∀ a b, -M ≤ K a b ∧ K a b ≤ M
  crossBounds : ∀ i a, -M ≤ D i a ∧ D i a ≤ M
  repertoireNonempty : (rationalRealRepertoire R r).Nonempty

theorem rational_gap_model_value_bounds {k m : ℕ} {I : Type*}
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    0 ≤ V ∧ V ≤ (d.M : ℝ) ∧
      fixedAnchorFeasible (rationalRealRepertoire d.R d.r)
        (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
        (fun a => (d.p a : ℝ)) d.M d.r V := by
  apply fixed_game_value_bounds _ _ _ _ _ _ (by exact_mod_cast le_of_lt d.positiveBound)
    (rational_real_repertoire_compact d.R d.r) d.repertoireNonempty
    (fun a => by exact_mod_cast d.anchorNonneg a) (by exact_mod_cast d.normalized)
    (fun _ h => h.2)
  · intro a b
    change (d.K a b : ℝ)= -(d.K b a : ℝ)
    exact_mod_cast d.anchorSkew a b
  · intro a b
    exact_mod_cast d.anchorBounds a b
  · intro i a
    exact_mod_cast d.crossBounds i a

theorem rational_gap_model_upper_feasible {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) :
    RationalGapExists d.K d.D d.p d.M d.r d.M d.η d.R := by
  obtain ⟨hV0,hVM,x,hx,hx0,hxm,B,hB,hb,hrows⟩ := rational_gap_model_value_bounds d
  obtain ⟨q,hq⟩ := exact_game_rational_gap_solve d.K d.D d.p x B d.M d.r d.M d.η d.R hx.1
    d.positiveBound hx0 hxm hB hb (fun a => le_trans (hrows a) hVM)
  have hs := rational_gap_solve_sound d.K d.D d.p d.M d.r d.M d.η d.R q hq
  exact ⟨q,(rational_gap_check_iff _ _ _ _ _ _ _ _).mp hs.1,hs.2⟩

def rationalGapApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (n : ℕ) :
    Option ((ℚ × ℚ) × ((Fin m → ℚ) × (Fin m → Fin m → ℚ))) :=
  let z := rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n
  (rationalGapAlgorithm d.K d.D d.p d.M d.r z.2 d.η d.R).map (fun w => (z,w))

theorem rational_gap_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (n : ℕ) :
    ∃ z q B, rationalGapApproximation d n=some (z,(q,B)) := by
  have hz := rational_gap_search_bracket d.K d.D d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_gap_model_upper_feasible d)
  obtain ⟨q,B,h⟩ := rational_gap_algorithm_complete d.K d.D d.p d.M d.r
    (rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n).2 d.η d.R
    d.positiveBound d.positiveSlack hz.2.2.2.1
  exact ⟨rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n,q,B,by
    simp only [rationalGapApproximation,h,Option.map_some]⟩

theorem rational_gap_approximation_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapApproximation d n=some (z,(q,B))) :
    z=rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n ∧
    rationalGapAlgorithm d.K d.D d.p d.M d.r z.2 d.η d.R=some (q,B) := by
  cases ha : rationalGapAlgorithm d.K d.D d.p d.M d.r
    (rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n).2 d.η d.R with
  | none => simp only [rationalGapApproximation,ha,Option.map_none] at h; cases h
  | some w =>
    have he := Option.some.inj (by simpa only [rationalGapApproximation,ha,Option.map_some] using h)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨rfl,ha⟩

theorem rational_gap_approximation_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (hout : rationalGapApproximation d n=some (z,(q,B))) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      z.2-z.1 ≤ d.M/((2 : ℕ) : ℚ)^n := by
  obtain ⟨hz,ha⟩ := rational_gap_approximation_output d n z q B hout
  have hbr := rational_gap_search_bracket d.K d.D d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_gap_model_upper_feasible d)
  rw [←hz] at hbr
  have hs := rational_gap_algorithm_sound d.K d.D d.p d.M d.r z.2 d.η d.R q B ha
  have hcheck := (rational_gap_check_iff _ _ _ _ _ _ _ _).mpr hs.2.1
  have hB : reconstructRationalGap d.D d.p q d.M z.2 d.η=some B := by
    unfold rationalGapAlgorithm at ha
    cases hq : rationalGapSolve d.K d.D d.p d.M d.r z.2 d.η d.R with
    | none => simp only [hq,Option.bind_none] at ha; cases ha
    | some y =>
      cases hb : rationalResidualCompletion y (rationalScore d.D d.p) d.M (z.2+d.η) with
      | none => simp only [hq,Option.bind_some,hb,Option.map_none] at ha; cases ha
      | some C =>
        have he : (y,C)=(q,B) := Option.some.inj (by simpa only [hq,Option.bind_some,hb,Option.map_some] using ha)
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        exact hb
  have hn := rational_gap_reconstruction_normalized_full_game d.K d.D d.p q d.M d.r z.2 d.η
    d.positiveSlack d.anchorNonneg d.normalized d.anchorSkew d.anchorBounds d.crossBounds hcheck B hB
  have hbR := rational_residual_completion_real_sound q (rationalScore d.D d.p) d.M (z.2+d.η) B hB
  have hqR : (fun i => (q i : ℝ)) ∈ rationalRealRepertoire d.R d.r := by
    refine ⟨(rational_linear_real_cast_iff d.R q).mpr hs.1,?_,?_⟩
    · intro i
      change (0 : ℝ) ≤ (q i : ℝ)
      exact_mod_cast hs.2.1.1 i
    · change (∑ i, (q i : ℝ))=(d.r : ℝ)
      exact_mod_cast hs.2.1.2.1
  have hu := le_trans (fixed_game_value_le_witness _ _ _ _ _
    (rational_real_repertoire_compact d.R d.r) _ _ ⟨hbR.1,hbR.2.1⟩ hqR)
    ((exploitability_le_iff _ _ _).mpr hn.2.2.2.2)
  refine ⟨?_,hu,hbr.2.2.2.2.2⟩
  obtain ⟨hV0,_,x,hx,hx0,hxm,C,hC,hcb,hrows⟩ := rational_gap_model_value_bounds d
  rcases hbr.2.2.2.2.1 with hzero | hno
  · rw [hzero,Rat.cast_zero]; exact hV0
  · by_contra hlow
    have hvL := le_of_lt (lt_of_not_ge hlow)
    obtain ⟨y,hy⟩ := exact_game_rational_gap_solve d.K d.D d.p x C d.M d.r z.1 d.η d.R hx.1
      d.positiveBound hx0 hxm hC hcb (fun a => le_trans (hrows a) hvL)
    have hh := rational_gap_solve_sound d.K d.D d.p d.M d.r z.1 d.η d.R y hy
    exact hno ⟨y,(rational_gap_check_iff _ _ _ _ _ _ _ _).mp hh.1,hh.2⟩

end SparseCompletion

/- Fixed source body: RationalLogRounds.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Logarithmic bisection rounds; no polynomial LP or bit-cost assertion. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalLogRounds (M ζ : ℚ) : ℕ := Nat.log2 (Nat.ceil (M/ζ))+1

theorem rational_log_rounds_width (M ζ : ℚ) (hζ : 0 < ζ) :
    M/((2 : ℕ) : ℚ)^rationalLogRounds M ζ < ζ := by
  have hc : M/ζ ≤ (Nat.ceil (M/ζ) : ℚ) := Nat.le_ceil (M/ζ)
  have hn : (Nat.ceil (M/ζ) : ℚ) < ((2 : ℕ) : ℚ)^rationalLogRounds M ζ := by
    unfold rationalLogRounds
    exact_mod_cast Nat.lt_log2_self (n := Nat.ceil (M/ζ))
  have hp : (0 : ℚ) < ((2 : ℕ) : ℚ)^rationalLogRounds M ζ := pow_pos (by norm_num) _
  have hm := (div_lt_iff₀ hζ).mp (lt_of_le_of_lt hc hn)
  exact (div_lt_iff₀ hp).mpr (by simpa only [mul_comm] using hm)

def rationalGapAccurateApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ζ : ℚ) :
    Option ((ℚ × ℚ) × ((Fin m → ℚ) × (Fin m → Fin m → ℚ))) :=
  rationalGapApproximation d (rationalLogRounds d.M ζ)

theorem rational_gap_accurate_complete {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) :
    ∃ z q B, rationalGapAccurateApproximation d ζ=some (z,(q,B)) :=
  rational_gap_approximation_complete d (rationalLogRounds d.M ζ)

theorem rational_gap_accurate_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (hout : rationalGapAccurateApproximation d ζ=some (z,(q,B))) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  have hb := rational_gap_approximation_value_enclosure d (rationalLogRounds d.M ζ) z q B hout
  have hw : z.2-z.1 < ζ := lt_of_le_of_lt hb.2.2 (rational_log_rounds_width d.M ζ hζ)
  have hwR : (z.2 : ℝ)-(z.1 : ℝ) < (ζ : ℝ) := by exact_mod_cast hw
  exact ⟨hb.1,hb.2.1,by linarith⟩

end SparseCompletion

/- Fixed source body: RationalAlgorithmCertificate.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Actual finite rational certificate output; the container may include zero weights. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def fullRationalCertificate {k m : ℕ} (p : Fin k → ℚ) (q : Fin m → ℚ)
    (B : Fin m → Fin m → ℚ) : RationalCertificate k m where
  support := Finset.univ
  anchors := p
  weights := fun i => q i
  residual := fun i j => B i j

theorem full_rational_certificate_q {k m : ℕ} (p : Fin k → ℚ) (q : Fin m → ℚ)
    (B : Fin m → Fin m → ℚ) (i : Fin m) : (fullRationalCertificate p q B).q i=q i := by
  simp [fullRationalCertificate,RationalCertificate.q]

theorem full_rational_certificate_b {k m : ℕ} (p : Fin k → ℚ) (q : Fin m → ℚ)
    (B : Fin m → Fin m → ℚ) (i j : Fin m) : (fullRationalCertificate p q B).b i j=B i j := by
  simp [fullRationalCertificate,RationalCertificate.b]

theorem rational_gap_algorithm_certificate {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ρ : ℚ) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapAlgorithm d.K d.D d.p d.M d.r ρ d.η d.R=some (q,B)) :
    (fullRationalCertificate d.p q B).check d.K d.D d.M (ρ+d.η)=true := by
  have hs := rational_gap_algorithm_sound d.K d.D d.p d.M d.r ρ d.η d.R q B h
  apply (RationalCertificate.check_iff _ _ _ _ _).mpr
  refine ⟨le_of_lt d.positiveBound,d.anchorNonneg,?_,?_,d.anchorSkew,d.anchorBounds,
    d.crossBounds,?_,?_,?_⟩
  · intro i
    rw [full_rational_certificate_q]
    exact hs.2.1.1 i
  · simp_rw [full_rational_certificate_q]
    rw [hs.2.1.2.1]
    exact d.normalized
  · intro i _ j _
    simpa only [full_rational_certificate_b] using hs.2.2.1 i j
  · intro i _ j _
    simpa only [full_rational_certificate_b] using hs.2.2.2.1 i j
  · refine ⟨?_,?_,?_⟩
    · intro a
      change (∑ b, d.K a b*d.p b)-(∑ i, d.D i a*(fullRationalCertificate d.p q B).q i) ≤ ρ+d.η
      simp_rw [full_rational_certificate_q]
      have ha := hs.2.1.2.2.2.1 a
      unfold rationalAnchorResponse at ha
      linarith [d.positiveSlack]
    · intro i _
      change (∑ a, d.D i a*d.p a)+(∑ j, (fullRationalCertificate d.p q B).b i j*
        (fullRationalCertificate d.p q B).q j) ≤ ρ+d.η
      simp_rw [full_rational_certificate_b,full_rational_certificate_q]
      simpa only [rationalScore] using hs.2.2.2.2 i
    · intro i hi
      exact False.elim (hi (Finset.mem_univ i))

def checkRationalGapOutput {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (σ : ℚ) (c : RationalCertificate k m) : Bool :=
  c.check d.K d.D d.M σ && decide (d.R.Satisfies c.q) && decide (c.anchors=d.p)

theorem rational_gap_algorithm_checked_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ρ : ℚ) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapAlgorithm d.K d.D d.p d.M d.r ρ d.η d.R=some (q,B)) :
    checkRationalGapOutput d (ρ+d.η) (fullRationalCertificate d.p q B)=true := by
  have hc := rational_gap_algorithm_certificate d ρ q B h
  have hs := (rational_gap_algorithm_sound d.K d.D d.p d.M d.r ρ d.η d.R q B h).1
  have he : (fullRationalCertificate d.p q B).q=q := by
    funext i
    exact full_rational_certificate_q d.p q B i
  unfold checkRationalGapOutput
  rw [hc,he]
  have ha : (fullRationalCertificate d.p q B).anchors=d.p := rfl
  rw [decide_eq_true hs,decide_eq_true ha]
  rfl

end SparseCompletion

/- Fixed source body: RationalCertifiedApproximation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Actual executable certificate payload and automatic accuracy bound. -/
@[expose] public section
namespace SparseCompletion

def rationalCertifiedApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ζ : ℚ) : Option ((ℚ × ℚ) × RationalCertificate k m) :=
  (rationalGapAccurateApproximation d ζ).map
    (fun w => (w.1,fullRationalCertificate d.p w.2.1 w.2.2))

theorem rational_certified_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) :
    ∃ z c, rationalCertifiedApproximation d ζ=some (z,c) := by
  obtain ⟨z,q,B,h⟩ := rational_gap_accurate_complete d ζ
  exact ⟨z,fullRationalCertificate d.p q B,by
    simp only [rationalCertifiedApproximation,h,Option.map_some]⟩

theorem rational_certified_approximation_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ζ : ℚ) (z : ℚ × ℚ) (c : RationalCertificate k m)
    (h : rationalCertifiedApproximation d ζ=some (z,c)) :
    ∃ q B, rationalGapAccurateApproximation d ζ=some (z,(q,B)) ∧
      c=fullRationalCertificate d.p q B := by
  cases ha : rationalGapAccurateApproximation d ζ with
  | none => simp only [rationalCertifiedApproximation,ha,Option.map_none] at h; cases h
  | some w =>
    have he := Option.some.inj (by simpa only [rationalCertifiedApproximation,ha,Option.map_some] using h)
    obtain ⟨hz,hc⟩ := Prod.mk.inj he
    exact ⟨w.2.1,w.2.2,by simp only [←hz],hc.symm⟩

theorem rational_certified_approximation_sound {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (c : RationalCertificate k m)
    (h : rationalCertifiedApproximation d ζ=some (z,c)) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    checkRationalGapOutput d (z.2+d.η) c=true ∧
      (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  obtain ⟨q,B,hout,rfl⟩ := rational_certified_approximation_output d ζ z c h
  have ha := (rational_gap_approximation_output d (rationalLogRounds d.M ζ) z q B hout).2
  exact ⟨rational_gap_algorithm_checked_output d z.2 q B ha,
    rational_gap_accurate_value_enclosure d ζ hζ z q B hout⟩

end SparseCompletion

/- Fixed source body: RationalIntervalRecovery.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalIntervalRecover {k m : ℕ} (lo V : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (i : Fin m) (a : Fin k) : ℚ := if q i=0 then lo i a else V i a/q i

def rationalMomentScore {k m : ℕ} (p : Fin k → ℚ) (V : Fin m → Fin k → ℚ) (i : Fin m) : ℚ :=
  ∑ a, V i a*p a

def rationalPerspectiveCall {m : ℕ} (q H : Fin m → ℚ) (ρ z : ℚ) : ℚ :=
  ∑ i, max (H i-(ρ+z)*q i) 0

theorem rational_interval_recovered_product {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (hV : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) :
    ∀ i a, q i*rationalIntervalRecover lo V q i a=V i a := by
  intro i a
  by_cases hz : q i=0
  · have hzero : V i a=0 := by
      have hbounds := hV i a
      simp only [hz,mul_zero] at hbounds
      exact le_antisymm hbounds.2 hbounds.1
    simp only [rationalIntervalRecover,hz,ite_true,zero_mul,hzero]
  · simp only [rationalIntervalRecover,hz,ite_false]
    field_simp

theorem rational_interval_recovered_bounds {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hV : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) :
    ∀ i a, lo i a ≤ rationalIntervalRecover lo V q i a ∧
      rationalIntervalRecover lo V q i a ≤ hi i a := by
  intro i a
  by_cases hz : q i=0
  · simp only [rationalIntervalRecover,hz,ite_true]
    exact ⟨le_refl _,hlu i a⟩
  · have hp : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
    simp only [rationalIntervalRecover,hz,ite_false]
    exact ⟨(le_div_iff₀ hp).mpr (hV i a).1,(div_le_iff₀ hp).mpr (hV i a).2⟩

theorem rational_recovered_score_moment {k m : ℕ}
    (lo V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (hprod : ∀ i a, q i*rationalIntervalRecover lo V q i a=V i a) :
    ∀ i, q i*rationalScore (rationalIntervalRecover lo V q) p i=rationalMomentScore p V i := by
  intro i
  unfold rationalScore rationalMomentScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [←mul_assoc,hprod i a]

theorem rational_perspective_call_identity {m : ℕ} (q t H : Fin m → ℚ) (ρ z : ℚ)
    (hq : ∀ i, 0 ≤ q i) (hH : ∀ i, q i*t i=H i) :
    rationalCall q (fun i => t i-ρ) z=rationalPerspectiveCall q H ρ z := by
  unfold rationalCall rationalPerspectiveCall
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ (hq i),mul_zero]
  congr 1
  linear_combination hH i

end SparseCompletion

/- Fixed source body: RationalIntervalGap.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalGapConditions {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) ∧
  (∀ a, (∑ b, K a b*p b)-(∑ i, V i a) ≤ ρ) ∧
  (∀ i, rationalScore lo p i ≤ ρ+M*r) ∧
  (∀ i, rationalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : Fin (rationalGridSize M r η),
    rationalPerspectiveCall q (rationalMomentScore p V) ρ
      (M*r-rationalGridNode M r η (l.val+1)) ≤
      rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))

instance rationalIntervalGapConditionsDecidable {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : Decidable (RationalIntervalGapConditions K lo hi V p q M r ρ η) := by
  unfold RationalIntervalGapConditions
  infer_instance

theorem rational_interval_gap_recovered {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    (∀ i a, lo i a ≤ rationalIntervalRecover lo V q i a ∧
      rationalIntervalRecover lo V q i a ≤ hi i a) ∧
    RationalGapConditions K (rationalIntervalRecover lo V q) p q M r ρ η := by
  rcases h with ⟨hq,hm,hV,ha,hlo,hcap,hcall⟩
  have hprod := rational_interval_recovered_product lo hi V q hV
  have hH := rational_recovered_score_moment lo V p q hprod
  refine ⟨rational_interval_recovered_bounds lo hi V q hq hlu hV,hq,hm,?_,?_,?_⟩
  · intro i
    by_cases hz : q i=0
    · simpa only [rationalScore,rationalIntervalRecover,hz,ite_true] using hlo i
    · have hp : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
      have hc := hcap i
      rw [←hH i] at hc
      nlinarith
  · intro a
    unfold rationalAnchorResponse
    have he : (∑ i, rationalIntervalRecover lo V q i a*q i)=∑ i, V i a := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm,hprod i a]
    rw [he]
    exact ha a
  · intro l
    rw [rational_perspective_call_identity q _ _ ρ _ hq hH]
    exact hcall l

theorem rational_interval_gap_rational_completion {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    ∃ B, reconstructRationalGap (rationalIntervalRecover lo V q) p q M ρ η=some B := by
  have hg := (rational_interval_gap_recovered K lo hi V p q M r ρ η hlu h).2
  exact rational_gap_reconstruction_complete K _ p q M r ρ η hM hη
    ((rational_gap_check_iff _ _ _ _ _ _ _ _).mpr hg)

end SparseCompletion

/- Fixed source body: RationalIntervalVariables.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalVariable (k m H : ℕ) :=
  Fin m ⊕ ((Fin m × Fin k) ⊕ ((Fin k × Fin k) ⊕ (Fin H × Fin m)))

def rationalIntervalVariableEquiv (k m H : ℕ) :
    RationalIntervalVariable k m H ≃ Fin (m+(m*k+(k*k+H*m))) :=
  (Equiv.sumCongr (Equiv.refl (Fin m))
    ((Equiv.sumCongr (finProdFinEquiv (m := m) (n := k))
      ((Equiv.sumCongr (finProdFinEquiv (m := k) (n := k))
        (finProdFinEquiv (m := H) (n := m))).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
          finSumFinEquiv

def intervalVariableDecode {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (v : RationalIntervalVariable k m H) : α :=
  x (rationalIntervalVariableEquiv k m H v)

def intervalVariableEncode {α : Type*} {k m H : ℕ}
    (f : RationalIntervalVariable k m H → α) (u : Fin (m+(m*k+(k*k+H*m)))) : α :=
  f ((rationalIntervalVariableEquiv k m H).symm u)

theorem interval_variable_decode_encode {α : Type*} {k m H : ℕ}
    (f : RationalIntervalVariable k m H → α) :
    intervalVariableDecode (intervalVariableEncode f)=f := by
  funext v
  exact congrArg f ((rationalIntervalVariableEquiv k m H).symm_apply_apply v)

theorem interval_variable_encode_decode {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) :
    intervalVariableEncode (intervalVariableDecode x)=x := by
  funext u
  exact congrArg x ((rationalIntervalVariableEquiv k m H).apply_symm_apply u)

end SparseCompletion

/- Fixed source body: RationalIntervalForms.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def intervalBasis {k m H : ℕ} (v : RationalIntervalVariable k m H)
    (u : Fin (m+(m*k+(k*k+H*m)))) : ℚ :=
  if u=rationalIntervalVariableEquiv k m H v then 1 else 0

def intervalQ {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (i : Fin m) : α := intervalVariableDecode x (.inl i)
def intervalV {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (i : Fin m) (a : Fin k) : α :=
  intervalVariableDecode x (.inr (.inl (i,a)))
def intervalK {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (a b : Fin k) : α :=
  intervalVariableDecode x (.inr (.inr (.inl (a,b))))
def intervalAux {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (l : Fin H) (i : Fin m) : α :=
  intervalVariableDecode x (.inr (.inr (.inr (l,i))))

theorem interval_basis_eval {k m H : ℕ} (v : RationalIntervalVariable k m H)
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) :
    (∑ u, intervalBasis v u*x u)=intervalVariableDecode x v := by
  simp only [intervalBasis,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    intervalVariableDecode]

theorem interval_basis_real_eval {k m H : ℕ} (v : RationalIntervalVariable k m H)
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) :
    (∑ u, (intervalBasis v u : ℝ)*x u)=intervalVariableDecode x v := by
  calc
    _ = ∑ u, if u=rationalIntervalVariableEquiv k m H v then x u else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : u=rationalIntervalVariableEquiv k m H v <;> simp [intervalBasis,h]
    _ = _ := by
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,intervalVariableDecode]

end SparseCompletion

/- Fixed source body: RationalLinearForms.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFormAdd {n : ℕ} (c d : Fin n → ℚ) : Fin n → ℚ := fun u => c u+d u
def rationalFormScale {n : ℕ} (a : ℚ) (c : Fin n → ℚ) : Fin n → ℚ := fun u => a*c u
def rationalFormSum {n : ℕ} {I : Type*} [Fintype I] (c : I → Fin n → ℚ) : Fin n → ℚ :=
  fun u => ∑ i, c i u

def rationalFormEval {n : ℕ} (c x : Fin n → ℚ) : ℚ := ∑ u, c u*x u
def rationalFormRealEval {n : ℕ} (c : Fin n → ℚ) (x : Fin n → ℝ) : ℝ :=
  ∑ u, (c u : ℝ)*x u

theorem rational_form_eval_add {n : ℕ} (c d x : Fin n → ℚ) :
    rationalFormEval (rationalFormAdd c d) x=rationalFormEval c x+rationalFormEval d x := by
  simp only [rationalFormEval,rationalFormAdd,add_mul,Finset.sum_add_distrib]

theorem rational_form_eval_scale {n : ℕ} (a : ℚ) (c x : Fin n → ℚ) :
    rationalFormEval (rationalFormScale a c) x=a*rationalFormEval c x := by
  simp only [rationalFormEval,rationalFormScale,mul_assoc,Finset.mul_sum]

theorem rational_form_eval_sum {n : ℕ} {I : Type*} [Fintype I]
    (c : I → Fin n → ℚ) (x : Fin n → ℚ) :
    rationalFormEval (rationalFormSum c) x=∑ i, rationalFormEval (c i) x := by
  simp only [rationalFormEval,rationalFormSum,Finset.sum_mul]
  exact Finset.sum_comm

theorem rational_form_real_eval_add {n : ℕ} (c d : Fin n → ℚ) (x : Fin n → ℝ) :
    rationalFormRealEval (rationalFormAdd c d) x=
      rationalFormRealEval c x+rationalFormRealEval d x := by
  simp only [rationalFormRealEval,rationalFormAdd,Rat.cast_add,add_mul,Finset.sum_add_distrib]

theorem rational_form_real_eval_scale {n : ℕ} (a : ℚ) (c : Fin n → ℚ) (x : Fin n → ℝ) :
    rationalFormRealEval (rationalFormScale a c) x=(a : ℝ)*rationalFormRealEval c x := by
  simp only [rationalFormRealEval,rationalFormScale,Rat.cast_mul,mul_assoc,Finset.mul_sum]

theorem rational_form_real_eval_sum {n : ℕ} {I : Type*} [Fintype I]
    (c : I → Fin n → ℚ) (x : Fin n → ℝ) :
    rationalFormRealEval (rationalFormSum c) x=∑ i, rationalFormRealEval (c i) x := by
  simp only [rationalFormRealEval,rationalFormSum,Rat.cast_sum,Finset.sum_mul]
  exact Finset.sum_comm

end SparseCompletion

/- Fixed source body: RationalIntervalEncoding.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

abbrev RationalIntervalTailRows (m H : ℕ) :=
  Fin m ⊕ (Fin m ⊕ ((Fin 2 × (Fin H × Fin m)) ⊕ Fin H))
abbrev RationalIntervalRows (k m H : ℕ) :=
  Fin m ⊕ (Fin 2 ⊕ ((Fin 2 × (Fin m × Fin k)) ⊕
    ((Fin 4 × (Fin k × Fin k)) ⊕ (Fin k ⊕ RationalIntervalTailRows m H))))

def intervalQForm (k m H : ℕ) (i : Fin m) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inl i)
def intervalVForm (k m H : ℕ) (i : Fin m) (a : Fin k) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inr (.inl (i,a)))
def intervalKForm (k m H : ℕ) (a b : Fin k) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inr (.inr (.inl (a,b))))
def intervalAuxForm (k m H : ℕ) (l : Fin H) (i : Fin m) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inr (.inr (.inr (l,i))))

def rationalIntervalCoefficient {k m : ℕ} (H : ℕ)
    (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalIntervalRows k m H → Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  let Q := intervalQForm k m H
  let V := intervalVForm k m H
  let K := intervalKForm k m H
  let A := intervalAuxForm k m H
  let scoreV := fun i => rationalFormSum (fun a => rationalFormScale (p a) (V i a))
  Sum.elim (fun i => rationalFormScale (-1) (Q i))
    (Sum.elim (fun s => rationalFormScale (if s.val=0 then 1 else -1) (rationalFormSum Q))
      (Sum.elim (fun row =>
        if row.1.val=0 then
          rationalFormAdd (rationalFormScale (lo row.2.1 row.2.2) (Q row.2.1))
            (rationalFormScale (-1) (V row.2.1 row.2.2))
        else rationalFormAdd (V row.2.1 row.2.2)
          (rationalFormScale (-hi row.2.1 row.2.2) (Q row.2.1)))
        (Sum.elim (fun row =>
          if row.1.val=0 then rationalFormAdd (K row.2.1 row.2.2) (K row.2.2 row.2.1)
          else if row.1.val=1 then rationalFormScale (-1)
            (rationalFormAdd (K row.2.1 row.2.2) (K row.2.2 row.2.1))
          else if row.1.val=2 then rationalFormScale (-1) (K row.2.1 row.2.2)
          else K row.2.1 row.2.2)
          (Sum.elim (fun a =>
            rationalFormAdd (rationalFormSum (fun b => rationalFormScale (p b) (K a b)))
              (rationalFormScale (-1) (rationalFormSum (fun i => V i a))))
            (Sum.elim (fun _ => fun _ => 0)
              (Sum.elim (fun i => rationalFormAdd (scoreV i) (rationalFormScale (-(ρ+M*r)) (Q i)))
                (Sum.elim (fun row =>
                  if row.1.val=0 then rationalFormScale (-1) (A row.2.1 row.2.2)
                  else rationalFormAdd
                    (rationalFormAdd (scoreV row.2.2)
                      (rationalFormScale (-(ρ+(M*r-rationalGridNode M r η (row.2.1.val+1))))
                        (Q row.2.2)))
                    (rationalFormScale (-1) (A row.2.1 row.2.2)))
                  (fun l => rationalFormSum (A l)))))))))

def rationalIntervalRightSide {k m : ℕ} (H : ℕ)
    (loK hiK : Fin k → Fin k → ℚ) (lo : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) : RationalIntervalRows k m H → ℚ :=
  Sum.elim (fun _ => 0)
    (Sum.elim (fun s => if s.val=0 then r else -r)
      (Sum.elim (fun _ => 0)
        (Sum.elim (fun row =>
          if row.1.val=0 then 0 else if row.1.val=1 then 0
          else if row.1.val=2 then -loK row.2.1 row.2.2 else hiK row.2.1 row.2.2)
          (Sum.elim (fun _ => ρ)
            (Sum.elim (fun i => ρ+M*r-rationalScore lo p i)
              (Sum.elim (fun _ => 0)
                (Sum.elim (fun _ => 0) (fun l =>
                  rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))))))))))

def rationalIntervalSystem {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) :
    RationalLinearSystem (RationalIntervalRows k m (rationalGridSize M r η))
      (m+(m*k+(k*k+rationalGridSize M r η*m))) :=
  ⟨rationalIntervalCoefficient (rationalGridSize M r η) lo hi p M r ρ η,
    rationalIntervalRightSide (rationalGridSize M r η) loK hiK lo p M r ρ η⟩

theorem rational_interval_row_count (k m H : ℕ) :
    Fintype.card (RationalIntervalRows k m H)=
      3*m+2+2*m*k+4*k*k+k+2*H*m+H := by
  simp only [RationalIntervalRows,RationalIntervalTailRows,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin]
  ring

end SparseCompletion

/- Fixed source body: RationalIntervalPoint.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalPoint {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) ∧
  (∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
  (∀ a, (∑ b, K a b*p b)-(∑ i, V i a) ≤ ρ) ∧
  (∀ i, rationalScore lo p i ≤ ρ+M*r) ∧
  (∀ i, rationalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : Fin (rationalGridSize M r η),
    (∀ i, 0 ≤ A l i) ∧
    (∀ i, rationalMomentScore p V i-
      (ρ+(M*r-rationalGridNode M r η (l.val+1)))*q i ≤ A l i) ∧
    (∑ i, A l i) ≤ rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))

instance rationalIntervalPointDecidable {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℚ) :
    Decidable (RationalIntervalPoint loK hiK lo hi V K p q M r ρ η A) := by
  unfold RationalIntervalPoint
  infer_instance

theorem rational_interval_point_gap {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℚ)
    (h : RationalIntervalPoint loK hiK lo hi V K p q M r ρ η A) :
    (∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η := by
  rcases h with ⟨hq,hm,hV,hK,hKb,ha,hlo,hcap,hA⟩
  refine ⟨hK,hKb,hq,hm,hV,ha,hlo,hcap,?_⟩
  intro l
  exact le_trans (Finset.sum_le_sum fun i _ => max_le ((hA l).2.1 i) ((hA l).1 i)) (hA l).2.2

theorem rational_interval_point_epigraph_iff {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    ((∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η) ↔
    ∃ A, RationalIntervalPoint loK hiK lo hi V K p q M r ρ η A := by
  constructor
  · rintro ⟨hK,hKb,hq,hm,hV,ha,hlo,hcap,hcall⟩
    let A := fun (l : Fin (rationalGridSize M r η)) i =>
      max (rationalMomentScore p V i-(ρ+(M*r-rationalGridNode M r η (l.val+1)))*q i) 0
    refine ⟨A,hq,hm,hV,hK,hKb,ha,hlo,hcap,?_⟩
    intro l
    exact ⟨fun i => le_max_right _ _,fun i => le_max_left _ _,hcall l⟩
  · rintro ⟨A,h⟩
    exact rational_interval_point_gap loK hiK lo hi V K p q M r ρ η A h

end SparseCompletion

/- Fixed source body: RationalIntervalEvaluation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem interval_q_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (i : Fin m) :
    rationalFormEval (intervalQForm k m H i) x=intervalQ x i := by
  exact interval_basis_eval _ x

theorem interval_q_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (i : Fin m) :
    rationalFormRealEval (intervalQForm k m H i) x=intervalQ x i := by
  exact interval_basis_real_eval _ x

theorem interval_v_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (i : Fin m) (a : Fin k) :
    rationalFormEval (intervalVForm k m H i a) x=intervalV x i a := by
  exact interval_basis_eval _ x

theorem interval_v_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (i : Fin m) (a : Fin k) :
    rationalFormRealEval (intervalVForm k m H i a) x=intervalV x i a := by
  exact interval_basis_real_eval _ x

theorem interval_k_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (a b : Fin k) :
    rationalFormEval (intervalKForm k m H a b) x=intervalK x a b := by
  exact interval_basis_eval _ x

theorem interval_k_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (a b : Fin k) :
    rationalFormRealEval (intervalKForm k m H a b) x=intervalK x a b := by
  exact interval_basis_real_eval _ x

theorem interval_aux_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (l : Fin H) (i : Fin m) :
    rationalFormEval (intervalAuxForm k m H l i) x=intervalAux x l i := by
  exact interval_basis_eval _ x

theorem interval_aux_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (l : Fin H) (i : Fin m) :
    rationalFormRealEval (intervalAuxForm k m H l i) x=intervalAux x l i := by
  exact interval_basis_real_eval _ x

end SparseCompletion

/- Fixed source body: RationalIntervalSystemPoint.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem rational_interval_system_point {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) :
    (rationalIntervalSystem loK hiK lo hi p M r ρ η).Satisfies x ↔
      RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
        M r ρ η (intervalAux x) := by
  change (∀ row, rationalFormEval
    (rationalIntervalCoefficient (rationalGridSize M r η) lo hi p M r ρ η row) x ≤
    rationalIntervalRightSide (rationalGridSize M r η) loK hiK lo p M r ρ η row) ↔ _
  simp only [RationalIntervalRows,RationalIntervalTailRows,Sum.forall,Prod.forall,
    rationalIntervalCoefficient,rationalIntervalRightSide,Sum.elim_inl,Sum.elim_inr]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,Fin.val_zero,Fin.val_succ]
  simp only [Nat.reduceAdd,Nat.reduceEqDiff,ite_true,ite_false,
    rational_form_eval_add,rational_form_eval_scale,rational_form_eval_sum,
    interval_q_form_eval,interval_v_form_eval,interval_k_form_eval,interval_aux_form_eval]
  unfold RationalIntervalPoint rationalMomentScore
  simp only [rationalFormEval,zero_mul,Finset.sum_const_zero,neg_one_mul,one_mul]
  simp only [and_true,neg_nonpos,neg_le_neg_iff,neg_mul,←sub_eq_add_neg,
    sub_nonpos,sub_nonneg,mul_comm]
  constructor
  · rintro ⟨hq,hm,hV,hK,ha,hlo,hcap,hA,hcall⟩
    refine ⟨hq,le_antisymm hm.1 hm.2,?_,?_,?_,ha,hlo,hcap,?_⟩
    · intro i a
      exact ⟨hV.1 i a,hV.2 i a⟩
    · intro a b
      have hl := hK.1 a b
      have hu := hK.2.1 a b
      linarith
    · intro a b
      exact ⟨hK.2.2.1 a b,hK.2.2.2 a b⟩
    · intro l
      exact ⟨hA.1 l,hA.2 l,hcall l⟩
  · rintro ⟨hq,hm,hV,hK,hKb,ha,hlo,hcap,hA⟩
    refine ⟨hq,⟨le_of_eq hm,le_of_eq hm.symm⟩,⟨?_,?_⟩,⟨?_,?_,?_,?_⟩,ha,hlo,hcap,⟨?_,?_⟩,?_⟩
    · intro i a
      exact (hV i a).1
    · intro i a
      exact (hV i a).2
    · intro a b
      have he := hK a b
      linarith
    · intro a b
      have he := hK a b
      linarith
    · intro a b
      exact (hKb a b).1
    · intro a b
      exact (hKb a b).2
    · intro l
      exact (hA l).1
    · intro l
      exact (hA l).2.1
    · intro l
      exact (hA l).2.2
end SparseCompletion

/- Fixed source body: RationalIntervalPack.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def intervalPack {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    Fin (m+(m*k+(k*k+H*m))) → α :=
  intervalVariableEncode (Sum.elim q (Sum.elim (fun v => V v.1 v.2)
    (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))))

theorem interval_pack_q {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalQ (intervalPack q V K A)=q := by
  funext i
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

theorem interval_pack_v {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalV (intervalPack q V K A)=V := by
  funext i a
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

theorem interval_pack_k {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalK (intervalPack q V K A)=K := by
  funext a b
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

theorem interval_pack_aux {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalAux (intervalPack q V K A)=A := by
  funext l i
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

end SparseCompletion

/- Fixed source body: RationalIntervalSolver.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Total rational Fourier–Motzkin solve plus explicit residual reconstruction. -/
@[expose] public section
namespace SparseCompletion

def rationalIntervalAlgorithm {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) : Option ((Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) ×
      (Fin m → Fin m → ℚ)) :=
  (rationalLPSolve _ (rationalIntervalSystem loK hiK lo hi p M r ρ η)).bind (fun x =>
    (reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η).map (fun B => (x,B)))

theorem rational_interval_lp_feasible_iff {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) :
    (∃ x, (rationalIntervalSystem loK hiK lo hi p M r ρ η).Satisfies x) ↔
    ∃ q V K, (∀ a b, K a b= -K b a) ∧
      (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨intervalQ x,intervalV x,intervalK x,
      rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _
        ((rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hx)⟩
  · rintro ⟨q,V,K,h⟩
    obtain ⟨A,hA⟩ := (rational_interval_point_epigraph_iff loK hiK lo hi V K p q M r ρ η).mp h
    refine ⟨intervalPack q V K A,(rational_interval_system_point loK hiK lo hi p M r ρ η _).mpr ?_⟩
    simpa only [interval_pack_q,interval_pack_v,interval_pack_k,interval_pack_aux] using hA

theorem rational_interval_algorithm_output {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (h : rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B)) :
    RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
      M r ρ η (intervalAux x) ∧
    reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η=some B := by
  unfold rationalIntervalAlgorithm at h
  cases hs : rationalLPSolve _ (rationalIntervalSystem loK hiK lo hi p M r ρ η) with
  | none => simp only [hs,Option.bind_none] at h; cases h
  | some y =>
    cases hb : reconstructRationalGap (rationalIntervalRecover lo (intervalV y) (intervalQ y))
      p (intervalQ y) M ρ η with
    | none => simp only [hs,Option.bind_some,hb,Option.map_none] at h; cases h
    | some C =>
      have he : (y,C)=(x,B) := Option.some.inj
        (by simpa only [hs,Option.bind_some,hb,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact ⟨(rational_interval_system_point loK hiK lo hi p M r ρ η y).mp
        (rational_lp_solve_sound _ _ y hs),hb⟩

theorem rational_interval_algorithm_complete {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ q V K, (∀ a b, K a b= -K b a) ∧
      (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    ∃ x B, rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B) := by
  obtain ⟨x,hx⟩ := rational_lp_solve_complete _ _
    ((rational_interval_lp_feasible_iff loK hiK lo hi p M r ρ η).mpr hf)
  have hp := (rational_interval_system_point loK hiK lo hi p M r ρ η x).mp
    (rational_lp_solve_sound _ _ x hx)
  have hg := (rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _ hp).2.2
  obtain ⟨B,hB⟩ := rational_interval_gap_rational_completion _ lo hi _ p _ M r ρ η hM hη hlu hg
  exact ⟨x,B,by simp only [rationalIntervalAlgorithm,hx,Option.bind_some,hB,Option.map_some]⟩

end SparseCompletion

/- Fixed source body: RationalIntervalGameOutput.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_algorithm_full_game {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hloK : ∀ a b, -M ≤ loK a b) (hhiK : ∀ a b, hiK a b ≤ M)
    (hlo : ∀ i a, -M ≤ lo i a) (hhi : ∀ i a, hi i a ≤ M)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B)) :
    let q := intervalQ x
    let K := intervalK x
    let D := rationalIntervalRecover lo (intervalV x) q
    (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
    (∀ i a, lo i a ≤ D i a ∧ D i a ≤ hi i a) ∧
    (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a) ∧
    (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
    IsSkew (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ)) a b ∧
      blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ)) a b ≤ (M : ℝ)) ∧
    ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  obtain ⟨hpoint,hB⟩ := rational_interval_algorithm_output loK hiK lo hi p M r ρ η x B hout
  obtain ⟨hK,hKb,hgap⟩ := rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _ hpoint
  obtain ⟨hD,hG⟩ := rational_interval_gap_recovered _ lo hi _ p _ M r ρ η hlu hgap
  refine ⟨hKb,hD,?_⟩
  apply rational_gap_reconstruction_normalized_full_game _ _ p _ M r ρ η hη hp hnorm hK
    (fun a b => ⟨le_trans (hloK a b) (hKb a b).1,le_trans (hKb a b).2 (hhiK a b)⟩)
    (fun i a => ⟨le_trans (hlo i a) (hD i a).1,le_trans (hD i a).2 (hhi i a)⟩)
    ((rational_gap_check_iff _ _ _ _ _ _ _ _).mpr hG) B hB

end SparseCompletion

/- Fixed source body: RationalIntervalRealPoint.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalRealPoint {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi : Fin m → Fin k → ℚ) (V : Fin m → Fin k → ℝ) (K : Fin k → Fin k → ℝ)
    (p : Fin k → ℚ) (q : Fin m → ℝ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=(r : ℝ) ∧
  (∀ i a, (lo i a : ℝ)*q i ≤ V i a ∧ V i a ≤ (hi i a : ℝ)*q i) ∧
  (∀ a b, K a b= -K b a) ∧ (∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ)) ∧
  (∀ a, (∑ b, K a b*(p b : ℝ))-(∑ i, V i a) ≤ (ρ : ℝ)) ∧
  (∀ i, (rationalScore lo p i : ℝ) ≤ ((ρ+M*r : ℚ) : ℝ)) ∧
  (∀ i, (∑ a, V i a*(p a : ℝ)) ≤ ((ρ+M*r : ℚ) : ℝ)*q i) ∧
  ∀ l : Fin (rationalGridSize M r η),
    (∀ i, 0 ≤ A l i) ∧
    (∀ i, (∑ a, V i a*(p a : ℝ))-
      ((ρ+(M*r-rationalGridNode M r η (l.val+1)) : ℚ) : ℝ)*q i ≤ A l i) ∧
    (∑ i, A l i) ≤ (rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1)) : ℝ)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem rational_interval_system_real_point {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℝ) :
    (rationalIntervalSystem loK hiK lo hi p M r ρ η).RealSatisfies x ↔
      RationalIntervalRealPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
        M r ρ η (intervalAux x) := by
  change (∀ row, rationalFormRealEval
    (rationalIntervalCoefficient (rationalGridSize M r η) lo hi p M r ρ η row) x ≤
    (rationalIntervalRightSide (rationalGridSize M r η) loK hiK lo p M r ρ η row : ℝ)) ↔ _
  simp only [RationalIntervalRows,RationalIntervalTailRows,Sum.forall,Prod.forall,
    rationalIntervalCoefficient,rationalIntervalRightSide,Sum.elim_inl,Sum.elim_inr]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,Fin.val_zero,Fin.val_succ]
  simp only [Nat.reduceAdd,Nat.reduceEqDiff,ite_true,ite_false,
    rational_form_real_eval_add,rational_form_real_eval_scale,rational_form_real_eval_sum,
    interval_q_real_form_eval,interval_v_real_form_eval,interval_k_real_form_eval,interval_aux_real_form_eval]
  unfold RationalIntervalRealPoint
  push_cast
  simp only [rationalFormRealEval,Rat.cast_zero,zero_mul,Finset.sum_const_zero,neg_one_mul,one_mul]
  simp only [and_true,neg_nonpos,neg_le_neg_iff,neg_mul,←sub_eq_add_neg,
    sub_nonpos,sub_nonneg,mul_comm]
  constructor
  · rintro ⟨hq,hm,hV,hK,ha,hlo,hcap,hA,hcall⟩
    refine ⟨hq,le_antisymm hm.1 hm.2,?_,?_,?_,ha,hlo,hcap,?_⟩
    · intro i a
      exact ⟨hV.1 i a,hV.2 i a⟩
    · intro a b
      have hl := hK.1 a b
      have hu := hK.2.1 a b
      linarith
    · intro a b
      exact ⟨hK.2.2.1 a b,hK.2.2.2 a b⟩
    · intro l
      exact ⟨hA.1 l,hA.2 l,hcall l⟩
  · rintro ⟨hq,hm,hV,hK,hKb,ha,hlo,hcap,hA⟩
    refine ⟨hq,⟨le_of_eq hm,le_of_eq hm.symm⟩,⟨?_,?_⟩,⟨?_,?_,?_,?_⟩,ha,hlo,hcap,⟨?_,?_⟩,?_⟩
    · intro i a
      exact (hV i a).1
    · intro i a
      exact (hV i a).2
    · intro a b
      have he := hK a b
      linarith
    · intro a b
      have he := hK a b
      linarith
    · intro a b
      exact (hKb a b).1
    · intro a b
      exact (hKb a b).2
    · intro l
      exact (hA l).1
    · intro l
      exact (hA l).2.1
    · intro l
      exact (hA l).2.2
end SparseCompletion

/- Fixed source body: RationalIntervalRealNecessity.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem real_interval_completion_rational_lp {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ)
    (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (hK : IsSkew K) (hKb : ∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ))
    (hD : ∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (p a : ℝ)) q) a ≤ (ρ : ℝ)) :
    ∃ x, (rationalIntervalSystem loK hiK lo hi p M r ρ η).RealSatisfies x := by
  have hMR : (0 : ℝ)<(M : ℝ) := by exact_mod_cast hM
  have hh := (block_response_bounds_iff K D B (fun a => (p a : ℝ)) q (ρ : ℝ)).mp hrows
  have hc := (weighted_completion_iff q (score D (fun a => (p a : ℝ))) M r ρ
    (le_of_lt hMR) hq hr).mp ⟨B,hB,hb,hh.2⟩
  let V := fun i a => q i*D i a
  let A := fun (l : Fin (rationalGridSize M r η)) i =>
    max ((∑ a, V i a*(p a : ℝ))-
      ((ρ+(M*r-rationalGridNode M r η (l.val+1)) : ℚ) : ℝ)*q i) 0
  have hprod : ∀ i a, q i*D i a=V i a := fun _ _ => rfl
  have hH : ∀ i, q i*score D (fun a => (p a : ℝ)) i=∑ a, V i a*(p a : ℝ) := by
    intro i
    unfold score
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by dsimp only [V]; ring
  have hpoint : RationalIntervalRealPoint loK hiK lo hi V K p q M r ρ η A := by
    refine ⟨hq,hr,?_,hK,hKb,?_,?_,?_,?_⟩
    · intro i a
      exact ⟨mul_le_mul_of_nonneg_right (hD i a).1 (hq i) |>.trans_eq (mul_comm _ _),
        (mul_comm (q i) (D i a)).le.trans (mul_le_mul_of_nonneg_right (hD i a).2 (hq i))⟩
    · intro a
      rw [←anchor_response_of_perspective K D V (fun a => (p a : ℝ)) q hprod a]
      exact hh.1 a
    · intro i
      have hs := score_lower_from_intervals (fun i a => (lo i a : ℝ)) D (fun a => (p a : ℝ))
        (fun a => by exact_mod_cast hp a) (fun i a => (hD i a).1) i
      have ht := le_trans hs (hc.1 i)
      simpa only [←rational_score_real,Rat.cast_add,Rat.cast_mul] using ht
    · intro i
      rw [←hH i]
      have ht := mul_le_mul_of_nonneg_right (hc.1 i) (hq i)
      simpa only [mul_comm (q i),Rat.cast_add,Rat.cast_mul] using ht
    · intro l
      refine ⟨fun i => le_max_right _ _,fun i => le_max_left _ _,?_⟩
      have ht := cuts_imply_call_bound q (fun i => score D (fun a => (p a : ℝ)) i-(ρ : ℝ))
        M r hMR hc.2 ((M*r-rationalGridNode M r η (l.val+1) : ℚ) : ℝ)
      rw [perspective_call_identity q _ _ _ _ hq hH] at ht
      simpa only [perspectiveCall,A,rational_envelope_real,Rat.cast_add] using ht
  refine ⟨intervalPack q V K A,(rational_interval_system_real_point loK hiK lo hi p M r ρ η _).mpr ?_⟩
  simpa only [interval_pack_q,interval_pack_v,interval_pack_k,interval_pack_aux] using hpoint

end
end SparseCompletion

/- Fixed source body: RationalIntervalRealSolver.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_algorithm_real_lp_complete {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ x, (rationalIntervalSystem loK hiK lo hi p M r ρ η).RealSatisfies x) :
    ∃ x B, rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B) := by
  apply rational_interval_algorithm_complete loK hiK lo hi p M r ρ η hM hη hlu
  exact (rational_interval_lp_feasible_iff loK hiK lo hi p M r ρ η).mp
    ((rational_linear_real_feasible_iff _).mp hf)

theorem real_interval_completion_algorithm_success {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ)
    (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (hK : IsSkew K) (hKb : ∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ))
    (hD : ∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (p a : ℝ)) q) a ≤ (ρ : ℝ)) :
    ∃ x C, rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,C) := by
  exact rational_interval_algorithm_real_lp_complete loK hiK lo hi p M r ρ η hM hη hlu
    (real_interval_completion_rational_lp loK hiK lo hi p M r ρ η K D q B hM hp hq hr hK hKb hD hB hb hrows)

end SparseCompletion

/- Fixed source body: RationalIntervalPhysical.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def intervalPhysicalEmbed {k m H : ℕ} :
    RationalIntervalVariable k m 0 → RationalIntervalVariable k m H :=
  Sum.elim Sum.inl (Sum.elim (fun v => Sum.inr (Sum.inl v))
    (Sum.elim (fun v => Sum.inr (Sum.inr (Sum.inl v))) (fun v => Fin.elim0 v.1)))

def intervalPhysicalVector {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) : Fin (m+(m*k+(k*k+0*m))) → α :=
  fun j => intervalVariableDecode x (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm j))

def intervalPhysicalForm (k m H : ℕ) (j : Fin (m+(m*k+(k*k+0*m)))) :
    Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm j))

theorem interval_physical_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (j : Fin (m+(m*k+(k*k+0*m)))) :
    rationalFormEval (intervalPhysicalForm k m H j) x=intervalPhysicalVector x j :=
  interval_basis_eval _ x

theorem interval_physical_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (j : Fin (m+(m*k+(k*k+0*m)))) :
    rationalFormRealEval (intervalPhysicalForm k m H j) x=intervalPhysicalVector x j :=
  interval_basis_real_eval _ x

theorem interval_physical_pack {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalPhysicalVector (intervalPack q V K A)=intervalPack q V K (H := 0) Fin.elim0 := by
  funext j
  obtain ⟨v,rfl⟩ := (rationalIntervalVariableEquiv k m 0).surjective j
  change intervalVariableDecode (intervalPack q V K A)
    (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm
      ((rationalIntervalVariableEquiv k m 0) v)))=
    intervalVariableDecode (intervalPack q V K (H := 0) Fin.elim0) v
  refine (congrArg
    (fun w : RationalIntervalVariable k m 0 => intervalVariableDecode (intervalPack q V K A)
      (intervalPhysicalEmbed w))
    ((rationalIntervalVariableEquiv k m 0).symm_apply_apply v)).trans ?_
  rcases v with i | v
  · exact congrFun (interval_pack_q q V K A) i |>.trans
      (congrFun (interval_pack_q q V K (H := 0) Fin.elim0) i).symm
  · rcases v with v | v
    · exact congrFun (congrFun (interval_pack_v q V K A) v.1) v.2 |>.trans
        (congrFun (congrFun (interval_pack_v q V K (H := 0) Fin.elim0) v.1) v.2).symm
    · rcases v with v | v
      · exact congrFun (congrFun (interval_pack_k q V K A) v.1) v.2 |>.trans
          (congrFun (congrFun (interval_pack_k q V K (H := 0) Fin.elim0) v.1) v.2).symm
      · exact Fin.elim0 v.1

end SparseCompletion

/- Fixed source body: RationalIntervalRepertoire.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Declared linear constraints act on physical q,V,K, independently of epigraph auxiliaries. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalIntervalRepertoireSystem {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    RationalLinearSystem (RationalIntervalRows k m (rationalGridSize M r η) ⊕ I)
      (m+(m*k+(k*k+rationalGridSize M r η*m))) where
  coefficient := Sum.elim (rationalIntervalSystem loK hiK lo hi p M r ρ η).coefficient
    (fun row => rationalFormSum (fun j => rationalFormScale (R.coefficient row j)
      (intervalPhysicalForm k m (rationalGridSize M r η) j)))
  rightSide := Sum.elim (rationalIntervalSystem loK hiK lo hi p M r ρ η).rightSide R.rightSide

theorem rational_interval_repertoire_system_iff {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) :
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).Satisfies x ↔
    (rationalIntervalSystem loK hiK lo hi p M r ρ η).Satisfies x ∧
      R.Satisfies (intervalPhysicalVector x) := by
  change (∀ row, rationalFormEval
    ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).coefficient row) x ≤
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).rightSide row) ↔ _
  simp only [rationalIntervalRepertoireSystem,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    rational_form_eval_sum,rational_form_eval_scale,interval_physical_form_eval]
  simp only [RationalLinearSystem.Satisfies,rationalFormEval,Sum.forall]

theorem rational_interval_repertoire_real_system_iff {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℝ) :
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x ↔
    (rationalIntervalSystem loK hiK lo hi p M r ρ η).RealSatisfies x ∧
      R.RealSatisfies (intervalPhysicalVector x) := by
  change (∀ row, rationalFormRealEval
    ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).coefficient row) x ≤
    ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).rightSide row : ℝ)) ↔ _
  simp only [rationalIntervalRepertoireSystem,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    rational_form_real_eval_sum,rational_form_real_eval_scale,interval_physical_real_form_eval]
  simp only [RationalLinearSystem.RealSatisfies,rationalFormRealEval,Sum.forall]

end SparseCompletion

/- Fixed source body: RationalIntervalPhysicalNecessity.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem real_interval_completion_physical_point {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ)
    (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (hK : IsSkew K) (hKb : ∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ))
    (hD : ∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (p a : ℝ)) q) a ≤ (ρ : ℝ)) :
    ∃ A, RationalIntervalRealPoint loK hiK lo hi (fun i a => q i*D i a) K p q M r ρ η A := by
  have hMR : (0 : ℝ)<(M : ℝ) := by exact_mod_cast hM
  have hh := (block_response_bounds_iff K D B (fun a => (p a : ℝ)) q (ρ : ℝ)).mp hrows
  have hc := (weighted_completion_iff q (score D (fun a => (p a : ℝ))) M r ρ
    (le_of_lt hMR) hq hr).mp ⟨B,hB,hb,hh.2⟩
  let V := fun i a => q i*D i a
  let A := fun (l : Fin (rationalGridSize M r η)) i =>
    max ((∑ a, V i a*(p a : ℝ))-
      ((ρ+(M*r-rationalGridNode M r η (l.val+1)) : ℚ) : ℝ)*q i) 0
  have hprod : ∀ i a, q i*D i a=V i a := fun _ _ => rfl
  have hH : ∀ i, q i*score D (fun a => (p a : ℝ)) i=∑ a, V i a*(p a : ℝ) := by
    intro i
    unfold score
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by dsimp only [V]; ring
  have hpoint : RationalIntervalRealPoint loK hiK lo hi V K p q M r ρ η A := by
    refine ⟨hq,hr,?_,hK,hKb,?_,?_,?_,?_⟩
    · intro i a
      exact ⟨mul_le_mul_of_nonneg_right (hD i a).1 (hq i) |>.trans_eq (mul_comm _ _),
        (mul_comm (q i) (D i a)).le.trans (mul_le_mul_of_nonneg_right (hD i a).2 (hq i))⟩
    · intro a
      rw [←anchor_response_of_perspective K D V (fun a => (p a : ℝ)) q hprod a]
      exact hh.1 a
    · intro i
      have hs := score_lower_from_intervals (fun i a => (lo i a : ℝ)) D (fun a => (p a : ℝ))
        (fun a => by exact_mod_cast hp a) (fun i a => (hD i a).1) i
      have ht := le_trans hs (hc.1 i)
      simpa only [←rational_score_real,Rat.cast_add,Rat.cast_mul] using ht
    · intro i
      rw [←hH i]
      have ht := mul_le_mul_of_nonneg_right (hc.1 i) (hq i)
      simpa only [mul_comm (q i),Rat.cast_add,Rat.cast_mul] using ht
    · intro l
      refine ⟨fun i => le_max_right _ _,fun i => le_max_left _ _,?_⟩
      have ht := cuts_imply_call_bound q (fun i => score D (fun a => (p a : ℝ)) i-(ρ : ℝ))
        M r hMR hc.2 ((M*r-rationalGridNode M r η (l.val+1) : ℚ) : ℝ)
      rw [perspective_call_identity q _ _ _ _ hq hH] at ht
      simpa only [perspectiveCall,A,rational_envelope_real,Rat.cast_add] using ht
  exact ⟨A,hpoint⟩

end
end SparseCompletion

/- Fixed source body: RationalIntervalRepertoireSolver.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def rationalIntervalRepertoireAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Option ((Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) × (Fin m → Fin m → ℚ)) :=
  (rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R)).bind
    (fun x => (reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η).map (fun B => (x,B)))

theorem rational_interval_repertoire_algorithm_output {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r ρ η R=some (x,B)) :
    RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
      M r ρ η (intervalAux x) ∧ R.Satisfies (intervalPhysicalVector x) ∧
    reconstructRationalGap (rationalIntervalRecover lo (intervalV x) (intervalQ x))
      p (intervalQ x) M ρ η=some B := by
  unfold rationalIntervalRepertoireAlgorithm at h
  cases hs : rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R) with
  | none => simp only [hs,Option.bind_none] at h; cases h
  | some y =>
    cases hb : reconstructRationalGap (rationalIntervalRecover lo (intervalV y) (intervalQ y))
      p (intervalQ y) M ρ η with
    | none => simp only [hs,Option.bind_some,hb,Option.map_none] at h; cases h
    | some C =>
      have he : (y,C)=(x,B) := Option.some.inj
        (by simpa only [hs,Option.bind_some,hb,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      have hf := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R y).mp
        (rational_lp_solve_sound _ _ y hs)
      exact ⟨(rational_interval_system_point loK hiK lo hi p M r ρ η y).mp hf.1,hf.2,hb⟩

theorem rational_interval_repertoire_algorithm_real_complete {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x) :
    ∃ x B, rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r ρ η R=some (x,B) := by
  obtain ⟨x,hx⟩ := rational_lp_real_complete _ _ hf
  have hp := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp
    (rational_lp_solve_sound _ _ x hx)
  have hpoint := (rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hp.1
  have hg := (rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _ hpoint).2.2
  obtain ⟨B,hB⟩ := rational_interval_gap_rational_completion _ lo hi _ p _ M r ρ η hM hη hlu hg
  exact ⟨x,B,by simp only [rationalIntervalRepertoireAlgorithm,hx,Option.bind_some,hB,Option.map_some]⟩

end SparseCompletion

/- Fixed source body: RationalIntervalRepertoireReal.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
theorem real_interval_repertoire_algorithm_success {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ)
    (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (hK : IsSkew K) (hKb : ∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ))
    (hD : ∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (p a : ℝ)) q) a ≤ (ρ : ℝ))
    (hR : R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)) :
    ∃ x C, rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r ρ η R=some (x,C) := by
  obtain ⟨A,hA⟩ := real_interval_completion_physical_point loK hiK lo hi p M r ρ η
    K D q B hM hp hq hr hK hKb hD hB hb hrows
  apply rational_interval_repertoire_algorithm_real_complete loK hiK lo hi p M r ρ η R hM hη hlu
  refine ⟨intervalPack q (fun i a => q i*D i a) K A,
    (rational_interval_repertoire_real_system_iff loK hiK lo hi p M r ρ η R _).mpr ⟨?_,?_⟩⟩
  · apply (rational_interval_system_real_point loK hiK lo hi p M r ρ η _).mpr
    simpa only [interval_pack_q,interval_pack_v,interval_pack_k,interval_pack_aux] using hA
  · simpa only [interval_physical_pack] using hR

end SparseCompletion

/- Fixed source body: RationalIntervalRepertoireGame.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_repertoire_algorithm_full_game {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hloK : ∀ a b, -M ≤ loK a b) (hhiK : ∀ a b, hiK a b ≤ M)
    (hlo : ∀ i a, -M ≤ lo i a) (hhi : ∀ i a, hi i a ≤ M)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r ρ η R=some (x,B)) :
    R.Satisfies (intervalPhysicalVector x) ∧
    let q := intervalQ x
    let K := intervalK x
    let D := rationalIntervalRecover lo (intervalV x) q
    (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
    (∀ i a, lo i a ≤ D i a ∧ D i a ≤ hi i a) ∧
    (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a) ∧
    (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
    IsSkew (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ)) a b ∧
      blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ)) a b ≤ (M : ℝ)) ∧
    ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  obtain ⟨hpoint,hR,hB⟩ := rational_interval_repertoire_algorithm_output loK hiK lo hi p M r ρ η R x B hout
  refine ⟨hR,?_⟩
  obtain ⟨hK,hKb,hgap⟩ := rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _ hpoint
  obtain ⟨hD,hG⟩ := rational_interval_gap_recovered _ lo hi _ p _ M r ρ η hlu hgap
  refine ⟨hKb,hD,?_⟩
  apply rational_gap_reconstruction_normalized_full_game _ _ p _ M r ρ η hη hp hnorm hK
    (fun a b => ⟨le_trans (hloK a b) (hKb a b).1,le_trans (hKb a b).2 (hhiK a b)⟩)
    (fun i a => ⟨le_trans (hlo i a) (hD i a).1,le_trans (hD i a).2 (hhi i a)⟩)
    ((rational_gap_check_iff _ _ _ _ _ _ _ _).mpr hG) B hB

end SparseCompletion

/- Fixed source body: RationalIntervalPhysicalProjection.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

theorem interval_physical_projection {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) :
    intervalPhysicalVector x=intervalPack (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0 := by
  funext j
  obtain ⟨v,rfl⟩ := (rationalIntervalVariableEquiv k m 0).surjective j
  change intervalVariableDecode x
    (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm
      ((rationalIntervalVariableEquiv k m 0) v)))=
    intervalVariableDecode (intervalPack (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) v
  refine (congrArg
    (fun w : RationalIntervalVariable k m 0 => intervalVariableDecode x
      (intervalPhysicalEmbed w))
    ((rationalIntervalVariableEquiv k m 0).symm_apply_apply v)).trans ?_
  rcases v with i | v
  · exact (congrFun (interval_pack_q (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) i).symm
  · rcases v with v | v
    · exact (congrFun (congrFun (interval_pack_v (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) v.1) v.2).symm
    · rcases v with v | v
      · exact (congrFun (congrFun (interval_pack_k (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) v.1) v.2).symm
      · exact Fin.elim0 v.1

end SparseCompletion

/- Fixed source body: RationalIntervalMonotone.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_perspective_call_antitone {m : ℕ}
    (q H : Fin m → ℚ) (ρ ρ' z : ℚ) (hq : ∀ i, 0 ≤ q i) (hρ : ρ ≤ ρ') :
    rationalPerspectiveCall q H ρ' z ≤ rationalPerspectiveCall q H ρ z := by
  unfold rationalPerspectiveCall
  apply Finset.sum_le_sum
  intro i _
  apply max_le_max _ (le_refl 0)
  have hm := mul_le_mul_of_nonneg_right (add_le_add_right hρ z) (hq i)
  linarith

theorem rational_interval_gap_monotone {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ ρ' η : ℚ) (hρ : ρ ≤ ρ')
    (h : RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    RationalIntervalGapConditions K lo hi V p q M r ρ' η := by
  rcases h with ⟨hq,hm,hV,ha,hlo,hcap,hcall⟩
  refine ⟨hq,hm,hV,fun a => le_trans (ha a) hρ,fun i => by linarith [hlo i],?_,?_⟩
  · intro i
    exact le_trans (hcap i) (mul_le_mul_of_nonneg_right (by linarith) (hq i))
  · intro l
    exact le_trans (rational_perspective_call_antitone q _ ρ ρ' _ hq hρ) (hcall l)

theorem rational_interval_repertoire_feasibility_monotone {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Monotone (fun ρ => ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).Satisfies x) := by
  intro ρ ρ' hρ
  rintro ⟨x,hx⟩
  obtain ⟨hbase,hR⟩ := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp hx
  obtain ⟨hK,hKb,hg⟩ := rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _
    ((rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hbase)
  obtain ⟨A,hA⟩ := (rational_interval_point_epigraph_iff loK hiK lo hi _ _ p _ M r ρ' η).mp
    ⟨hK,hKb,rational_interval_gap_monotone _ lo hi _ p _ M r ρ ρ' η hρ hg⟩
  refine ⟨intervalPack (intervalQ x) (intervalV x) (intervalK x) A,
    (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ' η R _).mpr ⟨?_,?_⟩⟩
  · apply (rational_interval_system_point loK hiK lo hi p M r ρ' η _).mpr
    simpa only [interval_pack_q,interval_pack_v,interval_pack_k,interval_pack_aux] using hA
  · rw [interval_physical_pack]
    simpa only [interval_physical_projection] using hR

end SparseCompletion

/- Fixed source body: RationalIntervalSearch.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def RationalIntervalFeasible {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) : Prop :=
  ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).Satisfies x

instance rationalIntervalFeasibleDecidable {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Decidable (RationalIntervalFeasible loK hiK lo hi p M r ρ η R) :=
  let S := rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R
  (Option.rec (motive := fun o => rationalLPSolve _ S=o →
      Decidable (RationalIntervalFeasible loK hiK lo hi p M r ρ η R))
    (fun he => isFalse ((rational_lp_solve_none_iff _ S).mp he))
    (fun x he => isTrue ⟨x,rational_lp_solve_sound _ S x he⟩)
    (rationalLPSolve _ S)) rfl

def rationalIntervalSearch {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ) : ℚ × ℚ :=
  RationalBisection.search (fun ρ => RationalIntervalFeasible loK hiK lo hi p M r ρ η R) n 0 M

theorem rational_interval_search_bracket {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ)
    (hM : 0 ≤ M) (hupper : RationalIntervalFeasible loK hiK lo hi p M r M η R) :
    let z := rationalIntervalSearch loK hiK lo hi p M r η R n
    0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ M ∧ RationalIntervalFeasible loK hiK lo hi p M r z.2 η R ∧
      (z.1=0 ∨ ¬RationalIntervalFeasible loK hiK lo hi p M r z.1 η R) ∧
      z.2-z.1 ≤ M/((2 : ℕ) : ℚ)^n := by
  simpa only [rationalIntervalSearch,sub_zero] using
    RationalBisection.search_spec (fun ρ => RationalIntervalFeasible loK hiK lo hi p M r ρ η R) n 0 M hM hupper

def rationalIntervalApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ) :
    Option ((ℚ × ℚ) × ((Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) ×
      (Fin m → Fin m → ℚ))) :=
  let z := rationalIntervalSearch loK hiK lo hi p M r η R n
  (rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r z.2 η R).map (fun w => (z,w))

theorem rational_interval_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hupper : RationalIntervalFeasible loK hiK lo hi p M r M η R) :
    ∃ z x B, rationalIntervalApproximation loK hiK lo hi p M r η R n=some (z,(x,B)) := by
  have hz := rational_interval_search_bracket loK hiK lo hi p M r η R n (le_of_lt hM) hupper
  let z := rationalIntervalSearch loK hiK lo hi p M r η R n
  have hf := (rational_linear_real_feasible_iff _).mpr hz.2.2.2.1
  obtain ⟨x,B,hout⟩ := rational_interval_repertoire_algorithm_real_complete loK hiK lo hi p M r z.2 η R hM hη hlu hf
  dsimp only [z] at hout
  exact ⟨rationalIntervalSearch loK hiK lo hi p M r η R n,x,B,by
    simp only [rationalIntervalApproximation,hout,Option.map_some]⟩

end SparseCompletion

/- Fixed source body: RationalIntervalModel.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure RationalIntervalModel (k m : ℕ) (I : Type*) where
  loK : Fin k → Fin k → ℚ
  hiK : Fin k → Fin k → ℚ
  lo : Fin m → Fin k → ℚ
  hi : Fin m → Fin k → ℚ
  p : Fin k → ℚ
  M : ℚ
  r : ℚ
  η : ℚ
  R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))
  positiveBound : 0 < M
  positiveSlack : 0 < η
  anchorNonneg : ∀ a, 0 ≤ p a
  normalized : (∑ a, p a)+r=1
  coreLower : ∀ a b, -M ≤ loK a b
  coreUpper : ∀ a b, hiK a b ≤ M
  crossLower : ∀ i a, -M ≤ lo i a
  crossUpper : ∀ i a, hi i a ≤ M
  orderedCross : ∀ i a, lo i a ≤ hi i a
  compatibleNonempty : ∃ (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
      (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ),
    (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=(r : ℝ) ∧ IsSkew K ∧
    (∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ)) ∧
    (∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ)) ∧
    IsSkew B ∧ (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
    R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)

theorem rational_interval_model_upper_feasible {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) :
    RationalIntervalFeasible d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R := by
  obtain ⟨q,K,D,B,hq,hr,hK,hKb,hD,hB,hBb,hR⟩ := d.compatibleNonempty
  have hpR : ∀ a, 0 ≤ (d.p a : ℝ) := fun a => by exact_mod_cast d.anchorNonneg a
  have hm : (∑ a, blockWeights (fun a => (d.p a : ℝ)) q a)=1 := by
    rw [blockWeights_mass,hr]
    exact_mod_cast d.normalized
  have hKb' : ∀ a b, -(d.M : ℝ) ≤ K a b ∧ K a b ≤ (d.M : ℝ) := by
    intro a b
    exact ⟨le_trans (by exact_mod_cast d.coreLower a b) (hKb a b).1,
      le_trans (hKb a b).2 (by exact_mod_cast d.coreUpper a b)⟩
  have hDb' : ∀ i a, -(d.M : ℝ) ≤ D i a ∧ D i a ≤ (d.M : ℝ) := by
    intro i a
    exact ⟨le_trans (by exact_mod_cast d.crossLower i a) (hD i a).1,
      le_trans (hD i a).2 (by exact_mod_cast d.crossUpper i a)⟩
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (d.p a : ℝ)) q) a ≤ (d.M : ℝ) := by
    intro a
    simpa only [mul_one] using (response_bounds _ _ d.M 1
      (blockWeights_nonneg _ _ hpR hq) hm (blockMatrix_bounds _ _ _ _ hKb' hDb' hBb) a).2
  obtain ⟨x,C,hout⟩ := real_interval_repertoire_algorithm_success d.loK d.hiK d.lo d.hi d.p
    d.M d.r d.M d.η d.R K D q B d.positiveBound d.positiveSlack d.orderedCross
    d.anchorNonneg hq hr hK hKb hD hB hBb hrows hR
  obtain ⟨hpoint,hRx,_⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
    d.p d.M d.r d.M d.η d.R x C hout
  exact ⟨x,(rational_interval_repertoire_system_iff d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R x).mpr
    ⟨(rational_interval_system_point d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η x).mpr hpoint,hRx⟩⟩

theorem rational_interval_model_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) :
    ∃ z x B, rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n=some (z,(x,B)) :=
  rational_interval_approximation_complete d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
    d.positiveBound d.positiveSlack d.orderedCross (rational_interval_model_upper_feasible d)

end SparseCompletion

/- Fixed source body: RationalIntervalClass.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

abbrev IntervalGameData (k m : ℕ) := (Fin m → ℝ) ×
  ((Fin m → Fin k → ℝ) × ((Fin k → Fin k → ℝ) × (Fin m → Fin m → ℝ)))

def intervalGamePhysical {k m : ℕ} (z : IntervalGameData k m) :
    Fin (m+(m*k+(k*k+0*m))) → ℝ :=
  intervalPack z.1 (fun i a => z.1 i*z.2.1 i a) z.2.2.1 (H := 0) Fin.elim0

theorem interval_game_physical_continuous {k m : ℕ}
    (j : Fin (m+(m*k+(k*k+0*m)))) :
    Continuous (fun z : IntervalGameData k m => intervalGamePhysical z j) := by
  unfold intervalGamePhysical intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with i | v
  · dsimp only [Sum.elim_inl]
    fun_prop
  · rcases v with v | v
    · dsimp only [Sum.elim_inr,Sum.elim_inl]
      fun_prop
    · rcases v with v | v
      · dsimp only [Sum.elim_inr,Sum.elim_inl]
        fun_prop
      · exact Fin.elim0 v.1

def intervalGameBox {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I) :
    Set (IntervalGameData k m) :=
  Set.Icc (fun _ => 0) (fun _ => (d.r : ℝ)) ×ˢ
    (Set.Icc (fun i a => (d.lo i a : ℝ)) (fun i a => (d.hi i a : ℝ)) ×ˢ
      (Set.Icc (fun a b => (d.loK a b : ℝ)) (fun a b => (d.hiK a b : ℝ)) ×ˢ skewBox d.M))

def intervalGameClass {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I) :
    Set (IntervalGameData k m) :=
  intervalGameBox d ∩ {z | (∑ i, z.1 i)=(d.r : ℝ) ∧ IsSkew z.2.2.1 ∧
    d.R.RealSatisfies (intervalGamePhysical z)}

theorem interval_game_class_compact {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) : IsCompact (intervalGameClass d) := by
  have hc : IsCompact (intervalGameBox d) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (skewBox_compact d.M)))
  apply hc.inter_right
  have he : {z : IntervalGameData k m | (∑ i, z.1 i)=(d.r : ℝ) ∧ IsSkew z.2.2.1 ∧
      d.R.RealSatisfies (intervalGamePhysical z)}=
    {z | (∑ i, z.1 i)=(d.r : ℝ)} ∩
      ((⋂ a, ⋂ b, {z | z.2.2.1 a b= -z.2.2.1 b a}) ∩
        (⋂ row, {z | (∑ j, (d.R.coefficient row j : ℝ)*intervalGamePhysical z j) ≤ (d.R.rightSide row : ℝ)})) := by
    ext z
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter,IsSkew,RationalLinearSystem.RealSatisfies]
  rw [he]
  exact (isClosed_eq (by fun_prop) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (by fun_prop) (by fun_prop)).inter
      (isClosed_iInter fun row => isClosed_le
        (continuous_finsetSum _ fun j _ => continuous_const.mul (interval_game_physical_continuous j)) continuous_const))

theorem interval_game_class_nonempty {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) : (intervalGameClass d).Nonempty := by
  obtain ⟨q,K,D,B,hq,hr,hK,hKb,hD,hB,hBb,hR⟩ := d.compatibleNonempty
  refine ⟨(q,D,K,B),⟨⟨hq,?_⟩,⟨fun i a => (hD i a).1,fun i a => (hD i a).2⟩,
    ⟨fun a b => (hKb a b).1,fun a b => (hKb a b).2⟩,hB,hBb⟩,hr,hK,hR⟩
  intro i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hq j)
    (Finset.mem_univ i)
  rwa [hr] at hi

end
end SparseCompletion

/- Fixed source body: RationalIntervalValue.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def intervalGameMatrix {k m : ℕ} (z : IntervalGameData k m) :
    (Fin k ⊕ Fin m) → (Fin k ⊕ Fin m) → ℝ := blockMatrix z.2.2.1 z.2.1 z.2.2.2

def intervalGameWeights {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I)
    (z : IntervalGameData k m) : (Fin k ⊕ Fin m) → ℝ :=
  blockWeights (fun a => (d.p a : ℝ)) z.1

def intervalGameExploitability {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) (z : IntervalGameData k m) : ℝ :=
  exploitability (intervalGameMatrix z) (intervalGameWeights d z)

theorem interval_game_exploitability_continuous {k m : ℕ} {I : Type*}
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) :
    Continuous (intervalGameExploitability d) := by
  unfold intervalGameExploitability intervalGameMatrix intervalGameWeights exploitability
  apply Continuous.finset_sup'_apply
  intro a _
  cases a with
  | inl a =>
    simp only [block_response_anchor,anchorResponse]
    fun_prop
  | inr i =>
    simp only [response,Fintype.sum_sum_type,blockMatrix,blockWeights,Sum.elim_inl,Sum.elim_inr]
    fun_prop

def intervalGameValue {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) : ℝ :=
  sInf (intervalGameExploitability d '' intervalGameClass d)

theorem interval_game_value_attained {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) :
    ∃ z ∈ intervalGameClass d, intervalGameExploitability d z=intervalGameValue d := by
  have hc := (interval_game_class_compact d).image (interval_game_exploitability_continuous d)
  have hn := (interval_game_class_nonempty d).image (intervalGameExploitability d)
  obtain ⟨z,hz,he⟩ := hc.sInf_mem hn
  exact ⟨z,hz,he⟩

theorem interval_game_value_le_witness {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) (z : IntervalGameData k m) (hz : z ∈ intervalGameClass d) :
    intervalGameValue d ≤ intervalGameExploitability d z := by
  apply csInf_le ((interval_game_class_compact d).image
    (interval_game_exploitability_continuous d)).bddBelow
  exact ⟨z,hz,rfl⟩

theorem interval_game_class_game_facts {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) (z : IntervalGameData k m) (hz : z ∈ intervalGameClass d) :
    (∀ a, 0 ≤ intervalGameWeights d z a) ∧ (∑ a, intervalGameWeights d z a)=1 ∧
    IsSkew (intervalGameMatrix z) ∧
    (∀ a b, -(d.M : ℝ) ≤ intervalGameMatrix z a b ∧ intervalGameMatrix z a b ≤ (d.M : ℝ)) := by
  rcases hz with ⟨⟨⟨hq,_⟩,⟨hDl,hDu⟩,⟨hKl,hKu⟩,hB,hBb⟩,hm,hK,_⟩
  have hKb : ∀ a b, -(d.M : ℝ) ≤ z.2.2.1 a b ∧ z.2.2.1 a b ≤ (d.M : ℝ) := by
    intro a b
    exact ⟨le_trans (by change -(d.M : ℝ) ≤ (d.loK a b : ℝ); exact_mod_cast d.coreLower a b) (hKl a b),
      le_trans (hKu a b) (by change (d.hiK a b : ℝ) ≤ (d.M : ℝ); exact_mod_cast d.coreUpper a b)⟩
  have hDb : ∀ i a, -(d.M : ℝ) ≤ z.2.1 i a ∧ z.2.1 i a ≤ (d.M : ℝ) := by
    intro i a
    exact ⟨le_trans (by change -(d.M : ℝ) ≤ (d.lo i a : ℝ); exact_mod_cast d.crossLower i a) (hDl i a),
      le_trans (hDu i a) (by change (d.hi i a : ℝ) ≤ (d.M : ℝ); exact_mod_cast d.crossUpper i a)⟩
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast d.anchorNonneg a) hq,?_,
    blockMatrix_skew _ _ _ hK hB,blockMatrix_bounds _ _ _ _ hKb hDb hBb⟩
  change (∑ a, blockWeights (fun a => (d.p a : ℝ)) z.1 a)=1
  rw [blockWeights_mass,hm]
  exact_mod_cast d.normalized

theorem interval_game_value_bounds {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) : 0 ≤ intervalGameValue d ∧ intervalGameValue d ≤ (d.M : ℝ) := by
  obtain ⟨z,hz,he⟩ := interval_game_value_attained d
  obtain ⟨hq,hm,hK,hb⟩ := interval_game_class_game_facts d z hz
  rw [←he]
  exact ⟨exploitability_nonnegative _ _ hK hq hm,
    exploitability_bounded_above _ _ _ (fun a b => (hb a b).2) hq hm⟩

end
end SparseCompletion

/- Fixed source body: RationalIntervalOutputClass.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def rationalIntervalOutputData {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ) : IntervalGameData k m :=
  (fun i => (intervalQ (α := ℚ) x i : ℝ),
    fun i a => (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ),
    fun a b => (intervalK (α := ℚ) x a b : ℝ),fun i j => (B i j : ℝ))

theorem rational_interval_output_physical {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hV : ∀ i a, d.lo i a*intervalQ (α := ℚ) x i ≤ intervalV (α := ℚ) x i a ∧
      intervalV (α := ℚ) x i a ≤ d.hi i a*intervalQ (α := ℚ) x i) :
    intervalGamePhysical (rationalIntervalOutputData d x B)=
      fun j => (intervalPhysicalVector (α := ℚ) x j : ℝ) := by
  have hprod := rational_interval_recovered_product d.lo d.hi (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) hV
  funext j
  simp only [interval_physical_projection]
  unfold intervalGamePhysical intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with i | v
  · rfl
  · rcases v with v | v
    · change (intervalQ (α := ℚ) x v.1 : ℝ)*
        (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) v.1 v.2 : ℝ)=(intervalV (α := ℚ) x v.1 v.2 : ℝ)
      exact_mod_cast hprod v.1 v.2
    · rcases v with v | v
      · rfl
      · exact Fin.elim0 v.1

theorem rational_interval_algorithm_output_class {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ρ : ℚ)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r ρ d.η d.R=some (x,B)) :
    rationalIntervalOutputData d x B ∈ intervalGameClass d := by
  obtain ⟨hpoint,hR,hB⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
    d.p d.M d.r ρ d.η d.R x B hout
  have hsave := hpoint
  obtain ⟨hq,hm,hV,hK,hKb,_⟩ := hsave
  have hD := (rational_interval_gap_recovered _ d.lo d.hi _ d.p _ d.M d.r ρ d.η d.orderedCross
    (rational_interval_point_gap d.loK d.hiK d.lo d.hi _ _ d.p _ d.M d.r ρ d.η _ hpoint).2.2).1
  have hbR := rational_residual_completion_real_sound (intervalQ (α := ℚ) x)
    (rationalScore (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x)) d.p) d.M (ρ+d.η) B hB
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,hbR.1,hbR.2.1⟩,?_,?_,?_⟩
  · intro i
    change (0 : ℝ) ≤ (intervalQ (α := ℚ) x i : ℝ)
    exact_mod_cast hq i
  · intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hq j)
      (Finset.mem_univ i)
    rw [hm] at hi
    change (intervalQ (α := ℚ) x i : ℝ) ≤ (d.r : ℝ)
    exact_mod_cast hi
  · intro i a
    change (d.lo i a : ℝ) ≤ (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ)
    exact_mod_cast (hD i a).1
  · intro i a
    change (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ) ≤ (d.hi i a : ℝ)
    exact_mod_cast (hD i a).2
  · intro a b
    change (d.loK a b : ℝ) ≤ (intervalK (α := ℚ) x a b : ℝ)
    exact_mod_cast (hKb a b).1
  · intro a b
    change (intervalK (α := ℚ) x a b : ℝ) ≤ (d.hiK a b : ℝ)
    exact_mod_cast (hKb a b).2
  · change (∑ i, (intervalQ (α := ℚ) x i : ℝ))=(d.r : ℝ)
    exact_mod_cast hm
  · intro a b
    change (intervalK (α := ℚ) x a b : ℝ)= -(intervalK (α := ℚ) x b a : ℝ)
    exact_mod_cast hK a b
  · rw [rational_interval_output_physical d x B hV]
    exact (rational_linear_real_cast_iff d.R _).mpr hR

end
end SparseCompletion

/- Fixed source body: RationalIntervalValueCertificate.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

theorem rational_interval_approximation_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n=some (z,(x,B))) :
    z=rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n ∧
    rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r z.2 d.η d.R=some (x,B) := by
  cases ha : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r
    (rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n).2 d.η d.R with
  | none => simp only [rationalIntervalApproximation,ha,Option.map_none] at h; cases h
  | some w =>
    have he := Option.some.inj (by simpa only [rationalIntervalApproximation,ha,Option.map_some] using h)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨rfl,ha⟩

theorem rational_interval_approximation_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ) (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n=some (z,(x,B))) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      z.2-z.1 ≤ d.M/((2 : ℕ) : ℚ)^n := by
  obtain ⟨hz,ha⟩ := rational_interval_approximation_output d n z x B hout
  have hbr := rational_interval_search_bracket d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_interval_model_upper_feasible d)
  rw [←hz] at hbr
  have hclass := rational_interval_algorithm_output_class d z.2 x B ha
  have hfull := rational_interval_repertoire_algorithm_full_game d.loK d.hiK d.lo d.hi d.p
    d.M d.r z.2 d.η d.R d.positiveSlack d.anchorNonneg d.normalized d.coreLower d.coreUpper
    d.crossLower d.crossUpper d.orderedCross x B ha
  rcases hfull with ⟨_,_,_,_,_,_,_,hrows⟩
  have hu : intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) := by
    apply le_trans (interval_game_value_le_witness d _ hclass)
    apply (exploitability_le_iff _ _ _).mpr
    exact hrows
  refine ⟨?_,hu,hbr.2.2.2.2.2⟩
  rcases hbr.2.2.2.2.1 with hzero | hno
  · rw [hzero,Rat.cast_zero]
    exact (interval_game_value_bounds d).1
  · by_contra hlow
    have hvL : intervalGameValue d ≤ (z.1 : ℝ) := le_of_lt (lt_of_not_ge hlow)
    obtain ⟨w,hw,he⟩ := interval_game_value_attained d
    rcases hw with ⟨⟨⟨hq,_⟩,⟨hDl,hDu⟩,⟨hKl,hKu⟩,hB,hBb⟩,hm,hK,hR⟩
    have hr : ∀ a, response (blockMatrix w.2.2.1 w.2.1 w.2.2.2)
        (blockWeights (fun a => (d.p a : ℝ)) w.1) a ≤ (z.1 : ℝ) := by
      intro a
      exact le_trans (response_le_exploitability _ _ a) (le_trans he.le hvL)
    obtain ⟨y,C,hC⟩ := real_interval_repertoire_algorithm_success d.loK d.hiK d.lo d.hi d.p
      d.M d.r z.1 d.η d.R w.2.2.1 w.2.1 w.1 w.2.2.2 d.positiveBound d.positiveSlack
      d.orderedCross d.anchorNonneg hq hm hK (fun a b => ⟨hKl a b,hKu a b⟩)
      (fun i a => ⟨hDl i a,hDu i a⟩) hB hBb hr hR
    obtain ⟨hpoint,hRy,_⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
      d.p d.M d.r z.1 d.η d.R y C hC
    exact hno ⟨y,(rational_interval_repertoire_system_iff d.loK d.hiK d.lo d.hi d.p d.M d.r z.1 d.η d.R y).mpr
      ⟨(rational_interval_system_point d.loK d.hiK d.lo d.hi d.p d.M d.r z.1 d.η y).mpr hpoint,hRy⟩⟩

end SparseCompletion

/- Fixed source body: RationalIntervalAccurate.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def rationalIntervalAccurateApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :=
  rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R (rationalLogRounds d.M ζ)

theorem rational_interval_accurate_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :
    ∃ z x B, rationalIntervalAccurateApproximation d ζ=some (z,(x,B)) :=
  rational_interval_model_approximation_complete d (rationalLogRounds d.M ζ)

theorem rational_interval_accurate_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ) (hout : rationalIntervalAccurateApproximation d ζ=some (z,(x,B))) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  have hb := rational_interval_approximation_value_enclosure d (rationalLogRounds d.M ζ) z x B hout
  have hw : z.2-z.1 < ζ := lt_of_le_of_lt hb.2.2 (rational_log_rounds_width d.M ζ hζ)
  have hwR : (z.2 : ℝ)-(z.1 : ℝ) < (ζ : ℝ) := by exact_mod_cast hw
  exact ⟨hb.1,hb.2.1,by linarith⟩

end SparseCompletion

/- Fixed source body: RationalIntervalParameters.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
structure RationalIntervalParameters (k m : ℕ) (I : Type*) where
  loK : Fin k → Fin k → ℚ
  hiK : Fin k → Fin k → ℚ
  lo : Fin m → Fin k → ℚ
  hi : Fin m → Fin k → ℚ
  p : Fin k → ℚ
  M : ℚ
  r : ℚ
  η : ℚ
  R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))
  positiveBound : 0 < M
  positiveSlack : 0 < η
  anchorNonneg : ∀ a, 0 ≤ p a
  normalized : (∑ a, p a)+r=1
  coreLower : ∀ a b, -M ≤ loK a b
  coreUpper : ∀ a b, hiK a b ≤ M
  crossLower : ∀ i a, -M ≤ lo i a
  crossUpper : ∀ i a, hi i a ≤ M
  orderedCross : ∀ i a, lo i a ≤ hi i a

def RationalIntervalParameters.Compatible {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) : Prop :=
  ∃ (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
      (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ),
    (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=(d.r : ℝ) ∧ IsSkew K ∧
    (∀ a b, (d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ)) ∧
    (∀ i a, (d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ)) ∧
    IsSkew B ∧ (∀ i j, -(d.M : ℝ) ≤ B i j ∧ B i j ≤ (d.M : ℝ)) ∧
    d.R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)

def RationalIntervalParameters.toModel {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (h : d.Compatible) : RationalIntervalModel k m I where
  loK := d.loK
  hiK := d.hiK
  lo := d.lo
  hi := d.hi
  p := d.p
  M := d.M
  r := d.r
  η := d.η
  R := d.R
  positiveBound := d.positiveBound
  positiveSlack := d.positiveSlack
  anchorNonneg := d.anchorNonneg
  normalized := d.normalized
  coreLower := d.coreLower
  coreUpper := d.coreUpper
  crossLower := d.crossLower
  crossUpper := d.crossUpper
  orderedCross := d.orderedCross
  compatibleNonempty := h

end SparseCompletion

/- Fixed source body: RationalIntervalConsistency.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem interval_pack_recovered_real {k m : ℕ} (lo hi V : Fin m → Fin k → ℚ)
    (K : Fin k → Fin k → ℚ) (q : Fin m → ℚ)
    (hV : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) :
    intervalPack (fun i => (q i : ℝ))
      (fun i a => (q i : ℝ)*(rationalIntervalRecover lo V q i a : ℝ))
      (fun a b => (K a b : ℝ)) (H := 0) Fin.elim0=
    fun j => (intervalPack (α := ℚ) q V K (H := 0) Fin.elim0 j : ℝ) := by
  have hprod := rational_interval_recovered_product lo hi V q hV
  funext j
  unfold intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with i | v
  · rfl
  · rcases v with v | v
    · change (q v.1 : ℝ)*(rationalIntervalRecover lo V q v.1 v.2 : ℝ)=(V v.1 v.2 : ℝ)
      exact_mod_cast hprod v.1 v.2
    · rcases v with v | v
      · rfl
      · exact Fin.elim0 v.1

theorem rational_interval_success_compatible {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R=some (x,B)) :
    d.Compatible := by
  obtain ⟨hpoint,hR,hB⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
    d.p d.M d.r d.M d.η d.R x B hout
  have hsave := hpoint
  obtain ⟨hq,hm,hV,hK,hKb,_⟩ := hsave
  have hD := (rational_interval_gap_recovered _ d.lo d.hi _ d.p _ d.M d.r d.M d.η d.orderedCross
    (rational_interval_point_gap d.loK d.hiK d.lo d.hi _ _ d.p _ d.M d.r d.M d.η _ hpoint).2.2).1
  have hbR := rational_residual_completion_real_sound (intervalQ (α := ℚ) x)
    (rationalScore (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x)) d.p) d.M (d.M+d.η) B hB
  refine ⟨(fun i => (intervalQ (α := ℚ) x i : ℝ)),(fun a b => (intervalK (α := ℚ) x a b : ℝ)),
    (fun i a => (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ)),
    (fun i j => (B i j : ℝ)),?_,?_,?_,?_,?_,hbR.1,hbR.2.1,?_⟩
  · intro i
    change (0 : ℝ) ≤ (intervalQ (α := ℚ) x i : ℝ)
    exact_mod_cast hq i
  · change (∑ i, (intervalQ (α := ℚ) x i : ℝ))=(d.r : ℝ)
    exact_mod_cast hm
  · intro a b
    change (intervalK (α := ℚ) x a b : ℝ)= -(intervalK (α := ℚ) x b a : ℝ)
    exact_mod_cast hK a b
  · intro a b
    change (d.loK a b : ℝ) ≤ (intervalK (α := ℚ) x a b : ℝ) ∧
      (intervalK (α := ℚ) x a b : ℝ) ≤ (d.hiK a b : ℝ)
    exact_mod_cast hKb a b
  · intro i a
    change (d.lo i a : ℝ) ≤ (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ) ∧
      (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ) ≤ (d.hi i a : ℝ)
    exact_mod_cast hD i a
  · rw [interval_pack_recovered_real d.lo d.hi (intervalV (α := ℚ) x) (intervalK (α := ℚ) x) (intervalQ (α := ℚ) x) hV]
    have hr := (rational_linear_real_cast_iff d.R (intervalPhysicalVector (α := ℚ) x)).mpr hR
    simpa only [interval_physical_projection] using hr

theorem rational_interval_compatible_success {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (h : d.Compatible) :
    ∃ x B, rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R=some (x,B) := by
  let model := d.toModel h
  have hf := rational_interval_model_upper_feasible model
  apply rational_interval_repertoire_algorithm_real_complete d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R
    d.positiveBound d.positiveSlack d.orderedCross
  exact (rational_linear_real_feasible_iff _).mpr hf

end SparseCompletion

/- Fixed source body: RationalIntervalInitialize.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Physical consistency is computed by the verified rational program, not arbitrary Real comparison. -/
@[expose] public section
namespace SparseCompletion

theorem rational_interval_algorithm_none_incompatible {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I)
    (h : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R=none) :
    ¬d.Compatible := by
  intro hc
  obtain ⟨x,B,hout⟩ := rational_interval_compatible_success d hc
  rw [h] at hout
  cases hout

instance rationalIntervalCompatibilityDecidable {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) : Decidable d.Compatible :=
  (Option.rec
    (motive := fun o => rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p
      d.M d.r d.M d.η d.R=o → Decidable d.Compatible)
    (fun he => isFalse (rational_interval_algorithm_none_incompatible d he))
    (fun w he => isTrue (rational_interval_success_compatible d w.1 w.2 he))
    (rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R)) rfl

def rationalIntervalInitialize {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) : Option (RationalIntervalModel k m I) :=
  dite d.Compatible (fun hc => some (d.toModel hc)) (fun _ => none)

theorem rational_interval_initialize_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (h : d.Compatible) :
    rationalIntervalInitialize d=some (d.toModel h) := by
  simp only [rationalIntervalInitialize,dite_eq_left h]

theorem rational_interval_initialize_sound {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (model : RationalIntervalModel k m I)
    (h : rationalIntervalInitialize d=some model) :
    ∃ hc : d.Compatible, model=d.toModel hc := by
  by_cases hc : d.Compatible
  · exact ⟨hc,(Option.some.inj (by simpa only [rationalIntervalInitialize,dite_eq_left hc] using h)).symm⟩
  · simp only [rationalIntervalInitialize,dite_eq_right hc] at h
    cases h

theorem rational_interval_initialize_none_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) : rationalIntervalInitialize d=none ↔ ¬d.Compatible := by
  by_cases hc : d.Compatible <;> simp only [rationalIntervalInitialize,hc,dite_eq_left,dite_eq_right,
    Option.some_ne_none,not_true_eq_false,not_false_eq_true]

end SparseCompletion

/- Fixed source body: RationalIntervalInitializedAlgorithm.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

structure RationalIntervalRationalOutput (k m : ℕ) where
  bracket : ℚ × ℚ
  q : Fin m → ℚ
  K : Fin k → Fin k → ℚ
  D : Fin m → Fin k → ℚ
  B : Fin m → Fin m → ℚ

def rationalIntervalPackOutput {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I)
    (w : (ℚ × ℚ) × ((Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ) ×
      (Fin m → Fin m → ℚ))) : RationalIntervalRationalOutput k m where
  bracket := w.1
  q := intervalQ w.2.1
  K := intervalK w.2.1
  D := rationalIntervalRecover d.lo (intervalV w.2.1) (intervalQ w.2.1)
  B := w.2.2

def rationalIntervalInitializedApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) : Option (RationalIntervalRationalOutput k m) :=
  (rationalIntervalInitialize d).bind (fun model =>
    (rationalIntervalAccurateApproximation model ζ).map (rationalIntervalPackOutput model))

theorem rational_interval_initialized_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o) :
    ∃ model, rationalIntervalInitialize d=some model ∧
      ∃ z x B, rationalIntervalAccurateApproximation model ζ=some (z,(x,B)) ∧
        o=rationalIntervalPackOutput model (z,(x,B)) := by
  cases hm : rationalIntervalInitialize d with
  | none => simp only [rationalIntervalInitializedApproximation,hm,Option.bind_none] at hout; cases hout
  | some model =>
    cases ha : rationalIntervalAccurateApproximation model ζ with
    | none => simp only [rationalIntervalInitializedApproximation,hm,Option.bind_some,ha,Option.map_none] at hout; cases hout
    | some w =>
      have he : rationalIntervalPackOutput model w=o := Option.some.inj
        (by simpa only [rationalIntervalInitializedApproximation,hm,Option.bind_some,ha,Option.map_some] using hout)
      exact ⟨model,rfl,w.1,w.2.1,w.2.2,ha,he.symm⟩

theorem rational_interval_initialized_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (hc : d.Compatible) :
    ∃ o, rationalIntervalInitializedApproximation d ζ=some o := by
  obtain ⟨z,x,B,hout⟩ := rational_interval_accurate_complete (d.toModel hc) ζ
  exact ⟨rationalIntervalPackOutput (d.toModel hc) (z,(x,B)),by
    simp only [rationalIntervalInitializedApproximation,rational_interval_initialize_complete d hc,
      Option.bind_some,hout,Option.map_some]⟩

theorem rational_interval_initialized_none_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) :
    rationalIntervalInitializedApproximation d ζ=none ↔ ¬d.Compatible := by
  constructor
  · intro hn hc
    obtain ⟨o,ho⟩ := rational_interval_initialized_complete d ζ hc
    rw [hn] at ho
    cases ho
  · intro hn
    have hi := (rational_interval_initialize_none_iff d).mpr hn
    simp only [rationalIntervalInitializedApproximation,hi,Option.bind_none]

end SparseCompletion

/- Fixed source body: RationalIntervalInitializedSoundness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

def RationalIntervalRationalOutput.realData {k m : ℕ} (o : RationalIntervalRationalOutput k m) :
    IntervalGameData k m :=
  (fun i => (o.q i : ℝ),fun i a => (o.D i a : ℝ),
    fun a b => (o.K a b : ℝ),fun i j => (o.B i j : ℝ))

theorem rational_interval_initialized_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o) :
    ∃ hc : d.Compatible,
      o.realData ∈ intervalGameClass (d.toModel hc) ∧
      ∀ a, response (intervalGameMatrix o.realData) (intervalGameWeights (d.toModel hc) o.realData) a ≤
        (o.bracket.2 : ℝ)+(d.η : ℝ) := by
  obtain ⟨model,hm,z,x,B,ha,rfl⟩ := rational_interval_initialized_output d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  have hAlg := (rational_interval_approximation_output (d.toModel hc)
    (rationalLogRounds d.M ζ) z x B ha).2
  have hClass := rational_interval_algorithm_output_class (d.toModel hc) z.2 x B hAlg
  have hGame := rational_interval_repertoire_algorithm_full_game d.loK d.hiK d.lo d.hi d.p
    d.M d.r z.2 d.η d.R d.positiveSlack d.anchorNonneg d.normalized d.coreLower d.coreUpper
    d.crossLower d.crossUpper d.orderedCross x B hAlg
  rcases hGame with ⟨_,_,_,_,_,_,_,hrows⟩
  exact ⟨hc,hClass,hrows⟩

theorem rational_interval_initialized_value {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalParameters k m I)
    (ζ : ℚ) (hζ : 0 < ζ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o) :
    ∃ hc : d.Compatible,
      (o.bracket.1 : ℝ) ≤ intervalGameValue (d.toModel hc) ∧
      intervalGameValue (d.toModel hc) ≤ (o.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (o.bracket.2 : ℝ)+(d.η : ℝ)-(o.bracket.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  obtain ⟨model,hm,z,x,B,ha,rfl⟩ := rational_interval_initialized_output d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  exact ⟨hc,rational_interval_accurate_value_enclosure (d.toModel hc) ζ hζ z x B ha⟩

end
end SparseCompletion

/- Fixed source body: AllocationReservoir.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def reservoirRounded {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) : α → ℝ :=
  transferredResidual (roundedAllocation s p δ) (removedAnchorMass s p δ) j

theorem reservoir_rounded_mass {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) :
    (∑ i, reservoirRounded s p δ j i) = ∑ i, p i := by
  rw [reservoirRounded, transferred_residual_mass]
  unfold removedAnchorMass
  rw [Finset.sum_sub_distrib]
  ring

theorem reservoir_rounded_floors {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    ∀ i, s i ≤ reservoirRounded s p δ j i := by
  intro i
  apply le_trans (rounded_anchor_bounds _ _ _ (hsp i) hδ).1
  apply le_add_of_nonneg_right
  split_ifs
  · exact (removed_anchor_mass_bounds s p δ hsp hδ).1
  · exact le_refl 0

theorem reservoir_rounded_distance {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    (∑ i, |p i-reservoirRounded s p δ j i|) ≤ (2 : ℕ)*(Fintype.card α : ℝ)*δ := by
  have hd := removed_anchor_mass_bounds s p δ hsp hδ
  have ha : (∑ i, |p i-roundedAllocation s p δ i|)=removedAnchorMass s p δ := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (sub_nonneg.mpr (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.1)
  calc
    (∑ i, |p i-reservoirRounded s p δ j i|) ≤
        ∑ i, (|p i-roundedAllocation s p δ i|+
          |roundedAllocation s p δ i-reservoirRounded s p δ j i|) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_sub_le _ _ _
    _ = removedAnchorMass s p δ+removedAnchorMass s p δ := by
      rw [Finset.sum_add_distrib,ha]
      rw [reservoirRounded,transferred_residual_distance _ _ j hd.1]
    _ ≤ _ := by norm_num only [Nat.cast_ofNat]; linarith

def reservoirGridAllocation {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (δ : ℝ) (j : α) (z : α → Fin (1+Nat.floor (1/δ))) : α → ℝ :=
  transferredResidual (fun i => s i+δ*(z i : ℕ))
    (1-∑ i, (s i+δ*(z i : ℕ))) j

theorem reservoir_grid_mass {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (δ : ℝ) (j : α) (z : α → Fin (1+Nat.floor (1/δ))) :
    (∑ i, reservoirGridAllocation s δ j z i)=1 := by
  rw [reservoirGridAllocation,transferred_residual_mass]
  ring

theorem reservoir_rounded_finite_grid {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) (hs : ∀ i, 0 ≤ s i)
    (hp : p ∈ floorStrategies s) (hδ : 0 < δ) :
    ∃ z : α → Fin (1+Nat.floor (1/δ)), reservoirRounded s p δ j=reservoirGridAllocation s δ j z := by
  obtain ⟨z,hz⟩ := rounded_allocation_finite_grid s p δ hs
    (fun i => (floor_strategy_coordinate_bounds s p hs hp i).2) hδ
  have he : roundedAllocation s p δ=(fun i => s i+δ*(z i : ℕ)) := funext hz
  have hm : removedAnchorMass s p δ=1-∑ i, (s i+δ*(z i : ℕ)) := by
    unfold removedAnchorMass
    rw [Finset.sum_sub_distrib,hp.2,he]
  exact ⟨z,by rw [reservoirRounded,reservoirGridAllocation,he,hm]⟩

end
end SparseCompletion

/- Fixed source body: AllocationReservoirValue.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem reservoir_rounding_in_floor_strategies {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) (hp : p ∈ floorStrategies s) (hδ : 0 < δ) :
    reservoirRounded s p δ j ∈ floorStrategies s :=
  ⟨reservoir_rounded_floors s p δ j hp.1 hδ,(reservoir_rounded_mass s p δ j).trans hp.2⟩

theorem reservoir_rounding_value_bound {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s p : α → ℝ) (δ M : ℝ) (j : α) (A : α → α → ℝ)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i l, |A i l| ≤ M) :
    exploitability A (reservoirRounded s p δ j) ≤
      exploitability A p+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  have h := (abs_le.mp (exploitability_strategy_distance A p
    (reservoirRounded s p δ j) M hA)).1
  have hd := mul_le_mul_of_nonneg_left (reservoir_rounded_distance s p δ j hsp hδ) hM
  norm_num only [Nat.cast_ofNat] at hd ⊢
  nlinarith

theorem reservoir_grid_approximation {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s p : α → ℝ) (δ M : ℝ) (j : α) (A : α → α → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hp : p ∈ floorStrategies s) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i l, |A i l| ≤ M) :
    ∃ z : α → Fin (1+Nat.floor (1/δ)),
      reservoirGridAllocation s δ j z ∈ floorStrategies s ∧
      exploitability A (reservoirGridAllocation s δ j z) ≤
        exploitability A p+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  obtain ⟨z,hz⟩ := reservoir_rounded_finite_grid s p δ j hs hp hδ
  exact ⟨z,hz ▸ reservoir_rounding_in_floor_strategies s p δ j hp hδ,
    hz ▸ reservoir_rounding_value_bound s p δ M j A hp.1 hδ hM hA⟩

end
end SparseCompletion

/- Fixed source body: RationalFiniteSelection.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def rationalFiniteSelect {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) : Option β :=
  (candidates.filterMap run).argmin score

theorem rational_finite_select_origin {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) (o : β)
    (hout : rationalFiniteSelect candidates run score=some o) :
    ∃ a ∈ candidates, run a=some o := by
  have hm : o ∈ (candidates.filterMap run).argmin score := hout
  exact List.mem_filterMap.mp (List.argmin_mem hm)

theorem rational_finite_select_minimal {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) (o : β)
    (hout : rationalFiniteSelect candidates run score=some o)
    (a : α) (ha : a ∈ candidates) (b : β) (hb : run a=some b) : score o ≤ score b := by
  have hm : o ∈ (candidates.filterMap run).argmin score := hout
  exact List.le_of_mem_argmin (List.mem_filterMap.mpr ⟨a,ha,hb⟩) hm

theorem rational_finite_select_none_iff {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) :
    rationalFiniteSelect candidates run score=none ↔ ∀ a ∈ candidates, run a=none := by
  rw [rationalFiniteSelect,List.argmin_eq_none]
  constructor
  · intro he a ha
    cases hr : run a with
    | none => rfl
    | some b =>
      have hm : b ∈ candidates.filterMap run := List.mem_filterMap.mpr ⟨a,ha,hr⟩
      rw [he] at hm
      cases hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro b hb
    obtain ⟨a,ha,hb⟩ := List.mem_filterMap.mp hb
    rw [h a ha] at hb
    cases hb

end SparseCompletion

/- Fixed source body: RationalAllocationGrid.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
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

/- Fixed source body: RationalAllocationRun.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalParameters.withAllocation {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (p : Fin k → ℚ) (hp : ∀ a, 0 ≤ p a) :
    RationalIntervalParameters k m I :=
  {d with p := p, r := 1-∑ a,p a, anchorNonneg := hp, normalized := by ring}

def rationalAllocationRun {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if h : ∀ a, s a ≤ p a then
    (rationalIntervalInitializedApproximation
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ).map (fun o => (p,o))
  else none

theorem rational_allocation_run_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationRun d s hs ζ p=some w) :
    ∃ h : ∀ a,s a ≤ p a,
      rationalIntervalInitializedApproximation
        (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ=some w.2 ∧ w.1=p := by
  by_cases h : ∀ a,s a ≤ p a
  · simp only [rationalAllocationRun,dite_eq_left h] at hout
    cases ho : rationalIntervalInitializedApproximation
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ with
    | none => simp only [ho,Option.map_none] at hout; cases hout
    | some o =>
      rw [ho,Option.map_some] at hout
      have he := Option.some.inj hout
      subst w
      exact ⟨h,ho,rfl⟩
  · simp only [rationalAllocationRun,dite_eq_right h] at hout
    cases hout

def rationalAllocationSearch {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  rationalFiniteSelect (rationalAllocationNodes k δ)
    (fun z => rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z))
    (fun w => w.2.bracket.2)

def rationalReservoirSearch {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (j : Fin k) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  rationalFiniteSelect (rationalAllocationNodes k δ)
    (fun z => rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z))
    (fun w => w.2.bracket.2)

theorem rational_allocation_search_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationSearch d s hs δ ζ=some w) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z)=some w := by
  obtain ⟨z,_,hz⟩ := rational_finite_select_origin _ _ _ w hout
  exact ⟨z,hz⟩

theorem rational_reservoir_search_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (j : Fin k) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalReservoirSearch d s hs δ ζ j=some w) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z)=some w := by
  obtain ⟨z,_,hz⟩ := rational_finite_select_origin _ _ _ w hout
  exact ⟨z,hz⟩

end SparseCompletion

/- Fixed source body: RationalAllocationSearchSoundness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_allocation_run_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationRun d s hs ζ p=some w) :
    ∃ h : ∀ a,s a ≤ w.1 a,
      ∃ hc : (d.withAllocation w.1 (fun a => le_trans (hs a) (h a))).Compatible,
        w.2.realData ∈ intervalGameClass
          ((d.withAllocation w.1 (fun a => le_trans (hs a) (h a))).toModel hc) ∧
        ∀ a, response (intervalGameMatrix w.2.realData)
          (intervalGameWeights ((d.withAllocation w.1
            (fun a => le_trans (hs a) (h a))).toModel hc) w.2.realData) a ≤
              (w.2.bracket.2 : ℝ)+(d.η : ℝ) := by
  obtain ⟨h,ho,hp⟩ := rational_allocation_run_output d s hs ζ p w hout
  rw [hp]
  obtain ⟨hc,hg,hr⟩ := rational_interval_initialized_game
    (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ w.2 ho
  exact ⟨h,hc,hg,hr⟩

theorem rational_allocation_search_minimal {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationSearch d s hs δ ζ=some w)
    (z : Fin k → Fin (1+Nat.floor (1/δ)))
    (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z)=some v) :
    w.2.bracket.2 ≤ v.2.bracket.2 :=
  rational_finite_select_minimal _ _ _ w hout z
    (rational_allocation_nodes_complete k δ z) v hv

theorem rational_reservoir_search_minimal {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (j : Fin k) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalReservoirSearch d s hs δ ζ j=some w)
    (z : Fin k → Fin (1+Nat.floor (1/δ)))
    (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z)=some v) :
    w.2.bracket.2 ≤ v.2.bracket.2 :=
  rational_finite_select_minimal _ _ _ w hout z
    (rational_allocation_nodes_complete k δ z) v hv

end
end SparseCompletion

/- Fixed source body: RationalReservoirApproximation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_reservoir_grid_approximation {k : ℕ} [Nonempty (Fin k)]
    (s : Fin k → ℚ) (p : Fin k → ℝ) (δ M : ℚ) (j : Fin k)
    (A : Fin k → Fin k → ℝ) (hs : ∀ i,0 ≤ s i)
    (hp : p ∈ floorStrategies (fun i => (s i : ℝ))) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i l,|A i l| ≤ (M : ℝ)) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      (fun i => (rationalReservoirAllocation s δ j z i : ℝ)) ∈
        floorStrategies (fun i => (s i : ℝ)) ∧
      exploitability A (fun i => (rationalReservoirAllocation s δ j z i : ℝ)) ≤
        exploitability A p+(2 : ℕ)*(M : ℝ)*k*(δ : ℝ) := by
  have hfloor : Nat.floor (1/(δ : ℝ))=Nat.floor (1/δ) := by
    rw [show 1/(δ : ℝ)=((1/δ : ℚ) : ℝ) by push_cast; rfl,rational_nat_floor_real_cast]
  obtain ⟨z,hz,hv⟩ := reservoir_grid_approximation (fun i => (s i : ℝ)) p
    (δ : ℝ) (M : ℝ) j A (fun i => by exact_mod_cast hs i) hp
    (by exact_mod_cast hδ) (by exact_mod_cast hM) hA
  let zQ : Fin k → Fin (1+Nat.floor (1/δ)) :=
    fun i => ⟨(z i).val,by rw [←hfloor]; exact (z i).isLt⟩
  have he : (fun i => (rationalReservoirAllocation s δ j zQ i : ℝ))=
      reservoirGridAllocation (fun i => (s i : ℝ)) (δ : ℝ) j z := by
    rw [rational_reservoir_allocation_real]
    congr 1
  refine ⟨zQ,he.symm ▸ hz,?_⟩
  rw [he]
  simpa only [Fintype.card_fin] using hv

end
end SparseCompletion

/- Fixed source body: RationalFloorRepertoire.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalResidualFloors {k m : ℕ} (t : Fin m → ℚ) :
    RationalLinearSystem (Fin m) (m+(m*k+(k*k+0*m))) :=
  ⟨fun i => rationalFormScale (-1) (intervalQForm k m 0 i),fun i => -t i⟩

theorem rational_residual_floors_iff {k m : ℕ} (t : Fin m → ℚ)
    (x : Fin (m+(m*k+(k*k+0*m))) → ℚ) :
    (rationalResidualFloors (k := k) t).Satisfies x ↔ ∀ i,t i ≤ intervalQ x i := by
  change (∀ i,rationalFormEval (rationalFormScale (-1) (intervalQForm k m 0 i)) x ≤ -t i) ↔ _
  simp only [rational_form_eval_scale,interval_q_form_eval,neg_one_mul,neg_le_neg_iff]

theorem rational_residual_floors_real_iff {k m : ℕ} (t : Fin m → ℚ)
    (x : Fin (m+(m*k+(k*k+0*m))) → ℝ) :
    (rationalResidualFloors (k := k) t).RealSatisfies x ↔ ∀ i,(t i : ℝ) ≤ intervalQ x i := by
  change (∀ i,rationalFormRealEval (rationalFormScale (-1) (intervalQForm k m 0 i)) x ≤ (-t i : ℚ)) ↔ _
  simp only [rational_form_real_eval_scale,interval_q_real_form_eval,Rat.cast_neg,Rat.cast_one,
    neg_one_mul,neg_le_neg_iff]

theorem rational_residual_floors_real_pack {k m : ℕ} (t : Fin m → ℚ)
    (q : Fin m → ℝ) (V : Fin m → Fin k → ℝ) (K : Fin k → Fin k → ℝ) :
    (rationalResidualFloors t).RealSatisfies (intervalPack q V K (H := 0) Fin.elim0) ↔
      ∀ i,(t i : ℝ) ≤ q i := by
  rw [rational_residual_floors_real_iff,interval_pack_q]

end SparseCompletion

/- Fixed source body: RationalAllocationCompleteness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

theorem rational_allocation_run_success_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) :
    (∃ w,rationalAllocationRun d s hs ζ p=some w) ↔
      ∃ h : ∀ a,s a ≤ p a,(d.withAllocation p (fun a => le_trans (hs a) (h a))).Compatible := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨h,ho,_⟩ := rational_allocation_run_output d s hs ζ p w hw
    obtain ⟨hc,_,_⟩ := rational_interval_initialized_game
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ w.2 ho
    exact ⟨h,hc⟩
  · rintro ⟨h,hc⟩
    obtain ⟨o,ho⟩ := rational_interval_initialized_complete
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ hc
    refine ⟨(p,o),?_⟩
    simp only [rationalAllocationRun,dite_eq_left h,ho,Option.map_some]

theorem rational_finite_select_success_iff {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) :
    (∃ o,rationalFiniteSelect candidates run score=some o) ↔
      ∃ a ∈ candidates, ∃ o,run a=some o := by
  constructor
  · rintro ⟨o,ho⟩
    obtain ⟨a,ha,hr⟩ := rational_finite_select_origin candidates run score o ho
    exact ⟨a,ha,o,hr⟩
  · rintro ⟨a,ha,o,hr⟩
    cases hs : rationalFiniteSelect candidates run score with
    | none =>
      have hn := (rational_finite_select_none_iff candidates run score).mp hs a ha
      rw [hn] at hr
      cases hr
    | some v => exact ⟨v,rfl⟩

theorem rational_allocation_search_success_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) :
    (∃ w,rationalAllocationSearch d s hs δ ζ=some w) ↔
      ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
        ∃ h : ∀ a,s a ≤ rationalAnchorAllocation s δ z a,
          (d.withAllocation (rationalAnchorAllocation s δ z)
            (fun a => le_trans (hs a) (h a))).Compatible := by
  rw [rationalAllocationSearch,rational_finite_select_success_iff]
  constructor
  · rintro ⟨z,_,hz⟩
    exact ⟨z,(rational_allocation_run_success_iff d s hs ζ _).mp hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,rational_allocation_nodes_complete k δ z,
      (rational_allocation_run_success_iff d s hs ζ _).mpr hz⟩

end SparseCompletion

/- Fixed source body: RationalAnchorApproximation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_anchor_rounding_enumerated {k : ℕ} (s : Fin k → ℚ)
    (p : Fin k → ℝ) (δ : ℚ) (hs : ∀ i,0 ≤ s i) (hp : ∀ i,p i ≤ 1) (hδ : 0 < δ) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      ∀ i,(rationalAnchorAllocation s δ z i : ℝ)=
        roundedAllocation (fun i => (s i : ℝ)) p (δ : ℝ) i := by
  have hfloor : Nat.floor (1/(δ : ℝ))=Nat.floor (1/δ) := by
    rw [show 1/(δ : ℝ)=((1/δ : ℚ) : ℝ) by push_cast; rfl,rational_nat_floor_real_cast]
  obtain ⟨z,hz⟩ := rounded_allocation_finite_grid (fun i => (s i : ℝ)) p (δ : ℝ)
    (fun i => by exact_mod_cast hs i) hp (by exact_mod_cast hδ)
  let zQ : Fin k → Fin (1+Nat.floor (1/δ)) :=
    fun i => ⟨(z i).val,by rw [←hfloor]; exact (z i).isLt⟩
  refine ⟨zQ,?_⟩
  intro i
  simpa only [rationalAnchorAllocation,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast] using (hz i).symm

end
end SparseCompletion

/- Fixed source body: RationalFloorGridPhysical.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_compatible {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ)
    (u : Fin m → ℚ) (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i)
    (hR : d.R=rationalResidualFloors u)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (hsp : ∀ a,(s a : ℝ) ≤ p a) (huq : ∀ i,(u i : ℝ) ≤ q i)
    (hmass : (∑ a,p a)+(∑ i,q i)=1) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (hDI : ∀ i a,(d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ))
    (hB : IsSkew B) (hBI : ∀ i l,-(d.M : ℝ) ≤ B i l ∧ B i l ≤ (d.M : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      ∃ h : ∀ a,s a ≤ rationalAnchorAllocation s δ z a,
        (∀ a,(rationalAnchorAllocation s δ z a : ℝ)=
          roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ) a) ∧
        (d.withAllocation (rationalAnchorAllocation s δ z)
          (fun a => le_trans (hs a) (h a))).Compatible := by
  have hp0 : ∀ a,0 ≤ p a := fun a => le_trans (by exact_mod_cast hs a) (hsp a)
  have hq0 : ∀ i,0 ≤ q i := fun i => le_trans (by exact_mod_cast hu i) (huq i)
  have hp1 : ∀ a,p a ≤ 1 := by
    intro a
    have hsingle := Finset.single_le_sum (fun b _ => hp0 b) (Finset.mem_univ a)
    have hqsum : 0 ≤ ∑ i,q i := Finset.sum_nonneg fun i _ => hq0 i
    linarith
  obtain ⟨z,hz⟩ := rational_anchor_rounding_enumerated s p δ hs hp1 hδ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hf := allocation_rounding_preserves_floors (fun a => (s a : ℝ)) p
    (fun i => (u i : ℝ)) q (δ : ℝ) j hsp huq hδR
  have hsz : ∀ a,s a ≤ rationalAnchorAllocation s δ z a := by
    intro a
    have hh := hf.1 a
    rw [←hz a] at hh
    exact_mod_cast hh
  let q' := transferredResidual q
    (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j
  have hm := allocation_rounding_mass (fun a => (s a : ℝ)) p q (δ : ℝ) j
  have hzsum : (∑ a,(rationalAnchorAllocation s δ z a : ℝ))=
      ∑ a,roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ) a :=
    Finset.sum_congr rfl (fun a _ => hz a)
  refine ⟨z,hsz,hz,q',K,D,B,?_,?_,hK,hKI,hDI,hB,hBI,?_⟩
  · exact fun i => le_trans (by exact_mod_cast hu i) (hf.2 i)
  · change (∑ i,q' i)=((1-∑ a,rationalAnchorAllocation s δ z a : ℚ) : ℝ)
    push_cast
    change (∑ i,transferredResidual q
      (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j i)=_
    linarith
  · change d.R.RealSatisfies (intervalPack q' (fun i a => q' i*D i a) K (H := 0) Fin.elim0)
    rw [hR,rational_residual_floors_real_pack]
    exact hf.2

end
end SparseCompletion

/- Fixed source body: RationalIntervalWitnessClass.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_game_class_of_witness {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (hq : ∀ i,0 ≤ q i) (hm : (∑ i,q i)=(d.r : ℝ)) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (hDI : ∀ i a,(d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ))
    (hB : IsSkew B) (hBI : ∀ i l,-(d.M : ℝ) ≤ B i l ∧ B i l ≤ (d.M : ℝ))
    (hR : d.R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)) :
    (q,D,K,B) ∈ intervalGameClass d := by
  refine ⟨⟨⟨hq,?_⟩,⟨fun i a => (hDI i a).1,fun i a => (hDI i a).2⟩,
    ⟨fun a b => (hKI a b).1,fun a b => (hKI a b).2⟩,hB,hBI⟩,hm,hK,hR⟩
  intro i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hq j)
    (Finset.mem_univ i)
  rwa [hm] at hi

end
end SparseCompletion

/- Fixed source body: RationalFloorGridGame.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_game {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ)
    (u : Fin m → ℚ) (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i)
    (hR : d.R=rationalResidualFloors u)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (hsp : ∀ a,(s a : ℝ) ≤ p a) (huq : ∀ i,(u i : ℝ) ≤ q i)
    (hmass : (∑ a,p a)+(∑ i,q i)=1) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (hDI : ∀ i a,(d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ))
    (hB : IsSkew B) (hBI : ∀ i l,-(d.M : ℝ) ≤ B i l ∧ B i l ≤ (d.M : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      ∃ h : ∀ a,s a ≤ rationalAnchorAllocation s δ z a,
        ∃ hc : (d.withAllocation (rationalAnchorAllocation s δ z)
          (fun a => le_trans (hs a) (h a))).Compatible,
          ∃ q' : Fin m → ℝ,
            (q',D,K,B) ∈ intervalGameClass
              ((d.withAllocation (rationalAnchorAllocation s δ z)
                (fun a => le_trans (hs a) (h a))).toModel hc) ∧
            exploitability (blockMatrix K D B)
              (blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q') ≤
              exploitability (blockMatrix K D B) (blockWeights p q)+
                (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ) := by
  obtain ⟨z,hsz,hz,hc⟩ := rational_floor_grid_compatible d s u hs hu hR
    p q K D B hsp huq hmass hK hKI hDI hB hBI δ hδ j
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  let q' := transferredResidual q
    (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j
  have hf := allocation_rounding_preserves_floors (fun a => (s a : ℝ)) p
    (fun i => (u i : ℝ)) q (δ : ℝ) j hsp huq hδR
  have hq' : ∀ i,0 ≤ q' i := fun i => le_trans (by exact_mod_cast hu i) (hf.2 i)
  have hm := allocation_rounding_mass (fun a => (s a : ℝ)) p q (δ : ℝ) j
  have hzsum : (∑ a,(rationalAnchorAllocation s δ z a : ℝ))=
      ∑ a,roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ) a :=
    Finset.sum_congr rfl (fun a _ => hz a)
  have hmq' : (∑ i,q' i)=
      (((d.withAllocation (rationalAnchorAllocation s δ z)
        (fun a => le_trans (hs a) (hsz a))).toModel hc).r : ℝ) := by
    change (∑ i,q' i)=((1-∑ a,rationalAnchorAllocation s δ z a : ℚ) : ℝ)
    push_cast
    change (∑ i,transferredResidual q
      (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j i)=_
    linarith
  have hRq' : d.R.RealSatisfies (intervalPack q' (fun i a => q' i*D i a) K (H := 0) Fin.elim0) := by
    rw [hR,rational_residual_floors_real_pack]
    exact hf.2
  refine ⟨z,hsz,hc,q',interval_game_class_of_witness _ q' K D B
    hq' hmq' hK hKI hDI hB hBI hRq',?_⟩
  have hAb := blockMatrix_bounds K D B (d.M : ℝ)
    (fun a b => ⟨le_trans (by exact_mod_cast d.coreLower a b) (hKI a b).1,
      le_trans (hKI a b).2 (by exact_mod_cast d.coreUpper a b)⟩)
    (fun i a => ⟨le_trans (by exact_mod_cast d.crossLower i a) (hDI i a).1,
      le_trans (hDI i a).2 (by exact_mod_cast d.crossUpper i a)⟩) hBI
  have hE := allocation_rounding_value_bound (fun a => (s a : ℝ)) p q
    (δ : ℝ) (d.M : ℝ) j (blockMatrix K D B) hsp hδR
    (by exact_mod_cast le_of_lt d.positiveBound) (fun a b => abs_le.mpr (hAb a b))
  have hw : blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q'=
      blockWeights (roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ)) q' := by
    funext a
    cases a with
    | inl a => exact hz a
    | inr i => rfl
  rw [hw]
  simpa only [Fintype.card_fin] using hE

end
end SparseCompletion

/- Fixed source body: RationalFloorGridAccuracy.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_search_accuracy {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ)
    (u : Fin m → ℚ) (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i)
    (hR : d.R=rationalResidualFloors u)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (hsp : ∀ a,(s a : ℝ) ≤ p a) (huq : ∀ i,(u i : ℝ) ≤ q i)
    (hmass : (∑ a,p a)+(∑ i,q i)=1) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (hDI : ∀ i a,(d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ))
    (hB : IsSkew B) (hBI : ∀ i l,-(d.M : ℝ) ≤ B i l ∧ B i l ≤ (d.M : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalAllocationSearch d s hs δ ζ=some w ∧
      ∀ a, response (intervalGameMatrix w.2.realData)
        (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a <
          exploitability (blockMatrix K D B) (blockWeights p q)+
            (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨z,hz,hc,q',hClass,hE⟩ := rational_floor_grid_game d s u hs hu hR
    p q K D B hsp huq hmass hK hKI hDI hB hBI δ hδ j
  let dz := d.withAllocation (rationalAnchorAllocation s δ z)
    (fun a => le_trans (hs a) (hz a))
  obtain ⟨v,hv⟩ := rational_interval_initialized_complete dz ζ hc
  have hRun : rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z)=
      some (rationalAnchorAllocation s δ z,v) := by
    simp only [rationalAllocationRun,dite_eq_left hz]
    change (rationalIntervalInitializedApproximation dz ζ).map
      (fun o => (rationalAnchorAllocation s δ z,o))=some (rationalAnchorAllocation s δ z,v)
    rw [hv]
    rfl
  have hSuccess : ∃ w,rationalAllocationSearch d s hs δ ζ=some w := by
    rw [rationalAllocationSearch,rational_finite_select_success_iff]
    exact ⟨z,rational_allocation_nodes_complete k δ z,_,hRun⟩
  obtain ⟨w,hw⟩ := hSuccess
  have hmin := rational_allocation_search_minimal d s hs δ ζ w hw z _ hRun
  obtain ⟨hc',hL,_,hwidth⟩ := rational_interval_initialized_value dz ζ hζ v hv
  have hVal := interval_game_value_le_witness (dz.toModel hc') (q',D,K,B) hClass
  change intervalGameValue (dz.toModel hc') ≤
    exploitability (blockMatrix K D B)
      (blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q') at hVal
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  obtain ⟨zw,hzw⟩ := rational_allocation_search_output d s hs δ ζ w hw
  obtain ⟨_,_,_,hrows⟩ := rational_allocation_run_game d s hs ζ _ w hzw
  refine ⟨w,hw,?_⟩
  intro a
  have hr := hrows a
  change response (intervalGameMatrix w.2.realData)
    (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a ≤
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) at hr
  linarith

end
end SparseCompletion

/- Fixed source body: RationalFloorClass.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

abbrev FloorIntervalGameData (k m : ℕ) := (Fin k → ℝ) × IntervalGameData k m

def floorIntervalGameBox {k m : ℕ} {I : Type*} (d : RationalIntervalParameters k m I) :
    Set (FloorIntervalGameData k m) :=
  Set.Icc (fun _ => 0) (fun _ => 1) ×ˢ
    (Set.Icc (fun _ => 0) (fun _ => 1) ×ˢ
      (Set.Icc (fun i a => (d.lo i a : ℝ)) (fun i a => (d.hi i a : ℝ)) ×ˢ
        (Set.Icc (fun a b => (d.loK a b : ℝ)) (fun a b => (d.hiK a b : ℝ)) ×ˢ skewBox d.M)))

def floorIntervalGameClass {k m : ℕ} {I : Type*} (d : RationalIntervalParameters k m I)
    (s : Fin k → ℚ) (u : Fin m → ℚ) : Set (FloorIntervalGameData k m) :=
  floorIntervalGameBox d ∩ {z | (∀ a,(s a : ℝ) ≤ z.1 a) ∧
    (∀ i,(u i : ℝ) ≤ z.2.1 i) ∧ (∑ a,z.1 a)+(∑ i,z.2.1 i)=1 ∧ IsSkew z.2.2.2.1}

theorem floor_interval_game_class_compact {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ) :
    IsCompact (floorIntervalGameClass d s u) := by
  have hc : IsCompact (floorIntervalGameBox d) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod (skewBox_compact d.M))))
  apply hc.inter_right
  have he : {z : FloorIntervalGameData k m | (∀ a,(s a : ℝ) ≤ z.1 a) ∧
      (∀ i,(u i : ℝ) ≤ z.2.1 i) ∧ (∑ a,z.1 a)+(∑ i,z.2.1 i)=1 ∧ IsSkew z.2.2.2.1}=
      (⋂ a,{z | (s a : ℝ) ≤ z.1 a}) ∩ ((⋂ i,{z | (u i : ℝ) ≤ z.2.1 i}) ∩
        ({z | (∑ a,z.1 a)+(∑ i,z.2.1 i)=1} ∩
          (⋂ a,⋂ b,{z | z.2.2.2.1 a b= -z.2.2.2.1 b a}))) := by
    ext z
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter,IsSkew]
  rw [he]
  exact (isClosed_iInter fun a => isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (by fun_prop) (by fun_prop))))

def floorIntervalGameExploitability {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (z : FloorIntervalGameData k m) : ℝ :=
  exploitability (intervalGameMatrix z.2) (blockWeights z.1 z.2.1)

theorem floor_interval_game_exploitability_continuous {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)] :
    Continuous (floorIntervalGameExploitability (k := k) (m := m)) := by
  unfold floorIntervalGameExploitability intervalGameMatrix exploitability
  apply Continuous.finset_sup'_apply
  intro a _
  cases a with
  | inl a => simp only [block_response_anchor,anchorResponse]; fun_prop
  | inr i =>
    simp only [response,Fintype.sum_sum_type,blockMatrix,blockWeights,Sum.elim_inl,Sum.elim_inr]
    fun_prop

def floorIntervalGameValue {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ) : ℝ :=
  sInf (floorIntervalGameExploitability '' floorIntervalGameClass d s u)

theorem floor_interval_game_value_attained {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hne : (floorIntervalGameClass d s u).Nonempty) :
    ∃ z ∈ floorIntervalGameClass d s u,
      floorIntervalGameExploitability z=floorIntervalGameValue d s u := by
  have hc := (floor_interval_game_class_compact d s u).image floor_interval_game_exploitability_continuous
  obtain ⟨v,hv,he⟩ := hc.sInf_mem (hne.image floorIntervalGameExploitability)
  exact ⟨v,hv,he⟩

end
end SparseCompletion

/- Fixed source body: RationalFloorGlobalAccuracy.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_global_accuracy {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalAllocationSearch d s hs δ ζ=some w ∧
      ∀ a, response (intervalGameMatrix w.2.realData)
        (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a <
          floorIntervalGameValue d s u+
            (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨⟨p,q,D,K,B⟩,hz,he⟩ := floor_interval_game_value_attained d s u hne
  rcases hz with ⟨⟨_,_,hDI,hKI,hB,hBI⟩,hsp,huq,hmass,hK⟩
  obtain ⟨w,hw,hr⟩ := rational_floor_grid_search_accuracy d s u hs hu hR p q K D B
    hsp huq hmass hK (fun a b => ⟨hKI.1 a b,hKI.2 a b⟩)
    (fun i a => ⟨hDI.1 i a,hDI.2 i a⟩) hB hBI δ hδ j ζ hζ
  change exploitability (blockMatrix K D B) (blockWeights p q)=floorIntervalGameValue d s u at he
  rw [he] at hr
  exact ⟨w,hw,hr⟩

end
end SparseCompletion

/- Fixed source body: RationalReservoirRepresentation.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_reservoir_rounding_enumerated {k : ℕ} (s : Fin k → ℚ)
    (p : Fin k → ℝ) (δ : ℚ) (j : Fin k) (hs : ∀ i,0 ≤ s i)
    (hp : p ∈ floorStrategies (fun i => (s i : ℝ))) (hδ : 0 < δ) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      (fun i => (rationalReservoirAllocation s δ j z i : ℝ))=
        reservoirRounded (fun i => (s i : ℝ)) p (δ : ℝ) j := by
  have hfloor : Nat.floor (1/(δ : ℝ))=Nat.floor (1/δ) := by
    rw [show 1/(δ : ℝ)=((1/δ : ℚ) : ℝ) by push_cast; rfl,rational_nat_floor_real_cast]
  obtain ⟨z,hz⟩ := reservoir_rounded_finite_grid (fun i => (s i : ℝ)) p (δ : ℝ) j
    (fun i => by exact_mod_cast hs i) hp (by exact_mod_cast hδ)
  let zQ : Fin k → Fin (1+Nat.floor (1/δ)) :=
    fun i => ⟨(z i).val,by rw [←hfloor]; exact (z i).isLt⟩
  refine ⟨zQ,?_⟩
  rw [rational_reservoir_allocation_real,hz]
  congr 1

end
end SparseCompletion

/- Fixed source body: RationalNoResidualGame.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_no_residual_grid_game {k : ℕ} [Nonempty (Fin k ⊕ Fin 0)]
    (d : RationalIntervalParameters k 0 (Fin 0)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (Fin.elim0 : Fin 0 → ℚ))
    (p : Fin k → ℝ) (hp : p ∈ floorStrategies (fun a => (s a : ℝ)))
    (K : Fin k → Fin k → ℝ) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin k) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      ∃ h : ∀ a,s a ≤ rationalReservoirAllocation s δ j z a,
        ∃ hc : (d.withAllocation (rationalReservoirAllocation s δ j z)
          (fun a => le_trans (hs a) (h a))).Compatible,
          (Fin.elim0,Fin.elim0,K,Fin.elim0) ∈ intervalGameClass
            ((d.withAllocation (rationalReservoirAllocation s δ j z)
              (fun a => le_trans (hs a) (h a))).toModel hc) ∧
          exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
            (blockWeights (fun a => (rationalReservoirAllocation s δ j z a : ℝ)) Fin.elim0) ≤
            exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
              (blockWeights p Fin.elim0)+(2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ) := by
  obtain ⟨z,hz⟩ := rational_reservoir_rounding_enumerated s p δ j hs hp hδ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hsz : ∀ a,s a ≤ rationalReservoirAllocation s δ j z a := by
    intro a
    have hh := reservoir_rounded_floors (fun a => (s a : ℝ)) p (δ : ℝ) j hp.1 hδR a
    rw [←hz] at hh
    change (s a : ℝ) ≤ (rationalReservoirAllocation s δ j z a : ℝ) at hh
    exact_mod_cast hh
  let dz := d.withAllocation (rationalReservoirAllocation s δ j z)
    (fun a => le_trans (hs a) (hsz a))
  have hm : (∑ i : Fin 0,(Fin.elim0 i : ℝ))=(dz.r : ℝ) := by
    change (∑ i : Fin 0,(Fin.elim0 i : ℝ))=((1-∑ a,rationalReservoirAllocation s δ j z a : ℚ) : ℝ)
    rw [rational_reservoir_allocation_mass]
    norm_num
  have hRp : dz.R.RealSatisfies
      (intervalPack (Fin.elim0 : Fin 0 → ℝ)
        (fun (i : Fin 0) (a : Fin k) => (Fin.elim0 i : ℝ)*((Fin.elim0 i : Fin k → ℝ) a)) K (H := 0) Fin.elim0) := by
    change d.R.RealSatisfies _
    rw [hR,rational_residual_floors_real_pack]
    exact fun i => Fin.elim0 i
  have hc : dz.Compatible :=
    ⟨Fin.elim0,K,Fin.elim0,Fin.elim0,(fun i => Fin.elim0 i),hm,hK,hKI,
      (fun i => Fin.elim0 i),(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),hRp⟩
  refine ⟨z,hsz,hc,interval_game_class_of_witness (dz.toModel hc)
    Fin.elim0 K Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) hm hK hKI
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hRp,?_⟩
  let A := blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0
  have hAb := blockMatrix_bounds K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0 (d.M : ℝ)
    (fun a b => ⟨le_trans (by exact_mod_cast d.coreLower a b) (hKI a b).1,
      le_trans (hKI a b).2 (by exact_mod_cast d.coreUpper a b)⟩)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hd : (∑ a : Fin k ⊕ Fin 0,
      |blockWeights p (Fin.elim0 : Fin 0 → ℝ) a-
        blockWeights (fun b => (rationalReservoirAllocation s δ j z b : ℝ)) Fin.elim0 a|) ≤
      (2 : ℕ)*(k : ℝ)*(δ : ℝ) := by
    rw [Fintype.sum_sum_type]
    simp only [blockWeights,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_zero,add_zero]
    simp_rw [show ∀ a,(rationalReservoirAllocation s δ j z a : ℝ)=
      reservoirRounded (fun a => (s a : ℝ)) p (δ : ℝ) j a from fun a => congrFun hz a]
    simpa only [Fintype.card_fin] using
      reservoir_rounded_distance (fun a => (s a : ℝ)) p (δ : ℝ) j hp.1 hδR
  have hh := (abs_le.mp (exploitability_strategy_distance A
    (blockWeights p Fin.elim0)
    (blockWeights (fun b => (rationalReservoirAllocation s δ j z b : ℝ)) Fin.elim0)
    (d.M : ℝ) (fun a b => abs_le.mpr (hAb a b)))).1
  have hdM := mul_le_mul_of_nonneg_left hd (by exact_mod_cast le_of_lt d.positiveBound : 0 ≤ (d.M : ℝ))
  norm_num only [Nat.cast_ofNat] at hdM ⊢
  nlinarith

end
end SparseCompletion

/- Fixed source body: RationalNoResidualAccuracy.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_no_residual_search_accuracy {k : ℕ} [Nonempty (Fin k ⊕ Fin 0)]
    (d : RationalIntervalParameters k 0 (Fin 0)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (Fin.elim0 : Fin 0 → ℚ))
    (p : Fin k → ℝ) (hp : p ∈ floorStrategies (fun a => (s a : ℝ)))
    (K : Fin k → Fin k → ℝ) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin k) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k 0,
      rationalReservoirSearch d s hs δ ζ j=some w ∧
      ∀ a, response (intervalGameMatrix w.2.realData)
        (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a <
          exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
            (blockWeights p Fin.elim0)+
            (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨z,hz,hc,hClass,hE⟩ := rational_no_residual_grid_game d s hs hR p hp K hK hKI δ hδ j
  let dz := d.withAllocation (rationalReservoirAllocation s δ j z)
    (fun a => le_trans (hs a) (hz a))
  obtain ⟨v,hv⟩ := rational_interval_initialized_complete dz ζ hc
  have hRun : rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z)=
      some (rationalReservoirAllocation s δ j z,v) := by
    simp only [rationalAllocationRun,dite_eq_left hz]
    change (rationalIntervalInitializedApproximation dz ζ).map
      (fun o => (rationalReservoirAllocation s δ j z,o))=some (rationalReservoirAllocation s δ j z,v)
    rw [hv]
    rfl
  have hSuccess : ∃ w,rationalReservoirSearch d s hs δ ζ j=some w := by
    rw [rationalReservoirSearch,rational_finite_select_success_iff]
    exact ⟨z,rational_allocation_nodes_complete k δ z,_,hRun⟩
  obtain ⟨w,hw⟩ := hSuccess
  have hmin := rational_reservoir_search_minimal d s hs δ ζ j w hw z _ hRun
  obtain ⟨hc',hL,_,hwidth⟩ := rational_interval_initialized_value dz ζ hζ v hv
  have hVal := interval_game_value_le_witness (dz.toModel hc')
    (Fin.elim0,Fin.elim0,K,Fin.elim0) hClass
  change intervalGameValue (dz.toModel hc') ≤
    exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
      (blockWeights (fun a => (rationalReservoirAllocation s δ j z a : ℝ)) Fin.elim0) at hVal
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  obtain ⟨zw,hzw⟩ := rational_reservoir_search_output d s hs δ ζ j w hw
  obtain ⟨_,_,_,hrows⟩ := rational_allocation_run_game d s hs ζ _ w hzw
  refine ⟨w,hw,?_⟩
  intro a
  have hr := hrows a
  change response (intervalGameMatrix w.2.realData)
    (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a ≤
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) at hr
  linarith

end
end SparseCompletion

/- Fixed source body: RationalInitializedUpperWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_initialized_upper_lt_witness {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalParameters k m I)
    (ζ : ℚ) (hζ : 0 < ζ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o)
    (hc : d.Compatible) (z : IntervalGameData k m) (hz : z ∈ intervalGameClass (d.toModel hc)) :
    (o.bracket.2 : ℝ) < intervalGameExploitability (d.toModel hc) z+(ζ : ℝ) := by
  obtain ⟨hc',hL,_,hwidth⟩ := rational_interval_initialized_value d ζ hζ o hout
  have hv := interval_game_value_le_witness (d.toModel hc) z hz
  have he : d.toModel hc'=d.toModel hc := rfl
  rw [he] at hL
  linarith

end
end SparseCompletion

/- Fixed source body: RationalFloorClassWitness.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem floor_interval_game_class_of_fixed {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u)
    (p : Fin k → ℚ) (hsp : ∀ a,s a ≤ p a)
    (hc : (d.withAllocation p (fun a => le_trans (hs a) (hsp a))).Compatible)
    (z : IntervalGameData k m)
    (hz : z ∈ intervalGameClass ((d.withAllocation p (fun a => le_trans (hs a) (hsp a))).toModel hc)) :
    ((fun a => (p a : ℝ)),z) ∈ floorIntervalGameClass d s u := by
  rcases hz with ⟨⟨⟨hq,_⟩,hD,hK,hB,hBI⟩,hm,hKs,hRp⟩
  have hp0 : ∀ a,0 ≤ (p a : ℝ) := fun a => by exact_mod_cast le_trans (hs a) (hsp a)
  have hmass : (∑ a,(p a : ℝ))+(∑ i,z.1 i)=1 := by
    change (∑ i,z.1 i)=((1-∑ a,p a : ℚ) : ℝ) at hm
    push_cast at hm
    linarith
  have hp1 : ∀ a,(p a : ℝ) ≤ 1 := by
    intro a
    have hsingle := Finset.single_le_sum (fun b _ => hp0 b) (Finset.mem_univ a)
    have hqsum : 0 ≤ ∑ i,z.1 i := Finset.sum_nonneg fun i _ => hq i
    linarith
  have hq1 : ∀ i,z.1 i ≤ 1 := by
    intro i
    have hsingle := Finset.single_le_sum (fun l _ => hq l) (Finset.mem_univ i)
    have hpsum : 0 ≤ ∑ a,(p a : ℝ) := Finset.sum_nonneg fun a _ => hp0 a
    linarith
  refine ⟨⟨⟨hp0,hp1⟩,⟨hq,hq1⟩,hD,hK,hB,hBI⟩,
    (fun a => by change (s a : ℝ) ≤ (p a : ℝ); exact_mod_cast hsp a),?_,hmass,hKs⟩
  change d.R.RealSatisfies
    (intervalPack z.1 (fun i a => z.1 i*z.2.1 i a) z.2.2.1 (H := 0) Fin.elim0) at hRp
  rw [hR,rational_residual_floors_real_pack] at hRp
  exact hRp

theorem floor_interval_game_value_le_witness {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (z : FloorIntervalGameData k m) (hz : z ∈ floorIntervalGameClass d s u) :
    floorIntervalGameValue d s u ≤ floorIntervalGameExploitability z := by
  apply csInf_le ((floor_interval_game_class_compact d s u).image
    floor_interval_game_exploitability_continuous).bddBelow
  exact ⟨z,hz,rfl⟩

theorem rational_floor_search_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (δ ζ : ℚ)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationSearch d s hs δ ζ=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  obtain ⟨z,hz⟩ := rational_allocation_search_output d s hs δ ζ w hout
  obtain ⟨hsp,hc,hClass,_⟩ := rational_allocation_run_game d s hs ζ _ w hz
  exact floor_interval_game_class_of_fixed d s u hs hR w.1 hsp hc w.2.realData hClass

end
end SparseCompletion

/- Fixed source body: RationalFloorValueCertificate.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_value_certificate {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalAllocationSearch d s hs δ ζ=some w ∧
      floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) < floorIntervalGameValue d s u+
        (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨⟨p,q,D,K,B⟩,hz0,he⟩ := floor_interval_game_value_attained d s u hne
  rcases hz0 with ⟨⟨_,_,hDI,hKI,hB,hBI⟩,hsp,huq,hmass,hK⟩
  obtain ⟨z,hz,hc,q',hClass,hE⟩ := rational_floor_grid_game d s u hs hu hR p q K D B
    hsp huq hmass hK (fun a b => ⟨hKI.1 a b,hKI.2 a b⟩)
    (fun i a => ⟨hDI.1 i a,hDI.2 i a⟩) hB hBI δ hδ j
  change exploitability (blockMatrix K D B) (blockWeights p q)=floorIntervalGameValue d s u at he
  rw [he] at hE
  let dz := d.withAllocation (rationalAnchorAllocation s δ z)
    (fun a => le_trans (hs a) (hz a))
  obtain ⟨v,hv⟩ := rational_interval_initialized_complete dz ζ hc
  have hRun : rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z)=
      some (rationalAnchorAllocation s δ z,v) := by
    simp only [rationalAllocationRun,dite_eq_left hz]
    change (rationalIntervalInitializedApproximation dz ζ).map
      (fun o => (rationalAnchorAllocation s δ z,o))=some (rationalAnchorAllocation s δ z,v)
    rw [hv]
    rfl
  have hSuccess : ∃ w,rationalAllocationSearch d s hs δ ζ=some w := by
    rw [rationalAllocationSearch,rational_finite_select_success_iff]
    exact ⟨z,rational_allocation_nodes_complete k δ z,_,hRun⟩
  obtain ⟨w,hw⟩ := hSuccess
  have hmin := rational_allocation_search_minimal d s hs δ ζ w hw z _ hRun
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  have hU := rational_initialized_upper_lt_witness dz ζ hζ v hv hc (q',D,K,B) hClass
  change (v.bracket.2 : ℝ) < exploitability (blockMatrix K D B)
    (blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q')+(ζ : ℝ) at hU
  have hGlobal := rational_floor_search_output_class d s u hs hR δ ζ w hw
  have hLower := floor_interval_game_value_le_witness d s u _ hGlobal
  obtain ⟨zw,hzw⟩ := rational_allocation_search_output d s hs δ ζ w hw
  obtain ⟨_,_,_,hrows⟩ := rational_allocation_run_game d s hs ζ _ w hzw
  have hUpper : floorIntervalGameExploitability ((fun a => (w.1 a : ℝ)),w.2.realData) ≤
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) := by
    exact (exploitability_le_iff _ _ _).mpr hrows
  exact ⟨w,hw,le_trans hLower hUpper,by linarith⟩

end
end SparseCompletion

/- Fixed source body: RationalReservoirClass.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_floor_reservoir_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (δ ζ : ℚ) (j : Fin k)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalReservoirSearch d s hs δ ζ j=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  obtain ⟨z,hz⟩ := rational_reservoir_search_output d s hs δ ζ j w hout
  obtain ⟨hsp,hc,hClass,_⟩ := rational_allocation_run_game d s hs ζ _ w hz
  exact floor_interval_game_class_of_fixed d s u hs hR w.1 hsp hc w.2.realData hClass

end
end SparseCompletion

/- Fixed source body: RationalNoResidualGlobal.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_no_residual_global_certificate {k : ℕ} [Nonempty (Fin k ⊕ Fin 0)]
    (d : RationalIntervalParameters k 0 (Fin 0)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (Fin.elim0 : Fin 0 → ℚ))
    (hne : (floorIntervalGameClass d s Fin.elim0).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (j : Fin k) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k 0,
      rationalReservoirSearch d s hs δ ζ j=some w ∧
      floorIntervalGameValue d s Fin.elim0 ≤ (w.2.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) < floorIntervalGameValue d s Fin.elim0+
        (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨⟨p,q,D,K,B⟩,hz0,he⟩ := floor_interval_game_value_attained d s Fin.elim0 hne
  have hq : q=(Fin.elim0 : Fin 0 → ℝ) := funext fun i => Fin.elim0 i
  have hD : D=(Fin.elim0 : Fin 0 → Fin k → ℝ) := funext fun i => Fin.elim0 i
  have hB : B=(Fin.elim0 : Fin 0 → Fin 0 → ℝ) := funext fun i => Fin.elim0 i
  subst q
  subst D
  subst B
  rcases hz0 with ⟨⟨_,_,_,hKI,_,_⟩,hsp,_,hmass,hK⟩
  have hp : p ∈ floorStrategies (fun a => (s a : ℝ)) :=
    ⟨hsp,by simpa only [Fin.sum_univ_zero,add_zero] using hmass⟩
  obtain ⟨z,hz,hc,hClass,hE⟩ := rational_no_residual_grid_game d s hs hR p hp K hK
    (fun a b => ⟨hKI.1 a b,hKI.2 a b⟩) δ hδ j
  change exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
    (blockWeights p Fin.elim0)=floorIntervalGameValue d s Fin.elim0 at he
  rw [he] at hE
  let dz := d.withAllocation (rationalReservoirAllocation s δ j z)
    (fun a => le_trans (hs a) (hz a))
  obtain ⟨v,hv⟩ := rational_interval_initialized_complete dz ζ hc
  have hRun : rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z)=
      some (rationalReservoirAllocation s δ j z,v) := by
    simp only [rationalAllocationRun,dite_eq_left hz]
    change (rationalIntervalInitializedApproximation dz ζ).map
      (fun o => (rationalReservoirAllocation s δ j z,o))=some (rationalReservoirAllocation s δ j z,v)
    rw [hv]
    rfl
  have hSuccess : ∃ w,rationalReservoirSearch d s hs δ ζ j=some w := by
    rw [rationalReservoirSearch,rational_finite_select_success_iff]
    exact ⟨z,rational_allocation_nodes_complete k δ z,_,hRun⟩
  obtain ⟨w,hw⟩ := hSuccess
  have hmin := rational_reservoir_search_minimal d s hs δ ζ j w hw z _ hRun
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  have hU := rational_initialized_upper_lt_witness dz ζ hζ v hv hc
    (Fin.elim0,Fin.elim0,K,Fin.elim0) hClass
  change (v.bracket.2 : ℝ) <
    exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
      (blockWeights (fun a => (rationalReservoirAllocation s δ j z a : ℝ)) Fin.elim0)+(ζ : ℝ) at hU
  have hGlobal := rational_floor_reservoir_output_class d s Fin.elim0 hs hR δ ζ j w hw
  have hLower := floor_interval_game_value_le_witness d s Fin.elim0 _ hGlobal
  obtain ⟨zw,hzw⟩ := rational_reservoir_search_output d s hs δ ζ j w hw
  obtain ⟨_,_,_,hrows⟩ := rational_allocation_run_game d s hs ζ _ w hzw
  have hUpper : floorIntervalGameExploitability ((fun a => (w.1 a : ℝ)),w.2.realData) ≤
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) := by
    exact (exploitability_le_iff _ _ _).mpr hrows
  exact ⟨w,hw,le_trans hLower hUpper,by linarith⟩

end
end SparseCompletion

/- Fixed source body: RationalFloorSearch.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def rationalFloorSearch {k m : ℕ} (d : RationalIntervalParameters k m (Fin m))
    (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a) (δ ζ : ℚ) :
    Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if 0 < m then rationalAllocationSearch d s hs δ ζ else
    if hk : 0 < k then rationalReservoirSearch d s hs δ ζ ⟨0,hk⟩ else none

noncomputable section

theorem rational_floor_search_value_certificate {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalFloorSearch d s hs δ ζ=some w ∧
      floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) < floorIntervalGameValue d s u+
        (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  cases m with
  | zero =>
    have hk : 0 < k := by
      have hcard := Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin k ⊕ Fin 0))
      simp only [Fintype.card_sum,Fintype.card_fin] at hcard
      omega
    have hu0 : u=(Fin.elim0 : Fin 0 → ℚ) := funext fun i => Fin.elim0 i
    subst u
    obtain ⟨w,hw,hlo,hhi⟩ := rational_no_residual_global_certificate d s hs hR hne δ hδ ⟨0,hk⟩ ζ hζ
    refine ⟨w,?_,hlo,hhi⟩
    simpa only [rationalFloorSearch,show ¬0 < (0 : ℕ) by omega,ite_false,dite_eq_left hk] using hw
  | succ m =>
    obtain ⟨w,hw,hlo,hhi⟩ := rational_floor_grid_value_certificate d s u hs hu hR hne δ hδ
      ⟨0,Nat.zero_lt_succ m⟩ ζ hζ
    refine ⟨w,?_,hlo,hhi⟩
    simpa only [rationalFloorSearch,Nat.zero_lt_succ,ite_true] using hw

end
end SparseCompletion

/- Fixed source body: RationalFloorAccuracyParameters.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

def rationalFloorAllocationStep (M ε : ℚ) (k : ℕ) : ℚ := ε/(((6 : ℕ) : ℚ)*M*((k : ℚ)+1))

theorem rational_third_positive (ε : ℚ) (hε : 0 < ε) : 0 < ε/((3 : ℕ) : ℚ) :=
  div_pos hε (by norm_num)

theorem rational_floor_allocation_step_positive (M ε : ℚ) (k : ℕ)
    (hM : 0 < M) (hε : 0 < ε) : 0 < rationalFloorAllocationStep M ε k := by
  unfold rationalFloorAllocationStep
  positivity

theorem rational_floor_allocation_error_budget (M ε : ℚ) (k : ℕ)
    (hM : 0 < M) (hε : 0 < ε) :
    ((2 : ℕ) : ℚ)*M*k*rationalFloorAllocationStep M ε k+ε/((3 : ℕ) : ℚ)+ε/((3 : ℕ) : ℚ) ≤ ε := by
  have hd : 0 < ((6 : ℕ) : ℚ)*M*((k : ℚ)+1) := by positivity
  have hs : ((2 : ℕ) : ℚ)*M*k*(ε/(((6 : ℕ) : ℚ)*M*((k : ℚ)+1))) ≤ ε/((3 : ℕ) : ℚ) := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_pos hε hM]
  change ((2 : ℕ) : ℚ)*M*k*(ε/(((6 : ℕ) : ℚ)*M*((k : ℚ)+1)))+ε/((3 : ℕ) : ℚ)+ε/((3 : ℕ) : ℚ) ≤ ε
  linarith

def RationalIntervalParameters.withSlack {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (η : ℚ) (hη : 0 < η) :
    RationalIntervalParameters k m I := {d with η := η, positiveSlack := hη}

def rationalFloorApproximation {k m : ℕ} (d : RationalIntervalParameters k m (Fin m))
    (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a) (ε : ℚ) :
    Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if he : 0 < ε then
    rationalFloorSearch (d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε he)) s hs
      (rationalFloorAllocationStep d.M ε k) (ε/((3 : ℕ) : ℚ))
  else none

end SparseCompletion

/- Fixed source body: RationalFloorAutomatic.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_floor_approximation_global {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty) (ε : ℚ) (hε : 0 < ε) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalFloorApproximation d s hs ε=some w ∧
      floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+(ε : ℝ)/((3 : ℕ) : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(ε : ℝ)/((3 : ℕ) : ℝ) < floorIntervalGameValue d s u+(ε : ℝ) := by
  let de := d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε hε)
  obtain ⟨w,hw,hlo,hhi⟩ := rational_floor_search_value_certificate de s u hs hu hR hne
    (rationalFloorAllocationStep d.M ε k)
    (rational_floor_allocation_step_positive d.M ε k d.positiveBound hε)
    (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε hε)
  change floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) at hlo
  change (w.2.bracket.2 : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) < floorIntervalGameValue d s u+
    (2 : ℕ)*(d.M : ℝ)*k*(rationalFloorAllocationStep d.M ε k : ℝ)+
      ((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) at hhi
  push_cast at hlo hhi
  have hBudget : (2 : ℕ)*(d.M : ℝ)*k*(rationalFloorAllocationStep d.M ε k : ℝ)+
      (ε : ℝ)/((3 : ℕ) : ℝ)+(ε : ℝ)/((3 : ℕ) : ℝ) ≤ (ε : ℝ) := by
    exact_mod_cast rational_floor_allocation_error_budget d.M ε k d.positiveBound hε
  refine ⟨w,?_,hlo,?_⟩
  · simp only [rationalFloorApproximation,dite_eq_left hε]
    exact hw
  · linarith

end
end SparseCompletion

/- Fixed source body: RationalFloorTotalClass.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_floor_total_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (δ ζ : ℚ)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSearch d s hs δ ζ=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  by_cases hm : 0 < m
  · simp only [rationalFloorSearch,hm,ite_true] at hout
    exact rational_floor_search_output_class d s u hs hR δ ζ w hout
  · by_cases hk : 0 < k
    · simp only [rationalFloorSearch,hm,ite_false,dite_eq_left hk] at hout
      exact rational_floor_reservoir_output_class d s u hs hR δ ζ ⟨0,hk⟩ w hout
    · simp only [rationalFloorSearch,hm,ite_false,dite_eq_right hk] at hout
      cases hout

theorem rational_floor_approximation_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (ε : ℚ)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorApproximation d s hs ε=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  by_cases he : 0 < ε
  · simp only [rationalFloorApproximation,dite_eq_left he] at hout
    exact rational_floor_total_output_class
      (d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε he)) s u hs hR
      (rationalFloorAllocationStep d.M ε k) (ε/((3 : ℕ) : ℚ)) w hout
  · simp only [rationalFloorApproximation,dite_eq_right he] at hout
    cases hout

end
end SparseCompletion

/- Fixed source body: RationalFloorDecision.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
@[expose] public section
namespace SparseCompletion

theorem floor_interval_class_nonempty_actions {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hne : (floorIntervalGameClass d s u).Nonempty) : Nonempty (Fin k ⊕ Fin m) := by
  by_cases hk : 0 < k
  · exact ⟨Sum.inl ⟨0,hk⟩⟩
  · by_cases hm : 0 < m
    · exact ⟨Sum.inr ⟨0,hm⟩⟩
    · have hk0 : k=0 := by omega
      have hm0 : m=0 := by omega
      subst k
      subst m
      obtain ⟨z,hz⟩ := hne
      have hmass := hz.2.2.2.1
      norm_num at hmass

theorem rational_floor_approximation_none_iff {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (ε : ℚ) (hε : 0 < ε) :
    rationalFloorApproximation d s hs ε=none ↔ ¬(floorIntervalGameClass d s u).Nonempty := by
  constructor
  · intro hn hne
    let _ := floor_interval_class_nonempty_actions d s u hne
    obtain ⟨w,hw,_,_⟩ := rational_floor_approximation_global d s u hs hu hR hne ε hε
    rw [hn] at hw
    cases hw
  · intro hn
    cases hr : rationalFloorApproximation d s hs ε with
    | none => rfl
    | some w =>
      exact False.elim (hn ⟨_,rational_floor_approximation_output_class d s u hs hR ε w hr⟩)

theorem rational_floor_approximation_empty (d : RationalIntervalParameters 0 0 (Fin 0))
    (s : Fin 0 → ℚ) (hs : ∀ a,0 ≤ s a) (ε : ℚ) :
    rationalFloorApproximation d s hs ε=none := by
  simp [rationalFloorApproximation,rationalFloorSearch]

def rationalFloorClassDecision {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (ε : ℚ) (hε : 0 < ε) : Decidable (floorIntervalGameClass d s u).Nonempty :=
  (Option.rec (motive := fun o => rationalFloorApproximation d s hs ε=o →
      Decidable (floorIntervalGameClass d s u).Nonempty)
    (fun he => isFalse ((rational_floor_approximation_none_iff d s u hs hu hR ε hε).mp he))
    (fun w he => isTrue ⟨_,rational_floor_approximation_output_class d s u hs hR ε w he⟩)
    (rationalFloorApproximation d s hs ε)) rfl

end SparseCompletion

/- Fixed source body: RationalGapCompression.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
Constructive solver preparation: real compression at the actual rational grid.
No computational complexity claim. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

noncomputable def rationalSparseFeatures {k m : ℕ} {I : Type}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (i : Fin m) :
    (Fin k ⊕ (Fin (rationalGridSize M r η) ⊕ I)) → ℝ :=
  Sum.elim (fun a => ((-D i a : ℚ) : ℝ))
    (Sum.elim (fun l => ((max (rationalScore D p i-ρ-
      (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ))
      (fun a => (R.coefficient a i : ℝ)))

/-- Real compression preserves every actual finite-grid inequality and every
supplied linear physical constraint. The support bound uses the actual rational
node count, and includes the number of additional rows. -/
theorem rational_gap_real_compression {k m : ℕ} {I : Type} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (x : Fin m → ℝ)
    (hx : ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x)
    (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ)) :
    ∃ y : Fin m → ℝ,
      ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies y ∧
      (∀ i, 0 ≤ y i) ∧ (∑ i, y i)=(r : ℝ) ∧
      (∀ i, x i=0 → y i=0) ∧
      (Finset.univ.filter fun i => y i ≠ 0).card ≤
        min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  classical
  have hr : (0 : ℝ) ≤ (r : ℝ) := by
    rw [←hm]
    exact Finset.sum_nonneg fun i _ => hq i
  by_cases hz : (r : ℝ)=0
  · have hzero : x=fun _ => 0 := nonnegative_mass_zero x hq (by simpa only [hz] using hm)
    refine ⟨x,hx,hq,hm,fun _ hi => hi,?_⟩
    simp [hzero]
  · obtain ⟨y,hy,hym,hys,hyc,hyf⟩ := finite_feature_compression
      (Fin k ⊕ (Fin (rationalGridSize M r η) ⊕ I)) x
      (rationalSparseFeatures D p M r ρ η R) (r : ℝ) hq hm
      (lt_of_le_of_ne hr (Ne.symm hz))
    have hparts := (rational_linear_real_append_iff _ _ x).mp hx
    refine ⟨y,(rational_linear_real_append_iff _ _ y).mpr ⟨?_,?_⟩,
      hy,hym,hys,Nat.le_min.mpr ⟨?_,?_⟩⟩
    · intro row
      rcases row with i | row
      · change (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*y j) ≤ ((0 : ℚ) : ℝ)
        have he : (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*y j)= -y i := by
          calc
            _ = ∑ j, if j=i then -y j else 0 := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : j=i <;> simp [hj]
            _ = _ := by simp
        rw [he,Rat.cast_zero]
        exact neg_nonpos.mpr (hy i)
      · rcases row with a | row
        · by_cases ha : a.val=0
          · change (∑ j, ((if a.val=0 then (1 : ℚ) else -1 : ℚ) : ℝ)*y j) ≤
              ((if a.val=0 then r else -r : ℚ) : ℝ)
            simpa only [ha,ite_true,Rat.cast_one,one_mul] using le_of_eq hym
          · change (∑ j, ((if a.val=0 then (1 : ℚ) else -1 : ℚ) : ℝ)*y j) ≤
              ((if a.val=0 then r else -r : ℚ) : ℝ)
            simpa only [ha,ite_false,Rat.cast_neg,Rat.cast_one,neg_one_mul,
              Finset.sum_neg_distrib] using neg_le_neg (le_of_eq hym.symm)
        · rcases row with i | row
          · have hh := hparts.1 (.inr (.inr (.inl i)))
            simpa only [RationalLinearSystem.RealSatisfies,rationalGapSystem,
              rationalGapCoefficient,Sum.elim_inr,Sum.elim_inl,Rat.cast_zero,
              zero_mul,Finset.sum_const_zero] using hh
          · rcases row with a | l
            · have he := hyf (.inl a)
              change (∑ i, y i*((-D i a : ℚ) : ℝ))=∑ i, x i*((-D i a : ℚ) : ℝ) at he
              have hh := hparts.1 (.inr (.inr (.inr (.inl a))))
              change (∑ i, ((-D i a : ℚ) : ℝ)*y i) ≤ _
              change (∑ i, ((-D i a : ℚ) : ℝ)*x i) ≤ _ at hh
              calc
                _ = ∑ i, y i*((-D i a : ℚ) : ℝ) :=
                  Finset.sum_congr rfl fun _ _ => mul_comm _ _
                _ = _ := he
                _ ≤ _ := by simpa only [mul_comm] using hh
            · have he := hyf (.inr (.inl l))
              change (∑ i, y i*((max (rationalScore D p i-ρ-
                (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ))=
                ∑ i, x i*((max (rationalScore D p i-ρ-
                  (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ) at he
              have hh := hparts.1 (.inr (.inr (.inr (.inr l))))
              change (∑ i, ((max (rationalScore D p i-ρ-
                (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ)*y i) ≤ _
              change (∑ i, ((max (rationalScore D p i-ρ-
                (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ)*x i) ≤ _ at hh
              calc
                _ = ∑ i, y i*((max (rationalScore D p i-ρ-
                    (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ) :=
                  Finset.sum_congr rfl fun _ _ => mul_comm _ _
                _ = _ := he
                _ ≤ _ := by simpa only [mul_comm] using hh
    · intro a
      have he := hyf (.inr (.inr a))
      change (∑ i, y i*(R.coefficient a i : ℝ))=∑ i, x i*(R.coefficient a i : ℝ) at he
      change (∑ i, (R.coefficient a i : ℝ)*y i) ≤ _
      calc
        _ = ∑ i, y i*(R.coefficient a i : ℝ) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ = _ := he
        _ ≤ _ := by simpa only [mul_comm] using hparts.2 a
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using hyc

end SparseCompletion

/- Fixed source body: RationalSparseSupport.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
Finite support search uses the verified rational LP solver. It may be exponential. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSupportMask {m : ℕ} (z : Fin m → Fin 2) : Finset (Fin m) :=
  Finset.univ.filter fun i => (z i).val ≠ 0

def rationalSupportZeros {m : ℕ} (z : Fin m → Fin 2) : RationalLinearSystem (Fin m) m :=
  ⟨fun a i => if (z a).val=0 ∧ i=a then 1 else 0,fun _ => 0⟩

theorem rational_support_zeros_iff {m : ℕ} (z : Fin m → Fin 2) (q : Fin m → ℚ) :
    (rationalSupportZeros z).Satisfies q ↔ ∀ i, (z i).val=0 → q i ≤ 0 := by
  constructor
  · intro h i hi
    have hh := h i
    simpa only [RationalLinearSystem.Satisfies,rationalSupportZeros,hi,true_and,
      ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  · intro h i
    by_cases hi : (z i).val=0
    · simpa only [rationalSupportZeros,hi,true_and,ite_mul,one_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h i hi
    · simp only [rationalSupportZeros,hi,false_and,ite_false,zero_mul,
        Finset.sum_const_zero,le_refl]

theorem rational_support_zeros_real {m : ℕ} (z : Fin m → Fin 2) (x : Fin m → ℝ)
    (h : ∀ i, (z i).val=0 → x i=0) : (rationalSupportZeros z).RealSatisfies x := by
  intro a
  by_cases ha : (z a).val=0
  · change (∑ i, ((if (z a).val=0 ∧ i=a then (1 : ℚ) else 0 : ℚ) : ℝ)*x i) ≤ ((0 : ℚ) : ℝ)
    have he : (∑ i, ((if (z a).val=0 ∧ i=a then (1 : ℚ) else 0 : ℚ) : ℝ)*x i)=x a := by
      calc
        _ = ∑ i, if i=a then x i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i=a <;> simp [ha,hi]
        _ = _ := by simp
    rw [he,h a ha,Rat.cast_zero]
  · change (∑ i, ((if (z a).val=0 ∧ i=a then (1 : ℚ) else 0 : ℚ) : ℝ)*x i) ≤ ((0 : ℚ) : ℝ)
    simp only [ha,false_and,ite_false,Rat.cast_zero,zero_mul,Finset.sum_const_zero,le_refl]

theorem rational_support_card_of_zeros {m : ℕ} (z : Fin m → Fin 2) (q : Fin m → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hz : (rationalSupportZeros z).Satisfies q) :
    (Finset.univ.filter fun i => q i ≠ 0).card ≤ (rationalSupportMask z).card := by
  apply Finset.card_le_card
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i,?_⟩
  intro he
  exact (Finset.mem_filter.mp hi).2 (le_antisymm
    ((rational_support_zeros_iff z q).mp hz i he) (hq i))

noncomputable def realSupportIndex {m : ℕ} (x : Fin m → ℝ) : Fin m → Fin 2 :=
  fun i => if x i=0 then ⟨0,Nat.zero_lt_succ 1⟩ else ⟨1,Nat.lt_succ_self 1⟩

theorem real_support_index_zero {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    (realSupportIndex x i).val=0 ↔ x i=0 := by
  classical
  by_cases hi : x i=0 <;> simp [realSupportIndex,hi]

theorem real_support_index_mask {m : ℕ} (x : Fin m → ℝ) :
    rationalSupportMask (realSupportIndex x)=Finset.univ.filter (fun i => x i ≠ 0) := by
  classical
  ext i
  simp only [rationalSupportMask,Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr (real_support_index_zero x i)

end SparseCompletion

/- Fixed source body: RationalSparseGapSearch.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
An actual finite support search; no polynomial operation or bit-cost claim. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSparseGapRun {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (z : Fin m → Fin 2) :
    Option (Fin m → ℚ) :=
  if (rationalSupportMask z).card ≤ k+rationalGridSize M r η+Fintype.card I+1 then
    rationalGapSolve K D p M r ρ η (R.append (rationalSupportZeros z)) else none

def rationalSparseGapSearch {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) : Option (Fin m → ℚ) :=
  rationalFiniteSelect (rationalGridTuples m 2)
    (rationalSparseGapRun K D p M r ρ η R) (fun _ => 0)

theorem rational_sparse_gap_run_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (z : Fin m → Fin 2) (q : Fin m → ℚ)
    (hout : rationalSparseGapRun K D p M r ρ η R z=some q) :
    RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  unfold rationalSparseGapRun at hout
  split at hout
  next hc =>
    have h := rational_gap_solve_sound K D p M r ρ η (R.append (rationalSupportZeros z)) q hout
    have hg := (rational_gap_check_iff K D p q M r ρ η).mp h.1
    have hp := (rational_linear_append_iff _ _ q).mp h.2
    refine ⟨hg,hp.1,Nat.le_min.mpr ⟨?_,?_⟩⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (rational_support_card_of_zeros z q hg.1 hp.2) hc
  next => cases hout

theorem rational_sparse_gap_search_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ)
    (hout : rationalSparseGapSearch K D p M r ρ η R=some q) :
    RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  obtain ⟨z,_,hz⟩ := rational_finite_select_origin (rationalGridTuples m 2)
    (rationalSparseGapRun K D p M r ρ η R) (fun _ => 0) q hout
  exact rational_sparse_gap_run_sound K D p M r ρ η R z q hz

/-- Completeness needs a real feasible finite-grid point, rather than an input
rational sparse witness or an oracle for choosing a support. -/
theorem rational_sparse_gap_search_complete {k m : ℕ} {I : Type} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (x : Fin m → ℝ)
    (hx : ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x)
    (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ)) :
    ∃ q, rationalSparseGapSearch K D p M r ρ η R=some q := by
  classical
  obtain ⟨y,hy,_,_,_,hc⟩ := rational_gap_real_compression K D p M r ρ η R x hx hq hm
  let z := realSupportIndex y
  have hzc : (rationalSupportMask z).card ≤ k+rationalGridSize M r η+Fintype.card I+1 := by
    rw [show z=realSupportIndex y from rfl,real_support_index_mask]
    exact le_trans hc (min_le_right _ _)
  have hzero : (rationalSupportZeros z).RealSatisfies y :=
    rational_support_zeros_real z y (fun i hi => (real_support_index_zero y i).mp hi)
  have hparts := (rational_linear_real_append_iff _ _ y).mp hy
  obtain ⟨q,hq⟩ := rational_lp_real_complete m
    ((rationalGapSystem K D p M r ρ η).append (R.append (rationalSupportZeros z)))
    ⟨y,(rational_linear_real_append_iff _ _ y).mpr
      ⟨hparts.1,(rational_linear_real_append_iff _ _ y).mpr ⟨hparts.2,hzero⟩⟩⟩
  have hrun : rationalSparseGapRun K D p M r ρ η R z=some q := by
    simpa only [rationalSparseGapRun,ite_eq_left hzc,rationalGapSolve] using hq
  cases ho : rationalSparseGapSearch K D p M r ρ η R with
  | some q => exact ⟨q,rfl⟩
  | none =>
    have hn := (rational_finite_select_none_iff (rationalGridTuples m 2)
      (rationalSparseGapRun K D p M r ρ η R) (fun _ => 0)).mp ho z
      (rational_grid_tuples_complete m 2 z)
    rw [hrun] at hn
    cases hn

end SparseCompletion

/- Fixed source body: RationalSparseGapAlgorithm.lean -/
/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Returns actual rational strategy/payoff data; Fourier–Motzkin cost may be exponential. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSparseGapAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) :
    Option ((Fin m → ℚ) × (Fin m → Fin m → ℚ)) :=
  (rationalSparseGapSearch K D p M r ρ η R).bind (fun q =>
    (rationalResidualCompletion q (rationalScore D p) M (ρ+η)).map (fun B => (q,B)))

theorem rational_sparse_gap_algorithm_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B)) :
    R.Satisfies q ∧ RationalGapConditions K D p q M r ρ η ∧
      ResidualRatConditions q (rationalScore D p) M (ρ+η) B ∧
      (Finset.univ.filter fun i => q i ≠ 0).card ≤
        min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  cases hq : rationalSparseGapSearch K D p M r ρ η R with
  | none => simp only [rationalSparseGapAlgorithm,hq,Option.bind_none] at h; cases h
  | some y =>
    cases hB : rationalResidualCompletion y (rationalScore D p) M (ρ+η) with
    | none => simp only [rationalSparseGapAlgorithm,hq,Option.bind_some,hB,Option.map_none] at h; cases h
    | some C =>
      have hp : (y,C)=(q,B) := Option.some.inj (by
        simpa only [rationalSparseGapAlgorithm,hq,Option.bind_some,hB,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
      have hh := rational_sparse_gap_search_sound K D p M r ρ η R y hq
      exact ⟨hh.2.1,hh.1,
        rational_residual_completion_rat_sound y (rationalScore D p) M (ρ+η) C hB,hh.2.2⟩

theorem rational_sparse_gap_algorithm_complete {k m : ℕ} {I : Type} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (hM : 0 < M) (hη : 0 < η)
    (x : Fin m → ℝ)
    (hx : ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x)
    (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ)) :
    ∃ q B, rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B) := by
  obtain ⟨q,hq⟩ := rational_sparse_gap_search_complete K D p M r ρ η R x hx hq hm
  have hc := rational_sparse_gap_search_sound K D p M r ρ η R q hq
  obtain ⟨B,hB⟩ := rational_gap_reconstruction_complete K D p q M r ρ η hM hη
    ((rational_gap_check_iff K D p q M r ρ η).mpr hc.1)
  change rationalResidualCompletion q (rationalScore D p) M (ρ+η)=some B at hB
  exact ⟨q,B,by simp only [rationalSparseGapAlgorithm,hq,Option.bind_some,hB,Option.map_some]⟩

end SparseCompletion

/- Fixed source body: RationalSparseGapGame.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_sparse_gap_algorithm_full_game {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hK : ∀ a b, K a b= -K b a)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (R : RationalLinearSystem I m)
    (B : Fin m → Fin m → ℚ) (h : rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B)) :
    (∀ a, 0 ≤ blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a) ∧
    (∑ a, blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
    IsSkew (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ)) a b ∧
      blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
        (fun i j => (B i j : ℝ)) a b ≤ (M : ℝ)) ∧
    ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  have hs := rational_sparse_gap_algorithm_sound K D p M r ρ η R q B h
  have hc := hs.2.1
  have hB := (residual_rat_real_iff q (rationalScore D p) M (ρ+η) B).mp hs.2.2.1
  have hrows : ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
    apply (block_response_bounds_iff _ _ _ _ _ _).mpr
    constructor
    · intro a
      have hh : (rationalAnchorResponse K D p q a : ℝ) ≤ (ρ : ℝ) := by
        exact_mod_cast hc.2.2.2.1 a
      rw [rational_anchor_response_real] at hh
      have hηR : (0 : ℝ)<(η : ℝ) := by exact_mod_cast hη
      linarith
    · intro i
      have hi := hB.2.2 i
      simpa only [response,←rational_score_real,Rat.cast_add] using hi
  have hKR : IsSkew (fun h a => (K h a : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a)
    (fun i => by exact_mod_cast hc.1 i),?_,blockMatrix_skew _ _ _ hKR hB.1,
    blockMatrix_bounds _ _ _ _ hKbR hDbR hB.2.1,
    hrows⟩
  rw [blockWeights_mass]
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast hc.2.1
  rw [hm]
  exact_mod_cast hnorm

theorem rational_sparse_gap_algorithm_full_support {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B)) :
    (Finset.univ.filter fun a => blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a ≠ 0).card ≤
      min (k+m) ((2 : ℕ)*k+rationalGridSize M r η+Fintype.card I+1) := by
  classical
  have hc := (rational_sparse_gap_algorithm_sound K D p M r ρ η R q B h).2.2.2
  have hcR : (Finset.univ.filter fun i => (q i : ℝ) ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
    have he : (Finset.univ.filter fun i => (q i : ℝ) ≠ 0)=
        Finset.univ.filter (fun i => q i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Rat.cast_ne_zero]
    rw [he]
    exact hc
  rw [block_support_card]
  have hpa : (Finset.univ.filter fun a => (p a : ℝ) ≠ 0).card ≤ k :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  have h1 := le_trans hcR (min_le_left _ _)
  have h2 := le_trans hcR (min_le_right _ _)
  exact Nat.le_min.mpr ⟨by omega,by omega⟩

end SparseCompletion

/- Fixed source body: RationalFrozenPhysical.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
After rational K,D recovery, physical constraints become linear in q. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFrozenCoefficient {k m : ℕ} (D : Fin m → Fin k → ℚ)
    (j : Fin (m+(m*k+(k*k+0*m)))) (i : Fin m) : ℚ :=
  Sum.elim (fun a => if i=a then 1 else 0)
    (Sum.elim (fun a => if i=a.1 then D a.1 a.2 else 0)
      (Sum.elim (fun _ => 0) (fun a => Fin.elim0 a.1)))
    ((rationalIntervalVariableEquiv k m 0).symm j)

def rationalFrozenConstant {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (j : Fin (m+(m*k+(k*k+0*m)))) : ℚ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun a => K a.1 a.2) (fun a => Fin.elim0 a.1)))
    ((rationalIntervalVariableEquiv k m 0).symm j)

theorem rational_frozen_physical_eval {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (j : Fin (m+(m*k+(k*k+0*m)))) :
    (∑ i, rationalFrozenCoefficient D j i*q i)+rationalFrozenConstant K j=
      intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0 j := by
  unfold rationalFrozenCoefficient rationalFrozenConstant intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with a | v
  · simp only [Sum.elim_inl,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true,add_zero]
  · rcases v with a | v
    · simp only [Sum.elim_inr,Sum.elim_inl,ite_mul,zero_mul,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,add_zero]
      exact mul_comm _ _
    · rcases v with a | a
      · simp only [Sum.elim_inr,Sum.elim_inl,zero_mul,Finset.sum_const_zero,zero_add]
      · exact Fin.elim0 a.1

def rationalFrozenPhysicalSystem {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) : RationalLinearSystem I m where
  coefficient := fun a i => ∑ j, R.coefficient a j*rationalFrozenCoefficient D j i
  rightSide := fun a => R.rightSide a-∑ j, R.coefficient a j*rationalFrozenConstant K j

theorem rational_frozen_physical_system_iff {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (q : Fin m → ℚ) :
    (rationalFrozenPhysicalSystem K D R).Satisfies q ↔
      R.Satisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0) := by
  have he (a : I) : (∑ i, (∑ j, R.coefficient a j*rationalFrozenCoefficient D j i)*q i)+
      (∑ j, R.coefficient a j*rationalFrozenConstant K j)=
      ∑ j, R.coefficient a j*intervalPack q (fun i b => q i*D i b) K (H := 0) Fin.elim0 j := by
    simp_rw [←rational_frozen_physical_eval K D q,mul_add,Finset.sum_add_distrib,
      Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
  change (∀ a, (∑ i, (∑ j, R.coefficient a j*rationalFrozenCoefficient D j i)*q i) ≤
    R.rightSide a-(∑ j, R.coefficient a j*rationalFrozenConstant K j)) ↔ _
  constructor
  · intro h a
    rw [←he a]
    linarith [h a]
  · intro h a
    have hh := h a
    rw [←he a] at hh
    linarith

end SparseCompletion

/- Fixed source body: RationalIntervalSparseReduction.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
Freeze rational interval recovery before sparsification; no second gap slack. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem interval_physical_recovered_pack {k m H : ℕ}
    (lo hi : Fin m → Fin k → ℚ) (x : Fin (m+(m*k+(k*k+H*m))) → ℚ)
    (hV : ∀ i a, lo i a*intervalQ x i ≤ intervalV x i a ∧
      intervalV x i a ≤ hi i a*intervalQ x i) :
    intervalPhysicalVector x=intervalPack (intervalQ x)
      (fun i a => intervalQ x i*rationalIntervalRecover lo (intervalV x) (intervalQ x) i a)
      (intervalK x) (H := 0) Fin.elim0 := by
  have hprod := rational_interval_recovered_product lo hi (intervalV x) (intervalQ x) hV
  rw [interval_physical_projection]
  congr 1
  funext i a
  exact (hprod i a).symm

theorem rational_interval_sparse_reduction {k m : ℕ} {I : Type} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hx : RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
      M r ρ η (intervalAux x)) (hR : R.Satisfies (intervalPhysicalVector x)) :
    let D := rationalIntervalRecover lo (intervalV x) (intervalQ x)
    ∃ q B, rationalSparseGapAlgorithm (intervalK x) D p M r ρ η
      (rationalFrozenPhysicalSystem (intervalK x) D R)=some (q,B) := by
  let D := rationalIntervalRecover lo (intervalV x) (intervalQ x)
  have hg := (rational_interval_gap_recovered (intervalK x) lo hi (intervalV x) p
    (intervalQ x) M r ρ η hlu
    (rational_interval_point_gap loK hiK lo hi (intervalV x) (intervalK x) p
      (intervalQ x) M r ρ η (intervalAux x) hx).2.2).2
  have hR' : (rationalFrozenPhysicalSystem (intervalK x) D R).Satisfies (intervalQ x) := by
    apply (rational_frozen_physical_system_iff (intervalK x) D R (intervalQ x)).mpr
    rw [←interval_physical_recovered_pack lo hi x hx.2.2.1]
    exact hR
  have hsys : ((rationalGapSystem (intervalK x) D p M r ρ η).append
      (rationalFrozenPhysicalSystem (intervalK x) D R)).Satisfies (intervalQ x) :=
    (rational_linear_append_iff _ _ _).mpr
      ⟨(rational_gap_conditions_iff_linear _ D p _ M r ρ η).mp hg,hR'⟩
  apply rational_sparse_gap_algorithm_complete (intervalK x) D p M r ρ η _ hM hη
    (fun i => (intervalQ (α := ℚ) x i : ℝ))
    ((rational_linear_real_cast_iff _ _).mpr hsys)
    (fun i => by exact_mod_cast hg.1 i)
  exact_mod_cast hg.2.1

end SparseCompletion

/- Fixed source body: RationalIntervalSparseAlgorithm.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
Actual rational interval recovery and finite-support search. No polynomial cost. -/
@[expose] public section
namespace SparseCompletion

abbrev RationalSparseIntervalData (k m : ℕ) :=
  (Fin m → ℚ) × ((Fin k → Fin k → ℚ) ×
    ((Fin m → Fin k → ℚ) × (Fin m → Fin m → ℚ)))

def rationalIntervalSparseAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Option (RationalSparseIntervalData k m) :=
  (rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R)).bind
    (fun x =>
      let K := intervalK x
      let D := rationalIntervalRecover lo (intervalV x) (intervalQ x)
      (rationalSparseGapAlgorithm K D p M r ρ η (rationalFrozenPhysicalSystem K D R)).map
        (fun w => (w.1,(K,(D,w.2)))))

theorem rational_interval_sparse_algorithm_origin {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (q : Fin m → ℚ) (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalSparseAlgorithm loK hiK lo hi p M r ρ η R=some (q,(K,(D,B)))) :
    ∃ x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ,
      RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
        M r ρ η (intervalAux x) ∧ R.Satisfies (intervalPhysicalVector x) ∧
      K=intervalK x ∧ D=rationalIntervalRecover lo (intervalV x) (intervalQ x) ∧
      rationalSparseGapAlgorithm K D p M r ρ η (rationalFrozenPhysicalSystem K D R)=some (q,B) := by
  unfold rationalIntervalSparseAlgorithm at hout
  cases hx : rationalLPSolve _ (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R) with
  | none => simp only [hx,Option.bind_none] at hout; cases hout
  | some x =>
    cases hs : rationalSparseGapAlgorithm (intervalK x)
      (rationalIntervalRecover lo (intervalV x) (intervalQ x)) p M r ρ η
      (rationalFrozenPhysicalSystem (intervalK x)
        (rationalIntervalRecover lo (intervalV x) (intervalQ x)) R) with
    | none => simp only [hx,Option.bind_some,hs,Option.map_none] at hout; cases hout
    | some w =>
      have he : (w.1,(intervalK x,(rationalIntervalRecover lo (intervalV x) (intervalQ x),w.2)))=
          (q,(K,(D,B))) := Option.some.inj
        (by simpa only [hx,Option.bind_some,hs,Option.map_some] using hout)
      obtain ⟨hqw,hrest⟩ := Prod.mk.inj he
      obtain ⟨hK,hrest⟩ := Prod.mk.inj hrest
      obtain ⟨hD,hB⟩ := Prod.mk.inj hrest
      have hp := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp
        (rational_lp_solve_sound _ _ x hx)
      refine ⟨x,(rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hp.1,
        hp.2,hK.symm,hD.symm,?_⟩
      have hw : w=(q,B) := Prod.ext hqw hB
      simpa only [hK,hD,hw] using hs

theorem rational_interval_sparse_algorithm_real_complete {k m : ℕ} {I : Type} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x) :
    ∃ w, rationalIntervalSparseAlgorithm loK hiK lo hi p M r ρ η R=some w := by
  obtain ⟨x,hx⟩ := rational_lp_real_complete _ _ hf
  have hp := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp
    (rational_lp_solve_sound _ _ x hx)
  obtain ⟨q,B,hq⟩ := rational_interval_sparse_reduction loK hiK lo hi p M r ρ η R x hM hη hlu
    ((rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hp.1) hp.2
  exact ⟨(q,(intervalK x,(rationalIntervalRecover lo (intervalV x) (intervalQ x),B))),by
    simp only [rationalIntervalSparseAlgorithm,hx,Option.bind_some,hq,Option.map_some]⟩

end SparseCompletion

/- Fixed source body: RationalIntervalSparseConditions.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_sparse_algorithm_conditions {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (q : Fin m → ℚ) (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalSparseAlgorithm loK hiK lo hi p M r ρ η R=some (q,(K,(D,B)))) :
    R.Satisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0) ∧
    (∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
    (∀ i a, lo i a ≤ D i a ∧ D i a ≤ hi i a) ∧
    RationalGapConditions K D p q M r ρ η ∧
    ResidualRatConditions q (rationalScore D p) M (ρ+η) B ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  obtain ⟨x,hpoint,_,hK,hD,hs⟩ := rational_interval_sparse_algorithm_origin
    loK hiK lo hi p M r ρ η R q K D B hout
  have hg := rational_interval_point_gap loK hiK lo hi (intervalV x) (intervalK x) p
    (intervalQ x) M r ρ η (intervalAux x) hpoint
  have hd := (rational_interval_gap_recovered (intervalK x) lo hi (intervalV x) p
    (intervalQ x) M r ρ η hlu hg.2.2).1
  rw [←hK] at hg
  rw [←hD] at hd
  have hh := rational_sparse_gap_algorithm_sound K D p M r ρ η
    (rationalFrozenPhysicalSystem K D R) q B hs
  exact ⟨(rational_frozen_physical_system_iff K D R q).mp hh.1,hg.1,hg.2.1,hd,
    hh.2.1,hh.2.2.1,hh.2.2.2⟩

end SparseCompletion

/- Fixed source body: RationalIntervalSparseGame.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_sparse_algorithm_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ρ : ℚ)
    (q : Fin m → ℚ) (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r ρ d.η d.R=
      some (q,(K,(D,B)))) :
    ((fun i => (q i : ℝ)),(fun i a => (D i a : ℝ)),
      (fun a b => (K a b : ℝ)),(fun i j => (B i j : ℝ))) ∈ intervalGameClass d ∧
    (∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun a => (d.p a : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(d.η : ℝ)) ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize d.M d.r d.η+Fintype.card I+1) := by
  rcases rational_interval_sparse_algorithm_conditions d.loK d.hiK d.lo d.hi d.p d.M d.r
    ρ d.η d.R d.orderedCross q K D B hout with ⟨hR,hK,hKI,hDI,hg,hB,hc⟩
  have hBreal := (residual_rat_real_iff q (rationalScore D d.p) d.M (ρ+d.η) B).mp hB
  have hRR := (rational_linear_real_cast_iff d.R
    (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)).mpr hR
  have hpack : (fun j => (intervalPack (α := ℚ) q (fun i a => q i*D i a) K (H := 0) Fin.elim0 j : ℝ))=
      intervalPack (fun i => (q i : ℝ)) (fun i a => (q i : ℝ)*(D i a : ℝ))
        (fun a b => (K a b : ℝ)) (H := 0) Fin.elim0 := by
    funext j
    unfold intervalPack intervalVariableEncode
    generalize (rationalIntervalVariableEquiv k m 0).symm j=v
    rcases v with i | v
    · rfl
    · rcases v with a | v
      · exact Rat.cast_mul _ _
      · rcases v with a | a
        · rfl
        · exact Fin.elim0 a.1
  rw [hpack] at hRR
  have hclass := interval_game_class_of_witness d (fun i => (q i : ℝ))
    (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ)) (fun i j => (B i j : ℝ))
    (fun i => by exact_mod_cast hg.1 i) (by exact_mod_cast hg.2.1)
    (fun a b => by change (K a b : ℝ)= -(K b a : ℝ); exact_mod_cast hK a b)
    (fun a b => by exact_mod_cast hKI a b) (fun i a => by exact_mod_cast hDI i a)
    hBreal.1 hBreal.2.1 hRR
  obtain ⟨_,_,_,_,_,hs⟩ := rational_interval_sparse_algorithm_origin d.loK d.hiK d.lo d.hi d.p
    d.M d.r ρ d.η d.R q K D B hout
  have hfull := rational_sparse_gap_algorithm_full_game K D d.p q d.M d.r ρ d.η d.positiveSlack
    d.anchorNonneg d.normalized hK
    (fun a b => ⟨le_trans (d.coreLower a b) (hKI a b).1,
      le_trans (hKI a b).2 (d.coreUpper a b)⟩)
    (fun i a => ⟨le_trans (d.crossLower i a) (hDI i a).1,
      le_trans (hDI i a).2 (d.crossUpper i a)⟩)
    (rationalFrozenPhysicalSystem K D d.R) B hs
  exact ⟨hclass,hfull.2.2.2.2,hc⟩

end SparseCompletion

/- Fixed source body: RationalIntervalSparseApproximation.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
Sparse actual witnesses at the original interval bisection bracket. -/
@[expose] public section
namespace SparseCompletion

def rationalIntervalSparseApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) :
    Option ((ℚ × ℚ) × RationalSparseIntervalData k m) :=
  let z := rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
  (rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r z.2 d.η d.R).map
    (fun w => (z,w))

theorem rational_interval_sparse_approximation_origin {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) (z : ℚ × ℚ) (w : RationalSparseIntervalData k m)
    (hout : rationalIntervalSparseApproximation d n=some (z,w)) :
    z=rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n ∧
      rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r z.2 d.η d.R=some w := by
  cases ha : rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r
    (rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n).2 d.η d.R with
  | none => simp only [rationalIntervalSparseApproximation,ha,Option.map_none] at hout; cases hout
  | some v =>
    have he := Option.some.inj (by
      simpa only [rationalIntervalSparseApproximation,ha,Option.map_some] using hout)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨rfl,ha⟩

theorem rational_interval_sparse_approximation_complete {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) :
    ∃ z w, rationalIntervalSparseApproximation d n=some (z,w) := by
  have hz := rational_interval_search_bracket d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_interval_model_upper_feasible d)
  let z := rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
  obtain ⟨w,hw⟩ := rational_interval_sparse_algorithm_real_complete d.loK d.hiK d.lo d.hi d.p
    d.M d.r z.2 d.η d.R d.positiveBound d.positiveSlack d.orderedCross
    ((rational_linear_real_feasible_iff _).mpr hz.2.2.2.1)
  dsimp only [z] at hw
  exact ⟨z,w,by simp only [rationalIntervalSparseApproximation,hw,Option.map_some,z]⟩

theorem rational_interval_sparse_approximation_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (n : ℕ)
    (z : ℚ × ℚ) (w : RationalSparseIntervalData k m)
    (hout : rationalIntervalSparseApproximation d n=some (z,w)) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      z.2-z.1 ≤ d.M/((2 : ℕ) : ℚ)^n := by
  have hz := (rational_interval_sparse_approximation_origin d n z w hout).1
  obtain ⟨z',x,B,ha⟩ := rational_interval_model_approximation_complete d n
  have hz' := (rational_interval_approximation_output d n z' x B ha).1
  have hb := rational_interval_approximation_value_enclosure d n z' x B ha
  rw [hz',←hz] at hb
  exact hb

def rationalIntervalSparseAccurate {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :=
  rationalIntervalSparseApproximation d (rationalLogRounds d.M ζ)

theorem rational_interval_sparse_accurate_complete {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :
    ∃ z w, rationalIntervalSparseAccurate d ζ=some (z,w) :=
  rational_interval_sparse_approximation_complete d (rationalLogRounds d.M ζ)

theorem rational_interval_sparse_accurate_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (w : RationalSparseIntervalData k m)
    (hout : rationalIntervalSparseAccurate d ζ=some (z,w)) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  have hb := rational_interval_sparse_approximation_value_enclosure d (rationalLogRounds d.M ζ) z w hout
  have hw : z.2-z.1 < ζ := lt_of_le_of_lt hb.2.2 (rational_log_rounds_width d.M ζ hζ)
  have hwR : (z.2 : ℝ)-(z.1 : ℝ) < (ζ : ℝ) := by exact_mod_cast hw
  exact ⟨hb.1,hb.2.1,by linarith⟩

end SparseCompletion

/- Fixed source body: RationalIntervalSparseInitialized.lean -/
/- AI-assisted formalization under the repository Apache-2.0 license.
Physical compatibility and sparse value search form one actual rational program. -/
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSparseIntervalPackOutput {k m : ℕ}
    (w : (ℚ × ℚ) × RationalSparseIntervalData k m) : RationalIntervalRationalOutput k m where
  bracket := w.1
  q := w.2.1
  K := w.2.2.1
  D := w.2.2.2.1
  B := w.2.2.2.2

def rationalIntervalSparseInitialized {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) : Option (RationalIntervalRationalOutput k m) :=
  (rationalIntervalInitialize d).bind (fun model =>
    (rationalIntervalSparseAccurate model ζ).map rationalSparseIntervalPackOutput)

theorem rational_interval_sparse_initialized_origin {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalSparseInitialized d ζ=some o) :
    ∃ model, rationalIntervalInitialize d=some model ∧
      ∃ z w, rationalIntervalSparseAccurate model ζ=some (z,w) ∧
        o=rationalSparseIntervalPackOutput (z,w) := by
  cases hm : rationalIntervalInitialize d with
  | none => simp only [rationalIntervalSparseInitialized,hm,Option.bind_none] at hout; cases hout
  | some model =>
    cases ha : rationalIntervalSparseAccurate model ζ with
    | none => simp only [rationalIntervalSparseInitialized,hm,Option.bind_some,ha,Option.map_none] at hout; cases hout
    | some w =>
      have he : rationalSparseIntervalPackOutput w=o := Option.some.inj
        (by simpa only [rationalIntervalSparseInitialized,hm,Option.bind_some,ha,Option.map_some] using hout)
      exact ⟨model,rfl,w.1,w.2,ha,he.symm⟩

theorem rational_interval_sparse_initialized_complete {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (hc : d.Compatible) :
    ∃ o, rationalIntervalSparseInitialized d ζ=some o := by
  obtain ⟨z,w,hout⟩ := rational_interval_sparse_accurate_complete (d.toModel hc) ζ
  exact ⟨rationalSparseIntervalPackOutput (z,w),by
    simp only [rationalIntervalSparseInitialized,rational_interval_initialize_complete d hc,
      Option.bind_some,hout,Option.map_some]⟩

theorem rational_interval_sparse_initialized_none_iff {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) :
    rationalIntervalSparseInitialized d ζ=none ↔ ¬d.Compatible := by
  constructor
  · intro hn hc
    obtain ⟨o,ho⟩ := rational_interval_sparse_initialized_complete d ζ hc
    rw [hn] at ho
    cases ho
  · intro hn
    have hi := (rational_interval_initialize_none_iff d).mpr hn
    simp only [rationalIntervalSparseInitialized,hi,Option.bind_none]

theorem rational_interval_sparse_initialized_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalSparseInitialized d ζ=some o) :
    ∃ hc : d.Compatible,
      o.realData ∈ intervalGameClass (d.toModel hc) ∧
      (∀ a, response (intervalGameMatrix o.realData) (intervalGameWeights (d.toModel hc) o.realData) a ≤
        (o.bracket.2 : ℝ)+(d.η : ℝ)) ∧
      (Finset.univ.filter fun i => o.q i ≠ 0).card ≤
        min m (k+rationalGridSize d.M d.r d.η+Fintype.card I+1) := by
  obtain ⟨model,hm,z,w,ha,rfl⟩ := rational_interval_sparse_initialized_origin d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  have hAlg := (rational_interval_sparse_approximation_origin (d.toModel hc)
    (rationalLogRounds d.M ζ) z w ha).2
  exact ⟨hc,rational_interval_sparse_algorithm_game (d.toModel hc) z.2
    w.1 w.2.1 w.2.2.1 w.2.2.2 hAlg⟩

theorem rational_interval_sparse_initialized_value {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalParameters k m I)
    (ζ : ℚ) (hζ : 0 < ζ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalSparseInitialized d ζ=some o) :
    ∃ hc : d.Compatible,
      (o.bracket.1 : ℝ) ≤ intervalGameValue (d.toModel hc) ∧
      intervalGameValue (d.toModel hc) ≤ (o.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (o.bracket.2 : ℝ)+(d.η : ℝ)-(o.bracket.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  obtain ⟨model,hm,z,w,ha,rfl⟩ := rational_interval_sparse_initialized_origin d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  exact ⟨hc,rational_interval_sparse_accurate_value_enclosure (d.toModel hc) ζ hζ z w ha⟩

end SparseCompletion
