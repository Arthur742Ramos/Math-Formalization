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
