module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.LocallyConvex.Separation


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
