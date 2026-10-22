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
