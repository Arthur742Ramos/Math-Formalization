module
/-
Copyright (c) 2026. Licensed under Apache 2.0.
AI-assisted formalization of the anonymous manuscript
Sharp Sparse Witnesses for Incomplete Zero-Sum Games (revision 1a424f2).
Human authorship and responsible maintainer membership remain unconfirmed.
-/
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

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
