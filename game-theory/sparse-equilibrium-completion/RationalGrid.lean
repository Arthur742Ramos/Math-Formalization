/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GapCertificates
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Sqrt
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
