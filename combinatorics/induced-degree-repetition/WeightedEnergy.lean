module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

public section
namespace InducedDegreeRepetition

open Finset
open scoped Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Counting-measure convolution, as in §3. -/
@[expose] def convolution (f g : G → ℝ) (z : G) : ℝ := ∑ x, f x * g (z-x)

/-- Squared counting-measure ℓ² norm. -/
@[expose] def normSq (f : G → ℝ) : ℝ := ∑ x, f x ^ 2

private theorem sum_convolution (f g : G → ℝ) :
    ∑ z, convolution f g z = (∑ x, f x) * ∑ y, g y := by
  simp only [convolution]
  rw [sum_comm, sum_mul]
  apply sum_congr rfl
  intro x _
  rw [← mul_sum]
  exact congrArg (f x * ·) ((Equiv.subRight x).sum_comp g)

private theorem comm_convolution (f g : G → ℝ) (z : G) : convolution f g z = convolution g f z := by
  apply Fintype.sum_equiv (Equiv.subLeft z)
  intro x
  simp [mul_comm]

private theorem convolution_nonneg {f g : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (z : G) : 0 ≤ convolution f g z := sum_nonneg fun x _ => mul_nonneg (hf x) (hg _)

private theorem convolution_mono {f f' g g' : G → ℝ} (hf : ∀ x, f x ≤ f' x)
    (hg : ∀ x, g x ≤ g' x) (hg₀ : ∀ x, 0 ≤ g x) (hf₀ : ∀ x, 0 ≤ f' x) (z : G) :
    convolution f g z ≤ convolution f' g' z :=
  sum_le_sum fun x _ => mul_le_mul (hf x) (hg _) (hg₀ _) (hf₀ _)

private theorem convolution_le_normSq (f : G → ℝ) (z : G) : convolution f f z ≤ normSq f := by
  have h := sum_le_sum (s := (univ : Finset G)) (fun x _ =>
    show 2*(f x * f (z-x)) ≤ (f x)^2 + (f (z-x))^2 by nlinarith [sq_nonneg (f x-f (z-x))])
  rw [← mul_sum,sum_add_distrib] at h
  have hs : (∑ x, f (z-x)^2) = ∑ x, f x^2 := (Equiv.subLeft z).sum_comp (fun x => (f x)^2)
  rw [hs] at h
  unfold convolution normSq
  linarith

private theorem cutoff_energy {f m lo hi : G → ℝ} {a b : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hm : ∀ x, 0 ≤ m x) (hl : ∀ x, 0 ≤ lo x) (hh : ∀ x, 0 ≤ hi x)
    (hsplit : ∀ x, f x = (m x + lo x) + hi x)
    (hmass : ∑ x, f x = 1) (hlow : ∀ x, lo x ≤ a) (hhigh : ∑ x, hi x ≤ b) :
    normSq (convolution f f) ≤ normSq (convolution m m) + 4*a + 4*normSq f*b := by
  let F := convolution f f
  let M := convolution m m
  let L := convolution f lo
  let H := convolution f hi
  have m_le (x) : m x ≤ f x := by linarith [hsplit x, hl x, hh x]
  have expand (g : G → ℝ) (z : G) :
      convolution g f z = convolution g m z + convolution g lo z + convolution g hi z := by
    unfold convolution
    simp_rw [hsplit (z-_),mul_add,sum_add_distrib]
  have bound (z) : F z ≤ M z + 2*L z + 2*H z := by
    have h₁ := expand f z
    rw [comm_convolution f m,expand m] at h₁
    have h₂ := convolution_mono m_le (fun x => le_refl (lo x)) hl hf z
    have h₃ := convolution_mono m_le (fun x => le_refl (hi x)) hh hf z
    dsimp [F,M,L,H]
    linarith
  have fsum : ∑ z, F z = 1 := by simp [F,sum_convolution,hmass]
  have hsum : ∑ z, H z ≤ b := by simpa [H,sum_convolution,hmass] using hhigh
  have lmax (z) : L z ≤ a := by
    calc
      _ ≤ ∑ x, f x * a := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hlow _) (hf _))
      _ = _ := by rw [← sum_mul,hmass,one_mul]
  have hpoint (z) : (F z)^2 ≤ (M z)^2 + 4*a*F z + 4*normSq f*H z := by
    have hmF : M z ≤ F z := convolution_mono m_le m_le hm hf z
    have hF := convolution_nonneg hf hf z
    have hH := convolution_nonneg hf hh z
    have hle := mul_le_mul_of_nonneg_right (bound z) hF
    have hL := mul_le_mul_of_nonneg_right (lmax z) hF
    have hH' := mul_le_mul_of_nonneg_right (convolution_le_normSq f z) hH
    change 0 ≤ F z at hF
    change 0 ≤ H z at hH
    change F z * H z ≤ _ at hH'
    nlinarith [sq_nonneg (F z - M z)]
  have h := sum_le_sum (s := (univ : Finset G)) (fun z _ => hpoint z)
  simp only [sum_add_distrib, ← mul_sum, fsum, mul_one] at h
  have hn : 0 ≤ normSq f := sum_nonneg fun x _ => sq_nonneg _
  exact h.trans (by dsimp [normSq,M] at *; nlinarith [mul_le_mul_of_nonneg_left hsum hn])

/-- The mass discarded from the upper tail costs little in ℓ¹; the lower tail costs
little in ℓ∞. This supplies a single set on which point masses are comparable. -/
theorem energy_band (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hmass : ∑ x, f x = 1)
    (D : ℝ) (hD : 2 ≤ D)
    (henergy : normSq f / D^2 ≤ normSq (convolution f f)) :
    ∃ A : Finset G, (∀ x ∈ A, normSq f / D^6 ≤ f x ∧ f x ≤ D^6*normSq f) ∧
      normSq f / D^3 ≤ normSq (convolution (fun x => if x ∈ A then f x else 0)
        (fun x => if x ∈ A then f x else 0)) := by
  classical
  let e := normSq f
  have he : 0 < e := by
    obtain ⟨x,hx⟩ : ∃ x, 0 < f x := by
      by_contra! h
      have hz (x) := (hf x).antisymm' (h x)
      simp [hz] at hmass
    exact lt_of_lt_of_le (sq_pos_of_pos hx)
      (single_le_sum (f := fun x => f x ^ 2) (fun x _ => sq_nonneg _) (mem_univ x))
  have dpos : 0 < D := by linarith
  have d1 : 1 ≤ D^6 := one_le_pow₀ (by linarith)
  let A := univ.filter fun x => e/D^6 ≤ f x ∧ f x ≤ D^6*e
  let mid := fun x => if x ∈ A then f x else 0
  let lo := fun x => if f x < e/D^6 then f x else 0
  let hi := fun x => if D^6*e < f x then f x else 0
  have order : e/D^6 ≤ D^6*e := (div_le_self he.le d1).trans (le_mul_of_one_le_left he.le d1)
  have nonnegRest (p : Prop) [Decidable p] (x) : 0 ≤ (if p then f x else 0) := by split <;> simp [hf]
  have split' (x) : f x = mid x + lo x + hi x := by
    dsimp [A,mid,lo,hi]
    by_cases h : f x < e/D^6
    · simp [h,h.not_ge,(h.trans_le order).not_gt]
    · by_cases h' : D^6*e < f x <;> simp [le_of_not_gt h, *]
  have htop : ∑ x, hi x ≤ 1/D^6 := by
    have hpoint (x) : hi x * (D^6*e) ≤ (f x)^2 := by
      dsimp [hi]
      split
      · rename_i h; nlinarith [mul_nonneg (hf x) (sub_nonneg.mpr h.le)]
      · simp [sq_nonneg]
    have h := sum_le_sum (s := (univ : Finset G)) (fun x _ => hpoint x)
    rw [← sum_mul] at h
    change (∑ x, hi x) * (D^6*e) ≤ e at h
    apply (le_div_iff₀ (pow_pos dpos 6)).mpr
    exact (mul_le_mul_iff_left₀ he).mp (by nlinarith only [h])
  have h := cutoff_energy hf (fun x => nonnegRest _ x) (fun x => nonnegRest _ x)
    (fun x => nonnegRest _ x) split' hmass
    (fun x => show lo x ≤ e/D^6 by dsimp [lo]; split <;> first | assumption | positivity | linarith)
    htop
  refine ⟨A,fun x hx => (mem_filter.mp hx).2,?_⟩
  change e/D^3 ≤ normSq (convolution mid mid)
  change normSq (convolution f f) ≤ normSq (convolution mid mid) + 4*(e/D^6) + 4*e*(1/D^6) at h
  change e/D^2 ≤ _ at henergy
  have hlow : e/D^3 + 4*(e/D^6) + 4*e*(1/D^6) ≤ e/D^2 := by
    field_simp
    have h₁ : 8 ≤ D^3 := by exact_mod_cast (show (2:ℝ)^3 ≤ D^3 from pow_le_pow_left₀ (by norm_num) hD _)
    have h₂ := mul_le_mul_of_nonneg_right hD (pow_nonneg dpos.le 3)
    nlinarith [mul_nonneg he.le (show 0 ≤ D^4-D^3-8 by nlinarith only [h₁,h₂])]
  linarith


/-- Number of ordered pairs in A with the given sum. -/
@[expose] noncomputable def representations (A : Finset G) (z : G) : ℕ := (A.filter fun x => z-x ∈ A).card

private theorem clipped_energy_le (A : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (b : ℝ) (hb : 0 ≤ b) (hfb : ∀ x ∈ A, f x ≤ b) :
    let m := fun x => if x ∈ A then f x else 0
    normSq (convolution m m) ≤ b^4 * ∑ z, (representations A z : ℝ)^2 := by
  classical
  intro m
  have hm (x) : 0 ≤ m x := by dsimp [m]; split <;> simp [hf]
  have hconv (z) : convolution m m z ≤ b^2 * (representations A z : ℝ) := by
    calc
      _ ≤ ∑ x, if x ∈ A ∧ z-x ∈ A then b^2 else 0 := by
        apply sum_le_sum
        intro x _
        by_cases hx : x ∈ A <;> by_cases hy : z-x ∈ A <;> simp [m,hx,hy]
        simpa [sq] using mul_le_mul (hfb x hx) (hfb _ hy) (hf _) hb
      _ = _ := by
        rw [← sum_filter,sum_const,nsmul_eq_mul,mul_comm]
        congr 2
        apply congrArg Finset.card
        ext x
        simp
  unfold normSq
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  calc
    _ ≤ (b^2 * (representations A z : ℝ))^2 :=
      pow_le_pow_left₀ (convolution_nonneg hm hm _) (hconv z) 2
    _ = _ := by ring

/-- Extract an unweighted high-energy set with explicit size and point-mass bounds.
This is the step needed to use the finite-set version of BSG for arbitrary weights. -/
theorem weighted_to_set_energy (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hmass : ∑ x, f x = 1)
    (D : ℝ) (hD : 2 ≤ D) (hE : normSq f / D^2 ≤ normSq (convolution f f)) :
    ∃ A : Finset G, 1/(D^9 * normSq f) ≤ A.card ∧ (A.card : ℝ) ≤ D^6 / normSq f ∧
      (∀ x ∈ A, normSq f / D^6 ≤ f x) ∧
      (A.card : ℝ)^3 / D^45 ≤ ∑ z, (representations A z : ℝ)^2 := by
  classical
  let e := normSq f
  have he : 0 < e := by
    obtain ⟨x,hx⟩ : ∃ x, 0 < f x := by
      by_contra! h
      have hz (x) := (hf x).antisymm' (h x)
      simp [hz] at hmass
    exact lt_of_lt_of_le (sq_pos_of_pos hx)
      (single_le_sum (f := fun x => f x ^ 2) (fun x _ => sq_nonneg _) (mem_univ x))
  have hp : 0 < D := by linarith
  obtain ⟨A,hA,henergy⟩ := energy_band f hf hmass D hD hE
  let m := fun x => if x ∈ A then f x else 0
  change e/D^3 ≤ normSq (convolution m m) at henergy
  have hm (x) : 0 ≤ m x := by dsimp [m]; split <;> simp [hf]
  have hmf (x) : m x ≤ f x := by dsimp [m]; split <;> simp [hf]
  have hsum : ∑ x, m x ≤ 1 := hmass ▸ sum_le_sum fun x _ => hmf x
  have hsumA : ∑ x, m x = ∑ x ∈ A, f x := by
    simp [m]
  have lower : (A.card : ℝ)*(e/D^6) ≤ ∑ x, m x := by
    rw [hsumA]
    simpa using sum_le_sum (s := A) (fun x hx => (hA x hx).1)
  have upper : (∑ x, m x) ≤ A.card*(D^6*e) := by
    rw [hsumA]
    simpa using sum_le_sum (s := A) (fun x hx => (hA x hx).2)
  have hcard : (A.card : ℝ) ≤ D^6/e := by
    apply (le_div_iff₀ he).mpr
    have h := lower.trans hsum
    rwa [← mul_div_assoc, div_le_iff₀ (pow_pos hp _), one_mul] at h
  have hnorm : normSq (convolution m m) ≤ e * ∑ x, m x := by
    calc
      _ ≤ ∑ z, e * convolution m m z := by
        apply sum_le_sum
        intro z _
        have hle := (convolution_mono hmf hmf hm hf z).trans (convolution_le_normSq f z)
        exact (sq (convolution m m z)) ▸ mul_le_mul_of_nonneg_right hle (convolution_nonneg hm hm z)
      _ = e * ((∑ x, m x)*(∑ x, m x)) := by rw [← mul_sum,sum_convolution]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (sum_nonneg fun x _ => hm x) hsum) he.le
  have hAlo : 1 / (D^9 * e) ≤ A.card := by
    have h := (henergy.trans hnorm).trans (mul_le_mul_of_nonneg_left upper he.le)
    apply (div_le_iff₀ (mul_pos (pow_pos hp _) he)).mpr
    have h' := (div_le_iff₀ (pow_pos hp _)).mp h
    apply (mul_le_mul_iff_right₀ he).mp
    calc
      e*1 = e := mul_one _
      _ ≤ _ := h'
      _ = _ := by ring
  refine ⟨A,hAlo,hcard,fun x hx => (hA x hx).1,?_⟩
  have h := henergy.trans (clipped_energy_le A f hf (D^6*e) (by positivity) (fun x hx => (hA x hx).2))
  calc
    _ ≤ (D^6/e)^3 / D^45 := by gcongr
    _ = (e/D^3)/(D^6*e)^4 := by field_simp
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by rwa [mul_comm] at h)

end InducedDegreeRepetition
