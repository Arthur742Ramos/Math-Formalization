/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.CompletionCriterion

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
