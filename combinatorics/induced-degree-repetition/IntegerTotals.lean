module

public import IntegerShifts
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition

open Finset
open scoped Pointwise

variable {ι : Type*}

private theorem subset_approx (I : Finset ι) (w : ι → ℤ) (L t : ℤ)
    (hL : 0 ≤ L) (hw : ∀ i ∈ I, 0 ≤ w i ∧ w i ≤ L)
    (ht : 0 ≤ t) (hbound : t ≤ ∑ i ∈ I, w i) :
    ∃ J ⊆ I, (∑ i ∈ J, w i) ≤ t ∧ t ≤ (∑ i ∈ J, w i) + L := by
  classical
  induction I using Finset.induction_on generalizing t with
  | empty => exact ⟨∅, by simp, by simpa, by simp_all; omega⟩
  | @insert i I hi ih =>
    have h := hw i (mem_insert_self ..)
    have hrest := fun j hj => hw j (mem_insert_of_mem hj)
    rw [sum_insert hi] at hbound
    by_cases ht' : t < w i
    · exact ⟨∅, empty_subset _, by simpa, by simp; omega⟩
    · obtain ⟨J,hJ,hj₁,hj₂⟩ := ih (t - w i) hrest (by omega) (by omega)
      exact ⟨insert i J, insert_subset_insert _ hJ,
        by rw [sum_insert (fun hj => hi (hJ hj))]; omega,
        by rw [sum_insert (fun hj => hi (hJ hj))]; omega⟩

/-- Approximate an even total from below by a subset sum with even parity. -/
private theorem even_subset_approx (I : Finset ι) (w : ι → ℤ) (L : ℕ) (t : ℤ)
    (hw : ∀ i ∈ I, 0 ≤ w i ∧ w i ≤ L) (ht : 0 ≤ t)
    (hbound : t ≤ ∑ i ∈ I, w i) (he : Even t) :
    ∃ J ⊆ I, ∃ j : ℕ, j ≤ L ∧ t = (∑ i ∈ J, w i) + 2 * j := by
  classical
  obtain ⟨J,hJ,hlo,hhi⟩ := subset_approx I w L t (by omega) hw ht hbound
  suffices ∃ S ⊆ I, Even (∑ i ∈ S, w i) ∧ (∑ i ∈ S, w i) ≤ t ∧
      t ≤ (∑ i ∈ S, w i) + 2 * L by
    obtain ⟨S,hS,⟨a,ha⟩,hl,hh⟩ := this
    obtain ⟨b,hb⟩ := he
    exact ⟨S,hS,(b-a).toNat,by omega,by omega⟩
  by_cases he' : Even (∑ i ∈ J, w i)
  · exact ⟨J,hJ,he',hlo,by omega⟩
  · obtain ⟨x,hx,ho⟩ : ∃ x ∈ J, ¬Even (w x) := by
      by_contra! h
      exact he' (even_iff_two_dvd.mpr (dvd_sum fun i hi => even_iff_two_dvd.mp (h i hi)))
    have hsum := sum_erase_add J w hx
    have h := hw x (hJ hx)
    refine ⟨J.erase x,(erase_subset ..).trans hJ,?_,by omega,by omega⟩
    rw [Int.even_iff] at *
    omega

/-- Minima and maxima of the nonempty sets in Lemma 10. -/
@[expose] def low (S : Finset ℤ) : ℤ := if h : S.Nonempty then S.min' h else 0
@[expose] def high (S : Finset ℤ) : ℤ := if h : S.Nonempty then S.max' h else 0

private theorem low_mem {S : Finset ℤ} (hs : S.Nonempty) : low S ∈ S := by simpa [low, hs] using S.min'_mem hs
private theorem high_mem {S : Finset ℤ} (hs : S.Nonempty) : high S ∈ S := by simpa [high, hs] using S.max'_mem hs
private theorem low_le_high {S : Finset ℤ} (hs : S.Nonempty) : low S ≤ high S := by
  simpa [low, hs] using S.min'_le _ (high_mem hs)

private theorem repeated_sum (I : Finset ι) {f : ι → Finset ℤ} {A : Finset ℤ}
    (h : ∀ i ∈ I, f i = A) :
    ∑ i ∈ I, (f i : Set ℤ) = I.card • (A : Set ℤ) := by
  rw [sum_congr rfl (g := fun _ => (A : Set ℤ)) fun i hi => by rw [h i hi], sum_const]

private theorem block_interval {P : Set ℤ} {n : ℕ} {a : ℤ}
    (ha : a ∈ n • P) (hb : a + 2 ∈ n • P) (m j : ℕ) (hj : j ≤ m) :
    (m : ℤ) * a + 2 * j ∈ (m * n) • P := by
  have h := Set.add_mem_add (Set.nsmul_mem_nsmul (n := m-j) ha) (Set.nsmul_mem_nsmul (n := j) hb)
  rw [← add_nsmul, Nat.sub_add_cancel hj, ← mul_nsmul] at h
  rw [Nat.mul_comm n m] at h
  convert h using 1
  simp [Nat.cast_sub hj]
  ring

/-- For a finite palette of short/long patterns, one bound works for the number of
copies needed to produce a difference of two. -/
private theorem uniform_blocks (L₀ L : ℕ) :
    ∃ B : ℕ, ∀ S ∈ (Icc (0 : ℤ) L).powerset, ∀ T ∈ (Icc (0 : ℤ) L).powerset,
      1 < S.card → (∀ x ∈ S, 0 ≤ x ∧ x ≤ (L₀ : ℤ)) → T.Nonempty →
      (∀ q, TestModulus L₀ q → ∃ x ∈ T, ∃ y ∈ T, ¬(q : ℤ) ∣ x-y) →
      ∃ n ≤ B, ∃ a : ℤ, a ∈ n • ((S : Set ℤ) + T) ∧ a+2 ∈ n • ((S : Set ℤ) + T) := by
  classical
  let palette := (Icc (0 : ℤ) L).powerset
  let Works (p : Finset ℤ × Finset ℤ) (n : ℕ) :=
    ∃ a : ℤ, a ∈ n • ((p.1 : Set ℤ) + p.2) ∧ a+2 ∈ n • ((p.1 : Set ℤ) + p.2)
  let need (p : Finset ℤ × Finset ℤ) := if h : ∃ n, Works p n then Nat.find h else 0
  refine ⟨(palette ×ˢ palette).sup need, ?_⟩
  intro S hS T hT hs hb ht hmod
  have h : ∃ n, Works (S,T) n := two_step_block L₀ S T hs hb ht hmod
  refine ⟨need (S,T), le_sup (mem_product.mpr ⟨hS,hT⟩), ?_⟩
  simpa only [need, dite_eq_left h] using Nat.find_spec h

/-- Extract disjoint sets of identical short and long positions. Doubling the number of
blocks makes both the starting total and the sum of the reserved minima even. -/
private theorem reserve (L₀ L : ℕ) :
    ∃ n₀ C : ℕ, ∀ {ι : Type} (I A B : Finset ι) (S : ι → Finset ℤ), A ⊆ I → B ⊆ I → Disjoint A B →
      n₀ ≤ A.card → n₀ ≤ B.card → (∀ i ∈ I, S i ⊆ Icc 0 (L : ℤ)) →
      (∀ i ∈ A, 1 < (S i).card ∧ S i ⊆ Icc 0 (L₀ : ℤ)) →
      (∀ i ∈ B, (S i).Nonempty ∧ ∀ q, TestModulus L₀ q →
        ∃ x ∈ S i, ∃ y ∈ S i, ¬ (q : ℤ) ∣ x-y) →
      ∃ R ⊆ I, R.card * L ≤ C ∧ Even (∑ i ∈ R, low (S i)) ∧
        ∃ a : ℤ, Even a ∧ ∀ j : ℕ, j ≤ L → a + 2*j ∈ ∑ i ∈ R, (S i : Set ℤ) := by
  classical
  obtain ⟨b,hb⟩ := uniform_blocks L₀ L
  let colors := (Icc (0 : ℤ) L).powerset
  let M := (2*L)*b
  refine ⟨colors.card * M + 1, (2*M)*L, ?_⟩
  intro ι I A B S hai hbi hd hA hB hr hshort hlong
  have pick (J : Finset ι) (hJ : J ⊆ I) (hc : colors.card * M < J.card) :
      ∃ X ∈ colors, M < (J.filter fun i => S i = X).card ∧ ∃ i ∈ J, S i = X := by
    obtain ⟨X,hX,hf⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := S) (fun i hi => mem_powerset.mpr (hr i (hJ hi))) hc
    obtain ⟨i,hi⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le M) hf)
    exact ⟨X,hX,hf,i,(mem_filter.mp hi).1,(mem_filter.mp hi).2⟩
  obtain ⟨X,hX,hxc,i,hi,hix⟩ := pick A hai hA
  obtain ⟨Y,hY,hyc,k,hk,hky⟩ := pick B hbi hB
  obtain ⟨hs,hr₀⟩ := hshort i hi
  obtain ⟨ht,hm⟩ := hlong k hk
  rw [hix] at hs hr₀
  rw [hky] at ht hm
  obtain ⟨n,hn,a,ha,ha'⟩ := hb X hX Y hY hs (fun v hv => mem_Icc.mp (hr₀ hv)) ht hm
  let m := (2*L)*n
  have hmb : m ≤ M := Nat.mul_le_mul_left _ hn
  obtain ⟨U,hU,hu⟩ := exists_subset_card_eq (hmb.trans hxc.le)
  obtain ⟨V,hV,hv⟩ := exists_subset_card_eq (hmb.trans hyc.le)
  have uA : U ⊆ A := hU.trans (filter_subset ..)
  have vB : V ⊆ B := hV.trans (filter_subset ..)
  have hUV := hd.mono uA vB
  have hux (i) (hi : i ∈ U) : S i = X := (mem_filter.mp (hU hi)).2
  have hvy (i) (hi : i ∈ V) : S i = Y := (mem_filter.mp (hV hi)).2
  refine ⟨U ∪ V, union_subset (uA.trans hai) (vB.trans hbi), ?_, ?_, (2*L : ℕ)*a, ?_, ?_⟩
  · rw [card_union_of_disjoint hUV,hu,hv]
    exact Nat.mul_le_mul_right L (by omega)
  · rw [sum_union hUV, sum_congr (s₁ := U) rfl (g := fun _ => low X) (fun i hi => by rw [hux i hi]),
      sum_congr (s₁ := V) rfl (g := fun _ => low Y) (fun i hi => by rw [hvy i hi]), sum_const, sum_const, hu,hv]
    refine ⟨(L*n : ℕ) * (low X + low Y), ?_⟩
    simp [m]
    ring
  · exact ⟨(L : ℤ)*a, by push_cast; ring⟩
  · intro j hj
    rw [sum_union hUV, repeated_sum U hux, repeated_sum V hvy, hu,hv, ← nsmul_add]
    exact block_interval ha ha' (2*L) j (by omega)

private theorem fill (L C : ℕ) (I R : Finset ι) (S : ι → Finset ℤ) (hR : R ⊆ I)
    (hsize : R.card * L ≤ C) (hne : ∀ i ∈ I, (S i).Nonempty) (hr : ∀ i ∈ I, S i ⊆ Icc 0 (L : ℤ))
    (he : Even (∑ i ∈ R, low (S i))) (a : ℤ) (ha : Even a)
    (hres : ∀ j : ℕ, j ≤ L → a + 2*j ∈ ∑ i ∈ R, (S i : Set ℤ))
    (z : ℤ) (hl : (∑ i ∈ I, low (S i)) + C ≤ z) (hh : z ≤ (∑ i ∈ I, high (S i)) - C)
    (hpar : Even (z - ∑ i ∈ I, low (S i))) : z ∈ ∑ i ∈ I, (S i : Set ℤ) := by
  classical
  let U := I \ R
  let lo := fun i => low (S i)
  let hi := fun i => high (S i)
  have hb (f : ι → ℤ) (hf : ∀ i ∈ R, f i ∈ S i) : 0 ≤ ∑ i ∈ R, f i ∧ (∑ i ∈ R, f i) ≤ C := by
    have h := fun i h => mem_Icc.mp (hr i (hR h) (hf i h))
    refine ⟨sum_nonneg fun i hi' => (h i hi').1, ?_⟩
    have hcard : (R.card : ℤ) * L ≤ C := by exact_mod_cast hsize
    exact (R.sum_le_card_nsmul f (L : ℤ) (fun i hi' => (h i hi').2)).trans hcard
  obtain ⟨v,hv,hvsum⟩ := (Set.mem_finsetSum R _ a).mp (by simpa using hres 0 (Nat.zero_le _))
  have hab := hb v (fun i hi' => hv hi')
  rw [hvsum] at hab
  have hlow := hb lo (fun i hi' => low_mem (hne i (hR hi')))
  have hhigh := hb hi (fun i hi' => high_mem (hne i (hR hi')))
  have hsl : (∑ i ∈ U, lo i) + (∑ i ∈ R, lo i) = ∑ i ∈ I, lo i := sum_sdiff hR
  have hsh : (∑ i ∈ U, hi i) + (∑ i ∈ R, hi i) = ∑ i ∈ I, hi i := sum_sdiff hR
  let t := z - a - ∑ i ∈ U, lo i
  change (∑ i ∈ I, lo i) + C ≤ z at hl
  change z ≤ (∑ i ∈ I, hi i) - C at hh
  change Even (∑ i ∈ R, lo i) at he
  change Even (z - ∑ i ∈ I, lo i) at hpar
  have heven : Even t := by
    obtain ⟨u,hu⟩ := he
    obtain ⟨v,hv⟩ := hpar
    obtain ⟨w,hw⟩ := ha
    exact ⟨v+u-w,by dsimp [t]; omega⟩
  obtain ⟨J,hJ,j,hj,hz⟩ := even_subset_approx U (fun i => hi i - lo i) L t
    (by
      intro i hi'
      have hI := sdiff_subset (show i ∈ I \ R from hi')
      have hl' := mem_Icc.mp (hr i hI (low_mem (hne i hI)))
      have hh' := mem_Icc.mp (hr i hI (high_mem (hne i hI)))
      exact ⟨sub_nonneg.mpr (low_le_high (hne i hI)), by dsimp [hi,lo]; omega⟩)
    (by dsimp [t]; omega) (by rw [sum_sub_distrib]; dsimp [t]; omega) heven
  let f := fun i => if i ∈ J then hi i else lo i
  have hf : (∑ i ∈ U, f i) ∈ ∑ i ∈ U, (S i : Set ℤ) :=
    (Set.mem_finsetSum _ _ _).mpr ⟨f,fun {i} hi' => by
      dsimp [f]
      split
      · exact high_mem (hne i (sdiff_subset hi'))
      · exact low_mem (hne i (sdiff_subset hi')),rfl⟩
  have hsum : (∑ i ∈ U, f i) = (∑ i ∈ U, lo i) + ∑ i ∈ J, (hi i - lo i) := by
    have splitSum : ∀ i, f i = lo i + (if i ∈ J then hi i-lo i else 0) := by
      intro i
      by_cases h : i ∈ J <;> simp [f,h]
    simp_rw [splitSum, sum_add_distrib, ← sum_filter]
    rw [show U.filter (· ∈ J) = J by ext i; simp; exact fun h => hJ h]
  rw [← sum_sdiff hR (f := fun i => (S i : Set ℤ))]
  have htot := Set.add_mem_add hf (hres j hj)
  convert htot using 1
  dsimp [t] at hz
  omega


/-- Lemma 10. A and B designate short and long positions in I. All other positions, if
present, need only have nonempty allowed sets within the long length. The exceptional
position may keep its original value even when that value is outside its allowed set. -/
theorem integer_totals (L₀ L : ℕ) :
    ∃ n₀ C : ℕ, ∀ {ι : Type} (I A B : Finset ι) (S : ι → Finset ℤ) (b : ι → ℤ),
      A ⊆ I → B ⊆ I → Disjoint A B → n₀ ≤ A.card → n₀ ≤ B.card →
      (∀ i ∈ I, (S i).Nonempty ∧ S i ⊆ Icc 0 (L : ℤ) ∧ b i ∈ Icc 0 (L : ℤ)) →
      (∀ i ∈ A, 1 < (S i).card ∧ S i ⊆ Icc 0 (L₀ : ℤ)) →
      (∀ i ∈ B, ∀ q, TestModulus L₀ q → ∃ x ∈ S i, ∃ y ∈ S i, ¬(q : ℤ) ∣ x-y) →
      ∀ z : ℤ, (∑ i ∈ I, low (S i)) + C ≤ z → z ≤ (∑ i ∈ I, high (S i)) - C →
      Even (z - ∑ i ∈ I, b i) →
      ∃ (f : ι → ℤ) (E : Finset ι), E ⊆ I ∧ E.card ≤ 1 ∧
        (∀ i ∈ I, i ∉ E → f i ∈ S i) ∧ (∀ i ∈ E, f i = b i) ∧ ∑ i ∈ I, f i = z := by
  classical
  obtain ⟨n,C,h⟩ := reserve L₀ L
  refine ⟨n+1,C+L,?_⟩
  intro ι I A B S b hA hB hd hna hnb hb hs hm z hlo hhi hpar
  let lo := fun i => low (S i)
  let hi := fun i => high (S i)
  have main (J A' B' : Finset ι) (hJ : J ⊆ I) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
      (haJ : A' ⊆ J) (hbJ : B' ⊆ J) (haN : n ≤ A'.card) (hbN : n ≤ B'.card)
      (v : ℤ) (hl : (∑ i ∈ J, lo i) + C ≤ v) (hh : v ≤ (∑ i ∈ J, hi i) - C)
      (he : Even (v - ∑ i ∈ J, lo i)) : ∃ f : ι → ℤ, (∀ i ∈ J, f i ∈ S i) ∧ ∑ i ∈ J, f i = v := by
    obtain ⟨R,hR,hsize,heven,a,ha,hres⟩ := h J A' B' S haJ hbJ (hd.mono hA' hB') haN hbN
      (fun i hi' => (hb i (hJ hi')).2.1) (fun i hi' => hs i (hA' hi'))
      (fun i hi' => ⟨(hb i (hJ (hbJ hi'))).1,hm i (hB' hi')⟩)
    obtain ⟨f,hf,hv⟩ := (Set.mem_finsetSum J _ _).mp (fill L C J R S hR hsize
      (fun i hi' => (hb i (hJ hi')).1) (fun i hi' => (hb i (hJ hi')).2.1)
      heven a ha hres v hl hh he)
    exact ⟨f,fun i hi' => hf hi',hv⟩
  change (∑ i ∈ I, lo i) + ↑(C+L) ≤ z at hlo
  change z ≤ (∑ i ∈ I, hi i) - ↑(C+L) at hhi
  by_cases he : Even (z - ∑ i ∈ I, lo i)
  · obtain ⟨f,hf,hv⟩ := main I A B Subset.rfl Subset.rfl Subset.rfl hA hB (by omega) (by omega)
      z (by omega) (by omega) he
    exact ⟨f,∅,empty_subset _,by simp,fun i hi' _ => hf i hi',by simp,hv⟩
  · obtain ⟨e,heI,he'⟩ : ∃ e ∈ I, ¬Even (b e - lo e) := by
      by_contra! hall
      have hdiff := even_iff_two_dvd.mpr (dvd_sum (s := I) fun i hi' => even_iff_two_dvd.mp (hall i hi'))
      rw [sum_sub_distrib] at hdiff
      exact he (by obtain ⟨v,hv⟩ := hpar; obtain ⟨w,hw⟩ := hdiff; exact ⟨v+w,by omega⟩)
    have bbound := mem_Icc.mp (hb e heI).2.2
    have lbound := mem_Icc.mp ((hb e heI).2.1 (low_mem (hb e heI).1))
    have ubound := mem_Icc.mp ((hb e heI).2.1 (high_mem (hb e heI).1))
    change 0 ≤ lo e ∧ lo e ≤ L at lbound
    change 0 ≤ hi e ∧ hi e ≤ L at ubound
    have sl := I.sum_erase_add lo heI
    have sh := I.sum_erase_add hi heI
    have eraseCount (U : Finset ι) (hu : n+1 ≤ U.card) : n ≤ (U.erase e).card := by
      by_cases h : e ∈ U
      · rw [card_erase_of_mem h]; omega
      · simpa [erase_eq_of_notMem h] using (show n ≤ U.card by omega)
    obtain ⟨g,hg,ht⟩ := main (I.erase e) (A.erase e) (B.erase e) (erase_subset ..)
      (erase_subset ..) (erase_subset ..) (erase_subset_erase _ hA) (erase_subset_erase _ hB)
      (eraseCount A hna) (eraseCount B hnb) (z-b e) (by omega) (by omega) (by
        simp only [Int.even_iff] at he he' ⊢
        omega)
    let f := Function.update g e (b e)
    refine ⟨f,{e}, by simpa,by simp,?_,by simp [f],?_⟩
    · intro i hI hne
      have hn : i ≠ e := by simpa using hne
      simpa [f,Function.update_of_ne hn] using hg i (mem_erase.mpr ⟨hn,hI⟩)
    · rw [← I.sum_erase_add f heI, sum_congr (s₁ := I.erase e) rfl (g := g)
        (fun i hi' => Function.update_of_ne (mem_erase.mp hi').1 _ _), ht]
      simp [f]

end InducedDegreeRepetition
