module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition

open Finset
open scoped Classical

variable {V : Type*}

/-- The atoms of the product law. Coordinates are ordered and may repeat. -/
@[expose] def tupleSpace : List (Finset V) → Finset (List V)
  | [] => {[]}
  | X :: tail => (X ×ˢ tupleSpace tail).map
      ⟨fun p => p.1 :: p.2, by rintro ⟨x,p⟩ ⟨y,q⟩ h; simpa using h⟩

private theorem tuple_length {sets : List (Finset V)} {p : List V} (hp : p ∈ tupleSpace sets) :
    p.length = sets.length := by
  induction sets generalizing p with
  | nil => simpa [tupleSpace] using congrArg List.length (mem_singleton.mp hp)
  | cons X tail ih =>
    obtain ⟨⟨x,q⟩,hq,rfl⟩ := mem_map.mp hp
    change (x :: q).length = _
    simpa using ih (mem_product.mp hq).2

/-- Number of coordinates failing the prescribed edge colour at a test vertex. -/
def misses (color : V → V → Prop) [DecidableRel color] (y : V) (p : List V) : ℕ :=
  p.countP fun x => decide (¬color x y)

section Process

variable (color : V → V → Prop) [DecidableRel color] (s τ : ℝ)

private def hit (U : Finset V) (x : V) := U.filter (color x)

private def bad (U : Finset V) (x : V) : Prop :=
  s ≤ U.card ∧ ((hit color U x).card : ℝ) < τ * U.card

private noncomputable def step (U : Finset V) (x : V) : Finset V := by
  classical exact if bad color s τ U x then U else hit color U x

private noncomputable def cost (U : Finset V) : List V → ℕ
  | [] => 0
  | x :: p => (if bad color s τ U x then 1 else 0) + cost (step color s τ U x) p
  decreasing_by simp_wf

private noncomputable def survivors (U : Finset V) : List V → Finset V
  | [] => U
  | x :: p => survivors (step color s τ U x) p
  decreasing_by simp_wf

private theorem step_sub (U : Finset V) (x : V) : step color s τ U x ⊆ U := by
  classical
  unfold step
  split
  · rfl
  · exact filter_subset ..

private theorem survival_spec (U : Finset V) (p : List V) :
    ∀ y ∈ survivors color s τ U p, y ∈ U ∧ misses color y p ≤ cost color s τ U p := by
  classical
  induction p generalizing U with
  | nil => intro y hy; exact ⟨by simpa [survivors] using hy,by simp [misses,cost]⟩
  | cons x p ih =>
    intro y hy
    rw [survivors] at hy
    obtain ⟨hu,hm⟩ := ih _ y hy
    refine ⟨step_sub _ _ _ _ _ hu, ?_⟩
    by_cases h : bad color s τ U x
    · simp only [misses,List.countP_cons] at hm ⊢
      simp only [cost,ite_eq_left h]
      split <;> omega
    · have hcol : color x y := (mem_filter.mp (show y ∈ hit color U x by simpa [step,h] using hu)).2
      simpa [misses,List.countP_cons,cost,h,hcol] using hm

private theorem survival_size (hτ : 0 ≤ τ) (hτ' : τ ≤ 1) (U : Finset V) (p : List V)
    (hlarge : s ≤ τ ^ p.length * U.card) :
    τ ^ p.length * U.card ≤ (survivors color s τ U p).card := by
  classical
  induction p generalizing U with
  | nil => simp [survivors]
  | cons x p ih =>
    have hnow : s ≤ U.card :=
      hlarge.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) (pow_le_one₀ hτ hτ'))
    have hstep : τ * U.card ≤ (step color s τ U x).card := by
      unfold step
      split
      · exact mul_le_of_le_one_left (Nat.cast_nonneg _) hτ'
      · rename_i hn; exact le_of_not_gt (fun h => hn ⟨hnow,h⟩)
    have hb := mul_le_mul_of_nonneg_left hstep (pow_nonneg hτ p.length)
    rw [← mul_assoc, ← pow_succ] at hb
    rw [survivors]
    exact hb.trans (ih _ (hlarge.trans hb))

private theorem exp_cost_bound (Y : Finset V) (sets : List (Finset V)) (w : ℝ)
    (hw : 1 ≤ w) (cut : ∀ X ∈ sets, ∀ U ⊆ Y,
      w * ((X.filter (bad color s τ U)).card : ℝ) ≤ X.card)
    (U : Finset V) (hU : U ⊆ Y) :
    (∑ p ∈ tupleSpace sets, w ^ cost color s τ U p) ≤
      2 ^ sets.length * (tupleSpace sets).card := by
  classical
  induction sets generalizing U with
  | nil => simp [tupleSpace,cost]
  | cons X tail ih =>
    let T := tupleSpace tail
    let F := fun x : V => w ^ (if bad color s τ U x then 1 else 0 : ℕ)
    have htail (x : V) := ih (fun X' hX' => cut X' (List.mem_cons_of_mem _ hX'))
      _ ((step_sub color s τ U x).trans hU)
    have hs : (∑ x ∈ X, F x) ≤ 2 * X.card := by
      have hcut := cut X (List.mem_cons_self ..) U hU
      simp only [F, apply_ite (HPow.hPow w), pow_one,pow_zero, sum_ite, sum_const, nsmul_eq_mul]
      have hsmall := card_filter_le X (fun x => ¬bad color s τ U x)
      nlinarith [show (((X.filter fun x => ¬bad color s τ U x).card : ℕ) : ℝ) ≤ X.card by exact_mod_cast hsmall]
    simp only [tupleSpace, sum_map, sum_product,
      card_map,card_product,Nat.cast_mul,List.length_cons]
    calc
      _ ≤ ∑ x ∈ X, F x * (2 ^ tail.length * T.card) := by
        apply sum_le_sum
        intro x _
        change (∑ p ∈ T, w ^ cost color s τ U (x :: p)) ≤ _
        simp only [cost, pow_add, ← mul_sum]
        exact mul_le_mul_of_nonneg_left (htail x) (pow_nonneg (by linarith : 0 ≤ w) _)
      _ ≤ (2 * X.card) * (2 ^ tail.length * T.card) := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by simp only [T,pow_succ]; ring

end Process

/-- Finite range estimate for one colour in Lemma 9. For any sufficiently large set Y
of possible exceptional testers, one member of Y has a low-miss atom in the conditional
law on Q. Applying the estimate to both colours supplies both ends of the range. -/
theorem range_atom (color : V → V → Prop) [DecidableRel color]
    (sets : List (Finset V)) (Q : Finset (List V)) (hQ : Q ⊆ tupleSpace sets)
    (Y : Finset V) (hY : Y.Nonempty) (s τ w : ℝ) (k : ℕ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1) (hw : 1 ≤ w)
    (hy : s ≤ τ ^ sets.length * Y.card) (hx : ∀ X ∈ sets, w*s ≤ X.card)
    (hcut : ∀ X ∈ sets, ∀ U ⊆ Y, s ≤ U.card → ∀ D ⊆ X, s ≤ D.card →
      (D.card : ℝ) * (τ * U.card) ≤ ∑ x ∈ D, ((U.filter (color x)).card : ℝ))
    (hfamily : 2 * (2 ^ sets.length * (tupleSpace sets).card : ℝ) ≤ Q.card * w ^ (k+1)) :
    ∃ y ∈ Y, ∃ c ≤ k, τ ^ sets.length * Q.card ≤
      2 * (k+1 : ℕ) * (((Q.filter fun p => misses color y p = c).card : ℕ) : ℝ) := by
  classical
  let D := fun (X U : Finset V) => X.filter (bad color s τ U)
  have density (X) (hX : X ∈ sets) (U) (hU : U ⊆ Y) : w * (D X U).card ≤ X.card := by
    suffices h : ((D X U).card : ℝ) ≤ s from
      (mul_le_mul_of_nonneg_left h (by linarith)).trans (hx X hX)
    by_contra! h
    have hne : (D X U).Nonempty := card_pos.mp (by exact_mod_cast hs.trans h)
    obtain ⟨x,hx'⟩ := (show (D X U).Nonempty from hne)
    have hthr := ((mem_filter.mp hx').2).1
    have hstrict := sum_lt_sum_of_nonempty hne (fun x h => ((mem_filter.mp (show x ∈ D X U from h)).2).2)
    rw [sum_const, nsmul_eq_mul] at hstrict
    exact hstrict.not_ge (hcut X hX U hU hthr (D X U) (filter_subset ..) h.le)
  let costY := cost color s τ Y
  let good := Q.filter fun p => costY p ≤ k
  let rare := Q.filter fun p => ¬costY p ≤ k
  have hmoment := exp_cost_bound color s τ Y sets w hw density Y Subset.rfl
  have hweight : 0 < w ^ (k+1) := by positivity
  have hmarkov : (rare.card : ℝ) * w ^ (k+1) ≤ 2 ^ sets.length * (tupleSpace sets).card := by
    calc
      _ = ∑ _p ∈ rare, w^(k+1) := by simp
      _ ≤ ∑ p ∈ rare, w^costY p := sum_le_sum fun p hp => pow_le_pow_right₀ hw
        (by have h := (mem_filter.mp hp).2; omega)
      _ ≤ ∑ p ∈ tupleSpace sets, w^costY p := sum_le_sum_of_subset_of_nonneg
        ((filter_subset ..).trans hQ) (fun _ _ _ => pow_nonneg (by linarith) _)
      _ ≤ _ := hmoment
  have hpartition : good.card + rare.card = Q.card := card_filter_add_card_filter_not ..
  have hhalf : (Q.card : ℝ) ≤ 2*good.card := by
    have hd : (2 * (rare.card : ℝ)) * w^(k+1) ≤ Q.card * w^(k+1) := by
      rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left hmarkov (by norm_num)).trans hfamily
    have hr : 2 * rare.card ≤ Q.card := by exact_mod_cast (le_of_mul_le_mul_right hd hweight)
    exact_mod_cast (show Q.card ≤ 2*good.card by omega)
  let count := fun y => (good.filter fun p => misses color y p ≤ k).card
  obtain ⟨y,hym,hymax⟩ := Y.exists_max_image count hY
  have avg : (good.card : ℝ) * (τ ^ sets.length * Y.card) ≤ Y.card * count y := by
    calc
      _ = ∑ _p ∈ good, τ ^ sets.length * (Y.card : ℝ) := by simp
      _ ≤ ∑ p ∈ good, ((Y.filter fun y' => misses color y' p ≤ k).card : ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpQ,hpk⟩ := mem_filter.mp hp
        have hl := tuple_length (hQ hpQ)
        have hsize := survival_size color s τ hτ hτ' Y p (by simpa [hl] using hy)
        rw [hl] at hsize
        apply hsize.trans
        apply Nat.cast_le.mpr
        apply card_le_card
        intro y' hy'
        obtain ⟨hyY,hm⟩ := survival_spec color s τ Y p y' hy'
        exact mem_filter.mpr ⟨hyY,hm.trans hpk⟩
      _ = ∑ y' ∈ Y, (count y' : ℝ) := by
        simp only [count, ← sum_boole]
        rw [sum_comm]
      _ ≤ Y.card * count y := by
        simpa using Y.sum_le_card_nsmul (fun y' => (count y' : ℝ)) (count y : ℝ)
          (fun z hz => Nat.cast_le.mpr (hymax z hz))
  have hypos : (0 : ℝ) < Y.card := by exact_mod_cast card_pos.mpr hY
  have hav : τ ^ sets.length * (good.card : ℝ) ≤ count y :=
    (mul_le_mul_iff_right₀ hypos).mp (by simpa only [mul_comm, mul_left_comm, mul_assoc] using avg)
  let freq := fun c => (Q.filter fun p => misses color y p = c).card
  obtain ⟨c,hc,hbest⟩ := (range (k+1)).exists_max_image freq (by simp)
  have hcount : count y ≤ (k+1) * freq c := by
    calc
      _ ≤ (Q.filter fun p => misses color y p ∈ range (k+1)).card := by
        apply card_le_card
        intro p hp
        obtain ⟨hp',hpk⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨(mem_filter.mp hp').1,mem_range.mpr (by omega)⟩
      _ = ∑ a ∈ range (k+1), freq a := (sum_card_fiberwise_eq_card_filter ..).symm
      _ ≤ _ := by simpa using (range (k+1)).sum_le_card_nsmul freq (freq c) hbest
  refine ⟨y,hym,c,by have := mem_range.mp hc; omega,?_⟩
  have hcount' : (count y : ℝ) ≤ (k+1 : ℕ) * (freq c : ℝ) := by exact_mod_cast hcount
  have h := mul_le_mul_of_nonneg_left hhalf (pow_nonneg hτ sets.length)
  dsimp [freq] at hcount'
  push_cast at *
  linarith

private theorem exp_dominates (a b : ℝ) (ha : 0 < a) :
    ∃ n : ℕ, ∀ r ≥ n, b ≤ Real.exp (a * (r : ℕ)) := by
  refine ⟨⌈b/a⌉₊,fun r hr => ?_⟩
  have h := (div_le_iff₀ ha).mp ((Nat.le_ceil _).trans (Nat.cast_le.mpr hr))
  linarith [Real.add_one_le_exp (a*r)]

/-- The large-r conclusion of Lemma 9 for one specified colour. The cut hypothesis is
stated for tester/position cuts only. Taking the two complementary colours gives the
low and high adjacency counts. The constants and threshold precede the host and Q. -/
theorem conditional_range_one_color (u τ θ : ℝ) (hu : 0 < u) (hτ : 0 < τ) (hτ' : τ ≤ 1)
    (hθ : 0 < θ) (L : ℕ) (D : ℝ) (hD : D ≤ θ * (u/16) * L / 10) :
    ∃ mass : ℝ, 0 < mass ∧ ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ {V : Type}
      (color : V → V → Prop) [DecidableRel color] (M : ℝ) (_hM : 0 < M)
      (sets : List (Finset V)) (Y : Finset V) (Q : Finset (List V)),
      sets.length = L → Q ⊆ tupleSpace sets →
      Real.exp (-D * r) * (tupleSpace sets).card ≤ Q.card →
      M * Real.exp (-u * r / 16) ≤ Y.card →
      (∀ X ∈ sets, M * Real.exp (-u * r / 16) ≤ X.card) →
      (∀ X ∈ sets, ∀ U ⊆ Y, M*Real.exp (-u*r) ≤ U.card → ∀ B ⊆ X,
        M*Real.exp (-u*r) ≤ B.card →
          (B.card : ℝ) * (τ * U.card) ≤ ∑ x ∈ B, ((U.filter (color x)).card : ℝ)) →
      ∃ E ⊆ Y, (E.card : ℝ) ≤ Real.exp (-u*r/4) * Y.card ∧ ∀ y ∈ Y, y ∉ E →
        ∃ c : ℕ, (c : ℝ) ≤ θ*L/5 ∧ mass * Q.card ≤
          ((Q.filter fun p => misses color y p = c).card : ℝ) := by
  classical
  let k := ⌊θ*L/5⌋₊
  have hk : θ*L/5 < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk' : (k:ℝ) ≤ θ*L/5 := Nat.floor_le (by positivity)
  let mass := τ^L / (2*((k:ℝ)+1))
  have hgap : 0 < ((k:ℝ)+1)*u/2-D := by
    nlinarith [mul_lt_mul_of_pos_right hk hu, mul_nonneg (mul_nonneg hθ.le hu.le) (Nat.cast_nonneg L)]
  obtain ⟨n,hn⟩ := exp_dominates _ (2*2^L) hgap
  obtain ⟨n',hn'⟩ := exp_dominates (11*u/16) (τ^L)⁻¹ (by positivity)
  refine ⟨mass, by dsimp [mass]; positivity, max n n', ?_⟩
  intro r hr V color _ M hM sets Y Q hl hQ hmass hy hx hcut
  let fail := fun y => ¬∃ c : ℕ, (c : ℝ) ≤ θ*L/5 ∧ mass * Q.card ≤
    ((Q.filter fun p => misses color y p = c).card : ℝ)
  let E := Y.filter fail
  refine ⟨E, filter_subset .., ?_, ?_⟩
  · by_contra! he
    have hU : M * Real.exp (-u*r) ≤ τ^L * E.card := by
      have hratio := hn' r (le_trans (le_max_right ..) hr)
      have powerpos : 0 < τ^L := pow_pos hτ _
      have hone : 1 ≤ τ^L * Real.exp (11*u/16*r) := by
        simpa [powerpos.ne'] using mul_le_mul_of_nonneg_left hratio powerpos.le
      calc
        _ ≤ (τ^L * Real.exp (11*u/16*r)) * (M*Real.exp (-u*r)) :=
          le_mul_of_one_le_left (by positivity) hone
        _ = τ^L * (Real.exp (-u*r/4) * (M * Real.exp (-u*r/16))) := by
          rw [show (11*u/16*r) = -u*r/4 + (-u*r/16) - (-u*r) by ring, Real.exp_sub,Real.exp_add]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_left hy (Real.exp_pos _).le).trans he.le) powerpos.le
    have hden (X) (hX : X ∈ sets) :
        Real.exp (u*r/2) * (M * Real.exp (-u*r)) ≤ X.card := by
      apply le_trans _ (hx X hX)
      rw [mul_left_comm, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hM.le
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hu.le (Nat.cast_nonneg r)]
    have hfamily : 2*(2^sets.length * (tupleSpace sets).card : ℝ) ≤
        Q.card * Real.exp (u*r/2)^(k+1) := by
      have hd := hn r (le_trans (le_max_left ..) hr)
      calc
        _ = (2*2^L : ℝ) * (tupleSpace sets).card := by rw [hl]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
        _ = (Real.exp (-D*r) * (tupleSpace sets).card) * Real.exp (u*r/2)^(k+1) := by
          rw [← Real.exp_nat_mul, show (((k:ℝ)+1)*u/2-D)*r = -D*r + ((k+1 : ℕ) : ℝ)*(u*r/2) by push_cast; ring,
            Real.exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmass (by positivity)
    have hene : E.Nonempty := card_pos.mp (by exact_mod_cast
      (lt_of_le_of_lt (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) he))
    obtain ⟨y,hye,c,hc,hfreq⟩ := range_atom color sets Q hQ E hene (M*Real.exp (-u*r))
      τ (Real.exp (u*r/2)) k (by positivity) hτ.le hτ'
      (Real.one_le_exp (by positivity)) (by rwa [hl]) hden
      (fun X hX U hU => hcut X hX U (hU.trans (filter_subset ..))) hfamily
    apply (mem_filter.mp hye).2
    refine ⟨c,(Nat.cast_le.mpr hc).trans hk',?_⟩
    rw [hl] at hfreq
    dsimp [mass]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    push_cast at hfreq
    linarith
  · intro y hy hye
    exact Classical.byContradiction fun h => hye (mem_filter.mpr ⟨hy,h⟩)

/-- The adjacency profile on a tuple counts coordinates, with repeated labels allowed. -/
@[expose] def tupleDegree (A : V → V → Bool) (y : V) (p : List V) : ℕ :=
  p.countP fun x => A y x

private theorem misses_false (A : V → V → Bool) (y : V) (p : List V) :
    misses (fun x y => A y x = false) y p = tupleDegree A y p := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp [misses,tupleDegree]

private theorem misses_true (A : V → V → Bool) (y : V) (p : List V) :
    misses (fun x y => A y x = true) y p + tupleDegree A y p = p.length := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp [misses,tupleDegree] at ih
    cases h : A y x <;> simp [misses,tupleDegree,h] <;> omega

/-- Lemma 9 under the two disjoint-cut density bounds inherited by the positional
and test sets. The statement permits every test-by-position Boolean matrix, including
adjacency restricted from a finite simple graph. -/
theorem conditional_range (u τ θ : ℝ) (hu : 0 < u) (hτ : 0 < τ) (hτ' : τ ≤ 1)
    (hθ : 0 < θ) (L : ℕ) (D : ℝ) (hD : D ≤ θ * (u/16) * L / 10) :
    ∃ β mass : ℝ, 0 < β ∧ 0 < mass ∧ ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ {V : Type}
      (A : V → V → Bool) (M : ℝ), 0 < M →
      ∀ (sets : List (Finset V)) (Y : Finset V) (Q : Finset (List V)),
      sets.length = L → Q ⊆ tupleSpace sets →
      Real.exp (-D*r) * (tupleSpace sets).card ≤ Q.card →
      M * Real.exp (-u*r/16) ≤ Y.card → (∀ X ∈ sets, M * Real.exp (-u*r/16) ≤ X.card) →
      (∀ b : Bool, ∀ X ∈ sets, ∀ U ⊆ Y, M*Real.exp (-u*r) ≤ U.card → ∀ B ⊆ X,
        M*Real.exp (-u*r) ≤ B.card → (B.card : ℝ) * (τ * U.card) ≤
          ∑ x ∈ B, ((U.filter fun y => A y x = b).card : ℝ)) →
      ∃ E ⊆ Y, (E.card : ℝ) ≤ Real.exp (-β*r) * Y.card ∧ ∀ y ∈ Y, y ∉ E →
        ∃ lowCount highCount : ℕ, (lowCount : ℝ) ≤ θ*L/5 ∧ (1-θ/5)*L ≤ (highCount : ℝ) ∧
          mass * Q.card ≤ ((Q.filter fun p => tupleDegree A y p = lowCount).card : ℝ) ∧
          mass * Q.card ≤ ((Q.filter fun p => tupleDegree A y p = highCount).card : ℝ) := by
  classical
  obtain ⟨m,hm,n,h⟩ := conditional_range_one_color u τ θ hu hτ hτ' hθ L D hD
  obtain ⟨n',hh⟩ := exp_dominates (u/8) 2 (by positivity)
  refine ⟨u/8,m,by positivity,hm,max n n',?_⟩
  intro r hr V A M hM sets Y Q hl hQ hfamily hy hx hcut
  have takeColor (b : Bool) := h r ((le_max_left ..).trans hr) (fun x y => A y x = b) M hM
    sets Y Q hl hQ hfamily hy hx (hcut b)
  obtain ⟨E₀,he₀,hc₀,h₀⟩ := takeColor false
  obtain ⟨E₁,he₁,hc₁,h₁⟩ := takeColor true
  refine ⟨E₀ ∪ E₁,union_subset he₀ he₁,?_,?_⟩
  · have hfac : 2*Real.exp (-u*r/4) ≤ Real.exp (-(u/8)*r) := by
      calc
        _ ≤ Real.exp (u/8*r)*Real.exp (-u*r/4) :=
          mul_le_mul_of_nonneg_right (hh r ((le_max_right ..).trans hr)) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hcount : ((E₀ ∪ E₁).card : ℝ) ≤ E₀.card + E₁.card := by exact_mod_cast card_union_le E₀ E₁
    exact hcount.trans ((add_le_add hc₀ hc₁).trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg Y.card)]))
  · intro y hyY hye
    obtain ⟨lo,hlo,hlo'⟩ := h₀ y hyY (fun hh => hye (mem_union_left _ hh))
    obtain ⟨c,hc,hc'⟩ := h₁ y hyY (fun hh => hye (mem_union_right _ hh))
    refine ⟨lo,L-c,hlo,?_,by simpa only [misses_false] using hlo',?_⟩
    · have hb : (L:ℝ) - c ≤ ((L-c : ℕ):ℝ) := by
        rcases le_total c L with h | h
        · rw [Nat.cast_sub h]
        · rw [Nat.sub_eq_zero_of_le h,Nat.cast_zero]
          exact sub_nonpos.mpr (Nat.cast_le.mpr h)
      linarith
    · apply hc'.trans
      apply Nat.cast_le.mpr
      apply card_le_card
      intro p hp
      obtain ⟨hpQ,hpc⟩ := mem_filter.mp hp
      have htot := misses_true A y p
      rw [tuple_length (hQ hpQ),hl,hpc] at htot
      exact mem_filter.mpr ⟨hpQ,by omega⟩

end InducedDegreeRepetition
