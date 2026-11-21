module

public import CosetMass
public import WeightedEnergy
import AddCombi.BSG
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

public section
namespace InducedDegreeRepetition

open Finset
open scoped Pointwise Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
private theorem representations_eq_pairs (A : Finset G) (z : G) :
    representations A z = ((A ×ˢ A).filter fun p => p.1+p.2 = z).card := by
  classical
  apply card_nbij' (fun x => (x,z-x)) Prod.fst
  · intro x hx
    simpa using (mem_filter.mp hx : x ∈ A ∧ z-x ∈ A)
  · rintro ⟨x,y⟩ h
    obtain ⟨hp,rfl⟩ := mem_filter.mp h
    simpa [add_comm] using mem_product.mp hp
  · intro _ _; rfl
  · rintro ⟨x,y⟩ h
    obtain ⟨_,rfl⟩ := mem_filter.mp h
    simp

private theorem bsg_card [DecidableEq G] (A : Finset G) (hA : A.Nonempty) (K : ℝ) (hK : 0 < K)
    (he : (A.card:ℝ)^3 / K ≤ ∑ z, (representations A z : ℝ)^2) :
    ∃ B ⊆ A, (A.card : ℝ) / (16*K) ≤ B.card ∧
      ((B-B).card : ℝ) ≤ 2^14*K^6*B.card := by
  classical
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have energy : (A.addEnergy' A : ℝ) =
      (∑ z, (representations A z : ℝ)^2) / (Fintype.card G : ℝ)^3 := by
    simp only [Finset.addEnergy'_eq_sum_sq,representations_eq_pairs]
    simp [NNRat.cast_sum, NNRat.cast_pow]
    congr 1
    funext z
    congr 3
    ext p
    simp
  have hdens (s : Finset G) : (s.dens : ℝ) = s.card / (Fintype.card G : ℝ) := by simp [dens]
  obtain ⟨B,hB,hsize,hsub⟩ := BSG_self' hK.le hA (K := K) (by
    rw [energy,hdens,div_pow,← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rwa [div_eq_inv_mul] at he)
  refine ⟨B,hB,?_,?_⟩
  · rw [hdens,hdens,← mul_div_assoc,div_le_div_iff_of_pos_right hcard] at hsize
    convert hsize using 1
    ring
  · rwa [hdens,hdens,← mul_div_assoc,div_le_div_iff_of_pos_right hcard] at hsub

omit [Fintype G] in
private theorem double_of_difference [DecidableEq G] (A : Finset G) (hA : A.Nonempty)
    (K : ℝ) (_hK : 0 ≤ K) (h : ((A-A).card:ℝ) ≤ K*A.card) :
    ((A+A).card : ℝ) ≤ K^2*A.card := by
  classical
  have hpl := pluennecke_ruzsa_inequality_nsmul_sub hA A 2
  rw [two_nsmul] at hpl
  have h' : ((A+A).card : ℝ) ≤ (((A-A).card : ℝ)/A.card)^2*A.card := by
    simpa [NNRat.cast_div, NNRat.cast_pow, NNRat.cast_mul] using (NNRat.cast_le (K := ℝ)).mpr hpl
  apply h'.trans
  gcongr
  exact (div_le_iff₀ (by exact_mod_cast card_pos.mpr hA)).mpr h

/-- Lemma 6, with counting measure, in the equivalent squared-norm form. The proof also
covers non-symmetric probability weights. The exponent depends only on the torsion bound. -/
theorem coset_concentration (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℕ, ∀ {G : Type} [AddCommGroup G] [Fintype G], (∀ x : G, q • x = 0) →
      ∀ (f : G → ℝ), (∀ x, 0 ≤ f x) → (∑ x, f x) = 1 → ∀ D : ℝ, 2 ≤ D →
      normSq f / D^2 ≤ normSq (convolution f f) →
      ∃ (H : AddSubgroup G) (z : G), (Nat.card H : ℝ) ≤ D^C / normSq f ∧
        1 / D^C ≤ massOn f {x | x-z ∈ H} := by
  classical
  let t := 568 * (256*q^3+1)
  let C := q+t+64
  refine ⟨C,?_⟩
  intro G _ _ htor f hf htotal D hD henergy
  have dpos : 0 < D := by linarith
  have d1 : 1 ≤ D := by linarith
  let e := normSq f
  have epos : 0 < e := by
    obtain ⟨x,hx⟩ : ∃ x, 0 < f x := by
      by_contra! h
      have hz (x) := (hf x).antisymm' (h x)
      simp [hz] at htotal
    exact lt_of_lt_of_le (sq_pos_of_pos hx)
      (single_le_sum (f := fun x => f x^2) (fun x _ => sq_nonneg _) (mem_univ x))
  obtain ⟨A,ha,hA,hpoint,hlarge⟩ := weighted_to_set_energy f hf htotal D hD henergy
  change 1/(D^9 * e) ≤ A.card at ha
  have apos : (0:ℝ) < A.card := (by positivity : 0 < 1/(D^9*e)).trans_le ha
  obtain ⟨B,hBA,hb,hB⟩ := bsg_card A (card_pos.mp (by exact_mod_cast apos)) (D^45)
    (by positivity) hlarge
  have bpos : (0:ℝ) < B.card := (by positivity : 0 < (A.card:ℝ)/(16*D^45)).trans_le hb
  have diff : ((B-B).card : ℝ) ≤ D^284*B.card := by
    apply hB.trans
    calc
      _ ≤ D^14 * (D^45)^6 * B.card := by gcongr
      _ = _ := by ring
  have hdbl := double_of_difference B (card_pos.mp (by exact_mod_cast bpos)) (D^284) (by positivity) diff
  have hset : (Nat.card ((B : Set G)+(B : Set G)) : ℝ) ≤ D^568 * (B : Set G).ncard := by
    simpa only [← coe_add,Nat.card_coe_set_eq,Set.ncard_coe_finset,← pow_mul] using hdbl
  obtain ⟨H,z,hH,hcover⟩ := coset_mass_of_small_doubling q hq htor f hf B
    (by simpa using card_pos.mp (by exact_mod_cast bpos : 0 < B.card)) (D^568) hset
  refine ⟨H,z,?_,?_⟩
  · change ((H : Set G).ncard : ℝ) ≤ _
    have hle : (H : Set G).ncard ≤ A.card := hH.trans (by simpa using card_le_card hBA)
    exact (Nat.cast_le.mpr hle).trans (hA.trans (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ d1 (by dsimp [C]; omega)) epos.le))
  · have hmB : (B.card:ℝ)*(e/D^6) ≤ massOn f B := by
      unfold massOn
      simpa using sum_le_sum (s := B) (fun x hx => hpoint x (hBA hx))
    have h16 : (16:ℝ) ≤ D^4 := by
      convert pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hD 4 using 1
      norm_num
    have hmin : 1 / D^64 ≤ massOn f B := by
      calc
        _ = 1/(D^4*D^45) * (1/(D^9*e)) * (e/D^6) := by field_simp
        _ ≤ 1/(16*D^45) * (A.card:ℝ) * (e/D^6) := by gcongr
        _ ≤ (B.card:ℝ)*(e/D^6) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rwa [one_div_mul_eq_div]
        _ ≤ _ := hmB
    let m := massOn f {x | x-z ∈ H}
    have hm : 0 ≤ m := by unfold m massOn; exact sum_nonneg fun x _ => by split <;> simp [hf]
    have qle : (q:ℝ) ≤ D^q := by
      have hq₂ : q ≤ 2^q := Nat.le_of_lt (Nat.lt_two_pow_self)
      exact (show (q:ℝ) ≤ (2:ℝ)^q by exact_mod_cast hq₂).trans (pow_le_pow_left₀ (by norm_num) hD _)
    have hlast : 1/D^64 ≤ D^(q+t)*m := by
      apply hmin.trans (hcover.trans _)
      rw [pow_add D q t, show D^t = (D^568)^(256*q^3+1) from pow_mul ..]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right qle (by positivity)) hm
    change 1/D^C ≤ m
    rw [div_le_iff₀ (pow_pos dpos _)]
    have h' := (div_le_iff₀ (pow_pos dpos _)).mp hlast
    simpa only [C,pow_add,mul_assoc,mul_left_comm,mul_comm] using h'

end InducedDegreeRepetition
