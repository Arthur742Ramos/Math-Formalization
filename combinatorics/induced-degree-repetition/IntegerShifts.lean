module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition

open Finset
open scoped Pointwise

/-- The moduli in §5, including the special modulus four. -/
@[expose] def TestModulus (L q : ℕ) : Prop := q = 4 ∨ (q.Prime ∧ 3 ≤ q ∧ q ≤ L)

theorem exists_test_divisor {g L : ℕ} (hg : 3 ≤ g) (hL : g ≤ L) :
    ∃ q, TestModulus L q ∧ q ∣ g := by
  by_cases h4 : 4 ∣ g
  · exact ⟨4, Or.inl rfl, h4⟩
  have oddPrime {a : ℕ} (ha : a ≠ 1) (had : a ∣ g) (hodd : ¬ 2 ∣ a) :
      ∃ q, TestModulus L q ∧ q ∣ g := by
    obtain ⟨q,hq,hqa⟩ := Nat.exists_prime_and_dvd ha
    have hqg := hqa.trans had
    have hn : q ≠ 2 := fun hh => hodd (hh ▸ hqa)
    exact ⟨q, Or.inr ⟨hq, by have := hq.two_le; omega, (Nat.le_of_dvd (by omega) hqg).trans hL⟩, hqg⟩
  by_cases h2 : 2 ∣ g
  · obtain ⟨a, rfl⟩ := h2
    apply oddPrime (a := a) (by omega) (dvd_mul_left ..)
    omega
  · exact oddPrime (by omega) dvd_rfl h2

/-- Differences obtainable with the same number of copies of a single allowed set. -/
private def shifts (T : Set ℤ) : AddSubgroup ℤ where
  carrier := {e | ∃ (n : ℕ) (a b : ℤ), a ∈ n • T ∧ b ∈ n • T ∧ e = b - a}
  zero_mem' := ⟨0,0,0,by simp,by simp,by simp⟩
  add_mem' := by
    rintro u v ⟨n,a,b,ha,hb,rfl⟩ ⟨m,c,d,hc,hd,rfl⟩
    exact ⟨n+m,a+c,b+d,by rw [add_nsmul]; exact Set.add_mem_add ha hc,
      by rw [add_nsmul]; exact Set.add_mem_add hb hd, by omega⟩
  neg_mem' := by
    rintro u ⟨n,a,b,ha,hb,rfl⟩
    exact ⟨n,b,a,hb,ha,by omega⟩

/-- A repeated short/long pair admits two assignments whose totals differ by exactly two. -/
theorem two_step_block (L : ℕ) (S T : Finset ℤ)
    (hs : 1 < S.card) (hb : ∀ x ∈ S, 0 ≤ x ∧ x ≤ L) (ht : T.Nonempty)
    (hmod : ∀ q, TestModulus L q → ∃ x ∈ T, ∃ y ∈ T, ¬ (q : ℤ) ∣ x-y) :
    ∃ (n : ℕ) (a : ℤ), a ∈ n • ((S : Set ℤ) + T) ∧ a + 2 ∈ n • ((S : Set ℤ) + T) := by
  classical
  let D := (S - S) ∪ (T - T)
  let g := (D.gcd id).natAbs
  have hd {x : ℤ} (hx : x ∈ D) : (g : ℤ) ∣ x :=
    Int.natAbs_dvd.mpr (D.gcd_dvd (f := id) hx)
  obtain ⟨x,hx,y,hy,hne⟩ := Finset.one_lt_card.mp hs
  have hxy := hd (mem_union_left _ (Finset.mem_sub.mpr ⟨x,hx,y,hy,rfl⟩))
  have hpos : 0 < (x-y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hd' : g ∣ (x-y).natAbs := Int.ofNat_dvd_left.mp hxy
  have hgpos : 0 < g := by
    by_contra! he
    rw [show g = 0 by omega, zero_dvd_iff] at hd'
    omega
  have hgle : g ≤ L := by
    apply (Nat.le_of_dvd hpos hd').trans
    have hx' := hb x hx
    have hy' := hb y hy
    omega
  have hgsmall : g ≤ 2 := by
    by_contra! h
    obtain ⟨q,hq,hqg⟩ := exists_test_divisor h hgle
    obtain ⟨v,hv,w,hw,hn⟩ := hmod q hq
    exact hn ((Int.natCast_dvd_natCast.mpr hqg).trans
      (hd (mem_union_right _ (Finset.mem_sub.mpr ⟨v,hv,w,hw,rfl⟩))))
  have htwo : (2 : ℤ) ∈ AddSubgroup.closure (D : Set ℤ) := by
    rw [Int.closure_eq_zmultiples_finsetGcd, Int.mem_zmultiples_iff, ← Int.natAbs_dvd]
    change (g : ℤ) ∣ 2
    rcases (show g = 1 ∨ g = 2 by omega) with h | h <;> simp [h]
  let P := (S : Set ℤ) + T
  have hsingle {v w : ℤ} (hv : v ∈ P) (hw : w ∈ P) : v-w ∈ shifts P :=
    ⟨1,w,v,by rwa [one_nsmul],by rwa [one_nsmul],rfl⟩
  have hle : AddSubgroup.closure (D : Set ℤ) ≤ shifts P := by
    apply (AddSubgroup.closure_le _).mpr
    intro e he
    rcases mem_union.mp he with hS | hT
    · obtain ⟨v,hv,w,hw,rfl⟩ := Finset.mem_sub.mp hS
      obtain ⟨t,ht'⟩ := ht
      simpa using hsingle (Set.add_mem_add (s := (S : Set ℤ)) (t := (T : Set ℤ)) hv ht')
        (Set.add_mem_add hw ht')
    · obtain ⟨v,hv,w,hw,rfl⟩ := Finset.mem_sub.mp hT
      simpa using hsingle (Set.add_mem_add (s := (S : Set ℤ)) (t := (T : Set ℤ)) hx hv)
        (Set.add_mem_add hx hw)
  obtain ⟨n,a,b,ha,hb',hab⟩ := hle htwo
  exact ⟨n,a,ha,by convert hb' using 1; omega⟩

end InducedDegreeRepetition
