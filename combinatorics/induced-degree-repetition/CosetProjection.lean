module

public import DifferenceLaw
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality.Law

open Finset
open scoped Classical
variable {G K V : Type*} [Fintype G] [Fintype K] [Fintype V]

theorem push_comp (f : Law G) (p : G → K) (s : K → V) :
    (f.push p).push s = f.push (s ∘ p) := by
  classical
  apply ext_law
  intro z
  let v := fun t : V => if t = z then (1:ℝ) else 0
  have h := push_test (f.push p) s v
  have h' := push_test f p (fun x => v (s x))
  have e := (h.trans h').trans (push_test f (s ∘ p) v).symm
  simpa [v,mul_ite] using e

variable [AddCommGroup G] [AddCommGroup K]

theorem card_domain (p : G →+ K) (sur : Function.Surjective p) :
    Nat.card G = Nat.card p.ker * Fintype.card K := by
  have h := p.ker.card_mul_index
  rw [AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr sur] at h
  simpa [Nat.card_eq_fintype_card] using h.symm

theorem card_quotient (H : AddSubgroup K) :
    (Fintype.card K : ℝ) = Fintype.card (K ⧸ H)*(Nat.card H:ℝ) := by
  exact_mod_cast (by simpa [AddSubgroup.index_eq_card,Nat.card_eq_fintype_card] using H.index_mul_card.symm :
    Fintype.card K = Fintype.card (K ⧸ H)*Nat.card H)

theorem quotient_mass (f : Law K) (H : AddSubgroup K) (z : K) :
    massOn f {x | x-z ∈ H} = (f.push (QuotientAddGroup.mk' H)) (QuotientAddGroup.mk' H z) := by
  classical
  simp only [massOn,push,sum_filter,Set.mem_ofPred_eq]
  apply sum_congr rfl
  intro x _
  congr 1
  apply propext
  rw [← sub_eq_zero,← map_sub,← AddMonoidHom.mem_ker,QuotientAddGroup.ker_mk']

theorem push_atom_of_cosets (f : Law G) (p : G →+ K) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ z, massOn f {x | x-z ∈ p.ker} ≤ b) : ∀ y, (f.push p) y ≤ b := by
  classical
  intro y
  by_cases im : ∃ z, p z = y
  · obtain ⟨z,rfl⟩ := im
    convert h z using 1
    simp only [massOn,push,sum_filter,Set.mem_ofPred_eq,AddMonoidHom.mem_ker,map_sub,sub_eq_zero]
  · have u (x : G) : p x ≠ y := fun eq => im ⟨x,eq⟩
    simpa [push,u] using hb

end InducedDegreeRepetition.Duality.Law
