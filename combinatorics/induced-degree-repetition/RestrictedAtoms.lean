module

public import RandomRestrictions
public import AmplificationRates
public import ResidueAtoms
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Residues

open Finset Filter Duality Law OpenProblems
open scoped Classical Topology
variable {q : ℕ} [NeZero q] {V : Type}

theorem push_id {G : Type*} [Fintype G] [AddCommGroup G] (f : Law G) :
    f.push (AddMonoidHom.id G) = f := by
  apply ext_law
  intro z
  classical
  simp only [push,AddMonoidHom.id_apply]
  rw [show (univ.filter (fun x : G => x=z)) = {z} by ext; simp]
  simp

theorem typical_atom {J r : ℕ} (G : SimpleGraph V) (ys : Fin J → V) (l : List (Finset V))
    (a D A : ℝ) (j : ℕ) (len : l.length = 2^j)
    (nonempty : ∀ X ∈ l, X.Nonempty)
    (amp : ∀ f : Law (Fin J → ZMod q),
      (∀ H : AddSubgroup (Fin J → ZMod q), (Nat.card H:ℝ) ≤ Real.exp (D*r) →
        ∀ z, massOn f {x | x-z ∈ H} ≤ Real.exp (-a*r)) →
      quotientBound f j A 1 r)
    (good : ∀ X ∈ l, ¬ HeavyRestriction q G X ys r D a) (t : Fin J → ZMod q) :
    (((tupleSpace l).filter (fun P => ∀ i, (tupleDegree (adj G) (ys i) P : ZMod q) = t i)).card:ℝ) ≤
      Real.exp (-A*r)*(tupleSpace l).card := by
  classical
  let v := fun x i => adjMod q G x (ys i)
  let fs := l.map (poolLaw v)
  have leaf (f : Law (Fin J → ZMod q)) (hf : f ∈ fs) (z : Fin J → ZMod q) :
      f.iter j z ≤ Real.exp (-A*r) := by
    obtain ⟨X,hx,rfl⟩ := List.mem_map.mp hf
    have hs (H : AddSubgroup (Fin J → ZMod q)) (hH : (Nat.card H:ℝ) ≤ Real.exp (D*r)) (z') :
        massOn (poolLaw v X) {x | x-z' ∈ H} ≤ Real.exp (-a*r) := by
      have n := good X hx
      have h : ((X.filter (fun x => v x-z' ∈ H)).card:ℝ) ≤ Real.exp (-a*r)*X.card :=
        le_of_not_gt fun fail => n ⟨H,z',hH,fail⟩
      apply le_of_mul_le_mul_left (a := (X.card:ℝ)) _ (by exact_mod_cast card_pos.mpr (nonempty X hx))
      rw [pool_mass v X (fun x => x-z' ∈ H),mul_comm (X.card:ℝ)]
      exact h
    have h := amp (poolLaw v X) hs (Fin J → ZMod q) (AddMonoidHom.id _) Function.surjective_id
      (le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_exp_iff.mpr (by positivity))) z
    simpa only [push_id] using h
  have h := dyadic_mixed fs j _ (Real.exp_pos _).le (by simpa [fs] using len) leaf t
  have eq : (tupleSpace l).filter (fun P => ∀ i, (tupleDegree (adj G) (ys i) P : ZMod q) = t i) =
      (tupleSpace l).filter (fun P => vectorSum v P = t) := by
    ext P
    simp only [mem_filter,and_congr_right_iff]
    intro _
    rw [funext_iff]
    simp [v,sum_adj]
  rw [eq,mul_comm (Real.exp _)]
  apply le_trans _ (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (tupleSpace l).card))
  apply le_of_eq
  convert tuple_atom v l t using 1
  apply congrArg Nat.cast
  apply congrArg Finset.card
  ext P
  simp

theorem union_bad_lists {α : Type*} (L : List α) {X : Type*} (T : Finset X)
    (bad : α → X → Prop) (w : ℝ) (nn : 0 ≤ w)
    (per : ∀ i ∈ L, ((T.filter (bad i)).card:ℝ) ≤ w) :
    ((T.filter fun x => ∃ i ∈ L, bad i x).card:ℝ) ≤ L.length*w := by
  classical
  have sub : (T.filter fun x => ∃ i ∈ L, bad i x) ⊆ L.toFinset.biUnion (fun i => T.filter (bad i)) := by
    intro x hx
    obtain ⟨ht,i,hi,yes⟩ := mem_filter.mp hx
    exact mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr hi,mem_filter.mpr ⟨ht,yes⟩⟩
  have c := (card_le_card sub).trans (card_biUnion_le ..)
  calc
    _ ≤ ∑ i ∈ L.toFinset, ((T.filter (bad i)).card : ℝ) := by exact_mod_cast c
    _ ≤ ∑ _i ∈ L.toFinset, w := sum_le_sum fun i hi => per i (List.mem_toFinset.mp hi)
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right (Nat.cast_le.mpr L.toFinset_card_le) nn

end InducedDegreeRepetition.Residues
