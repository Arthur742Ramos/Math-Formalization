module

public import Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

variable {V : Type*} (G : SimpleGraph V)

/-- Every pair in S has the indicated adjacency status. -/
@[expose] def Homogeneous (p : Prop) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (G.Adj x y ↔ p)

private theorem extendHomogeneous {S : Finset V} {v : V} {p : Prop}
    [DecidableEq V] (h : Homogeneous G p S) (hv : ∀ x ∈ S, G.Adj v x ↔ p) :
    Homogeneous G p (insert v S) := by
  intro x hx y hy hne
  rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
  · exact (hne rfl).elim
  · exact hv _ hy
  · exact (G.adj_comm _ _).trans (hv _ ((Finset.mem_insert.mp hx).resolve_left hne))
  · exact h _ hx _ hy hne

private def HasColor (p : Prop) (k : ℕ) (U : Finset V) : Prop :=
  ∃ S ⊆ U, S.card = k ∧ Homogeneous G p S

private theorem singletonColor {U : Finset V} (hu : U.Nonempty) (p : Prop) :
    HasColor G p 1 U := by
  classical
  obtain ⟨v, hv⟩ := hu
  refine ⟨{v}, by simpa, by simp, ?_⟩
  intro x hx y hy hne
  simp_all

/-- Two-colour Ramsey bound by successively restricting to neighbours or non-neighbours. -/
private theorem ramsey (a b : ℕ) (U : Finset V) (hU : 2 ^ (a + b) ≤ U.card) :
    HasColor G True (a + 1) U ∨ HasColor G False (b + 1) U := by
  classical
  have hu : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by positivity) hU)
  match a, b with
  | 0, _ => exact Or.inl (singletonColor G hu True)
  | _, 0 => exact Or.inr (singletonColor G hu False)
  | a+1, b+1 =>
    obtain ⟨v, hv⟩ := hu
    let R := U.erase v
    let A := R.filter (G.Adj v)
    let B := R.filter fun x => ¬ G.Adj v x
    have hsum : A.card + B.card = U.card - 1 := by
      rw [← Finset.card_erase_of_mem hv]
      exact Finset.card_filter_add_card_filter_not ..
    have hsize : 2 * 2 ^ (a + b + 1) ≤ U.card := by
      convert hU using 1
      rw [show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, pow_succ _ (a + b + 1), Nat.mul_comm]
    have hA : A ⊆ U := (Finset.filter_subset ..).trans (Finset.erase_subset ..)
    have hB : B ⊆ U := (Finset.filter_subset ..).trans (Finset.erase_subset ..)
    by_cases ha : 2 ^ (a + b + 1) ≤ A.card
    · rcases ramsey a (b+1) A (by simpa [Nat.add_assoc] using ha) with
        ⟨S, hS, hc, hp⟩ | ⟨S, hS, hc, hp⟩
      · have hmem (x) (hx : x ∈ S) := Finset.mem_filter.mp (hS hx : x ∈ A)
        have hnot : v ∉ S := fun hh => (Finset.mem_erase.mp (hmem _ hh).1).1 rfl
        exact Or.inl ⟨insert v S, Finset.insert_subset hv (hS.trans hA),
          by simp [hnot, hc], extendHomogeneous G hp fun x hx => iff_true_intro (hmem _ hx).2⟩
      · exact Or.inr ⟨S, hS.trans hA, hc, hp⟩
    · have hb : 2 ^ (a + 1 + b) ≤ B.card := by
        rw [show a+1+b = a+b+1 by omega]
        omega
      rcases ramsey (a+1) b B hb with ⟨S, hS, hc, hp⟩ | ⟨S, hS, hc, hp⟩
      · exact Or.inl ⟨S, hS.trans hB, hc, hp⟩
      · have hmem (x) (hx : x ∈ S) := Finset.mem_filter.mp (hS hx : x ∈ B)
        have hnot : v ∉ S := fun hh => (Finset.mem_erase.mp (hmem _ hh).1).1 rfl
        exact Or.inr ⟨insert v S, Finset.insert_subset hv (hS.trans hB),
          by simp [hnot, hc], extendHomogeneous G hp fun x hx => iff_false_intro (hmem _ hx).2⟩
termination_by a + b

private theorem homogeneous_class {p : Prop} {S : Finset V} (h : Homogeneous G p S) :
    ∃ d, degreeClass G S d = S := by
  classical
  by_cases hp : p
  · refine ⟨S.card - 1, Finset.filter_true_of_mem (fun x hx => ?_)⟩
    have he : S.filter (G.Adj x) = S.erase x := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact ⟨fun ⟨hy, ha⟩ => ⟨ha.ne.symm, hy⟩, fun ⟨hne, hy⟩ => ⟨hy, (h _ hx _ hy hne.symm).mpr hp⟩⟩
    simp [degreeOn, he, Finset.card_erase_of_mem hx]
  · refine ⟨0, Finset.filter_true_of_mem (fun x hx => ?_)⟩
    have he : S.filter (G.Adj x) = ∅ := by
      apply Finset.filter_false_of_mem
      intro y hy ha
      exact hp ((h _ hx _ hy ha.ne).mp ha)
    simp [degreeOn, he]

/-- Diagonal Ramsey bound with the colour of the witness retained. -/
theorem ramsey_colored_witness (a : ℕ) (U : Finset V) (hU : 4 ^ a ≤ U.card) :
    ∃ S ⊆ U, S.card = a + 1 ∧ (Homogeneous G True S ∨ Homogeneous G False S) := by
  have h : 2 ^ (a + a) ≤ U.card := by simpa [← two_mul, pow_mul] using hU
  rcases ramsey G a a U h with ⟨S,hs,hc,hp⟩ | ⟨S,hs,hc,hp⟩
  · exact ⟨S,hs,hc,Or.inl hp⟩
  · exact ⟨S,hs,hc,Or.inr hp⟩

theorem ramsey_regular_witness (a : ℕ) (U : Finset V) (hU : 4 ^ a ≤ U.card) :
    ∃ S ⊆ U, S.card = a + 1 ∧ ∃ d, degreeClass G S d = S := by
  obtain ⟨S,hs,hc,hp⟩ := ramsey_colored_witness G a U hU
  exact ⟨S,hs,hc,hp.elim (homogeneous_class G) (homogeneous_class G)⟩

theorem threshold_spec (k : ℕ) : Forces k (threshold k) := by
  change sInf {n | Forces k n} ∈ {n | Forces k n}
  apply Nat.sInf_mem
  refine ⟨4 ^ k, ?_⟩
  intro N h G
  obtain ⟨S, _, hs, d, hd⟩ := ramsey_regular_witness G k Finset.univ (by simpa using h.le)
  exact ⟨S, d, by rw [hd, hs]; omega⟩

theorem threshold_le {n k : ℕ} (h : Forces k n) : threshold k ≤ n := Nat.sInf_le h

end InducedDegreeRepetition
