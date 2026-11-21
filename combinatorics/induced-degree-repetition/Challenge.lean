module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs

public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs

@[expose] public section

namespace InducedDegreeRepetition

section
variable {V : Type*}

/-- The degree in the graph induced on S, when x belongs to S. -/
noncomputable def degreeOn (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ := by
  classical exact (S.filter (G.Adj x)).card

noncomputable def degreeClass (G : SimpleGraph V) (S : Finset V) (d : ℕ) : Finset V := by
  classical exact S.filter fun x => degreeOn G S x = d

/-- The paper's Theorem 1, with a witness for the repeated degree. -/
def LogScaleRepetition : Prop :=
  ∀ K : ℝ, 0 < K → ∀ η : ℝ, 0 < η → η < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ G : SimpleGraph (Fin N), ∃ S : Finset (Fin N), ∃ d : ℕ,
      ⌈K * Real.log N⌉₊ ≤ S.card ∧ S.card < 2 * ⌈K * Real.log N⌉₊ ∧
      (1 - η) * S.card ≤ ((degreeClass G S d).card : ℝ)

/-- Caro and Yuster use hosts of order strictly greater than n. -/
def Forces (k n : ℕ) : Prop :=
  ∀ N > n, ∀ G : SimpleGraph (Fin N), ∃ S : Finset (Fin N), ∃ d, k ≤ (degreeClass G S d).card

noncomputable def threshold (k : ℕ) : ℕ := sInf {n | Forces k n}

def SubexponentialThreshold : Prop :=
  (fun k : ℕ => Real.log (threshold k)) =o[Filter.atTop] (fun k : ℕ => (k : ℝ))

/-- Theorem 1 of the paper, for every positive logarithmic scale. -/
theorem logScale_repetition : LogScaleRepetition := by sorry

/-- Corollary 2 of the paper, with the strict host-size convention in Forces. -/
theorem subexponential_threshold : SubexponentialThreshold := by sorry

end

open Finset
open scoped Classical

section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def convolution (f g : G → ℝ) (z : G) : ℝ := ∑ x, f x * g (z-x)

def normSq (f : G → ℝ) : ℝ := ∑ x, f x ^ 2

noncomputable def massOn (w : G → ℝ) (A : Set G) : ℝ := by
  classical exact ∑ x, if x ∈ A then w x else 0

end

theorem coset_concentration (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℕ, ∀ {G : Type} [AddCommGroup G] [Fintype G], (∀ x : G, q • x = 0) →
      ∀ (f : G → ℝ), (∀ x, 0 ≤ f x) → (∑ x, f x) = 1 → ∀ D : ℝ, 2 ≤ D →
      normSq f / D^2 ≤ normSq (convolution f f) →
      ∃ (H : AddSubgroup G) (z : G), (Nat.card H : ℝ) ≤ D^C / normSq f ∧
        1 / D^C ≤ massOn f {x | x-z ∈ H} := by sorry

variable {V : Type*}

def tupleSpace (sets : List (Finset V)) : Finset (List V) :=
  sets.foldr (fun X tail => (X ×ˢ tail).map
    ⟨fun p => p.1 :: p.2, by rintro ⟨x,p⟩ ⟨y,q⟩ h; simpa using h⟩) {[]}

def tupleDegree (A : V → V → Bool) (y : V) (p : List V) : ℕ :=
  p.countP fun x => A y x

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
          mass * Q.card ≤ ((Q.filter fun p => tupleDegree A y p = highCount).card : ℝ) := by sorry

def TestModulus (L q : ℕ) : Prop := q = 4 ∨ (q.Prime ∧ 3 ≤ q ∧ q ≤ L)

def low (S : Finset ℤ) : ℤ := if h : S.Nonempty then S.min' h else 0
def high (S : Finset ℤ) : ℤ := if h : S.Nonempty then S.max' h else 0

theorem integer_totals (L₀ L : ℕ) :
    ∃ n₀ C : ℕ, ∀ {ι : Type} (I A B : Finset ι) (S : ι → Finset ℤ) (b : ι → ℤ),
      A ⊆ I → B ⊆ I → Disjoint A B → n₀ ≤ A.card → n₀ ≤ B.card →
      (∀ i ∈ I, (S i).Nonempty ∧ S i ⊆ Icc 0 (L : ℤ) ∧ b i ∈ Icc 0 (L : ℤ)) →
      (∀ i ∈ A, 1 < (S i).card ∧ S i ⊆ Icc 0 (L₀ : ℤ)) →
      (∀ i ∈ B, ∀ q, TestModulus L₀ q → ∃ x ∈ S i, ∃ y ∈ S i, ¬(q : ℤ) ∣ x-y) →
      ∀ z : ℤ, (∑ i ∈ I, low (S i)) + C ≤ z → z ≤ (∑ i ∈ I, high (S i)) - C →
      Even (z - ∑ i ∈ I, b i) →
      ∃ (f : ι → ℤ) (E : Finset ι), E ⊆ I ∧ E.card ≤ 1 ∧
        (∀ i ∈ I, i ∉ E → f i ∈ S i) ∧ (∀ i ∈ E, f i = b i) ∧ ∑ i ∈ I, f i = z := by sorry

theorem logScale_ramsey_range (K : ℝ) (hK : 0 < K) (hsmall : K * Real.log 4 ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) (G : SimpleGraph (Fin N)) :
    ∃ S : Finset (Fin N), S.card = ⌈K * Real.log N⌉₊ ∧ ∃ d, degreeClass G S d = S := by sorry

theorem subexponential_of_logScale (main : LogScaleRepetition) : SubexponentialThreshold := by sorry

end InducedDegreeRepetition
