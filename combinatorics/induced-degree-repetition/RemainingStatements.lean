module

public import Statement
public import CountRange
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Statement interfaces for the open parts of Sections 2–5. -/
@[expose] public section
namespace InducedDegreeRepetition
namespace OpenProblems

open Finset Filter Matrix
open scoped Classical Topology

variable {V : Type*}

noncomputable def adj (G : SimpleGraph V) (x y : V) : Bool := decide (G.Adj x y)

/-- Each colour occupies at least a τ proportion of every disjoint cut above the cutoff. -/
def CutBounds (G : SimpleGraph V) (B : Finset V) (s τ : ℝ) : Prop :=
  ∀ X ⊆ B, ∀ Y ⊆ B, Disjoint X Y → s ≤ X.card → s ≤ Y.card → ∀ b : Bool,
    τ * X.card * Y.card ≤ ∑ x ∈ X, ((Y.filter fun y => adj G x y = b).card : ℝ)

/-- The Euclidean operator norm inequality, tested on every vector supported on B.
Both sides have been multiplied by the square of the size of B. -/
def SpectralBound (G : SimpleGraph V) (B : Finset V) (p ε : ℝ) : Prop :=
  ∀ v : V → ℝ,
    ∑ x ∈ B, (∑ y ∈ B, ((if G.Adj x y then (1:ℝ) else 0) - p) * v y)^2 ≤
      (ε * B.card)^2 * ∑ y ∈ B, (v y)^2

/-- Lemma 3. All rates, density constants and order thresholds precede the host graph.
The epsilon formulation gives uniform convergence of both errors. -/
def DensityReduction : Prop :=
  ∀ K : ℝ, 0 < K → ∃ u τ c C : ℝ, 0 < u ∧ 0 < τ ∧ 0 < c ∧ 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ G : SimpleGraph (Fin N),
    let r := ⌈K * Real.log N⌉₊
    (∃ (S : Finset (Fin N)) (d : ℕ), r ≤ S.card ∧ S.card < 2*r ∧ degreeClass G S d = S) ∨
    ∃ (B : Finset (Fin N)) (p : ℝ), Real.exp (c*r) ≤ B.card ∧
      (B.card : ℝ) ≤ Real.exp (C*r) ∧ τ ≤ p ∧ p ≤ 1-τ ∧
      CutBounds G B (B.card * Real.exp (-u*r)) τ ∧
      (∀ x ∈ B, |(degreeOn G B x : ℝ) - p * B.card| ≤ ε * B.card) ∧ SpectralBound G B p ε

/-- Lemma 4. The functions on labels need not be injective. Dot products
factor through n coordinates, including over composite moduli. -/
def BiasedRectangle : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ [NeZero q], ∃ C : ℝ, 0 < C ∧ ∀ n a b : ℕ, 0 < a → 0 < b →
    ∀ (v : Fin a → Fin n → ZMod q) (w : Fin b → Fin n → ZMod q),
    (a : ℝ)*b/4 ≤ ‖∑ x, ∑ y, ZMod.stdAddChar (v x ⬝ᵥ w y)‖ →
    let ρ := Real.exp (-C*(1 + n / Real.log (n+2 : ℝ)))
    ∃ (S : Finset (Fin a)) (T : Finset (Fin b)) (t : ZMod q),
      ρ*a ≤ S.card ∧ ρ*b ≤ T.card ∧ ∀ x ∈ S, ∀ y ∈ T, v x ⬝ᵥ w y = t

/-- The inherited assumptions used in Sections 3–5 after decreasing u. The positive
constant c records the exponential growth of the absolute cut threshold. -/
def Core (G : SimpleGraph V) (B : Finset V) (r : ℕ) (u τ c : ℝ) : Prop :=
  Real.exp (c*r) ≤ B.card * Real.exp (-u*r) ∧ CutBounds G B (B.card * Real.exp (-u*r)) τ

def Large (B X : Finset V) (r : ℕ) (u : ℝ) (k : ℕ) : Prop :=
  X ⊆ B ∧ B.card * Real.exp (-u*r/k) ≤ X.card

noncomputable def adjMod (q : ℕ) (G : SimpleGraph V) (x y : V) : ZMod q :=
  if G.Adj x y then 1 else 0

/-- Lemma 5. The disagreement constant is chosen before D and the cut scale. -/
def AdjacencyApproximation : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ [NeZero q], ∀ τ : ℝ, 0 < τ → ∃ γ : ℝ, 0 < γ ∧
    ∀ D u c : ℝ, 0 < D → 0 < u → 0 < c → ∀ᶠ r : ℕ in atTop,
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B X Y : Finset (Fin N)), Core G B r u τ c →
    Disjoint X Y → Large B X r u 4 → Large B Y r u 4 → ∀ A : Matrix X Y (ZMod q),
    Real.log (Nat.card A.mulVecLin.toAddMonoidHom.range) ≤ D*r →
      γ * X.card * Y.card ≤ ∑ x : X, ((univ.filter fun y : Y => A x y ≠ adjMod q G x y).card : ℝ)

/-- On a fixed tester list, some small coset contains too large a proportion of the rows. -/
def HeavyRestriction (q : ℕ) (G : SimpleGraph V) (X : Finset V) {J : ℕ}
    (ys : Fin J → V) (r : ℕ) (D a : ℝ) : Prop :=
  ∃ (H : AddSubgroup (Fin J → ZMod q)) (z : Fin J → ZMod q),
    (Nat.card H : ℝ) ≤ Real.exp (D*r) ∧ Real.exp (-a*r) * X.card <
      ((X.filter fun x => (fun j => adjMod q G x (ys j) - z j) ∈ H).card : ℝ)

/-- Lemma 7. The mass exponent a is fixed before the subgroup budget D. -/
def RandomRestrictions : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ u τ c : ℝ, 0 < u → 0 < τ → 0 < c →
    ∃ a : ℝ, 0 < a ∧ ∀ D : ℝ, 0 < D → ∃ C β : ℝ, 0 < C ∧ 0 < β ∧
    ∀ᶠ r : ℕ in atTop, ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B X Y : Finset (Fin N)),
    Core G B r u τ c → Disjoint X Y → Large B X r u 8 → Large B Y r u 8 →
    let J := ⌈C*r⌉₊
    let lists := Fintype.piFinset fun _ : Fin J => Y
    ((lists.filter fun ys => HeavyRestriction q G X ys r D a).card : ℝ) ≤
      Real.exp (-β*(r:ℝ)^2) * lists.card

def Positional (B Y : Finset V) (Xs : List (Finset V)) (r : ℕ) (u : ℝ) : Prop :=
  Large B Y r u 16 ∧ ∀ X ∈ Xs, Large B X r u 16 ∧ Disjoint X Y

/-- Lemma 8. A length is written 2^j, so the rate condition is a limit on precisely the
dyadic sequence. The bad set may depend on Q, whereas the two constants precede Q. -/
def ConditionalResidues : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ u τ c : ℝ, 0 < u → 0 < τ → 0 < c →
    ∃ b : ℕ → ℝ, Tendsto (fun j : ℕ => b (2^j) / Real.log ((2:ℝ)^j+1)) atTop atTop ∧
    ∀ j : ℕ, 2 ≤ j → let L := 2^j
    ∀ D : ℝ, 0 < D → D < b L → ∃ β atomMass : ℝ, 0 < β ∧ 0 < atomMass ∧
    ∀ᶠ r : ℕ in atTop, ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B Y : Finset (Fin N))
      (Xs : List (Finset (Fin N))) (Q : Finset (List (Fin N))),
    Core G B r u τ c → Positional B Y Xs r u → Xs.length = L → Q ⊆ tupleSpace Xs →
    Real.exp (-D*r) * (tupleSpace Xs).card ≤ Q.card →
      ∃ E ⊆ Y, (E.card : ℝ) ≤ Real.exp (-β*r) * Y.card ∧ ∀ y ∈ Y, y ∉ E →
      ∃ k l : ℕ, ¬ Nat.ModEq q k l ∧
        atomMass * Q.card ≤ ((Q.filter fun P => tupleDegree (adj G) y P = k).card : ℝ) ∧
        atomMass * Q.card ≤ ((Q.filter fun P => tupleDegree (adj G) y P = l).card : ℝ)

/-- All row and target choices are inside one event on the reference and test sample.
Exterior labels are registered separately for each tuple. -/
def Adjustable {n ℓ : ℕ} (G : SimpleGraph V) (θ : ℝ) (Xs : Fin n → List (Finset V))
    (exterior : Fin n → List V) (ref : Fin n → List V) (ys : Fin ℓ → V) : Prop :=
  let degree := tupleDegree (adj G)
  let f := ∑ i, (Xs i).length
  let initial := fun j => ∑ i, degree (ys j) (ref i)
  ∀ (R : Finset (Fin ℓ)) (d : Fin ℓ → ℕ),
    (∀ j ∈ R, θ*f ≤ d j ∧ (d j : ℝ) ≤ (1-θ)*f ∧ Even ((d j : ℤ) - initial j)) →
    ∃ repl : Fin n → List V, (∀ i, repl i ∈ tupleSpace (Xs i)) ∧
      (∀ i, ∀ x ∈ exterior i, degree x (repl i) = degree x (ref i)) ∧
      (∀ j ∈ R, (∑ i, degree (ys j) (repl i)) = d j) ∧
      ∀ j, j ∉ R → (∑ i, degree (ys j) (repl i)) = initial j

/-- Lemma 11. Uniform probability tending to one is expressed by an arbitrary positive
error tolerance. A fixed polynomial growth order precedes the uniform host threshold.
Fixed exterior lists suffice since independent random lists can be conditioned on. -/
def SimultaneousAdjustment : Prop :=
  ∀ u τ c θ : ℝ, 0 < u → 0 < τ → 0 < c → 0 < θ → θ < 1/2 →
    ∃ (L₀ L₁ : ℕ) (a : ℝ) (n₁ : ℕ), 0 < L₀ ∧ L₀ < L₁ ∧ 0 < a ∧
    ∀ (power : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ r : ℕ in atTop,
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B Y : Finset (Fin N)) (n ℓ : ℕ),
    Core G B r u τ c → n ≤ r^power → (ℓ : ℝ) ≤ a*r →
    ∀ (Xs : Fin n → List (Finset (Fin N))) (exterior : Fin n → List (Fin N)),
    (∀ i, Positional B Y (Xs i) r u ∧ ((Xs i).length = L₀ ∨ (Xs i).length = L₁) ∧
      (exterior i).length ≤ 4*r) →
    n₁ ≤ (univ.filter fun i => (Xs i).length = L₀).card →
    n₁ ≤ (univ.filter fun i => (Xs i).length = L₁).card →
    let draws := (Fintype.piFinset fun i => tupleSpace (Xs i)) ×ˢ
      (Fintype.piFinset fun _ : Fin ℓ => Y)
    ((draws.filter fun z => ¬ Adjustable G θ Xs exterior z.1 z.2).card : ℝ) ≤ ε * draws.card

end OpenProblems
end InducedDegreeRepetition
