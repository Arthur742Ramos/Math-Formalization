module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs

public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fintype.BigOperators

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

theorem density_reduction : DensityReduction := by sorry

theorem biased_rectangle : BiasedRectangle := by sorry

theorem adjacency_approximation : AdjacencyApproximation := by sorry

theorem random_restrictions : RandomRestrictions := by sorry

theorem conditional_residues : ConditionalResidues := by sorry

theorem simultaneous_adjustment : SimultaneousAdjustment := by sorry

end OpenProblems
end InducedDegreeRepetition
