module

public import Challenge

-- BEGIN material-imported-definition audit
open Filter Finset InducedDegreeRepetition
open scoped Asymptotics
example : SubexponentialThreshold ↔ ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ‖Real.log (threshold k)‖ ≤ ε * ‖(k : ℝ)‖ := by
  simp only [SubexponentialThreshold, Asymptotics.isLittleO_iff, eventually_atTop]

example (b : ℕ → ℝ) : Tendsto b atTop atTop ↔ ∀ t : ℝ, ∃ i : ℕ, ∀ j ≥ i, t ≤ b j :=
  tendsto_atTop_atTop
example (x : ℝ) (n : ℕ) : ⌈x⌉₊ ≤ n ↔ x ≤ n := Nat.ceil_le
example (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x := Real.exp_log hx
example {V : Type} (G : SimpleGraph V) (S : Finset V) (x : S) :
    degreeOn G S x = @SimpleGraph.degree _ (G.induce (S : Set V)) x (by classical infer_instance) := by
  classical
  let H := G.induce (S : Set V)
  change (S.filter (G.Adj x)).card = (H.neighborFinset x).card
  rw [← Finset.card_map (Function.Embedding.subtype (· ∈ S)) (s := H.neighborFinset x)]
  congr 1
  ext y
  simp [H, and_comm]
example {V : Type} (A B : Finset V) : Disjoint A B ↔ ∀ ⦃x⦄, x ∈ A → x ∉ B :=
  Finset.disjoint_left
example (z : ℤ) : Even z ↔ ∃ x : ℤ, z = x + x := Iff.rfl
example (q x y : ℕ) : Nat.ModEq q x y ↔ x % q = y % q := Iff.rfl
example (q : ℕ) : q.Prime ↔ 2 ≤ q ∧ ∀ m < q, m ∣ q → m = 1 := Nat.prime_def_lt
example (n q : ℕ) (v w : Fin n → ZMod q) : v ⬝ᵥ w = ∑ i, v i * w i := rfl
example (q : ℕ) [NeZero q] (z : ℤ) :
    ZMod.stdAddChar (z : ZMod q) = Complex.exp (2 * Real.pi * Complex.I * z / q) :=
  ZMod.stdAddChar_coe z
example {m n q : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (w : Fin m → ZMod q) :
    w ∈ A.mulVecLin.toAddMonoidHom.range ↔ ∃ v, A.mulVec v = w := Iff.rfl
example {α : Type} [Fintype α] : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
example {α : Type} [AddGroup α] (H : AddSubgroup α) (x z : α) :
    x ∈ {y : α | y-z ∈ H} ↔ x-z ∈ H := Iff.rfl
example {V : Type} {n : ℕ} (Y : Fin n → Finset V) (f : Fin n → V) :
    f ∈ Fintype.piFinset Y ↔ ∀ j, f j ∈ Y j := Fintype.mem_piFinset
-- END material-imported-definition audit
