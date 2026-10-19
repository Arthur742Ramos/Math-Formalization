module
public import BMChallenge

open BanachMazur Set

#check BanachMazur.exists_compatiblePlay
#check BanachMazur.follows_intersection_eq
#check BanachMazur.exists_commonPoint_play
#check BanachMazur.not_firstWins_of_baireSpace
#check BanachMazur.exists_firstWins_of_not_baireSpace
#check BanachMazur.baireSpace_iff_no_firstWins
#check BanachMazur.isEmpty_firstStrategy
#check BanachMazur.OpenMove
#check BanachMazur.history
#check BanachMazur.Follows
#check BanachMazur.FirstWins

section Contracts
variable {X : Type u} [TopologicalSpace X]

example (σ : FirstStrategy X) : ∃ a : ℕ → OpenMove X, Follows X σ a :=
  exists_compatiblePlay σ

example (σ : FirstStrategy X) (a : ℕ → OpenMove X) (ha : Follows X σ a) :
    (⋂ n, (σ.move (history X a n)).val) = ⋂ n, (a n).val :=
  follows_intersection_eq σ a ha

example [BaireSpace X] (σ : FirstStrategy X) :
    ∃ a : ℕ → OpenMove X, Follows X σ a ∧ (⋂ n, (a n).val).Nonempty :=
  exists_commonPoint_play σ

example [BaireSpace X] (σ : FirstStrategy X) : ¬ FirstWins X σ :=
  not_firstWins_of_baireSpace σ

example (hX : ¬ BaireSpace X) : ∃ σ : FirstStrategy X, FirstWins X σ :=
  exists_firstWins_of_not_baireSpace hX

example : BaireSpace X ↔ ∀ σ : FirstStrategy X, ¬ FirstWins X σ :=
  baireSpace_iff_no_firstWins

example [IsEmpty X] : IsEmpty (FirstStrategy X) := isEmpty_firstStrategy

-- Literal model definitions, including the order of every stored move.
example : OpenMove X = {U : Set X // IsOpen U ∧ U.Nonempty} := rfl
example (a : ℕ → OpenMove X) : history X a 0 = [] := rfl
example (a : ℕ → OpenMove X) (n : ℕ) :
    history X a (n + 1) = a n :: history X a n := rfl
example (a : ℕ → OpenMove X) : history X a 3 = [a 2, a 1, a 0] := rfl
example (a : ℕ → OpenMove X) (n : ℕ) :
    history X a n = (List.range n).reverse.map a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, List.range_succ, ih]
example (a : ℕ → OpenMove X) : history X a 2 ≠ history X a 3 := by
  intro h
  have := congrArg List.length h
  simp only [history_length] at this
  omega
example (σ : FirstStrategy X) (a : ℕ → OpenMove X) :
    Follows X σ a ↔ ∀ n, (a n).val ⊆ (σ.move (history X a n)).val := Iff.rfl
example (σ : FirstStrategy X) : FirstWins X σ ↔
    ∀ a, Follows X σ a → ¬ (⋂ n, (a n).val).Nonempty := Iff.rfl

-- A strategy may depend on every past opponent move. Its field is not a
-- stationary map. The only response requirement is non-strict inclusion.
example (f : List (OpenMove X) → OpenMove X)
    (hf : ∀ a h, (f (a :: h)).val ⊆ a.val) :
    ∃ σ : FirstStrategy X, σ.move = f := ⟨⟨f, hf⟩, rfl⟩
example (σ : FirstStrategy X) (a : OpenMove X) (h : List (OpenMove X)) :
    (σ.move (a :: h)).val ⊆ a.val := σ.responds a h

-- Payoff means there is a single point in every move, not one point per move.
example (a : ℕ → OpenMove X) : (⋂ n, (a n).val).Nonempty ↔
    ∃ x : X, ∀ n, x ∈ (a n).val := by simp only [Set.Nonempty, mem_iInter]
end Contracts

-- BEGIN material-imported-definition audit
section MaterialDefinitions
variable {X : Type u} [TopologicalSpace X]

example (t : TopologicalSpace X) : t.IsOpen Set.univ ∧
    (∀ A B, t.IsOpen A → t.IsOpen B → t.IsOpen (A ∩ B)) ∧
    (∀ S, (∀ A ∈ S, t.IsOpen A) → t.IsOpen (⋃₀ S)) :=
  ⟨t.isOpen_univ, t.isOpen_inter, t.isOpen_sUnion⟩
example (U : Set X) : IsOpen U ↔ TopologicalSpace.IsOpen U := Iff.rfl
example (A : Set X) : A.Nonempty ↔ ∃ x, x ∈ A := Iff.rfl
example (A : Set X) : Dense A ↔ ∀ x, x ∈ closure A := Iff.rfl
example (A : Set X) : closure A = ⋂₀ {C : Set X | IsClosed C ∧ A ⊆ C} := rfl
example : BaireSpace X ↔ ∀ D : ℕ → Set X,
    (∀ n, IsOpen (D n)) → (∀ n, Dense (D n)) → Dense (⋂ n, D n) :=
  ⟨fun h => h.baire_property, fun h => ⟨h⟩⟩
example : IsEmpty X ↔ ∀ _ : X, False :=
  ⟨fun h => h.false, fun h => ⟨h⟩⟩
example (A : Set X) : Dense A ↔
    ∀ U, IsOpen U → U.Nonempty → (U ∩ A).Nonempty := dense_iff_inter_open
example {ι : Type v} (F : Set ι) (f : ι → Set X) :
    F.PairwiseDisjoint f ↔
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (f i) (f j) := Iff.rfl
example {ι : Type v} (F : Set ι) (f : ι → Set X) :
    F.PairwiseDisjoint f ↔
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ x, x ∈ f i → x ∈ f j → False := by
  simp only [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left]
end MaterialDefinitions
-- END material-imported-definition audit

-- Non-Hausdorff, non-T0 topology: no hidden separation assumption is needed.
section IndiscreteBoundary
local instance : TopologicalSpace Bool := ⊤
example : BaireSpace Bool := baire_of_finite
example : ∀ σ : FirstStrategy Bool, ¬ FirstWins Bool σ :=
  baireSpace_iff_no_firstWins.mp baire_of_finite
end IndiscreteBoundary

section EmptyBoundary
variable [TopologicalSpace Empty]
example : IsEmpty (FirstStrategy Empty) := isEmpty_firstStrategy
example : BaireSpace Empty := baire_of_finite
example : ∀ σ : FirstStrategy Empty, ¬ FirstWins Empty σ := by
  intro σ
  exact isEmptyElim ((σ.move []).property.2.choose)
end EmptyBoundary

-- Same last move and same round can give different responses on two legal
-- finite histories. Thus the model is not restricted even to Markov strategies.
section FullHistoryBoundary
local instance : TopologicalSpace (Fin 3) := ⊥
local instance : DiscreteTopology (Fin 3) := discreteTopology_bot _

example : ∃ (σ : FirstStrategy (Fin 3)) (U V : OpenMove (Fin 3)),
    U.val ⊆ V.val ∧
    U.val ⊆ (σ.move []).val ∧ V.val ⊆ (σ.move []).val ∧
    U.val ⊆ (σ.move [U]).val ∧ U.val ⊆ (σ.move [V]).val ∧
    (σ.move [U, U]).val ≠ (σ.move [U, V]).val := by
  classical
  let U : OpenMove (Fin 3) := ⟨{0, 1}, isOpen_discrete _, ⟨0, by simp⟩⟩
  let V : OpenMove (Fin 3) := ⟨univ, isOpen_univ, ⟨0, mem_univ _⟩⟩
  let Z : OpenMove (Fin 3) := ⟨{0}, isOpen_discrete _, ⟨0, by simp⟩⟩
  let O : OpenMove (Fin 3) := ⟨{1}, isOpen_discrete _, ⟨1, by simp⟩⟩
  let f : List (OpenMove (Fin 3)) → OpenMove (Fin 3) := fun h => match h with
    | [] => V
    | [a] => a
    | a :: b :: _ => if a.val = U.val then (if b.val = V.val then Z else O) else a
  have hf : ∀ a h, (f (a :: h)).val ⊆ a.val := by
    intro a h
    cases h with
    | nil => exact subset_rfl
    | cons b h =>
      change (if a.val = U.val then (if b.val = V.val then Z else O) else a).val ⊆ a.val
      split
      · next ha =>
        rw [ha]
        split <;> simp [U, Z, O]
      · exact subset_rfl
  let σ : FirstStrategy (Fin 3) := ⟨f, hf⟩
  have huv : U.val ≠ V.val := by
    intro heq
    have h2 : (2 : Fin 3) ∈ U.val := heq.symm ▸ mem_univ _
    simp [U] at h2
  refine ⟨σ, U, V, subset_univ _, subset_univ _, subset_univ _, subset_rfl,
    subset_univ _, ?_⟩
  change (f [U, U]).val ≠ (f [U, V]).val
  simp only [f, ite_eq_left rfl, ite_eq_right huv]
  change ({1} : Set (Fin 3)) ≠ {0}
  intro heq
  have hx : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := heq ▸ (by simp)
  simp at hx
end FullHistoryBoundary
