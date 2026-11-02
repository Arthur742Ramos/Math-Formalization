/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.NumeralReduction

@[expose] public section

namespace LambdaTuring

/-- Rice's theorem for exact numerical observations of closed lambda terms. -/
theorem no_computable_closed_extensional_decider
    (C : Set (Nat →. Nat)) {f g : Nat →. Nat}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfC : f ∈ C) (hgC : g ∉ C) :
    ¬ ∃ d : Term → Bool, Computable d ∧
      ∀ t, Scoped 0 t → (d t = true ↔ numericalValue t ∈ C) := by
  rintro ⟨d, hd, hcorrect⟩
  have hd' : ComputablePred (fun c : Nat.Partrec.Code => d (compileLambdaTotal c) = true) := by
    apply Computable.computablePred
    simpa using hd.comp primrec_compileLambdaTotal.to_comp
  have heval (c : Nat.Partrec.Code) : numericalValue (compileLambdaTotal c) = Nat.Partrec.Code.eval c := by
    funext n
    exact (compileLambdaTotal_sound c).2 n
  have hcode : ComputablePred (fun c : Nat.Partrec.Code => Nat.Partrec.Code.eval c ∈ C) := by
    apply hd'.of_eq
    intro c
    rw [← heval c]
    exact hcorrect _ (compileLambdaTotal_sound c).1
  exact hgC (ComputablePred.rice C hcode hf hg hfC)

/-- Even for a fixed numerical input, numerical definedness cannot be decided on closed terms. -/
theorem no_computable_closed_input_domain_decider (n : Nat) :
    ¬ ∃ d : Term → Bool, Computable d ∧
      ∀ t, Scoped 0 t → (d t = true ↔ (numericalValue t n).Dom) := by
  apply no_computable_closed_extensional_decider {f : Nat →. Nat | (f n).Dom}
    (f := fun _ : Nat => Part.some 0) (g := fun _ : Nat => Part.none)
    Nat.Partrec.zero Nat.Partrec.none
  · trivial
  · change ¬ (Part.none : Part Nat).Dom
    exact id

/-- Numerical totality is undecidable for closed lambda programs. -/
theorem no_computable_closed_totality_decider :
    ¬ ∃ d : Term → Bool, Computable d ∧
      ∀ t, Scoped 0 t → (d t = true ↔ ∀ n, (numericalValue t n).Dom) := by
  apply no_computable_closed_extensional_decider {f : Nat →. Nat | ∀ n, (f n).Dom}
    (f := fun _ : Nat => Part.some 0) (g := fun _ : Nat => Part.none)
    Nat.Partrec.zero Nat.Partrec.none
  · intro n
    trivial
  · change ¬ ∀ n : Nat, (Part.none : Part Nat).Dom
    intro h
    exact h 0
#print axioms no_computable_closed_extensional_decider
#print axioms no_computable_closed_input_domain_decider
#print axioms no_computable_closed_totality_decider

end LambdaTuring
