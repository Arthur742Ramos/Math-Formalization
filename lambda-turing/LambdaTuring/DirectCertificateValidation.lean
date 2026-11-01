/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectBetaTraceCode
public meta import LambdaTuring.DirectBetaTraceCode

@[expose] public section

namespace LambdaTuring

/-- Validate a list encoding using a validator for each encoded element. -/
def encodedListValid (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n.unpair.1 && encodedListValid p n.unpair.2
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le n)

theorem encodedListValid_spec {α : Type} [Encodable α] (p : Nat → Bool)
    (hp : ∀ n, p n = true ↔ ∃ a : α, Encodable.encode a = n) (n : Nat) :
    encodedListValid p n = true ↔ ∃ xs : List α, Encodable.encode xs = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [encodedListValid, true_iff]
      exact ⟨[], rfl⟩
    | succ n =>
      rw [encodedListValid]
      simp only [Bool.and_eq_true, hp, ih n.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le n))]
      constructor
      · rintro ⟨⟨a, ha⟩, ⟨xs, hxs⟩⟩
        refine ⟨a :: xs, ?_⟩
        simp [Encodable.encode_list_cons, ha, hxs, Nat.pair_unpair]
      · rintro ⟨xs, hx⟩
        cases xs with
        | nil => simp at hx
        | cons a xs =>
          simp only [Encodable.encode_list_cons, Nat.succ.injEq] at hx
          have hpair : (Nat.pair (Encodable.encode a) (Encodable.encode xs)).unpair = n.unpair :=
            congrArg Nat.unpair hx
          simp only [Nat.unpair_pair] at hpair
          exact ⟨⟨a, congrArg Prod.fst hpair⟩, ⟨xs, congrArg Prod.snd hpair⟩⟩

def encodedBoolValid (n : Nat) : Bool := n < 2
def encodedPathValid : Nat → Bool := encodedListValid encodedBoolValid
def encodedCertificateValid : Nat → Bool := encodedListValid encodedPathValid

theorem encodedBoolValid_spec (n : Nat) :
    encodedBoolValid n = true ↔ ∃ b : Bool, Encodable.encode b = n := by
  simp only [encodedBoolValid, decide_eq_true_eq]
  constructor
  · intro h
    cases n with
    | zero => exact ⟨false, rfl⟩
    | succ n =>
      cases n with
      | zero => exact ⟨true, rfl⟩
      | succ n => omega
  · rintro ⟨b, rfl⟩
    cases b <;> decide

theorem encodedPathValid_spec (n : Nat) :
    encodedPathValid n = true ↔ ∃ path : List Bool, Encodable.encode path = n :=
  encodedListValid_spec encodedBoolValid encodedBoolValid_spec n

theorem encodedCertificateValid_spec (n : Nat) :
    encodedCertificateValid n = true ↔ ∃ paths : List (List Bool), Encodable.encode paths = n :=
  encodedListValid_spec encodedPathValid encodedPathValid_spec n

#print axioms encodedCertificateValid_spec
end LambdaTuring
