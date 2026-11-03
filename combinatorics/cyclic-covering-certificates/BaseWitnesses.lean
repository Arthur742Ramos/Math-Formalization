module
/- Original covering predicates for the exact small positive matrices. -/
public import Std
public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CoveringScheme

instance (n : Nat) (P : Fin n → Prop) [DecidablePred P] : Decidable (∃ r : Fin n, P r) :=
  decidable_of_iff (∃ m : Nat, ∃ h : m < n, P ⟨m,h⟩) (by
    constructor
    · rintro ⟨m,h,hm⟩; exact ⟨⟨m,h⟩,hm⟩
    · rintro ⟨⟨m,h⟩,hm⟩; exact ⟨m,h,hm⟩)


/-- Every residue occurs as a row difference between any two distinct columns.
    The addition of q makes Nat subtraction implement modular subtraction. -/
@[expose] def Covers (q n k : Nat) (m : Fin n → Fin k → Fin q) : Prop :=
  ∀ a b : Fin k, a ≠ b → ∀ d : Fin q,
    ∃ r : Fin n, ((m r a).val + q - (m r b).val) % q = d.val

@[expose] def table : Array (Array Nat) := #[
  #[0, 0, 0, 1, 2],
  #[0, 0, 1, 0, 8],
  #[0, 1, 0, 0, 4],
  #[0, 2, 4, 7, 0],
  #[0, 3, 6, 3, 3],
  #[0, 4, 8, 6, 0],
  #[0, 5, 3, 8, 6],
  #[0, 6, 2, 4, 1],
  #[0, 7, 7, 2, 7],
  #[0, 8, 5, 5, 5]
]

@[expose] def witness (r : Fin 10) (c : Fin 5) : Fin 9 :=
  ⟨table[r.val]![c.val]! % 9, Nat.mod_lt _ (by decide)⟩

theorem witness_covers : Covers 9 10 5 witness := by
  unfold Covers
  decide

theorem exists_covering_9_10_5 :
    ∃ m : Fin 10 → Fin 5 → Fin 9, Covers 9 10 5 m :=
  ⟨witness, witness_covers⟩


@[expose] def table11 : Array (Array Nat) := #[
  #[0, 0, 0, 1, 2, 0],
  #[0, 0, 1, 0, 8, 4],
  #[0, 1, 0, 0, 4, 7],
  #[0, 2, 4, 7, 0, 3],
  #[0, 3, 6, 3, 3, 1],
  #[0, 4, 8, 6, 0, 0],
  #[0, 5, 3, 8, 6, 8],
  #[0, 6, 2, 4, 1, 5],
  #[0, 7, 7, 2, 7, 6],
  #[0, 8, 5, 5, 5, 2],
  #[0, 7, 7, 7, 8, 0]
]

@[expose] def witness11 (r : Fin 11) (c : Fin 6) : Fin 9 :=
  ⟨table11[r.val]![c.val]! % 9, Nat.mod_lt _ (by decide)⟩

theorem witness11_covers : Covers 9 11 6 witness11 := by
  unfold Covers
  decide

theorem exists_covering_9_11_6 :
    ∃ m : Fin 11 → Fin 6 → Fin 9, Covers 9 11 6 m :=
  ⟨witness11, witness11_covers⟩


@[expose] def table11x7 : Array (Array Nat) := #[
  #[0, 0, 0, 0, 0, 0, 0],
  #[0, 1, 8, 6, 7, 5, 4],
  #[0, 1, 3, 7, 5, 4, 6],
  #[0, 1, 7, 8, 3, 6, 2],
  #[0, 8, 4, 3, 2, 7, 5],
  #[0, 4, 3, 4, 3, 5, 8],
  #[0, 6, 1, 7, 4, 8, 8],
  #[0, 5, 6, 8, 1, 2, 3],
  #[0, 2, 5, 1, 6, 3, 7],
  #[0, 3, 2, 5, 8, 1, 1],
  #[0, 7, 5, 2, 8, 0, 6]
]

@[expose] def witness11x7 (r : Fin 11) (c : Fin 7) : Fin 9 :=
  ⟨table11x7[r.val]![c.val]! % 9, Nat.mod_lt _ (by decide)⟩

theorem witness11x7_covers : Covers 9 11 7 witness11x7 := by
  unfold Covers
  decide

theorem exists_covering_9_11_7 :
    ∃ m : Fin 11 → Fin 7 → Fin 9, Covers 9 11 7 m :=
  ⟨witness11x7, witness11x7_covers⟩


#print axioms witness_covers
#print axioms exists_covering_9_10_5
#print axioms witness11_covers
#print axioms exists_covering_9_11_6
#print axioms witness11x7_covers
#print axioms exists_covering_9_11_7
end CoveringScheme
