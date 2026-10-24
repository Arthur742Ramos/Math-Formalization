# Core nonemptiness and finite indices

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean
SHA256 `cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39`

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

Nonempty
https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L839-L841
```lean
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α
```

Fin
https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L2450-L2464
```lean
structure Fin (n : Nat) where
  /-- Creates a `Fin n` from `i : Nat` and a proof that `i < n`. -/
  mk ::
  /--
  The number that is strictly less than `n`.

  `Fin.val` is a coercion, so any `Fin n` can be used in a position where a `Nat` is expected.
  -/
  val  : Nat
  /--
  The number `val` is strictly less than the bound `n`.
  -/
  isLt : LT.lt val n

attribute [coe] Fin.val
```

Nonempty X means an element exists. Fin k is a natural value strictly below k; Fin0 has no indices, so its function product is a singleton. Both routes compile literal nonemptiness/Fin-bound bridges and explicit empty-family/zeroth-power tests.

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Function.lean
SHA256 `88217ed8ec91da1ec655c8a10f737b659a4570b4c05dbd6b084162a3157cf030`

```lean
/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[expose]
def Surjective (f : α → β) : Prop :=
  ∀ b, Exists fun a => f a = b
```
Literal surjectivity means every target has a preimage; it is derived in the main theorem.
