# Natural return times and strict order

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean
SHA256 `cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39`

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

Nat
https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1359-L1373
```lean
inductive Nat where
  /--
  Zero, the smallest natural number.

  Using `Nat.zero` explicitly should usually be avoided in favor of the literal `0`, which is the
  [simp normal form](lean-manual://section/simp-normal-forms).
  -/
  | zero : Nat
  /--
  The successor of a natural number `n`.

  Using `Nat.succ n` should usually be avoided in favor of `n + 1`, which is the [simp normal
  form](lean-manual://section/simp-normal-forms).
  -/
  | succ (n : Nat) : Nat
```

Nat.le
https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L2022-L2026
```lean
protected inductive Nat.le (n : Nat) : Nat → Prop
  /-- Non-strict inequality is reflexive: `n ≤ n` -/
  | refl     : Nat.le n n
  /-- If `n ≤ m`, then `n ≤ m + 1`. -/
  | step {m} : Nat.le n m → Nat.le n (succ m)
```

Nat.lt
https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L2036-L2040
```lean
@[implicit_reducible] protected def Nat.lt (n m : Nat) : Prop :=
  Nat.le (succ n) m

instance instLTNat : LT Nat where
  lt := Nat.lt
```

Natural constructors include zero and successor; n>N means succ N <= n. Both semantic routes check strict-order expansion and positive late witnesses. Zero is not a stage witness.
