# Exact Lean-core history infrastructure

This supplement retains compiler-owned List constructors and List.length independently from Mathlib. `history a n` stores exactly the previous n first-player moves in reverse order. `SecondStrategy.move` receives the current move separately, and `metricStrategy` uses the full stored length to choose its radius bound. Nil/cons/length and explicit three-round ordering are semantic test obligations; the source hashes alone do not claim their compilation.

Compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`; toolchain `leanprover/lean4:v4.35.0-rc2`. Full-file SHA256 `cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39`; Git blob `f87ee970af5149d74434f09a89aedff1a8fdb2d2`. Installed exact-toolchain bytes were compared to these retained exact-commit source excerpts.

Apache-2.0. Upstream attribution preserved:

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

## `List`

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L3110-L3117

Excerpt SHA256 `22924dff4fd3d23b1edb5e5dcd13a4234b7beffd6c2dec74051991eb306d9906`.

```lean
inductive List (α : Type u) where
  /-- The empty list, usually written `[]`. -/
  | nil : List α
  /--
  The list whose first element is `head`, where `tail` is the rest of the list.
  Usually written `head :: tail`.
  -/
  | cons (head : α) (tail : List α) : List α

```

## `List.length`

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L3192-L3197

Excerpt SHA256 `82e7a80439440da89b7c309bdda2ccff1b59e03d52fffcbcf6f3a0f0aec724eb`.

```lean
-/
/- One might expect/hope that this was `implicit_reducible` rather than `instance_reducible`.
Currently, the test `tests/elab/implicit_reducible_list_length.lean` fails if we make this change. -/
@[instance_reducible] def List.length : List α → Nat
  | nil       => 0
  | cons _ as => HAdd.hAdd (length as) 1

```

