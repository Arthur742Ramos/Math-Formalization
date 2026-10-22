# Exact Lean-core full-history infrastructure

Exact List nil/cons and length encode the entire reverse marked-opponent history. Current input is supplied separately. History length controls shrinking scale; strategies may distinguish earlier marked points at equal lengths. Actual legal-play existence and boundary tests have separate build receipts.

Compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`; toolchain `leanprover/lean4:v4.35.0-rc2`; SHA256 `cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39`; Git blob `f87ee970af5149d74434f09a89aedff1a8fdb2d2`. Installed source bytes are equal to the retained exact compiler source. Prior Oxtoby/Choquet/category-game records supply credited provenance; compilation and semantic review are separate.

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

## `List`

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L3110-L3117

SHA256 `22924dff4fd3d23b1edb5e5dcd13a4234b7beffd6c2dec74051991eb306d9906`.

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

SHA256 `82e7a80439440da89b7c309bdda2ccff1b59e03d52fffcbcf6f3a0f0aec724eb`.

```lean
-/
/- One might expect/hope that this was `implicit_reducible` rather than `instance_reducible`.
Currently, the test `tests/elab/implicit_reducible_list_length.lean` fails if we make this change. -/
@[instance_reducible] def List.length : List α → Nat
  | nil       => 0
  | cons _ as => HAdd.hAdd (length as) 1
```

## Surjectivity
Every target y has a source x with f x=y. This is not injectivity or dense range. Both entrypoints compile the literal forall-exists equality bridge.
https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Function.lean#L62-L64
Full source SHA256 `88217ed8ec91da1ec655c8a10f737b659a4570b4c05dbd6b084162a3157cf030`, Git blob `d3526ccde628989d0d4658dbec3c3f334bcb7a7f`.
```lean
def Surjective (f : α → β) : Prop :=
  ∀ b, Exists fun a => f a = b

```
