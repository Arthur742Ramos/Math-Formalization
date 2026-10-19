# Exact Lean-core history infrastructure

List is a finite sequence with nil and cons; cons places the newest move at the head. List.length counts every cons, so no previous opponent move is dropped. Both test entrypoints prove history equals reverse(range n).map a and lengthn, including explicit three-round ordering. These are compiled bridges; the literal recursive model remains a fixed non-target dependency for Comparator comparison, with no definition holes. This supplement retains the Lean-core source separately from the Mathlib manifest.

Full-file SHA256 cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39; Git blob f87ee970af5149d74434f09a89aedff1a8fdb2d2. Apache-2.0; original Microsoft copyright retained below.

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

List: https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L3110-L3117

Excerpt SHA256 22924dff4fd3d23b1edb5e5dcd13a4234b7beffd6c2dec74051991eb306d9906

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

List.length: https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L3192-L3197

Excerpt SHA256 82e7a80439440da89b7c309bdda2ccff1b59e03d52fffcbcf6f3a0f0aec724eb

```lean
-/
/- One might expect/hope that this was `implicit_reducible` rather than `instance_reducible`.
Currently, the test `tests/elab/implicit_reducible_list_length.lean` fails if we make this change. -/
@[instance_reducible] def List.length : List α → Nat
  | nil       => 0
  | cons _ as => HAdd.hAdd (length as) 1
```
