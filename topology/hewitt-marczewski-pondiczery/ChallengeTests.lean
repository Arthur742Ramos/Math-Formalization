module

import HMPChallenge

open HMP TopologicalSpace
open scoped Cardinal

universe u v

-- Challenge elaborates with Mathlib-only imports, independently of Solution.
example {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, SeparableSpace (X i)] (h : #ι ≤ 𝔠) : SeparableSpace (∀ i, X i) :=
  separable_product h

example {ι : Type u} : SeparableSpace (ι → Bool) ↔ #ι ≤ 𝔠 :=
  boolean_cube_separable_iff

-- The selected definition has its literal table-decoding value across imports.
example {ι : Type u} {X : ι → Type v} (e : ι → ℕ → Bool)
    (d : ∀ i, ℕ → X i) (c : RowCode) (i : ι) :
    row e d c i = d i (c.2 (fun k => e i k)) := rfl

-- Every selected name resolves in the independent Challenge import.
#check HMP.finite_interpolation
#check HMP.denseRange_rows
#check HMP.continuum_bound_iff
#check HMP.separable_product_of_embedding
#check HMP.separable_product
#check HMP.coordinate_patterns_injective
#check HMP.boolean_cube_separable_iff
#check HMP.row
