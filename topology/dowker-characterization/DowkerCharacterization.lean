/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Insertion
public import InsertionReverse
public import Product
public import ProductReverse

/-!
# Dowker's characterization

Normality together with ordinary countable paracompactness is equivalent both
to normality of the unit-interval product and to strict continuous insertion
between arbitrary real upper and lower semicontinuous bounds. The first factor
has no additional separation assumption. The companion theorem covers every compact
metrizable second factor.
-/

@[expose] public section

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

theorem normal_countablyParacompact_iff_normal_interval_product :
    (NormalSpace X ∧ CountablyParacompact X) ↔ NormalSpace (X × unitInterval) := by
  constructor
  · rintro ⟨hN, hC⟩
    let := hN
    exact hC.normal_compact_metrizable_product
  · intro hP
    let := hP
    exact ⟨normal_space_of_normal_product (Y := unitInterval),
      countably_paracompact_of_normal_interval_product⟩

theorem normal_countablyParacompact_iff_strict_insertion :
    (NormalSpace X ∧ CountablyParacompact X) ↔ StrictInsertion X := by
  constructor
  · rintro ⟨hN, hC⟩
    let := hN
    exact hC.strict_insertion
  · intro hI
    exact ⟨hI.normal_space, hI.countably_paracompact⟩

theorem normal_interval_product_iff_strict_insertion :
    NormalSpace (X × unitInterval) ↔ StrictInsertion X :=
  normal_countablyParacompact_iff_normal_interval_product.symm.trans
    normal_countablyParacompact_iff_strict_insertion

end Dowker
