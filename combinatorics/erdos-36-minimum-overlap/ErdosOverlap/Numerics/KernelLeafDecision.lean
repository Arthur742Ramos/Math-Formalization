/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierCheckedLeafLists

public section
namespace ErdosOverlap.FrontierLeaves

/-- Every prefix and the complete remaining tail are checked. -/
theorem all_check_take_drop {α : Type} (n : ℕ) {xs : List α} {p : α → Bool}
    (first : (xs.take n).all p = true) (rest : (xs.drop n).all p = true) :
    xs.all p = true := by
  have joined : (xs.take n ++ xs.drop n).all p = true := by
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨first, rest⟩
  simpa only [List.take_append_drop] using joined

/-- Check fifteen prefixes of32 leaves, then every remaining leaf. The final
tail is always checked, including when the list length differs from512. -/
macro "erdos_leaves_decide" : tactic =>
  `(tactic| (
    apply all_check_take_drop 32
    · decide +kernel
    · apply all_check_take_drop 32
      · decide +kernel
      · apply all_check_take_drop 32
        · decide +kernel
        · apply all_check_take_drop 32
          · decide +kernel
          · apply all_check_take_drop 32
            · decide +kernel
            · apply all_check_take_drop 32
              · decide +kernel
              · apply all_check_take_drop 32
                · decide +kernel
                · apply all_check_take_drop 32
                  · decide +kernel
                  · apply all_check_take_drop 32
                    · decide +kernel
                    · apply all_check_take_drop 32
                      · decide +kernel
                      · apply all_check_take_drop 32
                        · decide +kernel
                        · apply all_check_take_drop 32
                          · decide +kernel
                          · apply all_check_take_drop 32
                            · decide +kernel
                            · apply all_check_take_drop 32
                              · decide +kernel
                              · apply all_check_take_drop 32
                                · decide +kernel
                                · decide +kernel
  ))

end ErdosOverlap.FrontierLeaves
