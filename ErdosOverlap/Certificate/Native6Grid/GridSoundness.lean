/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.TransitionSoundness
public import ErdosOverlap.Certificate.Native6Grid.SeedChecks
public import ErdosOverlap.Certificate.Native6Grid.InitialCheck

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem stateRows_correct (j : ℕ) (hj : j < 1024) :
    RowCorrect seeds (stateRow j) j := by
  apply rowCorrect_of_checked_transitions seeds stateRow 1024 _ transitions_checked hj
  exact initial_checked

theorem trigRows_correct (j : ℕ) (hj : j < 1024) :
    RowTrigCorrect Native6Trig.terms (stateRow j) j := by
  simpa only [seeds_terms] using (stateRows_correct j hj).trig seeds_checked

end
end ErdosOverlap.Native6Grid
