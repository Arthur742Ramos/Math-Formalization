/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Certificate.Native6JumpTable
public import ErdosOverlap.Certificate.Native6MergeNode07

/-! # Native6 exact jump source binding

Untrusted generated proposal from source SHA256 `9d10c1adbc22fe542618d95cc9746920ca234aa24bba4737cfd2db6936b764ff`.
The displayed compiler identity is checked by Lean kernel reduction.
-/

namespace ErdosOverlap.Native6Jumps

@[expose] public section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def componentBlocks : List (List AffineJump) := [periodic00, periodic01, periodic02, periodic03, periodic04, periodic05, periodic06, periodic07, periodic08, periodic09, periodic10, periodic11, periodic12, periodic13, periodic14, periodic15, periodic16, periodic17, periodic18, periodic19, periodic20, periodic21, periodic22, periodic23, periodic24, periodic25, periodic26, periodic27, periodic28, periodic29, periodic30, periodic31, periodic32, periodic33, periodic34, periodic35, periodic36, periodic37, periodic38, periodic39, phase00, phase01, phase02, phase03, phase04, phase05, phase06, phase07, phase08, phase09, phase10, phase11, phase12, phase13, phase14, phase15, phase16, phase17, phase18, phase19, phase20, phase21, phase22]

def componentJumps : List AffineJump := componentBlocks.flatten

theorem finalJumps_eq : finalJumps = mergeNode07 := by
  apply affineJumpsEqual_sound
  decide +kernel

theorem finalJumps_value (t : ℝ) : affineJumpSum finalJumps t =
    affineJumpSum componentBlocks.flatten t := by
  rw [finalJumps_eq, mergeNode07_value]
  simp only [componentBlocks, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

end
end ErdosOverlap.Native6Jumps
