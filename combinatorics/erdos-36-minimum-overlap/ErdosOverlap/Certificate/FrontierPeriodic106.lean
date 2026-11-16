/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.KernelAssembly

/-! Exact data for the fully_joint32 kernel.
Frozen rational input SHA-256: `1a45087c780286a6c997fe9933bfcac502e79283569264f12f9f8aeea0b5eaae`.
Generation is not verification; the finite checks below must compile. -/

namespace ErdosOverlap.FrontierData
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def periodic106 : List PeriodicCellRow := [
  ⟨11, 27, 11920, false, (-797505983997 / 65536000000000000000000 : ℚ)⟩,
  ⟨8, 31, 56985, false, (-3794110466657 / 131072000000000000000000 : ℚ)⟩,
  ⟨1, 24, 56985, false, (-25638052171 / 131072000000000000000000 : ℚ)⟩,
  ⟨16, 55, 53774, false, (-432145032683 / 32768000000000000000000 : ℚ)⟩,
  ⟨7, 40, 37441, false, (-131635749765763 / 131072000000000000000000 : ℚ)⟩,
  ⟨15, 33, 61170, false, (-1601278376737 / 26214400000000000000000 : ℚ)⟩,
  ⟨4, 25, 65522, false, (-1217308414941 / 13107200000000000000000 : ℚ)⟩,
  ⟨20, 46, 13104, false, (-8646740666207 / 65536000000000000000000 : ℚ)⟩,
  ⟨9, 53, 8935, false, (-3252798715697 / 131072000000000000000000 : ℚ)⟩,
  ⟨7, 20, 56181, false, (-11947845318907 / 131072000000000000000000 : ℚ)⟩,
  ⟨2, 49, 27886, false, (-121406084233 / 6553600000000000000000 : ℚ)⟩,
  ⟨2, 21, 34495, false, (-11816859257 / 16384000000000000000000 : ℚ)⟩,
  ⟨15, 37, 8734, false, (-14614925392321 / 65536000000000000000000 : ℚ)⟩,
  ⟨3, 26, 22797, false, (-1860497672919 / 131072000000000000000000 : ℚ)⟩,
  ⟨6, 52, 31344, false, (-928557568799 / 16384000000000000000000 : ℚ)⟩,
  ⟨15, 61, 31344, false, (-15471394384833 / 131072000000000000000000 : ℚ)⟩,
  ⟨9, 47, 51737, false, (-142443001329 / 6553600000000000000000 : ℚ)⟩,
  ⟨13, 55, 15602, false, (-1405489122551 / 26214400000000000000000 : ℚ)⟩,
  ⟨4, 22, 14560, false, (-724308935193 / 65536000000000000000000 : ℚ)⟩,
  ⟨4, 31, 14561, false, (-1250251239589 / 131072000000000000000000 : ℚ)⟩,
  ⟨2, 25, 28491, false, (-12878104499 / 26214400000000000000000 : ℚ)⟩
]

theorem periodic106_valid : periodic106.all (PeriodicCellRow.valid 131072) = true := by
  decide +kernel

end
end ErdosOverlap.FrontierData
