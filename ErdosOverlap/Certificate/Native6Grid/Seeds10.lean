module

public import ErdosOverlap.Numerics.RotationGrid

/-! Untrusted integer witnesses; their use requires the associated checked proofs. -/

namespace ErdosOverlap.Native6Grid

open Numerics

@[expose] public section

def seeds10 : List (CosineTerm × RotationSeed) := [
  (⟨(3915822093438757/1000000000000), (-890989251545037/62500000000000000000000)⟩, ⟨(-264068765621954992460674485225013718813, -214615414777720932809010349722254388968), (69567332950842858585829033143657572896, 333095294808291713992204451091214963554)⟩)
]

end
end ErdosOverlap.Native6Grid
