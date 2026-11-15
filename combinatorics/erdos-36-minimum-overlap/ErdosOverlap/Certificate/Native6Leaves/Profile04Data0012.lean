/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.GeometryCheck0099
public import ErdosOverlap.Numerics.NativeLeafCertificateData

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Leaves0012Chunk00 : List (CheckedProfileLeaf (4 : Fin 10)) := [
  ⟨⟨checkedGeometry25381, (some 344), (8820014605871/500000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25382, (some 344), (8820014605871/500000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25383, (some 344), (8820014605871/500000000000000000 : ℚ), (Int.negSucc 12948455169364129546722344959)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25384, (some 344), (8820014605871/500000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25385, (some 345), (9663829313071/500000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25386, (some 345), (9663829313071/500000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25387, (some 345), (9663829313071/500000000000000000 : ℚ), (Int.negSucc 1341976731207537062741803007)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25388, (some 345), (9663829313071/500000000000000000 : ℚ), (Int.negSucc 1585085487619792814064271359)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25389, (some 346), (8935132431919/500000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25390, (some 346), (8935132431919/500000000000000000 : ℚ), (Int.negSucc 169782270584398367778930687)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25391, (some 346), (8935132431919/500000000000000000 : ℚ), (Int.negSucc 840961106223379100272164863)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25392, (some 346), (8935132431919/500000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25393, (some 347), (1647915444131/100000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25394, (some 347), (1647915444131/100000000000000000 : ℚ), (Int.negSucc 499616804316268428492013567)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25395, (some 347), (1647915444131/100000000000000000 : ℚ), (Int.negSucc 281474976710655)⟩, by decide +kernel⟩,
  ⟨⟨checkedGeometry25396, (some 347), (1647915444131/100000000000000000 : ℚ), (Int.negSucc 1996454152014790254621884415)⟩, by decide +kernel⟩
]

def profile04Leaves0012 : List (CheckedProfileLeaf (4 : Fin 10)) := profile04Leaves0012Chunk00

end
end ErdosOverlap.Native6Leaves
