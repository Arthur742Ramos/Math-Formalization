module

public import ErdosOverlap.Numerics.FixedBox

/-! Compact literal storage for untrusted interval witnesses.

This uses 160-bit words, with an offset of 2^159 for signed integers.
It is an ordinary total Lean decoder. No correctness, injectivity, range,
or provenance fact about an external encoder is assumed. Consumers check the
decoded boxes against their original source expressions using kernel
reduction. The packet format merely reduces source elaboration overhead.
-/

namespace ErdosOverlap.Numerics

@[expose] public section

namespace BoxPacket

def wordBase : ℕ := 1461501637330902918203684832716283019655932542976
def wordOffset : ℤ := 730750818665451459101842416358141509827966271488
def boxBase : ℕ := 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576

def word (packet : ℕ) : ℤ := ((packet % wordBase : ℕ) : ℤ)-wordOffset

def box (packet : ℕ) : FixedBox := ⟨word packet, word (packet/wordBase)⟩

def boxes : ℕ → ℕ → List FixedBox
  | 0, _ => []
  | n+1, packet => box packet :: boxes n (packet/boxBase)

end BoxPacket
end
end ErdosOverlap.Numerics
