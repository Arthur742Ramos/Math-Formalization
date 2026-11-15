module

public import ErdosOverlap.Numerics.BoxPacket
public import ErdosOverlap.Numerics.PolynomialBoxTrace

namespace ErdosOverlap.Numerics

@[expose] public section

def HornerTrace.ofPacket (tailCount packet : ℕ) : HornerTrace :=
  ⟨BoxPacket.box packet, BoxPacket.boxes tailCount (packet/BoxPacket.boxBase)⟩

end
end ErdosOverlap.Numerics
