module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows123
public import ErdosOverlap.Certificate.Native6Grid.Rows124

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0984 : transitionRowCheck seeds row0984 row0985 = true := by
  decide +kernel

theorem transition0985 : transitionRowCheck seeds row0985 row0986 = true := by
  decide +kernel

theorem transition0986 : transitionRowCheck seeds row0986 row0987 = true := by
  decide +kernel

theorem transition0987 : transitionRowCheck seeds row0987 row0988 = true := by
  decide +kernel

theorem transition0988 : transitionRowCheck seeds row0988 row0989 = true := by
  decide +kernel

theorem transition0989 : transitionRowCheck seeds row0989 row0990 = true := by
  decide +kernel

theorem transition0990 : transitionRowCheck seeds row0990 row0991 = true := by
  decide +kernel

theorem transition0991 : transitionRowCheck seeds row0991 row0992 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
