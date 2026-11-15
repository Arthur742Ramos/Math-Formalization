module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import ErdosOverlap.Certificate.Native6Grid.Factors00
public import ErdosOverlap.Certificate.Native6Grid.Factors01
public import ErdosOverlap.Certificate.Native6Grid.Factors02
public import ErdosOverlap.Certificate.Native6Grid.Factors03
public import ErdosOverlap.Certificate.Native6Grid.Factors04

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

@[expose] def factorRow (k : ℕ) : List ℤ :=
  if k < 10 then
    if k < 5 then
      if k < 2 then
        if k < 1 then
          factors00
        else
          factors01
      else
        if k < 3 then
          factors02
        else
          if k < 4 then
            factors03
          else
            factors04
    else
      if k < 7 then
        if k < 6 then
          factors05
        else
          factors06
      else
        if k < 8 then
          factors07
        else
          if k < 9 then
            factors08
          else
            factors09
  else
    if k < 15 then
      if k < 12 then
        if k < 11 then
          factors10
        else
          factors11
      else
        if k < 13 then
          factors12
        else
          if k < 14 then
            factors13
          else
            factors14
    else
      if k < 17 then
        if k < 16 then
          factors15
        else
          factors16
      else
        if k < 18 then
          factors17
        else
          if k < 19 then
            factors18
          else
            factors19


end
end ErdosOverlap.Native6Grid
