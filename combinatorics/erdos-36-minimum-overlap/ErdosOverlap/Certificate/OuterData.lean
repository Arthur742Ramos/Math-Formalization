/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Certificate.OuterData00
public import ErdosOverlap.Certificate.OuterData01
public import ErdosOverlap.Certificate.OuterData02
public import ErdosOverlap.Certificate.OuterData03
public import ErdosOverlap.Certificate.OuterData04
public import ErdosOverlap.Certificate.OuterData05
public import ErdosOverlap.Certificate.OuterData06
public import ErdosOverlap.Certificate.OuterData07
public import ErdosOverlap.Certificate.OuterData08
public import ErdosOverlap.Certificate.OuterData09
public import ErdosOverlap.Certificate.OuterData10
public import ErdosOverlap.Certificate.OuterData11
public import ErdosOverlap.Certificate.OuterData12
public import ErdosOverlap.Certificate.OuterData13
public import ErdosOverlap.Certificate.OuterData14
public import ErdosOverlap.Certificate.OuterData15
public import ErdosOverlap.Certificate.OuterData16
public import ErdosOverlap.Certificate.OuterData17

/-! # All selected outer kernel inputs

Source SHA256 `c8019383dbcf7eb5892c27be2d918e0095e11cabe9b2f3d5b0e8184a1a16d93b`.
Transcendental bounds require separate Lean proofs; all finite checks
and compiler equalities are proved by kernel reduction.
-/

namespace ErdosOverlap.Outer180
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def bins : List OuterBinData :=
  bins00 ++
  bins01 ++
  bins02 ++
  bins03 ++
  bins04 ++
  bins05 ++
  bins06 ++
  bins07 ++
  bins08 ++
  bins09 ++
  bins10 ++
  bins11 ++
  bins12 ++
  bins13 ++
  bins14 ++
  bins15 ++
  bins16 ++
  bins17

theorem bins_checked : bins.all (OuterBinData.check frequencies) = true := by
  simp only [bins, List.all_append, bins00_checked, bins01_checked, bins02_checked, bins03_checked, bins04_checked, bins05_checked, bins06_checked, bins07_checked, bins08_checked, bins09_checked, bins10_checked, bins11_checked, bins12_checked, bins13_checked, bins14_checked, bins15_checked, bins16_checked, bins17_checked, Bool.and_self]

theorem bins_length : bins.length = 180 := by
  decide +kernel

end
end ErdosOverlap.Outer180
