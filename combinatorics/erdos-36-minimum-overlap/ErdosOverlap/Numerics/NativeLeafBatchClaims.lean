/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativeLeafBatch
public import ErdosOverlap.Numerics.NativeLeafAssembly

/-! Claim maps of checked batches are exactly the maps of the raw data. -/

namespace ErdosOverlap.Native6Leaves

public section

theorem profileClaims_profileBatch (mode : Fin 10) (raw : List ProfileLeaf)
    (h : raw.all (fun leaf => leaf.check mode) = true) :
    profileClaims (profileBatch mode raw h) = raw.map ProfileLeaf.claim :=
  profileBatch_map mode raw h ProfileLeaf.claim

theorem centralClaims_centralBatch (raw : List CentralLeaf)
    (h : raw.all CentralLeaf.check = true) :
    centralClaims (centralBatch raw h) = raw.map CentralLeaf.claim :=
  centralBatch_map raw h CentralLeaf.claim

theorem denominatorClaims_denominatorBatch (raw : List DenominatorLeaf)
    (h : raw.all DenominatorLeaf.check = true) :
    denominatorClaims (denominatorBatch raw h) = raw.map DenominatorLeaf.claim :=
  denominatorBatch_map raw h DenominatorLeaf.claim

end
end ErdosOverlap.Native6Leaves
