/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierLeafCertificateData

/-! Attach a proved executable check to every member of an ordered leaf list. -/

namespace ErdosOverlap.FrontierLeaves
@[expose] public section

def mapCheckedBool {α : Type} (p : α → Bool) (leaves : List α)
    (checked : leaves.all p = true) : List {leaf : α // p leaf = true} :=
  leaves.attach.map fun leaf =>
    ⟨leaf.val, (List.all_eq_true (p := p) (l := leaves)).mp checked leaf.val leaf.property⟩

def checkedProfileLeaves (mode : Fin 20) (leaves : List ProfileLeaf)
    (checked : leaves.all (fun leaf => leaf.check mode) = true) : List (CheckedProfileLeaf mode) :=
  mapCheckedBool (α := ProfileLeaf) (fun leaf : ProfileLeaf => leaf.check mode) leaves checked

def checkedCentralLeaves (leaves : List CentralLeaf)
    (checked : leaves.all (fun leaf => leaf.check) = true) : List CheckedCentralLeaf :=
  mapCheckedBool (α := CentralLeaf) (fun leaf : CentralLeaf => leaf.check) leaves checked

def checkedDenominatorLeaves (leaves : List DenominatorLeaf)
    (checked : leaves.all (fun leaf => leaf.check) = true) : List CheckedDenominatorLeaf :=
  mapCheckedBool (α := DenominatorLeaf) (fun leaf : DenominatorLeaf => leaf.check) leaves checked

end
end ErdosOverlap.FrontierLeaves
