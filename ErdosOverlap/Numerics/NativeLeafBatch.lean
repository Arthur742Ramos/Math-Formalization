/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativeLeafCertificateData

/-!
# One kernel check for a batch of native leaves

The data list remains independent of its proof. A single `List.all` check
supplies the proof fields of all checked leaves. Projecting values or any
ordinary data function gives exactly the original raw map, without unfolding
the proof of the batch check.
-/

namespace ErdosOverlap.Native6Leaves

public section

@[expose] def checkedOfAll {α : Type*} (check : α → Bool) (raw : List α)
    (h : raw.all check = true) : List {a : α // check a = true} :=
  raw.attachWith (fun a => check a = true) (fun a ha => (List.all_eq_true.mp h) a ha)

theorem checkedOfAll_map_val {α : Type*} (check : α → Bool) (raw : List α)
    (h : raw.all check = true) : (checkedOfAll check raw h).map Subtype.val = raw :=
  List.attachWith_map_subtype_val _

theorem checkedOfAll_map {α β : Type*} (check : α → Bool) (raw : List α)
    (h : raw.all check = true) (f : α → β) :
    (checkedOfAll check raw h).map (fun a => f a.val) = raw.map f :=
  List.attachWith_map_val _

@[expose] def profileBatch (mode : Fin 10) (raw : List ProfileLeaf)
    (h : raw.all (fun leaf => leaf.check mode) = true) : List (CheckedProfileLeaf mode) :=
  checkedOfAll (fun (leaf : ProfileLeaf) => leaf.check mode) raw h

@[expose] def centralBatch (raw : List CentralLeaf)
    (h : raw.all CentralLeaf.check = true) : List CheckedCentralLeaf :=
  checkedOfAll CentralLeaf.check raw h

@[expose] def denominatorBatch (raw : List DenominatorLeaf)
    (h : raw.all DenominatorLeaf.check = true) : List CheckedDenominatorLeaf :=
  checkedOfAll DenominatorLeaf.check raw h

theorem profileBatch_map_val (mode : Fin 10) (raw : List ProfileLeaf)
    (h : raw.all (fun leaf => leaf.check mode) = true) :
    (profileBatch mode raw h).map Subtype.val = raw :=
  checkedOfAll_map_val _ raw h

theorem centralBatch_map_val (raw : List CentralLeaf) (h : raw.all CentralLeaf.check = true) :
    (centralBatch raw h).map Subtype.val = raw :=
  checkedOfAll_map_val _ raw h

theorem denominatorBatch_map_val (raw : List DenominatorLeaf)
    (h : raw.all DenominatorLeaf.check = true) :
    (denominatorBatch raw h).map Subtype.val = raw :=
  checkedOfAll_map_val _ raw h

theorem profileBatch_map {β : Type*} (mode : Fin 10) (raw : List ProfileLeaf)
    (h : raw.all (fun leaf => leaf.check mode) = true) (f : ProfileLeaf → β) :
    (profileBatch mode raw h).map (fun leaf => f leaf.val) = raw.map f :=
  checkedOfAll_map _ raw h f

theorem centralBatch_map {β : Type*} (raw : List CentralLeaf)
    (h : raw.all CentralLeaf.check = true) (f : CentralLeaf → β) :
    (centralBatch raw h).map (fun leaf => f leaf.val) = raw.map f :=
  checkedOfAll_map _ raw h f

theorem denominatorBatch_map {β : Type*} (raw : List DenominatorLeaf)
    (h : raw.all DenominatorLeaf.check = true) (f : DenominatorLeaf → β) :
    (denominatorBatch raw h).map (fun leaf => f leaf.val) = raw.map f :=
  checkedOfAll_map _ raw h f

end
end ErdosOverlap.Native6Leaves
