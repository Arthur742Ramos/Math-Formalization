/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Solution
public import Lean

open Lean Elab Command

/-! Check actual elaborated statement dependencies, without following theorem
proof bodies. This audit is not a premise of any mathematical theorem. -/

run_cmd do
  let configText ← IO.FS.readFile "comparator.json"
  let config ← match Json.parse configText with
    | .ok value => pure value
    | .error error => throwError "Invalid Comparator JSON: {error}"
  let statements ← match config.getObjValAs? (Array String) "theorem_names" with
    | .ok value => pure value
    | .error error => throwError "Invalid theorem names: {error}"
  let holes ← match config.getObjValAs? (Array String) "definition_names" with
    | .ok value => pure value
    | .error error => throwError "Invalid definition-hole list: {error}"
  unless holes.isEmpty do
    throwError "Fixed model definitions must not be declared as definition holes"
  let inventoryText ← IO.FS.readFile "verification/fixed-definitions.json"
  let inventory ← match Json.parse inventoryText with
    | .ok value => pure value
    | .error error => throwError "Invalid fixed-definition JSON: {error}"
  let fixed ← match inventory.getObjValAs? (Array String) "fixed_definition_names" with
    | .ok value => pure value
    | .error error => throwError "Invalid fixed-definition names: {error}"
  unless fixed.size == 15 && !statements.isEmpty do
    throwError "Expected fifteen fixed model definitions and selected statement types"
  let env ← getEnv
  let mut pending : Array (Name × List Name) := #[]
  for statement in statements do
    let name := statement.toName
    let some info := env.find? name | throwError "Missing selected theorem: {name}"
    -- Public module interfaces can expose theorem statements as axiomInfo.
    -- The separate transitive axiom audit checks their proof dependencies.
    match info with
    | .thmInfo _ | .axiomInfo _ => pure ()
    | _ => throwError "Not a selected theorem statement: {name}"
    for dependency in info.type.getUsedConstants do
      pending := pending.push (dependency, [name, dependency])
  let mut visited : Std.HashSet Name := {}
  let mut paths : Std.HashMap Name (List Name) := {}
  while !pending.isEmpty do
    let (name, path) := pending.back!
    pending := pending.pop
    if (`ErdosOverlap).isPrefixOf name && !visited.contains name then
      visited := visited.insert name
      paths := paths.insert name path
      let some info := env.find? name | throwError "Missing statement dependency {name}"
      let mut dependencies := info.type.getUsedConstants
      if let .defnInfo definition := info then
        dependencies := dependencies ++ definition.value.getUsedConstants
      for dependency in dependencies do
        pending := pending.push (dependency, path ++ [dependency])
  let mut fixedSeen : Std.HashSet Name := {}
  for entry in fixed do
    let name := entry.toName
    if fixedSeen.contains name then
      throwError "Duplicate fixed-definition name {name}"
    fixedSeen := fixedSeen.insert name
    let some (.defnInfo _) := env.find? name | throwError "Not a definition: {name}"
    unless visited.contains name do
      throwError "Fixed definition is not reached from a selected theorem type: {name}"
  for entry in fixed do
    let name := entry.toName
    let path := paths[name]!.map toString
    IO.println s!"Fixed definition reached: {String.intercalate " -> " path}"
  IO.println "All fifteen fixed model definitions are reachable; definition_names is empty."
