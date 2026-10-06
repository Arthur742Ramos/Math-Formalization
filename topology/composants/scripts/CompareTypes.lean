module
public import Lean.Environment

/-! Export raw expression types, universe parameters, and literal project predicate values. -/
@[expose] public section
open Lean
def main (args : List String) : IO Unit := do
  let [moduleName] := args | throw <| IO.userError "Expected one module name"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := moduleName.toName }] {} (level := .exported)
  for name in #[`Composants.mem_composant_self,
      `Composants.dense_composant,
      `Composants.isConnected_composant,
      `Composants.composants_eq_or_disjoint,
      `Composants.iUnion_composant,
      `Composants.composant_countable_union,
      `Composants.isMeagre_composant,
      `Composants.uncountably_many_composants,
      `Composants.alexandroff_continua,
      `Composants.IsSubcontinuum,
      `Composants.IsIndecomposable,
      `Composants.composant,
      `Composants.IsOpenCover,
      `Composants.IsPartitionBetween,
      `Composants.IsOmegaMap,
      `Composants.IsContinuum] do
    let some info := env.find? name | throw <| IO.userError s!"Missing declaration: {name}"
    IO.println s!"RAW TYPE {name}"
    IO.println (reprStr info.levelParams)
    IO.println (reprStr info.type)
    if name == `Composants.IsSubcontinuum ||
        name == `Composants.IsIndecomposable ||
        name == `Composants.composant ||
        name == `Composants.IsOpenCover ||
        name == `Composants.IsPartitionBetween ||
        name == `Composants.IsOmegaMap ||
        name == `Composants.IsContinuum then
      IO.println (reprStr info.value?)
