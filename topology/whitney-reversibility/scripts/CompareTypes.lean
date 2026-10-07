module
public import Lean.Environment
@[expose] public section
open Lean
def main (args : List String) : IO Unit := do
  let [moduleName] := args | throw <| IO.userError "Expected one module name"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := moduleName.toName }] {} (level := .exported)
  for name in #[`WhitneyReversibility.isCompact_relativeLevel, `WhitneyReversibility.isConnected_relativeLevel, `WhitneyReversibility.familyUnion_relativeLevel, `WhitneyReversibility.exists_indecomposable_covering_family, `WhitneyReversibility.sequential_strong_whitney_reversibility, `WhitneyReversibility.Continuum, `WhitneyReversibility.singleton, `WhitneyReversibility.whole, `WhitneyReversibility.IsWhitneyMap, `WhitneyReversibility.IsSizeMap, `WhitneyReversibility.relativeLevel, `WhitneyReversibility.familyUnion, `WhitneyReversibility.IsDecomposable, `WhitneyReversibility.IsHereditarilyDecomposable] do
    let some info := env.find? name | throw <| IO.userError s!"Missing declaration: {name}"
    IO.println s!"RAW TYPE {name}"
    IO.println (reprStr info.levelParams)
    IO.println (reprStr info.type)
    if name ∈ #[`WhitneyReversibility.Continuum, `WhitneyReversibility.singleton, `WhitneyReversibility.whole, `WhitneyReversibility.IsWhitneyMap, `WhitneyReversibility.IsSizeMap, `WhitneyReversibility.relativeLevel, `WhitneyReversibility.familyUnion, `WhitneyReversibility.IsDecomposable, `WhitneyReversibility.IsHereditarilyDecomposable] then
      IO.println (reprStr info.value?)
