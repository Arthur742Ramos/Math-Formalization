module
public import Lean.Environment
@[expose] public section
open Lean
def main (args : List String) : IO Unit := do
  let [moduleName] := args | throw <| IO.userError "Expected one module name"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := moduleName.toName }] {} (level := .exported)
  for name in #[`HyperspaceComponents.proper_familyUnion, `HyperspaceComponents.joined_iff_common_continuum, `HyperspaceComponents.joined_iff_same_composant, `HyperspaceComponents.pathComponent_eq_composant, `HyperspaceComponents.uncountably_many_path_components, `HyperspaceComponents.no_proper_continuum_of_subsingleton, `Composants.IsSubcontinuum, `Composants.IsIndecomposable, `Composants.composant, `HyperspaceComponents.familyUnion, `HyperspaceComponents.ProperContinuum] do
    let some info := env.find? name | throw <| IO.userError s!"Missing declaration: {name}"
    IO.println s!"RAW TYPE {name}"
    IO.println (reprStr info.levelParams)
    IO.println (reprStr info.type)
    if name ∈ #[`Composants.IsSubcontinuum, `Composants.IsIndecomposable, `Composants.composant, `HyperspaceComponents.familyUnion, `HyperspaceComponents.ProperContinuum] then
      IO.println (reprStr info.value?)
