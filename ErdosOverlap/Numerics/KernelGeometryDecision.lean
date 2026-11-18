/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierPolynomialDirectFast

public meta import Lean.Elab.Tactic

namespace ErdosOverlap.Numerics
@[expose] public section

/-- The same input equality and five complete Horner results as `directCheckFast`. -/
structure CachedPolynomialTrace.FastConditions (t : CachedPolynomialTrace)
    (c : PolynomialBoxCache) (p : PolynomialPiece) (lo hi : ℚ) : Prop where
  inputCheck : t.inputs.check p lo hi = true
  rangeResult : t.trace.range.result = FixedBox.hornerBoxesPoint t.inputs.range c.coefficients
  primitiveLoResult : t.trace.primitiveLo.result = FixedBox.hornerBoxesPoint t.inputs.lo c.primitive
  primitiveHiResult : t.trace.primitiveHi.result = FixedBox.hornerBoxesPoint t.inputs.hi c.primitive
  weightedLoResult : t.trace.weightedLo.result = FixedBox.hornerBoxesPoint t.inputs.lo c.weightedPrimitive
  weightedHiResult : t.trace.weightedHi.result = FixedBox.hornerBoxesPoint t.inputs.hi c.weightedPrimitive

theorem CachedPolynomialTrace.directCheckFast_of_conditions {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (h : t.FastConditions c p lo hi) : t.directCheckFast c p lo hi = true := by
  simp only [CachedPolynomialTrace.directCheckFast, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.inputCheck, h.rangeResult, h.primitiveLoResult, h.primitiveHiResult,
    h.weightedLoResult, h.weightedHiResult⟩

end
end ErdosOverlap.Numerics

namespace ErdosOverlap.FrontierLeaves
open Numerics
open Lean Meta Elab Tactic

@[expose] public section

/-- Assemble the fourteen original checks using a single shared transport proof. -/
theorem Geometry.directTraceCheck_of_fast_conditions (g : Geometry)
    (ca cb : PolynomialBoxCache) (ta tb : CachedPolynomialTrace)
    (hg : g.Valid) (ha : ta.FastConditions ca g.patchA g.left g.right)
    (hb : tb.FastConditions cb g.patchB g.left g.right)
    (hcache : g.cache.tracedCheck ta.trace tb.trace g.patchA g.patchB = true) :
    g.directTraceCheck ca cb ta tb = true := by
  rw [← Geometry.directTraceCheckFast_eq]
  simp only [Geometry.directTraceCheckFast, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hg, CachedPolynomialTrace.directCheckFast_of_conditions ha⟩,
    CachedPolynomialTrace.directCheckFast_of_conditions hb⟩, hcache⟩

end

private meta def exposeFixedEndpoints (box : Expr) : MetaM Expr := do
  let value ← whnf box
  let args := value.getAppArgs
  if value.getAppFn.isConstOf ``FixedBox.mk && args.size == 2 then
    let lo ← whnf args[0]!
    let hi ← whnf args[1]!
    return mkApp2 value.getAppFn lo hi
  return box

private meta def canonicalCacheProjection (coefficients : Expr) : Expr := Id.run do
  let family := coefficients.getAppFn
  let args := coefficients.getAppArgs
  if args.size != 1 then return coefficients
  if !(family.isConstOf ``PolynomialBoxCache.coefficients ||
      family.isConstOf ``PolynomialBoxCache.primitive ||
      family.isConstOf ``PolynomialBoxCache.weightedPrimitive) then
    return coefficients
  let cache := args[0]!
  let projArgs := cache.getAppArgs
  if cache.getAppFn.isConstOf ``Subtype.val && projArgs.size == 3 then
    return mkApp family (.proj ``Subtype 0 projArgs[2]!)
  return coefficients

public section

/-- Expose only the stored input and output endpoints. Leave the fold and the
coefficient list unevaluated. Use the primitive projection for the cache
subtype so equivalent predicates do not distinguish closed auxiliary lemmas. -/
elab "erdos_decide_repeated_horner" : tactic => do
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    if let some (_, result, checked) := target.eq? then
      let fn := checked.getAppFn
      let args := checked.getAppArgs
      if fn.isConstOf ``FixedBox.hornerBoxesPoint && args.size == 2 then
        let result' ← exposeFixedEndpoints result
        let input' ← exposeFixedEndpoints args[0]!
        let coefficients := canonicalCacheProjection args[1]!
        let replacement ← mkEq result' (mkApp2 fn input' coefficients)
        let newGoal ← goal.change replacement
        replaceMainGoal [newGoal]
  evalTactic (← `(tactic| decide +kernel))

macro "erdos_geometry_decide" : tactic =>
  `(tactic| (
    refine Geometry.directTraceCheck_of_fast_conditions _ _ _ _ _ ?_
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
    all_goals erdos_decide_repeated_horner
  ))

end
end ErdosOverlap.FrontierLeaves
