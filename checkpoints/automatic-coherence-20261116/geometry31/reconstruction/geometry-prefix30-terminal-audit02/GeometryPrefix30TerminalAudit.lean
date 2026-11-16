import TopCatPushoutHomotopyInvariance

/-! SOURCE ONLY / UNCOMPILED. Positive terminal type/forward-map contracts and
selected dependency axioms. Not a complete public-declaration inventory, native
receipt, independent kernel check, negative control, or full-paper assertion. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology
namespace AutomaticCoherence.GeometryPrefix30TerminalAudit01
open DoubleCylinderCollapse01 DoubleCylinderComparison01 StrictSpanEquivalenceData01
open TopCatPushoutHomotopyInvariance01

variable {A B C A' B' C' : TopCat.{0}}
  {i : A ⟶ B} {j : A ⟶ C} {i' : A' ⟶ B'} {j' : A' ⟶ C'}

/-- Arbitrary actual double cylinders: no HEP or coherent inverse premise. -/
example (f : SpanMap i j i' j') (e : VerticalEquivalences f)
    (fd : DoubleCylinder i j) (fd' : DoubleCylinder i' j') :
    fd.D ≃ₕ fd'.D :=
  doubleEquivalence f e fd fd'

/-- The forward map is the literal strictly induced double-cylinder map. -/
example (f : SpanMap i j i' j') (e : VerticalEquivalences f)
    (fd : DoubleCylinder i j) (fd' : DoubleCylinder i' j') :
    (doubleEquivalence f e fd fd').toFun = (doubleMap f fd fd').hom :=
  doubleEquivalence_toFun f e fd fd'

variable {P P' : TopCat.{0}} {L : B ⟶ P} {R : C ⟶ P}
  {L' : B' ⟶ P'} {R' : C' ⟶ P'}

/-- Only the two original bare HEP hypotheses are required for ordinary pushouts. -/
example (f : SpanMap i j i' j') (e : VerticalEquivalences f)
    (hp : IsPushout i j L R) (hp' : IsPushout i' j' L' R')
    (hi : TopologicalHEPClosure01.HasHEP i)
    (hi' : TopologicalHEPClosure01.HasHEP i') :
    P ≃ₕ P' :=
  ordinaryEquivalence f e hp hp' hi hi'

/-- The forward map is the literal map of the given, not merely canonical, pushouts. -/
example (f : SpanMap i j i' j') (e : VerticalEquivalences f)
    (hp : IsPushout i j L R) (hp' : IsPushout i' j' L' R')
    (hi : TopologicalHEPClosure01.HasHEP i)
    (hi' : TopologicalHEPClosure01.HasHEP i') :
    (ordinaryEquivalence f e hp hp' hi hi').toFun = (ordinaryMap f hp hp').hom :=
  ordinaryEquivalence_toFun f e hp hp' hi hi'

end AutomaticCoherence.GeometryPrefix30TerminalAudit01

#print axioms AutomaticCoherence.TopologicalHEPClosure01.HasHEP
#print axioms AutomaticCoherence.TopologicalHEPClosure01.hasHEP_comp
#print axioms AutomaticCoherence.TopologicalHEPClosure01.hasHEP_pushout
#print axioms AutomaticCoherence.SimplexHomotopyExtension01.extendHomotopy
#print axioms AutomaticCoherence.SimplexHomotopyExtension01.extendHomotopy_bottom
#print axioms AutomaticCoherence.SimplexHomotopyExtension01.extendHomotopy_lateral
#print axioms AutomaticCoherence.DoubleCylinderCollapse01.sourceHomotopy
#print axioms AutomaticCoherence.DoubleCylinderCollapse01.targetHomotopy
#print axioms AutomaticCoherence.DoubleCylinderCollapse01.collapseEquivalence
#print axioms AutomaticCoherence.DoubleCylinderCollapse01.collapseEquivalence_toFun
#print axioms AutomaticCoherence.DoubleCylinderCollapse01.canonicalCollapseEquivalence
#print axioms AutomaticCoherence.DoubleCylinderCollapse01.canonicalCollapseEquivalence_toFun
#print axioms AutomaticCoherence.MappingCylinderInverseCompatibility01.inverseCompatibility
#print axioms AutomaticCoherence.MappingCylinderInverseCompatibility01.inverseCompatibility_free
#print axioms AutomaticCoherence.MappingCylinderLeftInverse01.leftInverse
#print axioms AutomaticCoherence.MappingCylinderLeftInverse01.leftInverse_free
#print axioms AutomaticCoherence.MappingCylinderLeftInverse01.leftInverse_base
#print axioms AutomaticCoherence.SplitDoubleCylinderInverse01.leftInverse
#print axioms AutomaticCoherence.SplitDoubleCylinderInverse01.equivalence
#print axioms AutomaticCoherence.SplitDoubleCylinderInverse01.equivalence_toFun
#print axioms AutomaticCoherence.SplitDoubleCylinderStrictMap01.equivalence
#print axioms AutomaticCoherence.SplitDoubleCylinderStrictMap01.equivalence_toFun
#print axioms AutomaticCoherence.SplitFullDoubleCylinder01.toFull_toSplit
#print axioms AutomaticCoherence.SplitFullDoubleCylinder01.toSplit_toFull
#print axioms AutomaticCoherence.SplitFullDoubleCylinder01.homeomorph
#print axioms AutomaticCoherence.SplitFullDoubleCylinderNaturality01.toFull_naturality
#print axioms AutomaticCoherence.DoubleCylinderComparison01.collapse_naturality
#print axioms AutomaticCoherence.HomotopyEquivalenceDescent01.descend
#print axioms AutomaticCoherence.HomotopyEquivalenceDescent01.descend_toFun
#print axioms AutomaticCoherence.StrictSpanEquivalenceData01.inverseData
#print axioms AutomaticCoherence.TopCatPushoutHomotopyInvariance01.splitEquivalence
#print axioms AutomaticCoherence.TopCatPushoutHomotopyInvariance01.splitEquivalence_toFun
#print axioms AutomaticCoherence.TopCatPushoutHomotopyInvariance01.doubleEquivalence
#print axioms AutomaticCoherence.TopCatPushoutHomotopyInvariance01.doubleEquivalence_toFun
#print axioms AutomaticCoherence.TopCatPushoutHomotopyInvariance01.ordinaryEquivalence
#print axioms AutomaticCoherence.TopCatPushoutHomotopyInvariance01.ordinaryEquivalence_toFun
