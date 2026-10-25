module
public import Descent
public import Examples
@[expose] public section
namespace ComputationalHodge.GeometricDescent
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology

def constantNullLoop : NullLoop OneLoop.system :=
  ⟨⟨(),.single ()⟩,_root_.Path.Homotopic.refl (_root_.Path.refl ())⟩

theorem constant_generator_killed :
    homologyMap OneLoop.presentation OneLoop.generator = 0 :=
  homologyMap_nullLoop OneLoop.presentation constantNullLoop

theorem geometric_homologyMap_not_injective :
    ¬ Function.Injective (homologyMap OneLoop.presentation) := by
  intro h
  apply OneLoop.generator_nonzero
  exact h (by rw [constant_generator_killed,map_zero])

theorem constant_cohomology_class_not_descending :
    OneLoop.cohomologyClass ∉ LinearMap.range (cohomologyMap OneLoop.presentation) := by
  intro h
  have hz := (cohomologyMap_range_iff _ _).mp h OneLoop.generator constant_generator_killed
  rw [OneLoop.evaluates_generator] at hz
  exact one_ne_zero hz

end ComputationalHodge.GeometricDescent
