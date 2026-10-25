module
public import Descent
public import Examples
@[expose] public section
namespace ComputationalHodge.GeometricDescent
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology

def constantNullLoop : NullLoop OneLoop.system :=
  ⟨⟨(),.single ()⟩,_root_.Path.Homotopic.refl (_root_.Path.refl ())⟩


end ComputationalHodge.GeometricDescent
