module
import RationalDeletionLattice
meta import RationalFeatureDeletion
open SparseCompletion

#guard rationalFeatureTheta (![1/3, 2/3] : Fin 2 → ℚ) ![-1, 1] = 2/3
#guard List.ofFn (rationalFeatureDelete (![1/3, 2/3] : Fin 2 → ℚ) ![-1, 1]) = [1, 0]
#guard List.ofFn (rationalFeatureDelete (![1/3, 2/3] : Fin 2 → ℚ) ![1, -1]) = [0, 1]
#guard rationalFeatureTheta (![1/4, 3/4] : Fin 2 → ℚ) ![1/2, -1/2] = 1/2
#guard rationalFeatureTheta (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) = 0
#guard List.ofFn (rationalFeatureDelete (![1/3, 2/3] : Fin 2 → ℚ) ![0, 0]) = [1/3, 2/3]
