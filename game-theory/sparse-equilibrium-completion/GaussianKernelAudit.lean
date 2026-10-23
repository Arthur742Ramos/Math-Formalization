module
public import RationalGaussianKernel
public import IntegerMinorHeight
public import RationalGaussianFeature
public meta import RationalGaussianKernel
public meta import RationalGaussianFeature
public section
#print axioms SparseCompletion.Gaussian.QVec
#print axioms SparseCompletion.Gaussian.QTable
#print axioms SparseCompletion.Gaussian.vecGet_ofFn
#print axioms SparseCompletion.Gaussian.tableOfFn
#print axioms SparseCompletion.Gaussian.entry
#print axioms SparseCompletion.Gaussian.entry_tableOfFn
#print axioms SparseCompletion.Gaussian.entry_tableOfFn_function
#print axioms SparseCompletion.Gaussian.dot
#print axioms SparseCompletion.Gaussian.IsKernel
#print axioms SparseCompletion.Gaussian.firstNonzero
#print axioms SparseCompletion.Gaussian.firstNonzero_none
#print axioms SparseCompletion.Gaussian.firstNonzero_some
#print axioms SparseCompletion.Gaussian.residual
#print axioms SparseCompletion.Gaussian.lift
#print axioms SparseCompletion.Gaussian.lift_succ
#print axioms SparseCompletion.Gaussian.dot_lift
#print axioms SparseCompletion.Gaussian.lift_tail_of_kernel
#print axioms SparseCompletion.Gaussian.kernel
#print axioms SparseCompletion.Gaussian.kernel_sound
#print axioms SparseCompletion.Gaussian.kernel_has_unit_coordinate
#print axioms SparseCompletion.Gaussian.kernel_none_injective
#print axioms SparseCompletion.Gaussian.kernel_complete
#print axioms SparseCompletion.Gaussian.kernel_none_iff
#print axioms SparseCompletion.Gaussian.quotient_num_height
#print axioms SparseCompletion.Gaussian.quotient_den_height
#print axioms SparseCompletion.Gaussian.determinant_height
#print axioms SparseCompletion.Gaussian.minor_quotient_height
#print axioms SparseCompletion.Gaussian.submatrix_determinant_height
#print axioms SparseCompletion.Gaussian.shared_denominator_ratio
#print axioms SparseCompletion.Gaussian.shared_minor_pivot_ratio_height
#print axioms SparseCompletion.Gaussian.residual_shared_minor_step
#print axioms SparseCompletion.Gaussian.clear_denominators_kernel_iff
#print axioms SparseCompletion.Gaussian.integer_first_residual
#print axioms SparseCompletion.Gaussian.residual_pivot_row_zero
#print axioms SparseCompletion.Gaussian.residual_preserves_zero_row
#print axioms SparseCompletion.gaussianFeatureRows
#print axioms SparseCompletion.gaussian_feature_equations_iff
#print axioms SparseCompletion.rationalGaussianFeatureKernel
#print axioms SparseCompletion.rational_gaussian_feature_sound
#print axioms SparseCompletion.rational_gaussian_feature_complete
#print axioms SparseCompletion.rationalGaussianFeatureDelete
#print axioms SparseCompletion.rational_gaussian_deletion_above_dimension

open SparseCompletion SparseCompletion.Gaussian
-- Execution evidence on a two-pivot dependency, injective/empty boundaries,
-- and actual feature deletion. These evaluations are not complexity claims.
#eval (kernel 2 3 (tableOfFn (fun i j =>
  if i = 0 then (if j = 1 then 0 else 1) else (if j = 0 then 0 else 1)))).map
  (fun v => v.toList)
#eval (kernel 2 2 (tableOfFn (fun i j => if i = j then 1 else 0))).map
  (fun v => v.toList)
#eval (kernel 0 1 (tableOfFn (fun i => Fin.elim0 i))).map (fun v => v.toList)
#eval (kernel 1 0 (tableOfFn (fun _ j => Fin.elim0 j))).map (fun v => v.toList)
#eval (rationalGaussianFeatureDelete (d := 1) (m := 2) (fun _ _ => 1)
  (fun _ => 1)).map List.ofFn
