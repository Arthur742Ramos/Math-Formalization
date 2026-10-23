/- Source-bound audit fixture; proof axioms and runtime controls have distinct scopes.
Exact status is recorded in receipts. Original uncompiled v1 is preserved.
-/
module
public import GaussianCramerOutput
public meta import RationalGaussianKernel
@[expose] public section
open SparseCompletion.Gaussian

#check scaleTable
#check entry_scaleTable
#check firstNonzero_scale
#check residual_scale
#check lift_scale
#check residual_scaleTable
#check kernel_scaleTable
#check integerNumeratorTable
#check integerNumeratorTable_eq_scale
#check kernel_integerNumeratorTable
#check oneBorder
#check oneBorder_det
#check twoBorder_sylvester
#check twoBorder_residual_update
#check appendMap
#check selectedBlock
#check selectedBorder
#check unitSumFinTwo
#check appendTwoEquiv
#check selectedBorder_sylvester
#check PrefixIndex
#check prefixIndexFintype
#check prefixIndexDecidableEq
#check prefixIndexZeroIsEmpty
#check prefixIndex_card
#check MinorStage
#check minorStage_invariant
#check minor_quotient_height_any
#check intCast_det
#check minorStage_integer_height
#check columnStepEquiv
#check minorStage_dimensions
#check minorStage_columns_bijective
#check minorStage_remaining_val
#check minorStage_selected_zero
#check minorStage_rows_injective
#check minorStage_pivots_le_rows
#check kernel_terminal_trace
#check kernel_terminal_data
#check terminal_prefix_equation
#check det_smul_eq_cramer_mulVec
#check integer_system_cramer
#check integer_system_coordinate_height
#check kernel_integer_output_height
#check kernel_rational_output_height

#print axioms scaleTable
#print axioms entry_scaleTable
#print axioms firstNonzero_scale
#print axioms residual_scale
#print axioms lift_scale
#print axioms residual_scaleTable
#print axioms kernel_scaleTable
#print axioms integerNumeratorTable
#print axioms integerNumeratorTable_eq_scale
#print axioms kernel_integerNumeratorTable
#print axioms oneBorder
#print axioms oneBorder_det
#print axioms twoBorder_sylvester
#print axioms twoBorder_residual_update
#print axioms appendMap
#print axioms selectedBlock
#print axioms selectedBorder
#print axioms unitSumFinTwo
#print axioms appendTwoEquiv
#print axioms selectedBorder_sylvester
#print axioms PrefixIndex
#print axioms prefixIndexFintype
#print axioms prefixIndexDecidableEq
#print axioms prefixIndexZeroIsEmpty
#print axioms prefixIndex_card
#print axioms MinorStage
#print axioms minorStage_invariant
#print axioms minor_quotient_height_any
#print axioms intCast_det
#print axioms minorStage_integer_height
#print axioms columnStepEquiv
#print axioms minorStage_dimensions
#print axioms minorStage_columns_bijective
#print axioms minorStage_remaining_val
#print axioms minorStage_selected_zero
#print axioms minorStage_rows_injective
#print axioms minorStage_pivots_le_rows
#print axioms kernel_terminal_trace
#print axioms kernel_terminal_data
#print axioms terminal_prefix_equation
#print axioms det_smul_eq_cramer_mulVec
#print axioms integer_system_cramer
#print axioms integer_system_coordinate_height
#print axioms kernel_integer_output_height
#print axioms kernel_rational_output_height

/- Existing runtime controls for zero rows, zero columns, all independent
columns and two actual pivots. New proofs do not change the frozen program. -/
#eval (kernel 0 1 (tableOfFn (fun i => Fin.elim0 i))).map (fun w => w.toList)
#eval (kernel 1 0 (tableOfFn (fun _ j => Fin.elim0 j))).map (fun w => w.toList)
#eval (kernel 2 2 (tableOfFn (fun i j => if i = j then 1 else 0))).map
  (fun w => w.toList)
#eval (kernel 2 3 (tableOfFn (fun i j =>
  if j = 2 then 1 else if i.val = j.val then 1 else 0))).map (fun w => w.toList)
