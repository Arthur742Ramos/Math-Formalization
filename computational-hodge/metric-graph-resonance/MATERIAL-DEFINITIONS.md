# Material definitions: incomplete draft

This file is a source-bound review draft. It is not a completed inventory, independent semantic review, compiled bridge or release evidence.

The retained Finset.prod source generates Finset.sum via to_additive. The sum and finite-univ semantic bridges remain uncompiled. Actual Bochner integral and volume meaning remain subject to review.

## HasDerivAtFilter

The scalar derivative along the explicitly stated filter, expressed through a one-dimensional continuous linear map.

Dependency expansion: HasFDerivAtFilter for the scalar toSpanSingleton continuous linear map and the stated product filter. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphResonancePrototype.sine_wronskian, MetricGraphResonancePrototype.cosine_wronskian, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphResonancePrototype.theta_forcing_obstruction, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

## HasDerivAt

The local scalar derivative at the stated real point; the interval system quantifies this only on each open edge interior.

Dependency expansion: HasDerivAtFilter over nhds x ×ˢ pure x; filter derivative expands to HasFDerivAtFilter for toSpanSingleton. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**statement_or_definition**: MetricGraphResonancePrototype.sine_wronskian, MetricGraphResonancePrototype.cosine_wronskian, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphResonancePrototype.theta_forcing_obstruction

## HasFDerivAtFilter

The Fréchet derivative along the stated filter, expressed by the little-o remainder; it does not itself assert an unrestricted global derivative.

Dependency expansion: Structure field is a little-o remainder between pairs of points along the specified filter. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphResonancePrototype.sine_wronskian, MetricGraphResonancePrototype.cosine_wronskian, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphResonancePrototype.theta_forcing_obstruction, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

## Continuous

Inverse images of open sets are open.

Dependency expansion: A structure asserting preimages of open sets are open. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**semantic_expansion**: ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize, MetricGraphPathPrototype.edgePath, MetricGraphTraceParametric.single_chart, MetricGraphTraceParametric.trans_chart_left, MetricGraphTraceParametric.trans_chart_right, MetricGraphTraceParametric.symm_chart, MetricGraphTraceParametric.realizedTrace_ae_local_velocity

**statement_or_definition**: MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.continuous_edge_extension

## ContinuousWithinAt

Actual Tendsto from the neighborhood-within filter to the target neighborhood.

Dependency expansion: Tendsto from the within-set neighborhood filter to the target neighborhood filter. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.continuous_edge_extension, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.theta_forcing_obstruction

## ContinuousOn

Actual pointwise ContinuousWithinAt at each member of the set. It is not global continuity.

Dependency expansion: For every point in the set, ContinuousWithinAt holds; this does not assert global continuity. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.continuous_edge_extension, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.theta_forcing_obstruction

## Set.EqOn

Actual pointwise equality on a specified set; retained as conservative infrastructure without a separate uniqueness claim.

Dependency expansion: Pointwise equality at every element of the named set. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphResonancePrototype.continuous_edge_extension, MetricGraphResonancePrototype.edge_moment_congr

## Set.Ioo

The open order interval contains exactly points strictly between its endpoints.

Dependency expansion: Membership is the conjunction of strict lower and upper inequalities. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**statement_or_definition**: MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphResonancePrototype.theta_forcing_obstruction

## Set.Icc

The closed order interval; used for edge continuity and the unit-interval chart.

Dependency expansion: Membership is the conjunction of weak lower and upper inequalities. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.continuous_edge_extension, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.edge_moment_congr, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.single_chart, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.theta_forcing_obstruction

## Set.Ioc

Actual strict lower and weak upper endpoint inequalities; the interval integral uses the corresponding restricted measure.

Dependency expansion: Membership has a strict lower and weak upper inequality. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceDensity.concat_density_integrable, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.concat_right_integral, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.edge_moment_congr, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphPathPrototype.graphPotential, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphPathPrototype.rawPotential, MetricGraphPathPrototype.rawPotential_glue, MetricGraphTraceDensity.reverse_density_integrable, MetricGraphTraceDensity.reverse_density_integral, MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.theta_cosine_balance, MetricGraphPathPrototype.traceChartIntegral, MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.traceDensity_integral

## IntervalIntegrable

Actual integrability on both oriented Ioc intervals.

Dependency expansion: IntegrableOn holds for both directed Ioc restrictions. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**statement_or_definition**: MetricGraphTraceDensity.concat_density_integrable, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.reverse_density_integrable, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.traceDensity_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments

## intervalIntegral

Actual ordinary oriented Bochner integral: forward Ioc integral minus backward Ioc integral.

Dependency expansion: The Bochner integral over Ioc(a,b) minus that over Ioc(b,a), for the supplied measure. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphResonancePrototype.theta_forcing_obstruction

**semantic_expansion**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff

**statement_or_definition**: MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.edge_moment_congr, MetricGraphPathPrototype.rawPotential, MetricGraphPathPrototype.rawPotential_glue, MetricGraphPathPrototype.graphPotential, MetricGraphPathPrototype.traceChartIntegral, MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference, MetricGraphTraceDensity.concat_right_integral, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.reverse_density_integral, MetricGraphTraceParametric.traceDensity_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.theta_cosine_balance

## MeasureTheory.IntegrableOn

Actual integrability against the measure restricted to the set.

Dependency expansion: Integrable against the measure restricted to the named set. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_semantic_expansion**: MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**semantic_expansion**: MetricGraphTraceDensity.concat_density_integrable, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.reverse_density_integrable, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.traceDensity_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments

## MeasureTheory.Integrable

Actual almost-everywhere strong measurability and finite norm integral.

Dependency expansion: Almost-everywhere strong measurability and finite norm integral. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_semantic_expansion**: MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**semantic_expansion**: MetricGraphTraceDensity.concat_density_integrable, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.reverse_density_integrable, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.traceDensity_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments

## MeasureTheory.ae

Actual conull-set filter; quantified assertions mean the set of failures has measure zero, via the retained null-complement equivalence.

Dependency expansion: The filter of properties holding outside measure-zero sets; the null-complement theorem requires its own contract. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphTraceParametric.realizedTrace_ae_local_velocity

## Filter.Eventually

Actual membership of the predicate truth set in the filter, underlying almost-everywhere quantification.

Dependency expansion: Membership of the truth set in the named filter. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphTraceParametric.realizedTrace_ae_local_velocity

## Irrational

The real number lies outside the range of the rational coercion; used in the almost-everywhere proof.

Dependency expansion: Negated membership in the range of the coercion from rationals to reals. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphTraceParametric.realizedTrace_ae_local_velocity

## Relation.EqvGen

The least reflexive, symmetric and transitive relation containing the edge relation.

Dependency expansion: Inductive least equivalence closure with rel, refl, symm and trans constructors. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphResonanceIncidence.reachable_delta_flow, MetricGraphResonanceIncidence.exists_divergence_of_sum_zero, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.exists_vertex_trace, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

## Fintype

A finite enumeration of the named index type, used for finite vertex and edge sums or the finite example; the glued graph point space is not asserted finite.

Dependency expansion: A class supplying a finite enumeration; finite univ and generated Finset.sum require separate bridges. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphResonanceIncidence.divergence, MetricGraphResonanceIncidence.divergenceLinear, MetricGraphResonanceIncidence.divergence_edge_unit, MetricGraphResonanceIncidence.reachable_delta_flow, MetricGraphResonanceIncidence.exists_divergence_of_sum_zero, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.theta_cosine_balance

## LinearMap

An additive and scalar-compatible map; the selected divergenceLinear sends finite edge data to vertex data.

Dependency expansion: An additive and scalar-compatible function between the stated modules. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphResonanceIncidence.reachable_delta_flow, MetricGraphResonanceIncidence.exists_divergence_of_sum_zero

**statement_or_definition**: MetricGraphResonanceIncidence.divergenceLinear

## Path

A continuous interval map with its two actual endpoint equations.

Dependency expansion: A continuous map on the unit interval with explicit source and target endpoint equations. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphTraceParametric.single_chart, MetricGraphTraceParametric.trans_chart_left, MetricGraphTraceParametric.trans_chart_right, MetricGraphTraceParametric.symm_chart, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphPathPrototype.edgeStepSystem, MetricGraphTraceParametric.traceDensity

**statement_or_definition**: ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize, MetricGraphPathPrototype.edgePath

## Path.refl

The constant continuous path.

Dependency expansion: The constant path at the specified point. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**selected_definition_body**: ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize

## Path.symm

Reversal of an actual continuous path.

Dependency expansion: The path composed with the unit-interval reversal; endpoints swap. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphTraceParametric.symm_chart

**selected_definition_body**: ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize

**transitive_proof_dependency**: MetricGraphTraceParametric.realizedTrace_ae_local_velocity

## Path.trans

Binary parametrized concatenation; it is not identified with equal-slot flattening.

Dependency expansion: Path concatenation rescales the first and second paths to the respective half intervals. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphTraceParametric.trans_chart_left, MetricGraphTraceParametric.trans_chart_right

**selected_definition_body**: ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize

**transitive_proof_dependency**: MetricGraphTraceParametric.realizedTrace_ae_local_velocity

## Path.extend

The continuous real extension is constant outside the unit interval.

Dependency expansion: IccExtend produces a continuous real-domain extension, clamped outside the unit interval. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphTraceParametric.single_chart, MetricGraphTraceParametric.trans_chart_left, MetricGraphTraceParametric.trans_chart_right, MetricGraphTraceParametric.symm_chart, MetricGraphTraceParametric.realizedTrace_ae_local_velocity

**semantic_expansion**: ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize

## Real.sin

Actual real part of complex sine applied to a real input.

Dependency expansion: The real part of the complex sine on the real embedding; its transitive definition remains to be reviewed. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphResonancePrototype.theta_forcing_obstruction

**semantic_expansion**: MetricGraphResonancePrototype.theta_cosine_balance, MetricGraphResonancePrototype.theta_forcing_obstruction

**statement_or_definition**: MetricGraphResonancePrototype.sine_wronskian, MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.cosine_wronskian, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.thetaForce

## Real.cos

The real part of complex cosine on a real argument; the graph criterion uses the stated endpoint conditions and cosine moments.

Dependency expansion: The real part of the complex cosine on the real embedding; its transitive definition remains to be reviewed. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphResonancePrototype.theta_forcing_obstruction

**statement_or_definition**: MetricGraphResonancePrototype.sine_wronskian, MetricGraphResonancePrototype.cosine_wronskian, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.theta_cosine_balance

## Real.pi

The pinned real pi constant, used by the sine-square calculation and concrete three-edge forcing.

Dependency expansion: Twice the selected real zero of cosine in the retained existence theorem. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.thetaForce, MetricGraphResonancePrototype.theta_cosine_balance, MetricGraphResonancePrototype.theta_forcing_obstruction

## MeasureTheory.integral

The ordinary Bochner integral, totalized outside its integrability domain; the stated edge and trace results use oriented interval integrals with their own assumptions.

Dependency expansion: The irreducible Bochner integral returns its L1 integral when complete-space and integrability conditions hold, and zero otherwise. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphResonancePrototype.theta_forcing_obstruction

**semantic_expansion**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff

**statement_or_definition**: MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.edge_moment_congr, MetricGraphPathPrototype.rawPotential, MetricGraphPathPrototype.rawPotential_glue, MetricGraphPathPrototype.graphPotential, MetricGraphPathPrototype.traceChartIntegral, MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference, MetricGraphTraceDensity.concat_right_integral, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.reverse_density_integral, MetricGraphTraceParametric.traceDensity_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.theta_cosine_balance

## MeasureTheory.MeasureSpace

A measurable space equipped with the volume measure field.

Dependency expansion: A measurable space equipped with a volume measure field; the real instance and its meaning require separate review. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**proof_dependency**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphResonancePrototype.theta_forcing_obstruction

**semantic_expansion**: MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff

**statement_or_definition**: MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.edge_moment_congr, MetricGraphPathPrototype.rawPotential, MetricGraphPathPrototype.rawPotential_glue, MetricGraphPathPrototype.graphPotential, MetricGraphPathPrototype.traceChartIntegral, MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference, MetricGraphTraceDensity.concat_right_integral, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.reverse_density_integral, MetricGraphTraceParametric.traceDensity_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.theta_cosine_balance, MetricGraphTraceDensity.concat_density_integrable, MetricGraphTraceDensity.reverse_density_integrable, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.realizedTrace_ae_local_velocity

## unitInterval

The actual path-parameter carrier is the real closed interval [0,1].

Dependency expansion: unitInterval is Set.Icc 0 1; elements used by graph edge charts carry the interval-membership proof. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphPathPrototype.Graph, MetricGraphPathPrototype.vertex, MetricGraphPathPrototype.edgePoint, MetricGraphPathPrototype.edgePoint_zero, MetricGraphPathPrototype.edgePoint_one, MetricGraphPathPrototype.edgePath, MetricGraphPathPrototype.edgeStepSystem, MetricGraphPathPrototype.rawPotential, MetricGraphPathPrototype.rawPotential_glue, MetricGraphPathPrototype.graphPotential, MetricGraphPathPrototype.traceChartIntegral, MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference, MetricGraphTraceParametric.single_chart, MetricGraphTraceParametric.trans_chart_left, MetricGraphTraceParametric.trans_chart_right, MetricGraphTraceParametric.symm_chart, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphTraceParametric.traceDensity

## TopologicalSpace

The topology class supplies the open-set structure on the named carriers; no metric or manifold structure is asserted.

Dependency expansion: TopologicalSpace provides its IsOpen predicate and the univ, finite-intersection and arbitrary-union laws. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**statement_or_definition**: ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize, MetricGraphPathPrototype.edgePath, MetricGraphPathPrototype.edgeStepSystem, MetricGraphTraceParametric.traceDensity, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.traceDensity_integral, MetricGraphTraceParametric.single_chart, MetricGraphTraceParametric.trans_chart_left, MetricGraphTraceParametric.trans_chart_right, MetricGraphTraceParametric.symm_chart, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphTraceParametric.exists_vertex_trace, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

## Set

A set on a type is a predicate on its elements.

Dependency expansion: Set α unfolds to α → Prop; the concrete interval and continuity meanings are recorded separately. Further dependency closure and per-use accuracy remain subject to independent review.

Proof status: DRAFT: no current-successor bridge compilation, completeness or semantic-fidelity pass is asserted.

**semantic_expansion**: MetricGraphPathPrototype.Graph, MetricGraphPathPrototype.edgePath, MetricGraphPathPrototype.edgePoint, MetricGraphPathPrototype.graphPotential, MetricGraphPathPrototype.rawPotential, MetricGraphPathPrototype.rawPotential_glue, MetricGraphPathPrototype.traceChartIntegral, MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference, MetricGraphResonancePrototype.continuous_edge_extension, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.edge_moment_congr, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.theta_cosine_balance, MetricGraphResonancePrototype.theta_forcing_obstruction, MetricGraphTraceDensity.concat_density_integrable, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.concat_right_integral, MetricGraphTraceDensity.reverse_density_integrable, MetricGraphTraceDensity.reverse_density_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphTraceParametric.single_chart, MetricGraphTraceParametric.traceDensity, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.traceDensity_integral

## Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean

SHA-256: e935efa96ad9381658f3158f900d04589c46d7e933cab15f4d8632e1af85527f

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Finset.sum generated producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean#L59-L69

```lean
/-- `∏ x ∈ s, f x` is the product of `f x` as `x` ranges over the elements of the finite set `s`.

When the index type is a `Fintype`, the notation `∏ x, f x`, is a shorthand for
`∏ x ∈ Finset.univ, f x`. -/
@[to_additive /-- `∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`.

When the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for
`∑ x ∈ Finset.univ, f x`. -/]
protected def prod [CommMonoid M] (s : Finset ι) (f : ι → M) : M :=
  (s.1.map f).prod
```

## Mathlib/Algebra/Module/LinearMap/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean

SHA-256: aea1c354ffc798aaa5397f2f58124bc2ed7b29d24227ae568d3f5745f839570d

```lean
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/```

### LinearMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean#L85-L99

```lean
structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂

/-- The `MulActionHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toMulActionHom

/-- The `AddHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toAddHom

/-- `M →ₛₗ[σ] N` is the type of `σ`-semilinear maps from `M` to `N`. -/
notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

/-- `M →ₗ[R] N` is the type of `R`-linear maps from `M` to `N`. -/
notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂
```

## Mathlib/Analysis/Calculus/Deriv/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean

SHA-256: f4c0077cb0e87c857f1fcfea2c9c6263d1a3dee9fa8403893e00debf28a4356b

```lean
/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/```

### HasDerivAtFilter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L116-L117

```lean
def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (L : Filter (𝕜 × 𝕜)) :=
  HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L
```

### HasDerivAt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L130-L131

```lean
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)
```

## Mathlib/Analysis/Calculus/FDeriv/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean

SHA-256: 27a7410d70541ab4a947cc95c30b16583d1f89fc073ca47e76c978b0b22f13ba

```lean
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/```

### HasFDerivAtFilter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L110-L112

```lean
structure HasFDerivAtFilter (f : E → F) (f' : E →L[𝕜] F) (L : Filter (E × E)) : Prop where
  of_isLittleOTVS ::
    isLittleOTVS : (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p ↦ p.1 - p.2)
```

## Mathlib/Analysis/Complex/Trigonometric.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Trigonometric.lean

SHA-256: b63dc0d49ca3deb88ffb47292745448b2611bf2d43b4ea05931628f8aa286b3b

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/```

### Real.sin

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Trigonometric.lean#L71-L74

```lean
/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
nonrec def sin (x : ℝ) : ℝ :=
  (sin x).re
```

### Real.cos

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Trigonometric.lean#L76-L79

```lean
/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
nonrec def cos (x : ℝ) : ℝ :=
  (cos x).re
```

## Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean

SHA-256: c8933a580347acc3ee7cf731a9034cff1d6e818be36d9323876d1f12a7b25ee4

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/```

### Real.pi

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean#L124-L129

```lean
see `Mathlib/Analysis/Real/Pi/Bounds.lean`.

Denoted `π`, once the `Real` namespace is opened. -/
@[wikidata Q167]
protected noncomputable def pi : ℝ :=
  2 * Classical.choose exists_cos_eq_zero
```

## Mathlib/Data/Fintype/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean

SHA-256: e69e8e7a3605d293a7ef6c4a7aaefde3191da4f33b43b7be09963eec2e44965c

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/```

### Fintype

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean#L57-L65

```lean
class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems

/-! ### Preparatory lemmas -/

namespace Finset
```

## Mathlib/Data/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

SHA-256: 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/```

### Set

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L51-L51

```lean
def Set (α : Type u) := α → Prop
```

## Mathlib/Data/Set/Operations.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

SHA-256: 60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/```

### Set.EqOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L290-L291

```lean
/-- Two functions `f₁ f₂ : α → β` are equal on `s` if `f₁ x = f₂ x` for all `x ∈ s`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x
```

## Mathlib/Logic/Relation.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Relation.lean

SHA-256: 2b678f33904c7e073de526d9d3243909e5d7d72bc0eed7f4cf9e65f443b72547

```lean
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Relation.EqvGen

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Relation.lean#L408-L417

```lean
variable (r) in
/-- `EqvGen r`: equivalence closure of `r`. -/
@[mk_iff]
inductive EqvGen : α → α → Prop
  | rel x y : r x y → EqvGen x y
  | refl x : EqvGen x x
  | symm x y : EqvGen x y → EqvGen y x
  | trans x y z : EqvGen x y → EqvGen y z → EqvGen x z

attribute [mk_iff] TransGen
```

## Mathlib/MeasureTheory/Function/L1Space/Integrable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean

SHA-256: 27797fe4384b5a8f3fab05c4c5b7d1b4f98c3801a9c441d7f75272d4f095df42

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/```

### Integrable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L59-L61

```lean
def Integrable {α} {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ
```

## Mathlib/MeasureTheory/Integral/Bochner/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean

SHA-256: a6341a15d805c17e6922cd9c3f69508d604574058e37b06ec8cb51626ebbfa4d

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/```

### ordinary_Bochner_integral

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L158-L161

```lean
irreducible_def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α → G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
  else 0
```

## Mathlib/MeasureTheory/Integral/IntegrableOn.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntegrableOn.lean

SHA-256: 4195a3becfc509b18adfbfc541dfd11a5a0f16954193e42e8d629a025636d0f9

```lean
/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/```

### IntegrableOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntegrableOn.lean#L92-L93

```lean
def IntegrableOn (f : α → ε) (s : Set α) (μ : Measure α := by volume_tac) : Prop :=
  Integrable f (μ.restrict s)
```

## Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean

SHA-256: 97e7a2efda146d0d1280f23d660cc07655dd7c48b51631752e9aa94deaa18ab9

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/```

### IntervalIntegrable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L74-L75

```lean
def IntervalIntegrable (f : ℝ → ε) (μ : Measure ℝ) (a b : ℝ) : Prop :=
  IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ
```

### intervalIntegral

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L659-L668

```lean
def intervalIntegral (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) : E :=
  (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ

@[inherit_doc intervalIntegral]
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"μ:70 => intervalIntegral r a b μ

/-- The interval integral `∫ x in a..b, f x` is defined
as `∫ x in Ioc a b, f x - ∫ x in Ioc b a, f x`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x`, otherwise it equals `-∫ x in Ioc b a, f x`. -/
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => intervalIntegral f a b volume) => r
```

## Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean

SHA-256: 628bcfc45fabd59501cdebf1cc3a8003ef3aba18fc7de4710ca9ffc1033b32d7

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/```

### real_Lebesgue_volume

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L54-L77

```lean
theorem volume_eq_stieltjes_id : (volume : Measure ℝ) = StieltjesFunction.id.measure := by
  have : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
      Eq.symm <|
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis ℝ ℝ)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis ℝ ℝ) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped, A]
  simp only [volume, Module.Basis.addHaar, one_smul]

theorem volume_val (s) : volume s = StieltjesFunction.id.measure s := by
  simp [volume_eq_stieltjes_id]

@[simp]
theorem volume_Ico {a b : ℝ} : volume (Ico a b) = ofReal (b - a) := by simp [volume_val]

```

## Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean

SHA-256: 9e7e2105e21cdb7dbe731515213bcd1f6cf78c902bcd2da7f33b468218d90664

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/```

### volume_measure_class

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean#L356-L359

```lean
class MeasureSpace (α : Type*) extends MeasurableSpace α where
  volume : Measure α

export MeasureSpace (volume)
```

## Mathlib/MeasureTheory/OuterMeasure/AE.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/OuterMeasure/AE.lean

SHA-256: de58d3b2aa42d801e9a268df285c32e5aa6ca7ffc5b42bf5eff8f12bda87a00d

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/```

### MeasureTheory.ae

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/OuterMeasure/AE.lean#L49-L52

```lean
def ae (μ : F) : Filter α :=
  .ofCountableUnion (μ · = 0) (fun _S hSc ↦ (measure_sUnion_null_iff hSc).2) fun _t ht _s hs ↦
    measure_mono_null hs ht
deriving CountableInterFilter
```

### AE_null_complement_contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/OuterMeasure/AE.lean#L132-L136

```lean
theorem mem_ae_iff {s : Set α} : s ∈ ae μ ↔ μ sᶜ = 0 :=
  Iff.rfl

theorem ae_iff {p : α → Prop} : (∀ᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0 :=
  Iff.rfl
```

## Mathlib/NumberTheory/Real/Irrational.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/NumberTheory/Real/Irrational.lean

SHA-256: 7f30a8a7ea3bc37867a9aff2fe63a5559996abe6a53a63554a8f952ef841bcbb

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov
-/
```

### Irrational

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/NumberTheory/Real/Irrational.lean#L34-L39

```lean

/-- A real number is irrational if it is not equal to any rational number. -/
@[wikidata Q607728]
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

```

## Mathlib/Order/Filter/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

SHA-256: d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/```

### Filter.Eventually

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L281-L282

```lean
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
```

## Mathlib/Order/Interval/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean

SHA-256: 53970116254a7e705eb85f92c9236be431966dbd61c1c1315a914a6d05e39b7b

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Set.Ioo

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L48-L53

```lean

/-- `Ioo a b` is the left-open right-open interval $(a, b)$. -/
@[to_dual self (reorder := a b)]
def Ioo (a b : α) := { x | a < x ∧ x < b }

to_dual_insert_cast Ioo := by simp only [and_comm]
```

### Set.Icc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L75-L76

```lean
@[to_dual self (reorder := a b)]
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }
```

### Set.Ioc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L62-L63

```lean
@[to_dual existing (reorder := a b)]
def Ioc (a b : α) := { x | a < x ∧ x ≤ b }
```

## Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA-256: 6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/```

### Continuous

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

### TopologicalSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L73-L85

```lean
class TopologicalSpace (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}
```

## Mathlib/Topology/Defs/Filter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

SHA-256: 3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/```

### ContinuousWithinAt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L185-L186

```lean
def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))
```

### ContinuousOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L188-L192

```lean
/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
@[fun_prop]
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
```

## Mathlib/Topology/Path.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean

SHA-256: 91c8fa5452d85bc35258afd61de0b694e82ae483d35d9257b599ce7eaddab038

```lean
/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/```

### Path

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L60-L64

```lean
structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y
```

### Path.refl

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L143-L147

```lean
def refl (x : X) : Path x x where
  toContinuousMap := .const I x
  source' := rfl
  target' := rfl

```

### Path.symm

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L153-L158

```lean
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

```

### Path.trans

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L277-L292

```lean
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by simp)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by simp
  target' := by norm_num

@[grind =]
theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_apply]
```

### Path.extend

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L188-L199

```lean
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) ↦ ContinuousMap.mk (g y))⟩

/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
def extend : C(ℝ, X) where
  toFun := IccExtend zero_le_one γ

/-- See Note [continuity lemma statement]. -/
@[continuity, fun_prop]
theorem _root_.Continuous.pathExtend {γ : Y → Path x y} {f : Y → ℝ} (hγ : Continuous ↿γ)
    (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.IccExtend hγ hf
```

### actual_path_reversal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L151-L160

```lean
/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps (attr := grind =)]
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
theorem symm_symm (γ : Path x y) : γ.symm.symm = γ := by grind
```

### actual_path_concatenation

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L274-L292

```lean
/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by simp)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by simp
  target' := by norm_num

@[grind =]
theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_apply]
```

## Mathlib/Topology/UnitInterval.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UnitInterval.lean

SHA-256: afaccfe8ef4d9ea05189b3bd50e0dbf58cb6b4e3f86441b2d4d55aef06c2626b

```lean
/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/```

### unitInterval

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UnitInterval.lean#L29-L41

```lean


/-- The unit interval `[0,1]` in ℝ. -/
abbrev unitInterval : Set ℝ :=
  Set.Icc 0 1

@[inherit_doc]
scoped[unitInterval] notation "I" => unitInterval

namespace unitInterval

theorem zero_mem : (0 : ℝ) ∈ I :=
  ⟨le_rfl, zero_le_one⟩
```


## Selected local formulas without separate imported-predicate rows

Independent source review identified the following selected definitions as local formulas whose own bodies do not introduce a further material imported predicate requiring a new row. They still depend on the stated foundational equality, real order and arithmetic; later trace consumers also use the imported path and integrability semantics recorded above. This is not a claim that all transitive dependency closure has been independently established.

- `MetricGraphResonanceIncidence.vertexDelta` is the real-valued equality indicator of the named vertex, using decidable equality and the constants zero and one.
- `MetricGraphTraceDensity.concatDensity` selects between the two real-valued functions under the `x ≤ 1/2` test, with the displayed doubling/rescaling and subtraction operations.
- `MetricGraphTraceDensity.reverseDensity` is the scalar function `x ↦ -f (1 - x)`.

## Nested unit-interval expansions

The path parameter `unitInterval` is `Set.Icc (0 : ℝ) 1`; the following selected uses therefore also involve the named closed interval and its underlying set semantics. These are semantic expansions, not additional hypotheses.

- `Set.Icc`: `MetricGraphPathPrototype.Graph`, `MetricGraphPathPrototype.edgePath`, `MetricGraphPathPrototype.edgePoint`, `MetricGraphPathPrototype.edgePoint_one`, `MetricGraphPathPrototype.edgePoint_zero`, `MetricGraphPathPrototype.edgeStepSystem`, `MetricGraphPathPrototype.graphPotential`, `MetricGraphPathPrototype.rawPotential`, `MetricGraphPathPrototype.rawPotential_glue`, `MetricGraphPathPrototype.traceChartIntegral`, `MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference`, `MetricGraphPathPrototype.vertex`, `MetricGraphTraceParametric.realizedTrace_ae_local_velocity`, `MetricGraphTraceParametric.single_chart`, `MetricGraphTraceParametric.symm_chart`, `MetricGraphTraceParametric.traceDensity`, `MetricGraphTraceParametric.trans_chart_left`, `MetricGraphTraceParametric.trans_chart_right`
- `Set`: `MetricGraphPathPrototype.edgePoint_one`, `MetricGraphPathPrototype.edgePoint_zero`, `MetricGraphPathPrototype.edgeStepSystem`, `MetricGraphPathPrototype.vertex`, `MetricGraphTraceParametric.symm_chart`, `MetricGraphTraceParametric.trans_chart_left`, `MetricGraphTraceParametric.trans_chart_right`

## Generated finite sum and real volume: draft contracts

### Finset.sum

The generated additive finite sum over the specified Finset; the unindexed finite-type notation uses Finset.univ.

The retained to_additive-annotated Finset.prod source generates Finset.sum. Actual generated sum and Finset.univ value/type contracts require separate compiled bridges.

DRAFT: generated declaration, per-use completeness and both bridge builds remain unverified.

**statement_or_definition**: MetricGraphResonanceIncidence.divergence, MetricGraphResonancePrototype.intervalGraphSolution, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonanceIncidence.exists_divergence_of_sum_zero, MetricGraphResonancePrototype.theta_cosine_balance, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**semantic_expansion**: MetricGraphResonanceIncidence.divergenceLinear, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphResonanceIncidence.divergence_edge_unit, MetricGraphResonanceIncidence.reachable_delta_flow

**proof_dependency**: MetricGraphResonanceIncidence.divergence_edge_unit, MetricGraphResonanceIncidence.reachable_delta_flow, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonanceIncidence.divergenceLinear, MetricGraphResonanceIncidence.exists_divergence_of_sum_zero, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals

**transitive_proof_dependency**: MetricGraphResonancePrototype.forced_connected_graph_interval_iff

### Real.volume_eq_stieltjes_id

The specific real volume measure equals the measure of the identity Stieltjes function; this does not identify arbitrary measures with real volume.

This theorem supplies the real-volume identification used in the stated real interval and almost-everywhere semantics. The Stieltjes measure and null-complement contracts require separate review and bridge compilation.

DRAFT: per-use completeness, actual real-volume bridge and both source-bound builds remain unverified.

**semantic_expansion**: MetricGraphPathPrototype.graphPotential, MetricGraphPathPrototype.rawPotential, MetricGraphPathPrototype.rawPotential_glue, MetricGraphPathPrototype.traceChartIntegral, MetricGraphPathPrototype.traceChartIntegral_eq_potential_difference, MetricGraphResonancePrototype.cosine_moment_identity_interval, MetricGraphResonancePrototype.edge_moment_congr, MetricGraphResonancePrototype.forced_connected_graph_interval_iff, MetricGraphResonancePrototype.forced_oscillator_construct, MetricGraphResonancePrototype.full_period_sine_cosine_zero, MetricGraphResonancePrototype.graphMomentConditions, MetricGraphResonancePrototype.interval_graph_moments_necessary, MetricGraphResonancePrototype.interval_graph_moments_sufficient, MetricGraphResonancePrototype.sin_squared_positive, MetricGraphResonancePrototype.sine_moment_identity_interval, MetricGraphResonancePrototype.theta_cosine_balance, MetricGraphTraceDensity.concat_density_integrable, MetricGraphTraceDensity.concat_density_integral, MetricGraphTraceDensity.concat_right_integral, MetricGraphTraceDensity.reverse_density_integrable, MetricGraphTraceDensity.reverse_density_integral, MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments, MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals, MetricGraphTraceParametric.realizedTrace_ae_local_velocity, MetricGraphTraceParametric.traceDensity_integrable, MetricGraphTraceParametric.traceDensity_integral

**transitive_proof_dependency**: MetricGraphResonancePrototype.theta_forcing_obstruction


Independent draft role review: the divergence-edge and reachable-delta results
include finite sums through the stated divergence definition as well as in proofs.
The interval necessity and sufficiency arguments also use finite sums in proofs;
the combined iff depends on those arguments transitively. The theta forcing
obstruction involves real volume through its proof dependencies, not its statement.
The real-volume equality is a proposed semantic contract, not a claim that each
selected result directly invokes that theorem. These mappings remain subject to
complete independent review and source-bound bridge elaboration.

## Supporting dependency expansions (draft)
These exact pinned source excerpts support the existing material rows. Their
interpretation and the Challenge/Solution bridges still require independent
source-bound elaboration and review. Equivalences and measure identities
below are proved contracts, not asserted definitional equalities. The
normed little-o equivalences retain the typeclass and nontrivial-field
assumptions in their pinned source context; their scope is not asserted
to extend beyond the conditions of the separately checked bridge.

### Mathlib/Analysis/Asymptotics/TVS.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/TVS.lean

SHA-256: `5a37f7656a1cbf7f06c87b47cfdb7a1e63fc2754a287029c7b7e036ac1d1834e`

```lean
/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
```

metric_IsLittleOTVS_structure: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/TVS.lean#L92-L95

```lean
structure IsLittleOTVS (l : Filter α) (f : α → E) (g : α → F) : Prop where
  exists_eventuallyLE_mul : ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ (0 : ℝ≥0),
    (fun x ↦ egauge 𝕜 U (f x)) ≤ᶠ[l] (fun x ↦ ε * egauge 𝕜 V (g x))

```

metric_IsLittleOTVS_normed_iff: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/TVS.lean#L756-L758

```lean
lemma isLittleOTVS_iff_isLittleO : f =o[𝕜; l] g ↔ f =o[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
```

### Mathlib/Analysis/Asymptotics/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/Defs.lean

SHA-256: `68ef9c1b2d13f99770bcd0c679a23f078f634ea344ff914d7d634ba1682104ed`

```lean
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
```

metric_IsLittleO_definition: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/Defs.lean#L167-L170

```lean
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g
```

metric_IsLittleO_eventual_bound: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/Defs.lean#L181-L183

```lean
/-- Definition of `IsLittleO` in terms of filters. -/
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsLittleO_def, IsBigOWith_def]
```

### Mathlib/Analysis/Calculus/FDeriv/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean

SHA-256: `27a7410d70541ab4a947cc95c30b16583d1f89fc073ca47e76c978b0b22f13ba`

```lean
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
```

metric_fderiv_normed_little_o_iff: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L219-L221

```lean
theorem hasFDerivAtFilter_iff_isLittleO {L : Filter (E × E)} :
    HasFDerivAtFilter f f' L ↔ (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[L] fun p => p.1 - p.2 :=
  (hasFDerivAtFilter_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO
```

### Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean

SHA-256: `a1dc11dc7e22a7c20fa382b909d6eb3496b3d346224b9896cb377f2ae5f4418a`

```lean
/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
```

metric_AEStronglyMeasurable_definition: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean#L67-L69

```lean
def AEStronglyMeasurable [m : MeasurableSpace α] {m₀ : MeasurableSpace α} (f : α → β)
    (μ : Measure[m₀] α := by volume_tac) : Prop :=
  ∃ g : α → β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g
```

### Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean

SHA-256: `09f9234723516bbb3d61b8b341d2868c94c8b32ce5f47975983ce8dd67c16712`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
```

metric_HasFiniteIntegral_definition: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean#L82-L84

```lean
def HasFiniteIntegral {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
```

### Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean

SHA-256: `628bcfc45fabd59501cdebf1cc3a8003ef3aba18fc7de4710ca9ffc1033b32d7`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
```

metric_real_volume_Ioc: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L109-L110

```lean
@[simp]
theorem volume_Ioc {a b : ℝ} : volume (Ioc a b) = ofReal (b - a) := by simp [volume_val]
```

### Mathlib/MeasureTheory/Measure/Stieltjes.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Stieltjes.lean

SHA-256: `a539002bedb8054fe0c346bbc104edfb49ef0a9786729e85312844f04c4e6cb5`

```lean
/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel
-/
```

metric_Stieltjes_measure_and_Ioc: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Stieltjes.lean#L518-L529

```lean
/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. If there is a bot element, it gives zero mass to it. -/
protected irreducible_def measure : Measure R where
  toOuterMeasure := f.outer
  m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ <| by
    borelize R
    exact hs i
  trim_le := f.outer_trim.le

@[simp]
theorem measure_Ioc (a b : R) : f.measure (Ioc a b) = ofReal (f b - f a) := by
  rw [StieltjesFunction.measure]
```

Lean core `Quot`, `Quot.mk`, and `Quot.sound` are a trusted
foundational boundary for the local `EdgeGlue` quotient. This note
does not replace the required source-bound transitive axiom audit.

## Additional graph and path carrier expansions (draft)

Each selected declaration below also uses `unitInterval`, `Set.Icc`,
and `Set` via the `Graph` carrier or, for realization, the `Path`
parameter. These are semantic expansions rather than new hypotheses.

- `MetricGraphTraceParametric.traceDensity_integrable`
- `MetricGraphTraceParametric.traceDensity_integral`
- `MetricGraphTraceParametric.closed_trace_integrals_iff_exact_moments`
- `MetricGraphTraceParametric.exists_vertex_trace`
- `MetricGraphTraceParametric.forced_interval_iff_closed_trace_integrals`
- `ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize`
