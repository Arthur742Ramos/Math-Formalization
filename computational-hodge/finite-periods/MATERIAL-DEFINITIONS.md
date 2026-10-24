# Material imported definitions

Exact Mathlib source and semantic expansion inventory for the selected computational-path/cochain interface.
This records 53 declarations. It is not a total inventory of Lean core or every algebraic hierarchy ancestor.
The actual upstream geometric definitions have a separate literal source-provenance manifest and retained MIT license.

EuclideanSpace is a WithLp wrapper, not literally an ordinary function type. Finite E, not finite A or Cell P, yields finite-dimensional Exact and its derived completeness.
The quotient relation uses a proved difference-membership equivalence; it is not described as a literal x-y predicate. Homotopy is relative to both endpoints.
Periods are discrete signed edge sums; no analytic path integral, period continuity or ambient de Rham comparison is asserted.

Selected declarations:

- `ComputationalHodge.period_d0`
- `ComputationalHodge.d1_d0`
- `ComputationalHodge.closed_iff_rewrite_invariant`
- `ComputationalHodge.quotientPeriod_compose`
- `ComputationalHodge.unique_harmonic_representative`
- `ComputationalHodge.hodgeEquiv_preserves_periods`
- `ComputationalHodge.periodPairing_compose`
- `ComputationalHodge.exact_iff_zero_loop_periods`
- `ComputationalHodge.harmonic_determined_by_periods`
- `ComputationalHodge.periodPairing_separates`
- `ComputationalHodge.ParallelEdges.omega_harmonic`
- `ComputationalHodge.ParallelEdges.omega_loop_period`
- `ComputationalHodge.ParallelEdges.omega_not_exact`
- `ComputationalHodge.ParallelEdges.loop_geometrically_null`
- `ComputationalHodge.ParallelEdges.parallel_harmonic_zero`
- `ComputationalHodge.ParallelEdges.rewrite_changes_periods`
- `ComputationalHodge.Cochain`
- `ComputationalHodge.period`
- `ComputationalHodge.d0`
- `ComputationalHodge.d1`
- `ComputationalHodge.Closed`
- `ComputationalHodge.Exact`
- `ComputationalHodge.Harmonic`
- `ComputationalHodge.Boundaries`
- `ComputationalHodge.H1`
- `ComputationalHodge.harmonicProjection`
- `ComputationalHodge.hodgeEquiv`
- `ComputationalHodge.pathSetoid`
- `ComputationalHodge.quotientPeriod`
- `ComputationalHodge.compose`
- `ComputationalHodge.cohomologyPeriod`
- `ComputationalHodge.periodPairing`
- `ComputationalHodge.componentSetoid`
- `ComputationalHodge.componentRoot`
- `ComputationalHodge.rootTrace`
- `ComputationalHodge.potential`
- `ComputationalHodge.ParallelEdges.system`
- `ComputationalHodge.ParallelEdges.freePresentation`
- `ComputationalHodge.ParallelEdges.omega`
- `ComputationalHodge.ParallelEdges.parallelPresentation`
- `ComputationalHodge.ParallelEdges.edgeTopology`

## WithLp

A type wrapper carrying ofLp data; the underlying functions are accessed through an actual equivalence.

A type wrapper carrying ofLp data; the underlying functions are accessed through an actual equivalence. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## WithLp.equiv

The wrapper-to-underlying-type equivalence, not equality of types.

The wrapper-to-underlying-type equivalence, not equality of types. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## WithLp.linearEquiv

The linear equivalence between the WithLp wrapper and its underlying module.

The linear equivalence between the WithLp wrapper and its underlying module. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## PiLp

WithLp applied to a dependent function space; its function coercion evaluates ofLp.

WithLp applied to a dependent function space; its function coercion evaluates ofLp. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## EuclideanSpace

PiLp with exponent two and constant scalar fibers, giving the finite real coefficient space.

PiLp with exponent two and constant scalar fibers, giving the finite real coefficient space. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Inner

The actual scalar-valued pairing on vectors.

The actual scalar-valued pairing on vectors. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## InnerProductSpace

Inner product compatible with the norm and scalar/module operations; the coefficient space uses its actual finite-sum instance.

Inner product compatible with the norm and scalar/module operations; the coefficient space uses its actual finite-sum instance. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Fintype

An exhaustive finite enumeration of primitive generators, not an assumed finite point or relation space.

An exhaustive finite enumeration of primitive generators, not an assumed finite point or relation space. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## FiniteDimensional

Module.Finite: a finite spanning set for a module over the field.

Module.Finite: a finite spanning set for a module over the field. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Module.Finite

Finite generation of the top submodule.

Finite generation of the top submodule. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.FG

Existence of a finite set whose span is the submodule.

Existence of a finite set whose span is the submodule. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.span

The least submodule containing the specified vectors.

The least submodule containing the specified vectors. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Cauchy

A nontrivial filter whose pair filter tends to the uniformity.

A nontrivial filter whose pair filter tends to the uniformity. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## IsComplete

Cauchy filters supported in the set converge to a point in it.

Cauchy filters supported in the set converge to a point in it. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## CompleteSpace

Completeness of the whole uniform space; derived for Exact from finite dimensionality.

Completeness of the whole uniform space; derived for Exact from finite dimensionality. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.orthogonal

Vectors whose actual inner product with every vector of the submodule is zero.

Vectors whose actual inner product with every vector of the submodule is zero. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.HasOrthogonalProjection

Existence of a submodule vector with orthogonal residual, inferred from completeness here rather than supplied as a Hodge assumption.

Existence of a submodule vector with orthogonal residual, inferred from completeness here rather than supplied as a Hodge assumption. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.orthogonalProjectionOnto

The bundled continuous linear projection into the submodule subtype.

The bundled continuous linear projection into the submodule subtype. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.starProjection

Projection followed by subtype inclusion into the ambient coefficient space.

Projection followed by subtype inclusion into the ambient coefficient space. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## ContinuousLinearMap

A linear map with actual continuity, used by orthogonal projection.

A linear map with actual continuity, used by orthogonal projection. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.subtypeL

The continuous linear inclusion of a submodule.

The continuous linear inclusion of a submodule. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.projectionOntoL

The continuous projection supplied by a topological direct complement.

The continuous projection supplied by a topological direct complement. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearMap

An additive scalar-compatible map; period, d0 and d1 use actual operations.

An additive scalar-compatible map; period, d0 and d1 use actual operations. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearMap.comp

Actual composition of linear maps.

Actual composition of linear maps. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearMap.pi

A family of linear functionals assembled into a function-valued linear map, used for every named cell.

A family of linear functionals assembled into a function-valued linear map, used for every named cell. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule

A carrier closed under zero, addition and scalar multiplication.

A carrier closed under zero, addition and scalar multiplication. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.subtype

The actual linear subtype inclusion.

The actual linear subtype inclusion. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearMap.ker

The submodule of vectors sent to zero.

The submodule of vectors sent to zero. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearMap.range

The image submodule, so exactness requires an actual potential witness.

The image submodule, so exactness requires an actual potential witness. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.comap

The inverse-image submodule; boundaries are restricted to closed cochains before quotienting.

The inverse-image submodule; boundaries are restricted to closed cochains before quotienting. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.quotientRel

The additive quotient relation induced by the submodule; its difference-membership interpretation is proved in quotientRel_def.

The additive quotient relation induced by the submodule; its difference-membership interpretation is proved in quotientRel_def. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.Quotient.mk

The map to the actual additive quotient carrier.

The map to the actual additive quotient carrier. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.mkQ

The quotient map bundled as a linear map.

The quotient map bundled as a linear map. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.quotEquivOfEq

A linear identification between quotients by proved equal submodules.

A linear identification between quotients by proved equal submodules. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Submodule.liftQ

Descent of a linear map that kills the quotient submodule, with a checked representative computation.

Descent of a linear map that kills the quotient submodule, with a checked representative computation. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearEquiv

A linear map with a two-sided inverse, rather than an assumed abstract cohomology identification.

A linear map with a two-sided inverse, rather than an assumed abstract cohomology identification. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearMap.quotKerEquivRange

The proved first isomorphism theorem for a linear map.

The proved first isomorphism theorem for a linear map. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## LinearMap.quotKerEquivOfSurjective

The first isomorphism theorem with an actual proved surjectivity witness.

The first isomorphism theorem with an actual proved surjectivity witness. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Quotient.out

Classical choice of a representative of an existing quotient class, with out_eq; no global basepoint or connectivity is assumed.

Classical choice of a representative of an existing quotient class, with out_eq; no global basepoint or connectivity is assumed. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## TopologicalSpace

A topology on the point and step carriers; no metric or manifold structure on A is assumed.

A topology on the point and step carriers; no metric or manifold structure on A is assumed. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Continuous

Inverse images of open sets are open.

Inverse images of open sets are open. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## ContinuousMap

A function with an actual continuity proof.

A function with an actual continuity proof. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path

A continuous interval map with its two actual endpoint equations.

A continuous interval map with its two actual endpoint equations. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path.refl

The constant continuous path.

The constant continuous path. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path.symm

Reversal of an actual continuous path.

Reversal of an actual continuous path. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path.trans

Binary parametrized concatenation; it is not identified with equal-slot flattening.

Binary parametrized concatenation; it is not identified with equal-slot flattening. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## ContinuousMap.Homotopy

A jointly continuous interval family connecting two continuous maps.

A jointly continuous interval family connecting two continuous maps. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## ContinuousMap.HomotopyWith

A homotopy satisfying a specified constraint throughout the interval.

A homotopy satisfying a specified constraint throughout the interval. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## ContinuousMap.HomotopyRel

HomotopyWith the constraint of agreeing on a specified subset.

HomotopyWith the constraint of agreeing on a specified subset. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path.Homotopy

A homotopy relative to both interval endpoints; not arbitrary endpoint-changing motion.

A homotopy relative to both interval endpoints; not arbitrary endpoint-changing motion. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path.Homotopic

Nonempty actual endpoint-fixed homotopy type.

Nonempty actual endpoint-fixed homotopy type. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path.segment

The actual straight segment continuous path from zero to one in the real-line example.

The actual straight segment continuous path from zero to one in the real-line example. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Path.Homotopy.reflTransSymm

The explicit contraction of a path followed by its reversal, proving the example ambient loop is null-homotopic.

The explicit contraction of a path followed by its reversal, proving the example ambient loop is null-homotopic. Exact alias/parent definitions and supporting results are retained below. Lean core logic, Setoid, Quotient, equality, Fin and classical choice are the explicit compiler-checked infrastructure boundary; no analytic integration or ambient completeness is inferred.

Separate ChallengeSemantics and SolutionSemantics check literal operators, quotient membership, finite-sum inner product and the derived projection instance. Compilation and kernels have separate exact-source receipts; byte/schema checks alone prove no mathematical fidelity.

## Source Mathlib/Analysis/Normed/Lp/WithLp.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Lp/WithLp.lean

SHA256 `f02507031f01c655e61dd1894b74a3452b2f8aedcba55dda9fa0d60e4db0d57d`

```lean
/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
```

### WithLp

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Lp/WithLp.lean#L50-L55

```lean
structure WithLp (p : ℝ≥0∞) (V : Type*) where
  /-- Converts an element of `V` to an element of `WithLp p V`. -/
  toLp (p) ::
  /-- Converts an element of `WithLp p V` to an element of `V`. -/
  ofLp : V

```

### WithLp.equiv

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Lp/WithLp.lean#L72-L76

```lean
protected def equiv : WithLp p V ≃ V where
  toFun := ofLp
  invFun := toLp p
  left_inv _ := rfl
  right_inv _ := rfl
```

### WithLp.linearEquiv

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Lp/WithLp.lean#L237-L245

```lean
protected def linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : WithLp p V ≃ₗ[K] V where
  __ := WithLp.addEquiv p V
  map_smul' _ _ := rfl

lemma coe_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V) = ofLp := rfl

lemma coe_symm_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V).symm = toLp p := rfl
```

## Source Mathlib/Analysis/Normed/Lp/PiLp.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Lp/PiLp.lean

SHA256 `4f8af8ea06fcf3fee8f104ce25a245e2e226741ddb5cc1d9d8161fa15b24163c`

```lean
/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Jireh Loreaux
-/
```

### PiLp

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Lp/PiLp.lean#L87-L96

```lean
abbrev PiLp (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : Type _ :=
  WithLp p (∀ i : ι, α i)

/-The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithLp.equiv`. -/
instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : CoeFun (PiLp p α) (fun _ ↦ (i : ι) → α i) where
  coe := ofLp

instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨toLp p fun _ => default⟩
```

## Source Mathlib/Analysis/InnerProductSpace/PiL2.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/PiL2.lean

SHA256 `cd53aaefb8b1db37ebfc5afd37d9747dfd767da2292990f958255720b1cbab18`

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
```

### EuclideanSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L114-L115

```lean
abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜
```

### Euclidean_inner

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L103-L106

```lean

theorem PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι → Type*} [∀ i, NormedAddCommGroup (f i)]
    [∀ i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl
```

## Source Mathlib/Analysis/InnerProductSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Defs.lean

SHA256 `57823255e4a6e017197098517b8d33fef6821922b31212e4b5e224e5e81fe14b`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
```

### Inner

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Defs.lean#L81-L86

```lean
class Inner (𝕜 E : Type*) where
  /-- The inner product function. -/
  inner (𝕜) : E → E → 𝕜

export Inner (inner)

```

### InnerProductSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Defs.lean#L109-L118

```lean
class InnerProductSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] extends
    NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_re_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
```

## Source Mathlib/Data/Fintype/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean

SHA256 `e69e8e7a3605d293a7ef6c4a7aaefde3191da4f33b43b7be09963eec2e44965c`

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

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

## Source Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean

SHA256 `a3e88c4fe00ba476440d68a1568afecf6be685a488b5b8718f6b2ef969a15fa4`

```lean
/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
```

### FiniteDimensional

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean#L74-L75

```lean
abbrev FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V
```

## Source Mathlib/RingTheory/Finiteness/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Finiteness/Defs.lean

SHA256 `c22de11b826e235da8f48da713e7d22dba05c884c4982f64babeff3490a4a98b`

```lean
/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
```

### Module.Finite

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Finiteness/Defs.lean#L122-L126

```lean
protected class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  of_fg_top ::
    fg_top : (⊤ : Submodule R M).FG

attribute [inherit_doc Module.Finite] Module.Finite.fg_top
```

### Submodule.FG

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Finiteness/Defs.lean#L47-L49

```lean
def FG (N : Submodule R M) : Prop :=
  ∃ S : Finset M, span R ↑S = N

```

## Source Mathlib/LinearAlgebra/Span/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean

SHA256 `a0403eb6f96f384672a7b52d7ddb94405d3d3b1c43f699facc3e99ef8b0c00c6`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### Submodule.span

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean#L46-L49

```lean
def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }

/-- An `R`-submodule of `M` is principal if it is generated by one element. -/
```

## Source Mathlib/Topology/UniformSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean

SHA256 `68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### Cauchy

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L32-L34

```lean
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α

```

### IsComplete

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L37-L38

```lean
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
```

### CompleteSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L371-L378

```lean
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x

theorem isComplete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] :
    IsComplete (univ : Set α) := fun f hf _ => by
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩
```

## Source Mathlib/Analysis/InnerProductSpace/Orthogonal.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean

SHA256 `a72a848fec37640c3a1e589075b3a24ed1eda19009b5493f7a2535f92ef98d04`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
```

### Submodule.orthogonal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean#L43-L55

```lean
def orthogonal : Submodule 𝕜 E where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

/-- `v ∈ Kᗮ` if and only if `⟪u, v⟫ = 0` for all `u ∈ K`. -/
theorem mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 :=
  Iff.rfl

```

## Source Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean

SHA256 `dcda6e9b00d2325757b882e565564fc34e15bab772aad166f2f02b4b26961d09`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
```

### Submodule.HasOrthogonalProjection

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L49-L60

```lean
class HasOrthogonalProjection (K : Submodule 𝕜 E) : Prop where
  exists_orthogonal (v : E) : ∃ w ∈ K, v - w ∈ Kᗮ

variable (K : Submodule 𝕜 E)

instance (priority := 100) HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K] :
    K.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases K.exists_norm_eq_iInf_of_complete_subspace (completeSpace_coe_iff_isComplete.mp ‹_›) v
      with ⟨w, hwK, hw⟩
    refine ⟨w, hwK, (K.mem_orthogonal' _).2 ?_⟩
    rwa [← K.norm_eq_iInf_iff_inner_eq_zero hwK]
```

### Submodule.orthogonalProjectionOnto

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L121-L121

```lean
def orthogonalProjectionOnto : E →L[𝕜] K := K.projectionOntoL Kᗮ K.isTopCompl_orthogonal
```

### Submodule.starProjection

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L132-L133

```lean
def starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E →L[𝕜] E := U.subtypeL ∘L U.orthogonalProjectionOnto
```

### projection_residual

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L160-L177

```lean

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_mem := starProjection_apply_mem

/-- The characterization of the orthogonal projection. -/
@[simp]
theorem starProjection_inner_eq_zero (v w : E) (hw : w ∈ K) : ⟪v - K.starProjection v, w⟫ = 0 := by
  suffices v - K.projection Kᗮ K.isCompl_orthogonal v ∈ Kᗮ from inner_eq_zero_symm.mp <| this w hw
  simp [← projection_eq_self_sub_projection]

@[deprecated (since := "2026-06-10")] alias orthogonalProjectionFn_inner_eq_zero :=
  starProjection_inner_eq_zero

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`. -/
@[simp]
theorem sub_starProjection_mem_orthogonal (v : E) : v - K.starProjection v ∈ Kᗮ := by
  intro w hw
  rw [inner_eq_zero_symm]
  exact starProjection_inner_eq_zero _ _ hw
```

## Source Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean

SHA256 `d081051ca12363eeb95590a88decc17fd18f5bdc76c7fb30748f48ffc854d379`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### ContinuousLinearMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean#L60-L65

```lean
structure ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip

```

## Source Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean

SHA256 `c18d85d95c67c576783d9be561e9f8a2318cc1efd0dbb28060c9d47d6a573aea`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### Submodule.subtypeL

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean#L47-L51

```lean
def subtypeL (p : Submodule R M) : p →L[R] M where
  toLinearMap := p.subtype

@[simp, norm_cast]
theorem toLinearMap_subtypeL (p : Submodule R M) : (p.subtypeL : p →ₗ[R] M) = p.subtype := rfl
```

## Source Mathlib/Topology/Algebra/Module/Complement.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/Complement.lean

SHA256 `ea947529899c67508b6762a4d08f096520822095b0d892556811eaf97bff2a93`

```lean
/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sharvil Kesarwani
-/
```

### Submodule.projectionOntoL

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/Complement.lean#L161-L166

```lean
noncomputable def projectionOntoL (h : IsTopCompl p q) : M →L[R] p :=
  ⟨p.projectionOnto q h.isCompl, h.continuous_projectionOnto⟩

@[simp]
theorem toLinearMap_projectionOntoL (h : IsTopCompl p q) :
    p.projectionOntoL q h = p.projectionOnto q h.isCompl :=
```

## Source Mathlib/Algebra/Module/LinearMap/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean

SHA256 `aea1c354ffc798aaa5397f2f58124bc2ed7b29d24227ae568d3f5745f839570d`

```lean
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
```

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

### LinearMap.comp

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean#L479-L487

```lean
def comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :
    M₁ →ₛₗ[σ₁₃] M₃ where
  toFun x := f (g x)
  map_add' := by simp only [map_add, forall_const]
  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`
  map_smul' r x := by simp only [map_smulₛₗ _, RingHomCompTriple.comp_apply]

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)
```

## Source Mathlib/LinearAlgebra/Pi.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Pi.lean

SHA256 `d297e47c0b724513841774f50ecf57aa4d9baf9d0c48b83c4a9e06f38de42abb`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
```

### LinearMap.pi

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Pi.lean#L56-L63

```lean
def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
  { AddHom.pi fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }

@[simp]
theorem pi_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl
```

## Source Mathlib/Algebra/Module/Submodule/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Defs.lean

SHA256 `f1735fb71af000fc2047c5e6456fa2b31d0f5443d23a169ac25a6ce388fe2b78`

```lean
/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
```

### Submodule

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Defs.lean#L41-L51

```lean
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
    extends AddSubmonoid M, SubMulAction R M

/-- Reinterpret a `Submodule` as an `AddSubmonoid`. -/
add_decl_doc Submodule.toAddSubmonoid

/-- Reinterpret a `Submodule` as a `SubMulAction`. -/
add_decl_doc Submodule.toSubMulAction

namespace Submodule

```

## Source Mathlib/Algebra/Module/Submodule/LinearMap.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/LinearMap.lean

SHA256 `51b927c0a53b41f443cb053f81d6c065e0e462f1a016ea813111a0ecfa81f145`

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

### Submodule.subtype

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/LinearMap.lean#L82-L86

```lean
protected def subtype : p →ₗ[R] M where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

```

## Source Mathlib/Algebra/Module/Submodule/Ker.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Ker.lean

SHA256 `6820cd12f24bc4d7b00c6e508c2d2ecaff39549d74be47430eb76cd8b6ee34ee`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### LinearMap.ker

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Ker.lean#L60-L65

```lean
def ker (f : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=
  comap f ⊥

@[simp]
theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 :=
  mem_bot R₂
```

## Source Mathlib/Algebra/Module/Submodule/Range.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Range.lean

SHA256 `5d3c93d9b771e9aec611a0221bc138f9491dd2c37c3babcf42c2acbe570a4d45`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### LinearMap.range

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Range.lean#L57-L66

```lean
def range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm

theorem coe_range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : (range f : Set M₂) = Set.range f :=
  rfl

theorem range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubmonoid = AddMonoidHom.mrange f :=
  rfl

```

## Source Mathlib/Algebra/Module/Submodule/Map.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Map.lean

SHA256 `f0b02929b7aeeb359f7c9f207a7d78d3013ecf9a5e2e167431cf85422894ebc2`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### Submodule.comap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Map.lean#L172-L180

```lean
def comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

@[simp]
theorem comap_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl
```

## Source Mathlib/LinearAlgebra/Quotient/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean

SHA256 `ddb08efd66c7dd6f5e142ac3e1edc1189ea30de276f1e78f4193d6ee80676fb3`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
```

### Submodule.quotientRel

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L44-L45

```lean
def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup
```

### Submodule.Quotient.mk

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L61-L62

```lean
def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''
```

### Submodule.mkQ

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L227-L234

```lean
def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
  map_smul' := by simp

@[simp]
theorem mkQ_apply (x : M) : p.mkQ x = Quotient.mk x :=
  rfl
```

### Submodule.quotEquivOfEq

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L252-L261

```lean
def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }
```

### quotientRel_def

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L47-L58

```lean
theorem quotientRel_def {x y : M} : p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [quotientRel, leftRel_apply, sub_eq_add_neg, neg_add, neg_neg]
      rfl)
    neg_mem_iff

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩

namespace Quotient
```

## Source Mathlib/LinearAlgebra/Quotient/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Basic.lean

SHA256 `564aad5ee0111df700cb30aca030018f26939ed1c307f19ee6d9ac02b6bc4312`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
```

### Submodule.liftQ

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Basic.lean#L118-L127

```lean
def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp]
theorem liftQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x) = f x :=
  rfl

@[simp]
theorem liftQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f := by ext; rfl
```

## Source Mathlib/Algebra/Module/Equiv/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Equiv/Defs.lean

SHA256 `fea6294b3b6d6bdda0f62eb99a5977e4a73bbca7bf98e1be83c158c79e0e197a`

```lean
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
```

### LinearEquiv

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Equiv/Defs.lean#L49-L58

```lean
structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂

attribute [coe] LinearEquiv.toLinearMap

/-- The linear map underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toLinearMap

/-- The additive equivalence of types underlying a linear equivalence. -/
```

## Source Mathlib/LinearAlgebra/Isomorphisms.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Isomorphisms.lean

SHA256 `9b09cba140051ca8b9aa93f6cf22a85c3d9fd4d1c108939c6a6e0b44a0192d73`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
```

### LinearMap.quotKerEquivRange

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Isomorphisms.lean#L39-L44

```lean
noncomputable def quotKerEquivRange : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  -- TODO: We should fix this definition so that `fₗ.quotKerEquivRange.toAddEquiv` is definitionally
  -- equal to `QuotientAddGroup.quotientKerEquivRange f.toAddMonoidHom`.
  (LinearEquiv.ofInjective ((LinearMap.ker f).liftQ f <| le_rfl) <|
        ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ (le_refl (LinearMap.ker f))).trans
    (LinearEquiv.ofEq _ _ <| Submodule.range_liftQ _ _ _)
```

### LinearMap.quotKerEquivOfSurjective

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Isomorphisms.lean#L47-L59

```lean
noncomputable def quotKerEquivOfSurjective (f : M →ₗ[R] M₂) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] M₂ :=
  f.quotKerEquivRange.trans <| .ofTop (LinearMap.range f) <| range_eq_top.2 hf

@[simp]
theorem quotKerEquivRange_apply_mk (x : M) :
    (f.quotKerEquivRange (Submodule.Quotient.mk x) : M₂) = f x :=
  rfl

@[simp]
theorem quotKerEquivOfSurjective_apply_mk (hf : Function.Surjective f) (x : M) :
    (f.quotKerEquivOfSurjective hf (Submodule.Quotient.mk x) : M₂) = f x :=
  rfl
```

## Source Mathlib/Data/Quot.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Quot.lean

SHA256 `14af0ddf94e04029ce230f6635d339578d906014206fe4c3fc2a3f6bc25cb1a2`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Quotient.out

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Quot.lean#L375-L380

```lean
noncomputable def Quotient.out {s : Setoid α} : Quotient s → α :=
  Quot.out

@[simp]
theorem Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.out⟧ = q :=
  Quot.out_eq q
```

## Source Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA256 `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
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

### Continuous

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

## Source Mathlib/Topology/ContinuousMap/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ContinuousMap/Defs.lean

SHA256 `a4de4f3ae5c6d605a4c2449db2ace372e83b430e44da6919c808d633142711e3`

```lean
/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/
```

### ContinuousMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ContinuousMap/Defs.lean#L33-L40

```lean
structure ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The function `X → Y` -/
  protected toFun : X → Y
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun := by fun_prop

/-- `C(X, Y)` is the type of continuous maps from `X` to `Y`. -/
notation "C(" X ", " Y ")" => ContinuousMap X Y
```

## Source Mathlib/Topology/Path.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean

SHA256 `91c8fa5452d85bc35258afd61de0b694e82ae483d35d9257b599ce7eaddab038`

```lean
/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
```

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

## Source Mathlib/Topology/Homotopy/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Basic.lean

SHA256 `e983c30f4006516e0e300c887bee86d838abdcc1d8659362abf8d9324eaa912a`

```lean
/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
```

### ContinuousMap.Homotopy

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Basic.lean#L77-L83

```lean
structure Homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) where
  /-- value of the homotopy at 0 -/
  map_zero_left : ∀ x, toFun (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left : ∀ x, toFun (1, x) = f₁ x

section
```

### ContinuousMap.HomotopyWith

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Basic.lean#L386-L392

```lean
structure HomotopyWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends Homotopy f₀ f₁ where
  -- TODO: use `toHomotopy.curry t`
  /-- the intermediate maps of the homotopy satisfy the property -/
  prop' : ∀ t, P ⟨fun x ↦ toFun (t, x), continuous_toFun.comp (by fun_prop)⟩

namespace HomotopyWith

```

### ContinuousMap.HomotopyRel

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Basic.lean#L542-L543

```lean
abbrev HomotopyRel (f₀ f₁ : C(X, Y)) (S : Set X) :=
  HomotopyWith f₀ f₁ fun f ↦ ∀ x ∈ S, f x = f₀ x
```

## Source Mathlib/Topology/Homotopy/Path.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean

SHA256 `8eb18db7d886898d9bc9e3d9ea91ff6ac5fb958b0beebf26ae71c7f632fa895e`

```lean
/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
```

### Path.Homotopy

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L50-L51

```lean
abbrev Homotopy (p₀ p₁ : Path x₀ x₁) :=
  ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}
```

### Path.Homotopic

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L241-L242

```lean
def Homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.Homotopy p₁)
```

## Source Mathlib/Analysis/Convex/PathConnected.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/PathConnected.lean

SHA256 `e361be68d7c22691466bb61dbcbce809cd0fee45b4d0fb578c937ce6504bcadc`

```lean
/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
```

### Path.segment

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/PathConnected.lean#L35-L40

```lean
protected def segment (a b : E) : Path a b where
  toFun t := lineMap a b (t : ℝ)
  continuous_toFun := by dsimp [lineMap]; fun_prop
  source' := by simp
  target' := by simp

```

## Source Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean

SHA256 `8cfce24311c16e1e624e01e6bd2ace37fe6be4647340c901681235129acf41b2`

```lean
/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
```

### Path.Homotopy.reflTransSymm

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L62-L73

```lean
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by fun_prop
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    simp only [reflTransSymmAux, Path.trans]
    cases le_or_gt (x : ℝ) 2⁻¹ with
    | inl hx => simp [hx, ← extend_apply]
    | inr hx =>
      have : p.extend (2 - 2 * ↑x) = p.extend (1 - (2 * ↑x - 1)) := by ring_nf
      simpa [hx.not_ge, ← extend_apply]
  prop' t := by norm_num [reflTransSymmAux]
```

### null_homotopy_parameter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L42-L58

```lean
def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)

@[continuity, fun_prop]
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x ∈ I := by
  dsimp only [reflTransSymmAux]
  split_ifs
  · constructor
    · apply mul_nonneg <;> grind
    · rw [mul_assoc]
      apply (mul_le_of_le_one_left ?_ ?_).trans ?_ <;> grind
  · constructor
    · apply mul_nonneg <;> grind
    · apply (mul_le_of_le_one_left ?_ ?_).trans ?_ <;> grind
```

## Source Mathlib/Topology/Algebra/Module/FiniteDimension.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/FiniteDimension.lean

SHA256 `aae1cf2eb90fc1b11375074ec2bb8eccc904e3221d1ee4bfa65b806d971d9367`

```lean
/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker
-/
```

### finite_complete

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/FiniteDimension.lean#L504-L512

```lean
variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [AddCommGroup E] [UniformSpace E] [T2Space E] [IsUniformAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

include 𝕜 in
theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr this).1 inferInstance
```
