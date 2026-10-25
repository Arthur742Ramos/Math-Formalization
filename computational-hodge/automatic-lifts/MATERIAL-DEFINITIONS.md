# Material imported definitions

Exact pinned contracts for conservative retained-family coverage follow. Uniform continuity is for the constructed real topological lift; its AC regularity is derived by the local chord estimate and finite-disjoint-interval criterion. Actual homeomorphism inverse and covering APIs construct the lift. Candidate AmbientLoop supplies only complex interval-AC, interval unit norm and based endpoints. Input integrals, integer endpoint and finite computational representative/homotopy are proved. Outside input values are unrestricted. Finite energy is separately guarded and homotopy remains circle-valued. No general analytic Hodge or ambient-plane classification is claimed. Generic equivalence, field, metric/filter/measure, finite-set and Cauchy-limit foundations are credited infrastructure. Hashes alone certify neither semantic fidelity nor inventory completeness. Separate semantic builds and independent review remain required.

- `WithLp`: A type wrapper carrying ofLp data; the underlying functions are accessed through an actual equivalence.
- `WithLp.equiv`: The wrapper-to-underlying-type equivalence, not equality of types.
- `WithLp.linearEquiv`: The linear equivalence between the WithLp wrapper and its underlying module.
- `PiLp`: WithLp applied to a dependent function space; its function coercion evaluates ofLp.
- `EuclideanSpace`: PiLp with exponent two and constant scalar fibers, giving the finite real coefficient space.
- `Inner`: The actual scalar-valued pairing on vectors.
- `InnerProductSpace`: Inner product compatible with the norm and scalar/module operations; the coefficient space uses its actual finite-sum instance.
- `Fintype`: An exhaustive finite enumeration of primitive generators, not an assumed finite point or relation space.
- `Submodule.orthogonal`: Actual submodule of vectors orthogonal to every vector of the given submodule. Used in the retained actual Harmonic definition Closed intersect Exact orthogonal; no cycle-quotient norm identification is claimed.
- `ContinuousLinearMap`: Actual continuous linear map with its normed and continuity structure, used by the actual Frechet derivative and its one-dimensional scalar specialization. No orthogonal projection is constructed by this package.
- `LinearMap`: An additive scalar-compatible map; period, d0 and d1 use actual operations.
- `LinearMap.comp`: Actual composition of linear maps.
- `LinearMap.pi`: A family of linear functionals assembled into a function-valued linear map, used for every named cell.
- `Submodule`: A carrier closed under zero, addition and scalar multiplication.
- `Submodule.subtype`: The actual linear subtype inclusion.
- `LinearMap.ker`: The submodule of vectors sent to zero.
- `LinearMap.range`: Actual image submodule. Exact circleSystem is the range of the endpoint-difference operator d0: membership has an actual function-potential witness. No finite-support Relations or C2 construction is asserted here.
- `Submodule.comap`: Actual inverse image of a submodule under a linear map. Conservative linear-algebra dependency infrastructure for retained kernel/range and harmonic constructions; no relation-boundary or cycle quotient theorem is asserted here.
- `LinearEquiv`: A linear map with a two-sided inverse, rather than an assumed abstract cohomology identification.
- `TopologicalSpace`: A topology on the point and step carriers; no metric or manifold structure on A is assumed.
- `Continuous`: Inverse images of open sets are open.
- `ContinuousMap`: A function with an actual continuity proof.
- `Path`: A continuous interval map with its two actual endpoint equations.
- `Path.refl`: The constant continuous path.
- `Path.symm`: Reversal of an actual continuous path.
- `Path.trans`: Binary parametrized concatenation; it is not identified with equal-slot flattening.
- `ContinuousMap.Homotopy`: A jointly continuous interval family connecting two continuous maps.
- `ContinuousMap.HomotopyWith`: A homotopy satisfying a specified constraint throughout the interval.
- `ContinuousMap.HomotopyRel`: HomotopyWith the constraint of agreeing on a specified subset.
- `Path.Homotopy`: A homotopy relative to both interval endpoints; not arbitrary endpoint-changing motion.
- `Path.Homotopic`: Nonempty actual endpoint-fixed homotopy type.
- `Equiv.ofBijective`: Actual equivalence constructed from a bijective function by classical inverse choice. Retained generic dependency infrastructure; no new equivalence of this form is constructed as a claimed result here.
- `LinearEquiv.ofBijective`: Actual linear equivalence from a bijective linear map, using its classical inverse. Retained generic linear-algebra infrastructure; no new claimed quotient or ambient equivalence is constructed here.
- `Path.Homotopic.Quotient`: Actual quotient of endpoint-fixed paths by endpoint-fixed path homotopy, retained as conservative covering and fundamental-group infrastructure. The current representative homotopy is constructed in the additive circle, related to the complex unit circle by the explicit homeomorphism; no ambient-plane classification or separately mapped unitPath homotopy is claimed.
- `Path.Homotopic.Quotient.mk`: The canonical actual path-to-homotopy-class map.
- `Path.Homotopic.setoid`: The actual path-homotopy equivalence relation on continuous endpoint-fixed paths.
- `Path.Homotopy.hcomp`: Actual horizontal concatenation, with piecewise continuous path data and fixed endpoints.
- `Path.Homotopy.refl`: Constant actual path homotopy.
- `Path.Homotopy.reflSymmTrans`: Actual nullhomotopy of reversed p followed by p.
- `Path.Homotopy.reflTrans`: Actual left identity homotopy.
- `Path.Homotopy.symm`: Reverses homotopy time, preserving endpoint conditions.
- `Path.Homotopy.symm₂`: Reverses the path parameter in an actual homotopy, preserving the fixed-endpoint condition.
- `Path.Homotopy.trans`: Concatenates homotopies in homotopy time.
- `Path.Homotopy.transAssoc`: Actual associativity homotopy from a piecewise reparametrization.
- `Path.Homotopy.transRefl`: Actual right identity homotopy via explicit reparametrization.
- `Set`: The actual Mathlib set type is a predicate on its element type; it is not treated as an undefined core primitive.
- `Set.image`: Actual image of a specified set under a function. Conservative retained realization, covering and linear-algebra dependency infrastructure; no new submodule-map construction is asserted.
- `Set.ofPred`: Literal predicate-to-set constructor used by set-builder notation.
- `Set.range`: Actual image of the whole domain of a function. Conservative dependency infrastructure in retained map/range, covering and realization constructions; no absent NullSpan or NullClassSpan construction is claimed.
- `FundamentalGroup`: Actual based-loop group in the Mathlib fundamental groupoid, retained as conservative homotopy/covering infrastructure. Direct original-circle homotopies are used here; no candidate represented subgroup is constructed.
- `FundamentalGroupoid`: Wrapper of ambient points; arrows are actual endpoint-fixed homotopy classes of continuous paths.
- `Subgroup`: Actual subgroup with unit, multiplication and inverse closure, retained as conservative imported algebraic/covering infrastructure. No candidate representedGroup construction is retained or claimed.
- `Subgroup.subtype`: Actual inclusion homomorphism of a subgroup, retained as conservative imported algebraic/covering infrastructure. No candidate restriction-of-winding construction is claimed.
- `MonoidHom`: Ordinary identity- and product-preserving function. With target Multiplicative real numbers its product law is real additivity, not multiplicative real-valued weights.
- `Multiplicative`: Type tag reinterpreting real addition as multiplication; identity is real zero, inverse real negation.
- `Multiplicative.ofAdd`: Actual identity type-tag equivalence from real additive notation to multiplicative notation.
- `Multiplicative.toAdd`: Inverse of the ordinary type-tag equivalence; no new algebra or norm introduced.
- `AddCircle`: Actual real quotient by the subgroup of integer multiples of the period. The concrete period is 1; realized paths may leave the single computational endpoint.
- `IsCoveringMap`: Every ambient point has an evenly covered neighborhood with the actual fiber. Used through the proved standard real-to-additive-circle covering, not assumed as a new axiom.
- `IsCoveringMap.liftPath`: Classically chosen continuous path lift with specified starting lift, from a proved covering path-lifting theorem. Winding is its actual real endpoint, not an assumed invariant.
- `CategoryTheory.End`: The actual endomorphism type of an object. Its groupoid instance supplies the existing vertex group; multiplication reverses categorical composition.
- `OneHom`: Actual function with an identity-preservation field, inherited by MonoidHom. In Multiplicative real numbers identity means real zero.
- `MulHom`: Actual function with product-preservation field, inherited by MonoidHom. Tagged real multiplication is real addition.
- `Subsemigroup`: Carrier subset with multiplication closure; the actual first parent of Subgroup.
- `Submonoid`: Actual multiplication-closed subset containing identity, inherited by Subgroup before inverse closure.
- `IsEvenlyCovered`: The actual discrete fiber and local covering-trivialization condition at a point, underlying IsCoveringMap.
- `DiscreteTopology`: Actual discrete-topology property. Assumed explicitly for primitive E, separately proved for the real integer-period subgroup; finiteness alone does not assert discreteness of an arbitrary chosen topology.
- `Subgroup.zpowers`: Literal to_additive source producer of AddSubgroup.zmultiples: the actual subgroup of integer multiples. This generated additive declaration is not given an invented ordinary source header.
- `IsAddQuotientCoveringMap`: Actual additive quotient covering conditions, including topology, discrete action and fiber orbit relation. Standard real circle theorem proves these conditions.
- `IntervalIntegrable`: Actual integrability on both oriented Ioc intervals.
- `intervalIntegral`: Actual ordinary oriented Bochner integral: forward Ioc integral minus backward Ioc integral.
- `IntegrableOn`: Actual integrability against the measure restricted to the set.
- `Integrable`: Actual almost-everywhere strong measurability and finite norm integral.
- `HasFiniteIntegral`: Actual lintegral of enorm is finite.
- `StronglyMeasurable`: Actual pointwise approximation by simple functions.
- `AEStronglyMeasurable`: Actual a.e. equality with a strongly measurable function.
- `HasDerivAtFilter`: Actual Frechet derivative with one-dimensional scalar linear map.
- `HasDerivAt`: Actual derivative filter at the point.
- `deriv`: Actual Frechet derivative evaluated at one; totalized when nondifferentiable.
- `HasFDerivAtFilter`: Actual little-o TVS remainder condition, not a formal derivative certificate.
- `HasFDerivAt`: Actual Frechet derivative at the point.
- `DifferentiableAt`: Existence of an actual Frechet derivative at the point.
- `Differentiable`: Actual Frechet differentiability at every point, retained as generic calculus dependency infrastructure. Arbitrary admitted interval-AC lifts require only the proved almost-everywhere DifferentiableAt contract, not global differentiability.
- `Function.Periodic`: Actual equality f(x+c)=f(x) at every input. The canonical quotient-to-circle map uses a proved scaled-exponential period and the actual periodic lift; it is not a supplied analytic bridge.
- `ContinuousLinearMap.toSpanSingleton`: Actual scalar-to-vector linear map and evaluation used by HasDerivAt.
- `LipschitzWith`: Actual global extended-distance bound with a nonnegative real constant. Selected real-space uses are related to the ordinary distance bound by the retained proved equivalence.
- `NNReal`: Actual subtype of nonnegative real numbers, not an unconstrained bound.
- `Set.Finite`: Actual finiteness of the set subtype; underlying finite class is an equivalence with Fin n, retained below.
- `Set.Countable`: Actual countability of the set subtype; underlying class supplies an injection into Nat.
- `Countable`: Actual existence of an injective map into Nat, retained as conservative metric and measure infrastructure. This package claims no finite-corner differentiability result.
- `IsCompact`: Actual compactness predicate. The compact real interval supplies uniform continuity of the constructed real topological lift; other covering and integrability uses are retained as conservative infrastructure.
- `CompactSpace`: Actual compactness of the whole space; the real-circle instance is proved and retained.
- `Bornology.IsBounded`: Actual bornological boundedness through the cobounded complement, with its norm-bound equivalence retained.
- `Set.projIcc`: Actual interval projection by clamping, used to extend the actual covering lift to the real parameter line.
- `AbsolutelyContinuousOnInterval`: Actual filter convergence of finite sums of image distances as disjoint source interval total length tends to zero, restricted to uIcc endpoints. Equivalent to the retained epsilon-delta statement; regularity only on the specified interval.
- `AbsolutelyContinuousOnInterval.totalLengthFilter`: Actual comap of total finite source-distance sum along the real zero-neighborhood filter.
- `AbsolutelyContinuousOnInterval.disjWithin`: Actual finite-index interval endpoints in uIcc and pairwise disjoint uIoc intervals. It is not a finite exceptional differentiability set.
- `LipschitzOnWith`: Actual nonnegative edistance bound for all pairs in the specified set. Retained finite trace lifts derive their interval absolute continuity from the proved global Lipschitz bound; arbitrary admitted AC lifts are not assumed Lipschitz.
- `MeasureTheory.ae`: Actual conull-set filter; quantified assertions mean the set of failures has measure zero, via the retained null-complement equivalence.
- `Filter.Eventually`: Actual membership of the predicate truth set in the filter, underlying almost-everywhere quantification.
- `Set.uIcc`: Actual Icc between infimum and supremum of endpoints; for real ordered0≤1 this is Icc0 1.
- `Set.uIoc`: Actual Ioc between minimum and maximum of endpoints, used by interval integral a.e. congruence.
- `Set.EqOn`: Actual pointwise equality for every member of the specified set. Uniqueness is only Icc0 1, with no restriction outside it.
- `Set.Ioo`: Actual strict lower and upper endpoint inequalities, used for local derivative agreement in the interval interior.
- `Set.Ioc`: Actual strict lower and weak upper endpoint inequalities; the interval integral uses the corresponding restricted measure.
- `Set.Icc`: Actual weak lower and upper endpoint inequalities. Equality of minimizers is pointwise only on this interval.
- `Circle`: Actual complex unit circle as Submonoid.unitSphere complex numbers, with inherited topology. It is distinct from the candidate period-one additive CircleHodge.Circle alias.
- `Submonoid.unitSphere`: Actual submonoid with carrier Metric.sphere0 1; multiplication and unit are proved to preserve that carrier.
- `Metric.sphere`: Actual set of points with distance to the given center equal to the specified radius. At complex zero/radius one its membership is equivalent to norm one.
- `AddCircle.toCircle`: Actual periodic lift of the proved scaled Circle.exp map. At period1 its representative formula is exp(2*pi*i*x). At period0 the library instead gives constant1; this project uses period1 throughout.
- `Function.Periodic.lift`: Actual Quotient.liftOn of a function whose period c is proved; integer-multiple periodicity proves well-definedness on the additive quotient.
- `Circle.exp`: Actual continuous map sending real t to Complex.exp(t*i) together with a proof its norm is one. This is the unit-circle exponential, distinct from generic Complex.exp.
- `Complex`: Actual structure with real re and im fields. Ambient curves and derivatives take values in this real normed space.
- `Complex.ofReal`: Actual real-to-complex embedding with imaginary coordinate zero and its coercion instance.
- `Complex.I`: Actual complex imaginary unit with real coordinate0 and imaginary coordinate1.
- `Complex.normSq`: Actual multiplicative real function re(z)^2+im(z)^2, with full multiplicativity proof.
- `Complex.instNorm`: Actual complex norm is the nonnegative real square root of Complex.normSq. Its literal defining instance is not exposed, so the actual norm_def theorem is retained as the public semantic bridge.
- `starRingEnd`: Actual ring endomorphism whose function is star, denoted conj in ComplexConjugate scope. For complex numbers the retained StarRing instance negates the imaginary coordinate.
- `Complex.star_def`: Actual theorem identifying the complex Star.star function with the scoped conjugation map. The complete complex StarRing instance is retained separately.
- `Complex.exp`: Actual irreducible definition is the Cauchy limit of exp-prime, the Taylor partial-sum sequence. Cauchy-limit foundations remain credited generic infrastructure.
- `Complex.exp'`: Actual Cauchy sequence of partial sums of z^m/m!, with its convergence proof field.
- `Real.pi`: Actual positive half-turn constant defined as twice a chosen zero of cosine, with library positivity and exponential-period contracts. The project proves its normalization factors rather than assuming a speed or period identity.
- `Real.sqrt`: Actual real coercion of nonnegative square root after Real.toNNReal; negative inputs are totalized to zero.
- `NNReal.sqrt`: Actual inverse order isomorphism of nonnegative squaring, used by the real/complex norm infrastructure.
- `Real.toNNReal`: Actual subtype value max r0 and its nonnegative proof.
- `MeasureTheory.NullSingletonClass`: Actual assertion that every singleton has measure zero. The real Lebesgue measure instance justifies replacing Ioo by Ioc for the a.e. clamped derivative comparison.
- `circleMap`: Actual map θ to c+R*Complex.exp(θ*i), with its norm theorem. The selected embed_coe statement refers to this literal definition.
- `Path.map`: Actual map of a path through a globally continuous function, preserving the mapped endpoints. It delegates to the full map-prime construction; the unit-circle map is distinguished from complex coercion.
- `Path.map'`: Actual path structure obtained by composing with a function continuous on the path range, with explicit continuous and source/target proof fields.
- `Path.Homotopy.map`: Actual mapping of an endpoint-fixed path homotopy through a continuous map. Mapping through the circle subtype retains a homotopy within that subtype, while ambient complex homotopy alone would lose winding information.
- `Path.Homotopic.map`: Actual induced existence of a mapped homotopy by mapping the supplied homotopy witness.
- `UniformContinuous`: Actual Tendsto of the image pair map from source uniformity to target uniformity, retained as uniform-space infrastructure.
- `UniformContinuousOn`: Actual Tendsto of the pair map restricted by the principal filter on s times s. On real metric spaces the retained proved epsilon-delta equivalence is compiled separately; it is not claimed definitionally equal to that metric formula.
- `Homeomorph`: Actual equivalence of the underlying types together with continuity of forward and inverse maps. The candidate uses its actual inverse, not a presumed continuous inverse of an arbitrary function.
- `Homeomorph.symm`: Actual inverse homeomorphism, swapping the two continuity fields and using the inverse underlying equivalence.
- `Homeomorph.trans`: Actual composite homeomorphism, with forward/inverse continuity proved by composition and the underlying composed equivalence.
- `AddCircle.homeomorphCircle'`: Actual period-2*pi quotient homeomorphism to the complex unit circle. Its forward map is Angle.toCircle and inverse is argument modulo the angle quotient, with both inverse laws and both continuity proofs.
- `AddCircle.homeomorphCircle`: Actual nonzero-period quotient-to-complex-unit-circle homeomorphism, composing period rescaling with homeomorphCircle-prime. Period1 is proved nonzero in this candidate. The retained theorem identifies its forward map with AddCircle.toCircle.
- `AddCircle.homeomorphAddCircle`: Actual homeomorphism rescaling one nonzero quotient period to another, with quotient-induced forward/inverse continuity proofs.
- `AddCircle.equivAddCircle`: Actual additive quotient equivalence induced by multiplication by inverse source period times target period. The proof transports the cyclic subgroup, rather than assuming a quotient inverse exists.

## Selected family

- `ComputationalHodge.AutomaticLifts.chord_formula`
- `ComputationalHodge.AutomaticLifts.local_chord_lower`
- `ComputationalHodge.AutomaticLifts.ac_of_local_inverse`
- `ComputationalHodge.AutomaticLifts.circleEquiv_zero`
- `ComputationalHodge.AutomaticLifts.quotientPath_embed`
- `ComputationalHodge.AutomaticLifts.realLift_continuous`
- `ComputationalHodge.AutomaticLifts.lift_projection`
- `ComputationalHodge.AutomaticLifts.realLift_embed`
- `ComputationalHodge.AutomaticLifts.realLift_zero`
- `ComputationalHodge.AutomaticLifts.realLift_endpoint`
- `ComputationalHodge.AutomaticLifts.realLift_ac`
- `ComputationalHodge.AutomaticLifts.canonical_curve`
- `ComputationalHodge.AutomaticLifts.canonical_curve_on`
- `ComputationalHodge.AutomaticLifts.projected_canonical`
- `ComputationalHodge.AutomaticLifts.canonical_unique_on`
- `ComputationalHodge.AutomaticLifts.embed_real_lipschitz`
- `ComputationalHodge.AutomaticLifts.curve_ac`
- `ComputationalHodge.AutomaticLifts.lift_roundtrip`
- `ComputationalHodge.AutomaticLifts.input_deriv`
- `ComputationalHodge.AutomaticLifts.input_deriv_ae`
- `ComputationalHodge.AutomaticLifts.angular_integrands`
- `ComputationalHodge.AutomaticLifts.angular_integrable_input`
- `ComputationalHodge.AutomaticLifts.angularValue_eq`
- `ComputationalHodge.AutomaticLifts.angular_endpoint`
- `ComputationalHodge.AutomaticLifts.angular_winding`
- `ComputationalHodge.AutomaticLifts.energy_integrands`
- `ComputationalHodge.AutomaticLifts.finite_energy_input_iff`
- `ComputationalHodge.AutomaticLifts.input_energy_eq`
- `ComputationalHodge.AutomaticLifts.input_energy_lift`
- `ComputationalHodge.AutomaticLifts.input_class_minimum`
- `ComputationalHodge.AutomaticLifts.input_minimum_rigid`
- `ComputationalHodge.AutomaticLifts.integer_endpoint`
- `ComputationalHodge.AutomaticLifts.count_repeat`
- `ComputationalHodge.AutomaticLifts.count_integerTrace`
- `ComputationalHodge.AutomaticLifts.normalTrace_count`
- `ComputationalHodge.AutomaticLifts.representative_endpoint`
- `ComputationalHodge.AutomaticLifts.representative_homotopic`
- `ComputationalHodge.AutomaticLifts.angular_representative`
- `ComputationalHodge.AutomaticLifts.harmonic_representative`
- `ComputationalHodge.AutomaticLifts.minimum_representative`
- `ComputationalHodge.AutomaticLifts.ofLift_angular`
- `ComputationalHodge.AutomaticLifts.ofLift_energy`
- `ComputationalHodge.AutomaticLifts.raw_input_period`
- `ComputationalHodge.AutomaticLifts.raw_input_finite`
- `ComputationalHodge.AutomaticLifts.raw_lift_roundtrip`
- `ComputationalHodge.TraceIntegrals.rawLift_lipschitz`
- `ComputationalHodge.TraceIntegrals.actualLift_eq_rawLift`
- `ComputationalHodge.TraceIntegrals.rawLift_zero`
- `ComputationalHodge.TraceIntegrals.rawLift_one`
- `ComputationalHodge.TraceIntegrals.meanCochain_closed`
- `ComputationalHodge.TraceIntegrals.circle_exact_eq_bot`
- `ComputationalHodge.AutomaticLifts.circleEquiv`
- `ComputationalHodge.AutomaticLifts.unitPath`
- `ComputationalHodge.AutomaticLifts.quotientPath`
- `ComputationalHodge.AutomaticLifts.realLift`
- `ComputationalHodge.AutomaticLifts.canonicalLift`
- `ComputationalHodge.AutomaticLifts.ofLift`
- `ComputationalHodge.AutomaticLifts.angularValue`
- `ComputationalHodge.AutomaticLifts.InputFiniteEnergy`
- `ComputationalHodge.AutomaticLifts.inputEnergy`
- `ComputationalHodge.AutomaticLifts.repeatTrace`
- `ComputationalHodge.AutomaticLifts.integerTrace`
- `ComputationalHodge.AutomaticLifts.normalTrace`
- `ComputationalHodge.AutomaticLifts.ofTrace`
- `ComputationalHodge.UnitCircleGeometry.embed`
- `ComputationalHodge.UnitCircleGeometry.embedMap`
- `ComputationalHodge.UnitCircleGeometry.embeddedPath`
- `ComputationalHodge.UnitCircleGeometry.curve`
- `ComputationalHodge.UnitCircleGeometry.angularForm`
- `ComputationalHodge.UnitCircleGeometry.angularIntegral`
- `ComputationalHodge.UnitCircleGeometry.AmbientFiniteEnergy`
- `ComputationalHodge.UnitCircleGeometry.ambientEnergy`
- `ComputationalHodge.Dirichlet.FiniteEnergy`
- `ComputationalHodge.Dirichlet.energy`
- `ComputationalHodge.Dirichlet.defect`
- `ComputationalHodge.Dirichlet.affine`
- `ComputationalHodge.Dirichlet.affineHomotopy`
- `ComputationalHodge.ACLifts.ACLift`
- `ComputationalHodge.ACLifts.projectedLoop`
- `ComputationalHodge.ACLifts.fromTrace`
- `ComputationalHodge.TraceIntegrals.Trace`
- `ComputationalHodge.TraceIntegrals.count`
- `ComputationalHodge.TraceIntegrals.rawLift`
- `ComputationalHodge.TraceIntegrals.actualLift`
- `ComputationalHodge.TraceIntegrals.unitTrace`
- `ComputationalHodge.TraceIntegrals.unitCochain`
- `ComputationalHodge.TraceIntegrals.meanCochain`
- `ComputationalHodge.TraceIntegrals.meanHarmonic`
- `ComputationalHodge.CircleHodge.Circle`
- `ComputationalHodge.CircleHodge.Coefficient`
- `ComputationalHodge.CircleHodge.cover`
- `ComputationalHodge.CircleHodge.mean`
- `ComputationalHodge.Cochain`
- `ComputationalHodge.period`
- `ComputationalHodge.d0`
- `ComputationalHodge.d1`
- `ComputationalHodge.Closed`
- `ComputationalHodge.Exact`
- `ComputationalHodge.Harmonic`
- `ComputationalHodge.LoopCharacters.geometricPresentation`
- `ComputationalHodge.LoopCharacters.circleSystem`
- `ComputationalHodge.LoopCharacters.circleLift`
- `ComputationalHodge.LoopCharacters.winding`

## Exact pinned evidence

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

### ContinuousLinearMap.toSpanSingleton

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean#L743-L748

```lean
def toSpanSingleton (x : M₁) : R₁ →L[R₁] M₁ where
  toLinearMap := LinearMap.toSpanSingleton R₁ M₁ x

@[simp]
theorem toSpanSingleton_apply (x : M₁) (r : R₁) : toSpanSingleton R₁ x r = r • x :=
  rfl
```

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Equiv/Defs.lean#L49-L53

```lean
structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂

attribute [coe] LinearEquiv.toLinearMap
```

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

### Path.map

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L344-L352

```lean
/-- Image of a path from `x` to `y` by a continuous map -/
def map (γ : Path x y) {f : X → Y} (h : Continuous f) :
    Path (f x) (f y) := γ.map' h.continuousOn

@[simp, grind =]
theorem map_coe (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h : I → Y) = f ∘ γ := by
  ext t
  rfl
```

### Path.map'

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L337-L342

```lean
/-- Image of a path from `x` to `y` by a map which is continuous on the path. -/
def map' (γ : Path x y) {f : X → Y} (h : ContinuousOn f (range γ)) : Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x ↦ mem_range_self x)
  source' := by simp
  target' := by simp
```

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

### Path.Homotopic.Quotient

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L294-L295

```lean
protected def Quotient (x₀ x₁ : X) :=
  Quotient (Homotopic.setoid x₀ x₁)
```

### Path.Homotopic.Quotient.mk

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L305-L306

```lean
def mk (p : Path x₀ x₁) : Path.Homotopic.Quotient x₀ x₁ :=
  Quotient.mk' p
```

### Path.Homotopic.setoid

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L289-L290

```lean
protected def setoid (x₀ x₁ : X) : Setoid (Path x₀ x₁) :=
  ⟨Homotopic, equivalence⟩
```

### Path.Homotopy.hcomp

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L157-L169

```lean
def hcomp (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) : Homotopy (p₀.trans p₁) (q₀.trans q₁) where
  toFun x :=
    if (x.2 : ℝ) ≤ 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_toFun := continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
    (F.toHomotopy.continuous.comp (by fun_prop)).continuousOn
    (G.toHomotopy.continuous.comp (by fun_prop)).continuousOn fun x hx ↦ by norm_num [hx]
  map_zero_left x := by simp [Path.trans]
  map_one_left x := by simp [Path.trans]
  prop' x t ht := by
    rcases ht with ht | ht
    · norm_num [ht]
    · rw [Set.mem_singleton_iff] at ht
      norm_num [ht]
```

### Path.Homotopy.refl

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L99-L100

```lean
def refl (p : Path x₀ x₁) : Homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}
```

### Path.Homotopy.symm

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L105-L106

```lean
def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F
```

### Path.Homotopy.symm₂

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L209-L219

```lean
def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
  toFun x := F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
```

### Path.Homotopy.trans

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L119-L120

```lean
def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G
```

### Path.Homotopy.map

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L224-L235

```lean
-/
@[simps]
def map {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y)) :
    Homotopy (p.map f.continuous) (q.map f.continuous) where
  toFun := f ∘ F
  map_zero_left := by simp
  map_one_left := by simp
  prop' t x hx := by
    rcases hx with hx | hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]
```

### Path.Homotopic.map

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Path.lean#L270-L272

```lean
nonrec theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean

SHA256 `8cfce24311c16e1e624e01e6bd2ace37fe6be4647340c901681235129acf41b2`

```lean
/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
```

### Path.Homotopy.reflSymmTrans

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L77-L78

```lean
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
  (reflTransSymm p.symm).cast rfl <| congr_arg _ (Path.symm_symm _)
```

### Path.Homotopy.reflTrans

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L120-L121

```lean
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)
```

### Path.Homotopy.transAssoc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L161-L166

```lean
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm
```

### Path.Homotopy.transRefl

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L113-L117

```lean
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by fun_prop) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm
```

### FundamentalGroupoid

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L240-L242

```lean
structure FundamentalGroupoid (X : Type*) where
  /-- View a term of `FundamentalGroupoid X` as a term of `X`. -/
  as : X
```

### fundamental_groupoid_operations

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L287-L296

```lean
instance : Groupoid (FundamentalGroupoid X) where
  Hom x y := Path.Homotopic.Quotient x.as y.as
  id x := ⟦Path.refl x.as⟧
  comp := Path.Homotopic.Quotient.trans
  id_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.reflTrans f⟩
  comp_id := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.transRefl f⟩
  assoc := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact Quotient.sound ⟨Path.Homotopy.transAssoc f g h⟩
  inv := Quotient.lift (fun f ↦ ⟦f.symm⟧) (by rintro a b ⟨h⟩; exact Quotient.sound ⟨h.symm₂⟩)
  inv_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflSymmTrans f).symm⟩
  comp_inv := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflTransSymm f).symm⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean

SHA256 `c75fb2a102be49010eac04a1602160eaaa2c4c18d12b29bf6f5c45f622dad1e8`

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

### Equiv.ofBijective

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean#L821-L825

```lean
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Equiv.lean

SHA256 `12d18d55d3b5a01c63386566a3797fb3ddc4b6ea78873226cd93a8a80a65e6b9`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### LinearEquiv.ofBijective

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Equiv.lean#L183-L186

```lean
noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :
    M ≃ₛₗ[σ₁₂] M₂ :=
  (ofInjective f hf.injective).trans <| ofTop _ <|
    LinearMap.range_eq_top.2 hf.surjective
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

SHA256 `4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7`

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

### Set

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L51-L51

```lean
def Set (α : Type u) := α → Prop
```

### Set.image

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L266-L266

```lean
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}
```

### Set.ofPred

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L67-L68

```lean
def Set.ofPred {α : Type u} (p : α → Prop) : Set α :=
  p
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

SHA256 `60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e`

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

### Set.range

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L173-L173

```lean
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
```

### Set.EqOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L290-L291

```lean
/-- Two functions `f₁ f₂ : α → β` are equal on `s` if `f₁ x = f₂ x` for all `x ∈ s`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean

SHA256 `415e59cdbff01d813d4ae589c9d073da284c0d2df4e47a788784d1a565c04689`

```lean
/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
```

### FundamentalGroup

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean#L35-L46

```lean
abbrev FundamentalGroup (x : X) :=
  End (FundamentalGroupoid.mk x)

variable {X}

namespace FundamentalGroup

variable {x : X} {p q : FundamentalGroup X x}

theorem one_def : (1 : FundamentalGroup X x) = .refl x := rfl
theorem mul_def : p * q = q.trans p := rfl
theorem inv_def : p⁻¹ = p.symm := rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Defs.lean

SHA256 `552903abcab0523f0c6571210b6f3a00e51604402cfe11b2b13deb45eafa3662`

```lean
/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
```

### Subgroup

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Defs.lean#L297-L299

```lean
structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier
```

### Subgroup.subtype

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Defs.lean#L566-L572

```lean
protected def subtype : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]
lemma subtype_apply {s : Subgroup G} (x : s) :
    s.subtype x = x := rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Hom/Defs.lean

SHA256 `8f881402b407f768c9b3d1ef7c5d16e51586799a4d61b8375517c07020c371b9`

```lean
/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
```

### MonoidHom

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Hom/Defs.lean#L366-L367

```lean
structure MonoidHom (M : Type*) (N : Type*) [MulOne M] [MulOne N]
  extends OneHom M N, M →ₙ* N
```

### OneHom

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Hom/Defs.lean#L177-L181

```lean
structure OneHom (M : Type*) (N : Type*) [One M] [One N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves 1 -/
  protected map_one' : toFun 1 = 1
```

### MulHom

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Hom/Defs.lean#L294-L298

```lean
structure MulHom (M : Type*) (N : Type*) [Mul M] [Mul N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves multiplication -/
  protected map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/TypeTags/Basic.lean

SHA256 `7cc44af75709b67805a8a6c22ee07d904497dc342bd27e13aded169c275dca46`

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

### Multiplicative

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/TypeTags/Basic.lean#L46-L46

```lean
def Multiplicative (α : Type*) := α
```

### Multiplicative.ofAdd

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/TypeTags/Basic.lean#L86-L87

```lean
def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
```

### Multiplicative.toAdd

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/TypeTags/Basic.lean#L91-L91

```lean
def toAdd : Multiplicative α ≃ α := ofAdd.symm
```

### multiplicative_tagged_addition

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/TypeTags/Basic.lean#L160-L167

```lean
instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
  mul x y := ofAdd (x.toAdd + y.toAdd)

@[simp]
theorem ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y := rfl

@[simp]
theorem toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = x.toAdd + y.toAdd := rfl
```

### multiplicative_tagged_zero

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/TypeTags/Basic.lean#L240-L253

```lean
instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl

@[simp]
theorem ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  Iff.rfl

@[simp]
theorem toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0 :=
  rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean

SHA256 `f9329924aefc77847fe0bb04af7a7f34df11c077bc124beaf26006e70141f1ce`

```lean
/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
```

### AddCircle

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean#L189-L190

```lean
abbrev AddCircle [AddCommGroup 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p
```

### circle_quotient_operations

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean#L204-L229

```lean
theorem coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : AddCircle p) :=
  rfl

theorem coe_sub (x y : 𝕜) : (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : AddCircle p) :=
  rfl

theorem coe_neg {x : 𝕜} : (↑(-x) : AddCircle p) = -(x : AddCircle p) :=
  rfl

@[norm_cast]
theorem coe_zero : ↑(0 : 𝕜) = (0 : AddCircle p) :=
  rfl

theorem coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ ∃ n : ℤ, n • p = x := by
  simp [AddSubgroup.mem_zmultiples_iff]

theorem coe_period : (p : AddCircle p) = 0 :=
  (QuotientAddGroup.eq_zero_iff p).2 <| mem_zmultiples p

theorem coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCircle p) = x := by
  rw [coe_add, ← eq_sub_iff_add_eq', sub_self, coe_period]

@[continuity, nolint unusedArguments]
protected theorem continuous_mk' [TopologicalSpace 𝕜] :
    Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 → AddCircle p) :=
  continuous_coinduced_rng
```

### AddCircle.homeomorphAddCircle

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean#L525-L528

```lean
def homeomorphAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃ₜ AddCircle q :=
  ⟨equivAddCircle p q hp hq,
    (continuous_quotient_mk'.comp (continuous_mul_const (p⁻¹ * q))).quotient_lift _,
    (continuous_quotient_mk'.comp (continuous_mul_const (q⁻¹ * p))).quotient_lift _⟩
```

### AddCircle.equivAddCircle

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean#L499-L502

```lean
def equivAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃+ AddCircle q :=
  QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) <| by
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.coe_ofClass, AddAut.mulRight_apply, Units.val_mul,
      Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel_left₀ hp]
```

### actual_rescaling_representative_formulas

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean#L504-L512

```lean
@[simp]
theorem equivAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    equivAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
theorem equivAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (equivAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl
```

### actual_rescaling_homeomorphism_formulas

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean#L530-L538

```lean
@[simp]
theorem homeomorphAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    homeomorphAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
theorem homeomorphAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (homeomorphAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl
```

### actual_quotient_integer_endpoint

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Defs.lean#L216-L218

```lean

theorem coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ ∃ n : ℤ, n • p = x := by
  simp [AddSubgroup.mem_zmultiples_iff]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/Basic.lean

SHA256 `85517cbcabc90b4f0a79c8b9c38fc93ea2b1c2927db1d1a23e339bf7f3bfcb32`

```lean
/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
```

### IsCoveringMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/Basic.lean#L288-L289

```lean
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})
```

### IsEvenlyCovered

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/Basic.lean#L40-L42

```lean
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    ∃ H : f ⁻¹' U ≃ₜ U × I, ∀ x, (H x).1.1 = f x
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean

SHA256 `47b44da5cc6f4d708c6d234a8abceea6a6852da69cd5e25c70c8e34deda9b47c`

```lean
/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
```

### IsCoveringMap.liftPath

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L259-L262

```lean
def liftPath : C(I, E) := (cov.exists_path_lifts γ e γ_0).choose

lemma liftPath_lifts : p ∘ cov.liftPath γ e γ_0 = γ := (cov.exists_path_lifts γ e γ_0).choose_spec.1
lemma liftPath_zero : cov.liftPath γ e γ_0 0 = e := (cov.exists_path_lifts γ e γ_0).choose_spec.2
```

### covering_path_lift_existence

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L217-L256

```lean
/-- The path lifting property (existence) for covering maps. -/
theorem exists_path_lifts : ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  let U x := (cov x).2.choose
  choose mem_base U_open _ H _ using fun x ↦ (cov x).2.choose_spec
  obtain ⟨t, t_0, t_mono, ⟨n_max, h_max⟩, t_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
    (fun x ↦ (U_open x).preimage γ.continuous) fun t _ ↦ Set.mem_iUnion.2 ⟨γ t, mem_base _⟩
  suffices ∀ n, ∃ Γ : I → E, ContinuousOn Γ (Set.Icc 0 (t n)) ∧
      (Set.Icc 0 (t n)).EqOn (p ∘ Γ) γ ∧ Γ 0 = e by
    obtain ⟨Γ, cont, eqOn, Γ_0⟩ := this n_max
    rw [h_max _ le_rfl] at cont eqOn
    exact ⟨⟨Γ, continuousOn_univ.mp
      (by convert! cont; rw [eq_comm, Set.eq_univ_iff_forall]; exact fun t ↦ ⟨bot_le, le_top⟩)⟩,
      funext fun _ ↦ eqOn ⟨bot_le, le_top⟩, Γ_0⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ ↦ e, continuous_const.continuousOn, fun t ht ↦ ?_, rfl⟩
    rw [t_0, Set.Icc_self, Set.mem_singleton_iff] at ht; subst ht; exact γ_0.symm
  | succ n ih => ?_
  obtain ⟨Γ, cont, eqOn, Γ_0⟩ := ih
  obtain ⟨x, t_sub⟩ := t_sub n
  have pΓtn : p (Γ (t n)) = γ (t n) := eqOn ⟨t_0 ▸ t_mono n.zero_le, le_rfl⟩
  have : Nonempty (p ⁻¹' {x}) :=
    ⟨(H x ⟨Γ (t n), Set.mem_preimage.mpr (pΓtn ▸ t_sub ⟨le_rfl, t_mono n.le_succ⟩)⟩).2⟩
  let q := (cov x).toTrivialization
  refine ⟨fun s ↦ if s ≤ t n then Γ s else q.invFun (γ s, (q (Γ (t n))).2),
    .if (fun s hs ↦ ?_) (cont.mono fun _ h ↦ ?_) ?_, fun s hs ↦ ?_, ?_⟩
  · cases frontier_Iic_subset _ hs.2
    rw [← pΓtn]
    refine (q.symm_apply_mk_proj ?_).symm
    rw [q.mem_source, pΓtn]
    exact t_sub ⟨le_rfl, t_mono n.le_succ⟩
  · rw [closure_le_eq continuous_id' continuous_const] at h; exact ⟨h.1.1, h.2⟩
  · apply q.continuousOn_invFun.comp ((Continuous.prodMk_left _).comp γ.2).continuousOn
    simp_rw [not_le, q.target_eq]; intro s h
    exact ⟨t_sub ⟨closure_lt_subset_le continuous_const continuous_subtype_val h.2, h.1.2⟩, ⟨⟩⟩
  · rw [Function.comp_apply]; split_ifs with h
    exacts [eqOn ⟨hs.1, h⟩, q.proj_symm_apply' (t_sub ⟨le_of_not_ge h, hs.2⟩)]
  · dsimp only; rwa [ite_eq_left (t_0 ▸ t_mono n.zero_le)]
```

### lift_path_uniqueness

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L264-L273

```lean
variable {γ e}
lemma eq_liftPath_iff {Γ : I → E} : Γ = cov.liftPath γ e γ_0 ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e :=
  have lifts := cov.liftPath_lifts γ e γ_0
  have zero := cov.liftPath_zero γ e γ_0
  ⟨(· ▸ ⟨(cov.liftPath γ e γ_0).2, lifts, zero⟩), fun ⟨Γ_cont, Γ_lifts, Γ_0⟩ ↦ cov.eq_of_comp_eq
    Γ_cont (cov.liftPath γ e γ_0).continuous (Γ_lifts ▸ lifts.symm) 0 (Γ_0 ▸ zero.symm)⟩

/-- Unique characterization of the lifted path. -/
lemma eq_liftPath_iff' {Γ : C(I, E)} : Γ = cov.liftPath γ e γ_0 ↔ p ∘ Γ = γ ∧ Γ 0 = e := by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftPath_iff, and_iff_right (ContinuousMap.continuous _)]
```

### lift_constant_path

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L275-L277

```lean
omit γ_0
lemma liftPath_const {x : X} (hpe : x = p e) : cov.liftPath (.const I x) e hpe = .const I e :=
  .symm <| (cov.eq_liftPath_iff' _).mpr ⟨funext fun _ ↦ hpe.symm, rfl⟩
```

### lift_path_concatenation

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L279-L288

```lean
lemma liftPath_trans {x y z : X} {e : E} (hpe : x = p e) (γ : Path x y) (γ' : Path y z) :
    letI Γ := cov.liftPath γ e (γ.source.trans hpe)
    cov.liftPath (γ.trans γ') e (by simpa) = (⟨Γ, liftPath_zero .., rfl⟩ : Path e (Γ 1)).trans
      ⟨cov.liftPath γ' (Γ 1) (by simpa using congr($(cov.liftPath_lifts γ ..) 1).symm),
        liftPath_zero .., rfl⟩ := by
  refine .symm <| (cov.eq_liftPath_iff' _).mpr ⟨funext fun _ ↦ ?_, by simp⟩
  simp only [ContinuousMap.coe_coe, Function.comp_apply, Path.trans_apply]; split_ifs
  · exact congr_fun (cov.liftPath_lifts γ e (γ.source.trans hpe)) _
  · refine congr_fun (cov.liftPath_lifts γ' _ ?_) _
    simpa using congr($(cov.liftPath_lifts γ ..) 1).symm
```

### lift_homotopic_endpoint

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L378-L384

```lean
/-- Lifting two paths that are homotopic relative to `{0,1}`
  starting from the same point also ends up in the same point. -/
theorem liftPath_apply_one_eq_of_homotopicRel {γ₀ γ₁ : C(I, X)}
    (h : γ₀.HomotopicRel γ₁ {0,1}) (e : E) (h₀ : γ₀ 0 = p e) (h₁ : γ₁ 0 = p e) :
    cov.liftPath γ₀ e h₀ 1 = cov.liftPath γ₁ e h₁ 1 := by
  have := (cov.homotopicRel_liftPath h e h₀ h₁).some
  rw [← this.eq_fst 0 (.inr rfl), ← this.eq_snd 0 (.inr rfl)]
```

### actual_covering_lift_projection_and_zero

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L259-L262

```lean
def liftPath : C(I, E) := (cov.exists_path_lifts γ e γ_0).choose

lemma liftPath_lifts : p ∘ cov.liftPath γ e γ_0 = γ := (cov.exists_path_lifts γ e γ_0).choose_spec.1
lemma liftPath_zero : cov.liftPath γ e γ_0 0 = e := (cov.exists_path_lifts γ e γ_0).choose_spec.2
```

### actual_covering_lift_uniqueness

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homotopy/Lifting.lean#L265-L273

```lean
lemma eq_liftPath_iff {Γ : I → E} : Γ = cov.liftPath γ e γ_0 ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e :=
  have lifts := cov.liftPath_lifts γ e γ_0
  have zero := cov.liftPath_zero γ e γ_0
  ⟨(· ▸ ⟨(cov.liftPath γ e γ_0).2, lifts, zero⟩), fun ⟨Γ_cont, Γ_lifts, Γ_0⟩ ↦ cov.eq_of_comp_eq
    Γ_cont (cov.liftPath γ e γ_0).continuous (Γ_lifts ▸ lifts.symm) 0 (Γ_0 ▸ zero.symm)⟩

/-- Unique characterization of the lifted path. -/
lemma eq_liftPath_iff' {Γ : C(I, E)} : Γ = cov.liftPath γ e γ_0 ↔ p ∘ Γ = γ ∧ Γ 0 = e := by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftPath_iff, and_iff_right (ContinuousMap.continuous _)]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/AddCircle.lean

SHA256 `21e214b64c40eeb73dd1fb3b9e3047c59693aad10b590deef864a2bfd4837f25`

```lean
/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
```

### circle_covering_theorem

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/AddCircle.lean#L25-L33

```lean
variable {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  [DiscreteTopology (zmultiples p)]

theorem isAddQuotientCoveringMap_coe :
    IsAddQuotientCoveringMap ((↑) : 𝕜 → AddCircle p) (zmultiples p) :=
  isAddQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete

theorem isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p) :=
  (isAddQuotientCoveringMap_coe p).isCoveringMap
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Endomorphism.lean

SHA256 `7c9eb33bb74caeacb6efe3bab7f7e57ad77c07b42489ba91952eebf866fcca4f`

```lean
/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Kim Morrison, Simon Hudon
-/
```

### CategoryTheory.End

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Endomorphism.lean#L33-L33

```lean
def End {C : Type u} [CategoryStruct.{v} C] (X : C) := X ⟶ X
```

### endomorphism_one

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Endomorphism.lean#L41-L41

```lean
protected instance one : One (End X) := ⟨𝟙 X⟩
```

### endomorphism_mul

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Endomorphism.lean#L45-L47

```lean
/-- Multiplication of endomorphisms agrees with `Function.comp`, not with
`CategoryTheory.CategoryStruct.comp`. -/
protected instance mul : Mul (End X) := ⟨fun x y => y ≫ x⟩
```

### endomorphism_monoid

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Endomorphism.lean#L73-L76

```lean
instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) where
  mul_one := Category.id_comp
  one_mul := Category.comp_id
  mul_assoc := fun x y z => (Category.assoc z y x).symm
```

### endomorphism_group

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Endomorphism.lean#L101-L103

```lean
instance group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) where
  inv_mul_cancel := Groupoid.comp_inv
  inv := Groupoid.inv
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subsemigroup/Defs.lean

SHA256 `4ab4d0c29bf4550a10c9108bd64cc5cab58ade6021ffc97fc6ca7c6aa14021f2`

```lean
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
```

### Subsemigroup

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subsemigroup/Defs.lean#L80-L84

```lean
structure Subsemigroup (M : Type*) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Submonoid/Defs.lean

SHA256 `52ff47a2ba94c07e93e3f6774aa3c003bc3e40187fea1f0f2df848e68677cf70`

```lean
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
```

### Submonoid

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Submonoid/Defs.lean#L89-L91

```lean
structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (1 : M) ∈ carrier
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean

SHA256 `2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### DiscreteTopology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L309-L311

```lean
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/ZMultiples.lean

SHA256 `3ef91abb73e7a4201087b6e779b5bb1de0093ed4f62d1be389adc7d25a98ea9b`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### real_zmultiples_discreteness

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/ZMultiples.lean#L37-L47

```lean
/-- This is a special case of `NormedSpace.discreteTopology_zmultiples`. It exists only to simplify
dependencies. -/
instance {a : ℝ} : DiscreteTopology (AddSubgroup.zmultiples a) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := (⊥ : Submodule ℤ ℝ))
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨ball 0 |a|, isOpen_ball, ?_⟩
  ext ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  simp [ha, Real.dist_eq, abs_mul, (by norm_cast : |(k : ℝ)| < 1 ↔ |k| < 1)]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/ZPowers/Basic.lean

SHA256 `f89ba7ae44ad3d36d581858dc6d1186bf5c0a3ddc8d293792cc3d50858d89a01`

```lean
/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
```

### Subgroup.zpowers

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/ZPowers/Basic.lean#L28-L34

```lean
/-- The subgroup generated by an element. -/
@[to_additive /-- The additive subgroup generated by an element. -/]
def zpowers (g : G) : Subgroup G where
  carrier := Set.range (g ^ · : ℤ → G)
  one_mem' := ⟨0, zpow_zero g⟩
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, zpow_add ..⟩
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, zpow_neg ..⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coset/Defs.lean

SHA256 `54d12da7845705c511a89b705f4cb5ea55cb8017df66737af77d8319e229713c`

```lean
/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
```

### quotient_group_left_relation_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coset/Defs.lean#L63-L77

```lean
@[to_additive (attr := instance_reducible)
  /-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup. -/]
def leftRel : Setoid α :=
  MulAction.orbitRel s.op α

variable {s} in
@[to_additive]
theorem leftRel_apply {x y : α} : leftRel s x y ↔ x⁻¹ * y ∈ s :=
  calc
    (∃ a : s.op, y * MulOpposite.unop a = x) ↔ ∃ a : s, y * a = x :=
      s.equivOp.symm.exists_congr_left
    _ ↔ ∃ a : s, x⁻¹ * y = a⁻¹ := by
      simp only [inv_mul_eq_iff_eq_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y ∈ s := by simp [exists_inv_mem_iff_exists_mem]
```

### additive_quotient_carrier_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coset/Defs.lean#L92-L95

```lean
@[to_additive /-- `α ⧸ s` is the quotient type representing the left cosets of `s`. If `s` is a
normal subgroup, `α ⧸ s` is a group -/]
instance instHasQuotientSubgroup : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotient (leftRel s)⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/QuotientGroup/Defs.lean

SHA256 `932e6148c3bb93384ae8a1900c0d4a9120c46391c8d9cd810a769d7aa5b59c4d`

```lean
/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
```

### quotient_group_operations_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/QuotientGroup/Defs.lean#L59-L73

```lean
/-- The congruence relation generated by a normal subgroup. -/
@[to_additive /-- The additive congruence relation generated by a normal additive subgroup. -/]
protected def con : Con G where
  toSetoid := leftRel N
  mul' := fun {a b c d} hab hcd => by
    rw [leftRel_eq] at hab hcd ⊢
    dsimp only
    calc
      c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ * (c⁻¹ * d) ∈ N := N.mul_mem (nN.conj_mem _ hab _) hcd
      _ = (a * c)⁻¹ * (b * d) := by
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

@[to_additive]
instance Quotient.group : Group (G ⧸ N) :=
  inferInstanceAs <| Group (delta% QuotientGroup.con N).Quotient
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/Quotient.lean

SHA256 `3fb78db01f6f47c0075cefce57027b094b8e16b5762932880ba85d8f0c57c248`

```lean
/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
```

### IsAddQuotientCoveringMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/Quotient.lean#L28-L32

```lean
structure IsAddQuotientCoveringMap (G) [AddGroup G] [AddAction G E] : Prop
    extends IsQuotientMap f, ContinuousConstVAdd G E where
  apply_eq_iff_mem_orbit {e₁ e₂} : f e₁ = f e₂ ↔ e₁ ∈ AddAction.orbit G e₂
  disjoint (e : E) : ∃ U ∈ 𝓝 e, ∀ g : G, ((g +ᵥ ·) '' U ∩ U).Nonempty → g = 0

```

### additive_cover_conversion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Covering/Quotient.lean#L38-L52

```lean
structure IsQuotientCoveringMap : Prop extends IsQuotientMap f, ContinuousConstSMul G E where
  apply_eq_iff_mem_orbit {e₁ e₂} : f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂
  disjoint (e : E) : ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1

attribute [to_additive] isQuotientCoveringMap_iff

lemma IsAddQuotientCoveringMap.toMultiplicative (G) [AddGroup G] [AddAction G E]
    (hf : IsAddQuotientCoveringMap f G) :
    IsQuotientCoveringMap f (Multiplicative G) where
  __ := hf.toIsQuotientMap
  continuous_const_smul g := by simpa using hf.continuous_const_vadd (Multiplicative.ofAdd.symm g)
  apply_eq_iff_mem_orbit {e₁ e₂} := by simp [hf.apply_eq_iff_mem_orbit]
  disjoint e := by
    obtain ⟨U, hU, hU'⟩ := hf.disjoint e
    exact ⟨U, hU, fun g ↦ by simpa using hU' (Multiplicative.ofAdd.symm g)⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean

SHA256 `97e7a2efda146d0d1280f23d660cc07655dd7c48b51631752e9aa94deaa18ab9`

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
```

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

### nonnegative_interval_integral_zero_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L1284-L1292

```lean

section

variable {f g : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ}

theorem integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f)
    (hfi : IntervalIntegrable f μ a b) :
    ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b)] 0 := by
  rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]
```

### finite_energy_interval_conversion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L141-L144

```lean
theorem intervalIntegrable_iff_integrableOn_Icc_of_le [NullSingletonClass μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Icc a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab, integrableOn_Icc_iff_integrableOn_Ioc ha]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntegrableOn.lean

SHA256 `4195a3becfc509b18adfbfc541dfd11a5a0f16954193e42e8d629a025636d0f9`

```lean
/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
```

### IntegrableOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntegrableOn.lean#L92-L93

```lean
def IntegrableOn (f : α → ε) (s : Set α) (μ : Measure α := by volume_tac) : Prop :=
  Integrable f (μ.restrict s)
```

### bounded_measurable_integrability

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntegrableOn.lean#L174-L176

```lean
lemma IntegrableOn.of_bound (hs : μ s < ∞) {f : α → E} (hf : AEStronglyMeasurable f (μ.restrict s))
    (C : ℝ) (hfC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) : IntegrableOn f s μ :=
  ⟨hf, .restrict_of_bounded C hs hfC⟩
```

### integrable_squared_speed_bound

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntegrableOn.lean#L174-L176

```lean
lemma IntegrableOn.of_bound (hs : μ s < ∞) {f : α → E} (hf : AEStronglyMeasurable f (μ.restrict s))
    (C : ℝ) (hfC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) : IntegrableOn f s μ :=
  ⟨hf, .restrict_of_bounded C hs hfC⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean

SHA256 `27797fe4384b5a8f3fab05c4c5b7d1b4f98c3801a9c441d7f75272d4f095df42`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
```

### Integrable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L59-L61

```lean
def Integrable {α} {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean

SHA256 `09f9234723516bbb3d61b8b341d2868c94c8b32ce5f47975983ce8dd67c16712`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
```

### HasFiniteIntegral

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean#L82-L84

```lean
def HasFiniteIntegral {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean

SHA256 `bc488ed7d7218febe4c2508baca8d84eef8905b5b5972731c4d412d700591b20`

```lean
/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
```

### StronglyMeasurable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean#L65-L66

```lean
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean

SHA256 `a1dc11dc7e22a7c20fa382b909d6eb3496b3d346224b9896cb377f2ae5f4418a`

```lean
/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
```

### AEStronglyMeasurable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean#L67-L69

```lean
def AEStronglyMeasurable [m : MeasurableSpace α] {m₀ : MeasurableSpace α} (f : α → β)
    (μ : Measure[m₀] α := by volume_tac) : Prop :=
  ∃ g : α → β, StronglyMeasurable[m] g ∧ f =ᵐ[μ] g
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean

SHA256 `f4c0077cb0e87c857f1fcfea2c9c6263d1a3dee9fa8403893e00debf28a4356b`

```lean
/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
```

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

### deriv

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L153-L154

```lean
def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1
```

### derivative_default_zero

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L250-L253

```lean
theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt h]
  simp
```

### lipschitz_derivative_norm

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L937-L939

```lean
theorem norm_deriv_le_of_lipschitz {f : 𝕜 → F} {x₀ : 𝕜}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitz 𝕜 hlip
```

### lipschitz_actual_derivative_bound

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L934-L939

```lean
/-- Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `deriv`. -/
theorem norm_deriv_le_of_lipschitz {f : 𝕜 → F} {x₀ : 𝕜}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖deriv f x₀‖ ≤ C := by
  simpa [norm_deriv_eq_norm_fderiv] using norm_fderiv_le_of_lipschitz 𝕜 hlip
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean

SHA256 `27a7410d70541ab4a947cc95c30b16583d1f89fc073ca47e76c978b0b22f13ba`

```lean
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
```

### HasFDerivAtFilter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L110-L112

```lean
structure HasFDerivAtFilter (f : E → F) (f' : E →L[𝕜] F) (L : Filter (E × E)) : Prop where
  of_isLittleOTVS ::
    isLittleOTVS : (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p ↦ p.1 - p.2)
```

### HasFDerivAt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L123-L124

```lean
def HasFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' (𝓝 x ×ˢ pure x)
```

### DifferentiableAt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L145-L146

```lean
def DifferentiableAt (f : E → F) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFDerivAt f f' x
```

### Differentiable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L170-L171

```lean
def Differentiable (f : E → F) :=
  ∀ x, DifferentiableAt 𝕜 f x
```

### Frechet_derivative_choice

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Defs.lean#L151-L161

```lean
irreducible_def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
  if HasFDerivWithinAt f (0 : E →L[𝕜] F) s x
    then 0
  else if h : DifferentiableWithinAt 𝕜 f s x
    then Classical.choose h
  else 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
irreducible_def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
  fderivWithin 𝕜 f univ x
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Ring/Periodic.lean

SHA256 `6b402360ebbc1ad95a1cbbd40ddb1f6fb7bf57941dcf15fab5402be30d8507c9`

```lean
/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
```

### Function.Periodic

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Ring/Periodic.lean#L43-L44

```lean
def Periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x
```

### Function.Periodic.lift

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Ring/Periodic.lean#L216-L222

```lean
/-- Lift a periodic function to a function from the quotient group. -/
def Periodic.lift [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean

SHA256 `a6341a15d805c17e6922cd9c3f69508d604574058e37b06ec8cb51626ebbfa4d`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
```

### ordinary_Bochner_integral

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L158-L161

```lean
irreducible_def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α → G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
  else 0
```

### ordinary_integral_default_zero

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L204-L206

```lean
theorem integral_undef {f : α → G} (h : ¬Integrable f μ) : ∫ a, f a ∂μ = 0 := by
  simp only [integral_eq_setToFun]
  exact setToFun_undef (dominatedFinMeasAdditive_weightedSMul μ) h
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Bochner/L1.lean

SHA256 `4269e210eee8cd9e4e7a9c35f8c316eed7fee5488db5ca9c544d7a09ccf54fd4`

```lean
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
```

### L1_integral_extension

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/Bochner/L1.lean#L529-L538

```lean
nonrec def integralCLM' : (α →₁[μ] E) →L[𝕜] E :=
  (integralCLM' α E 𝕜 μ).extend (coeToLp α E 𝕜)

/-- The Bochner integral in L1 space as a continuous linear map over ℝ. -/
def integralCLM : (α →₁[μ] E) →L[ℝ] E :=
  integralCLM' ℝ

/-- The Bochner integral in L1 space -/
irreducible_def integral : (α →₁[μ] E) → E :=
  integralCLM
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean

SHA256 `5fd64054d9ae8bfce585ff809933a756bcf2d224ef144ae24c8fe8870c68050c`

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
```

### FTC_primitive

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L725-L728

```lean
theorem integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  (integral_hasStrictDerivAt_right hf hmeas hb).hasDerivAt
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean

SHA256 `c29cf7392ddbd5acbe615c55fc36315e65bd7563c84f0118273666ef523bd403`

```lean
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
```

### periodic_interval_translation

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean#L344-L363

```lean
theorem intervalIntegral_add_eq (hf : Periodic f T) (t s : ℝ) :
    ∫ x in t..t + T, f x = ∫ x in s..s + T, f x := by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with hT | hT
    · simp [hT]
    · rw [← neg_inj, ← integral_symm, ← integral_symm]
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        this hf.neg (t + T) (s + T) (neg_pos.mpr hT)
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s, hf.map_vadd_zmultiples]

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
theorem intervalIntegral_add_eq_add (hf : Periodic f T) (t s : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..s + T, f x = (∫ x in t..s, f x) + ∫ x in t..t + T, f x := by
  rw [hf.intervalIntegral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]
```

### integer_period_integral

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean#L367-L387

```lean
theorem intervalIntegral_add_zsmul_eq (hf : Periodic f T) (n : ℤ) (t : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x := by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0..(n • T), f x) = n • ∫ x in 0..T, f x by
    simp only [hf.intervalIntegral_add_eq t 0, (hf.zsmul n).intervalIntegral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : ∀ m : ℕ, (∫ x in 0..m • T, f x) = m • ∫ x in 0..T, f x := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [succ_nsmul, hf.intervalIntegral_add_eq_add 0 (m • T) h_int, ih, zero_add]
  -- Then prove it for all integers
  rcases n with n | n
  · simp [← this n]
  · conv_rhs => rw [negSucc_zsmul]
    have h₀ : Int.negSucc n • T + (n + 1) • T = 0 := by simp; linarith
    rw [integral_symm, ← (hf.nsmul (n + 1)).funext, neg_inj]
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n + 1), add_comm T,
      hf.intervalIntegral_add_eq ((n + 1) • T) 0, zero_add]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean

SHA256 `9e7e2105e21cdb7dbe731515213bcd1f6cf78c902bcd2da7f33b468218d90664`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### volume_measure_class

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean#L356-L359

```lean
class MeasureSpace (α : Type*) extends MeasurableSpace α where
  volume : Measure α

export MeasureSpace (volume)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean

SHA256 `628bcfc45fabd59501cdebf1cc3a8003ef3aba18fc7de4710ca9ffc1033b32d7`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
```

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

### Lebesgue_interval_length

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L110-L110

```lean
theorem volume_Ioc {a b : ℝ} : volume (Ioc a b) = ofReal (b - a) := by simp [volume_val]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Lipschitz.lean

SHA256 `25611eec76f2a5a9312506507c5064bdd826fde11c578658393f17cdac9a0cd6`

```lean
/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov, Winston Yin
-/
```

### LipschitzWith

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Lipschitz.lean#L60-L60

```lean
def LipschitzWith (K : ℝ≥0) (f : α → β) := ∀ x y, edist (f x) (f y) ≤ K * edist x y
```

### LipschitzOnWith

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Lipschitz.lean#L64-L65

```lean
def LipschitzOnWith (K : ℝ≥0) (f : α → β) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → edist (f x) (f y) ≤ K * edist x y
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean

SHA256 `5a94f78b3f6ce87106eea63ea8bfa48647de38cf2e51bff75f06a311ef821c99`

```lean
/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
```

### NNReal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean#L58-L58

```lean
def NNReal := { r : ℝ // 0 ≤ r }
```

### Real.toNNReal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean#L155-L156

```lean
def _root_.Real.toNNReal (r : ℝ) : ℝ≥0 :=
  .mk (max r 0) (le_max_right _ _)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Finite/Defs.lean

SHA256 `1e94b38b09b4fc3acaff3c22f60ee46f960dd45ccc5392ca9993abbbb1ef8cad`

```lean
/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
```

### Set.Finite

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Finite/Defs.lean#L185-L185

```lean
protected def Finite (s : Set α) : Prop := Finite s
```

### finite_type_contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Finite/Defs.lean#L101-L102

```lean
class inductive Finite (α : Sort*) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite _
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean

SHA256 `047d0f370cc830214b8dba702ec49434af0072523561404e40a314d2a5f24b98`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Set.Countable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L49-L49

```lean
protected def Countable (s : Set α) : Prop := Countable s
```

### finite_set_countable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L256-L257

```lean
theorem Finite.countable {s : Set α} (hs : s.Finite) : s.Countable :=
  have := hs.to_subtype; s.to_countable
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean

SHA256 `d42047c8b18f28b7eba8ceca5867e472fcb8e840ac3499f88d3cd1d01451bb9f`

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

### Countable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean#L41-L43

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

SHA256 `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

### IsCompact

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L290-L291

```lean
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

### CompactSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L297-L299

```lean
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean

SHA256 `427d7eff3bd67d3b8a3ba2df3636786b248405f789871161145d274f929d466e`

```lean
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
```

### Bornology.IsBounded

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L95-L100

```lean
def IsCobounded [Bornology α] (s : Set α) : Prop :=
  s ∈ cobounded α

/-- `IsBounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
def IsBounded [Bornology α] (s : Set α) : Prop :=
  IsCobounded sᶜ
```

### actual_bornology_class

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L51-L55

```lean
class Bornology (α : Type*) where
  /-- The filter of cobounded sets in a bornology. -/
  cobounded (α) : Filter α
  /-- The cobounded filter in a bornology is smaller than the cofinite filter. -/
  le_cofinite (α) : cobounded ≤ cofinite
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/ProjIcc.lean

SHA256 `7a5abf799ed82bdb55b690f4eb334e47747a71265d17da0755095f0269eca386`

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
```

### Set.projIcc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/ProjIcc.lean#L48-L49

```lean
def projIcc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩
```

### interval_projection_value

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/ProjIcc.lean#L60-L60

```lean
theorem coe_projIcc (a b : α) (h : a ≤ b) (x : α) : (projIcc a b h x : α) = max a (min b x) := rfl
```

### interval_projection_tails

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/ProjIcc.lean#L66-L70

```lean
theorem projIcc_of_le_left (hx : x ≤ a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, hx.trans h]

theorem projIcc_of_right_le (hx : b ≤ x) : projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, h]
```

### interval_projection_interior

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/ProjIcc.lean#L102-L103

```lean
theorem projIcc_of_mem (hx : x ∈ Icc a b) : projIcc a b h x = ⟨x, hx⟩ := by
  simp [projIcc, hx.1, hx.2]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Lipschitz.lean

SHA256 `abdafde82be94189e4779892c3cb06e3b1afa387167f0d9292680ee66d2ed0c2`

```lean
/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
```

### real_lipschitz_distance_contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Lipschitz.lean#L45-L50

```lean
theorem lipschitzWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} : LipschitzWith K f ↔ ∀ x y, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean

SHA256 `3fc7ffe7db4db0a2de07d6fdf0e65da486b3dced1f3bac4d58ab869a92f4ac64`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

### compact_continuous_range

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L969-L970

```lean
theorem isCompact_range [CompactSpace X] {f : X → Y} (hf : Continuous f) : IsCompact (range f) := by
  rw [← image_univ]; exact isCompact_univ.image hf
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Real.lean

SHA256 `e3106d477af53038e6eacf5da730df7a09c57f786ef88eb5e15655aa0016d625`

```lean
/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
```

### real_circle_compactness

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Instances/AddCircle/Real.lean#L33-L35

```lean
instance compactSpace [Fact (0 < p)] : CompactSpace <| AddCircle p := by
  rw [← isCompact_univ_iff, ← coe_image_Icc_eq p 0]
  exact isCompact_Icc.image (AddCircle.continuous_mk' p)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean

SHA256 `dbdb5dce531767c8e6b56f004d9d3a4cde9173a5a11ef40733a86cb432cadd2b`

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

### compact_metric_bounded

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L192-L194

```lean
theorem _root_.IsCompact.isBounded {s : Set α} (h : IsCompact s) : IsBounded s :=
  -- A compact set is totally bounded, thus bounded
  h.totallyBounded.isBounded
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Group/Bounded.lean

SHA256 `5e93b1cc169d5d5a4c0f7361ef09b0b481c881d3f32b0067deb6c62d90c3ed78`

```lean
/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
```

### norm_bound_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Group/Bounded.lean#L71-L77

```lean
@[to_additive isBounded_iff_forall_norm_le]
lemma isBounded_iff_forall_norm_le' : Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C := by
  simpa only [Set.subset_def, mem_closedBall_one_iff] using isBounded_iff_subset_closedBall (1 : E)

alias ⟨Bornology.IsBounded.exists_norm_le', _⟩ := isBounded_iff_forall_norm_le'

alias ⟨Bornology.IsBounded.exists_norm_le, _⟩ := isBounded_iff_forall_norm_le
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean

SHA256 `5fef7d93549afbdd095b2fef6d042c236fd2a581dbb46c2d5326757e479e3efd`

```lean
/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
```

### derivative_measurability

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L400-L402

```lean
theorem measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] (f : 𝕜 → F) : Measurable (deriv f) := by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const 𝕜 f 1
```

### derivative_strong_measurability

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L404-L410

```lean
theorem stronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [h : SecondCountableTopologyEither 𝕜 F] (f : 𝕜 → F) : StronglyMeasurable (deriv f) := by
  borelize F
  rcases h.out with h𝕜 | hF
  · exact stronglyMeasurable_iff_measurable_separable.2
      ⟨measurable_deriv f, isSeparable_range_deriv _⟩
  · exact (measurable_deriv f).stronglyMeasurable
```

### derivative_ae_measurability

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L416-L419

```lean
theorem aestronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [SecondCountableTopologyEither 𝕜 F] (f : 𝕜 → F) (μ : Measure 𝕜) :
    AEStronglyMeasurable (deriv f) μ :=
  (stronglyMeasurable_deriv f).aestronglyMeasurable
```

### measurable_actual_derivative

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L409-L419

```lean
      ⟨measurable_deriv f, isSeparable_range_deriv _⟩
  · exact (measurable_deriv f).stronglyMeasurable

theorem aemeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] (f : 𝕜 → F) (μ : Measure 𝕜) : AEMeasurable (deriv f) μ :=
  (measurable_deriv f).aemeasurable

theorem aestronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [SecondCountableTopologyEither 𝕜 F] (f : 𝕜 → F) (μ : Measure 𝕜) :
    AEStronglyMeasurable (deriv f) μ :=
  (stronglyMeasurable_deriv f).aestronglyMeasurable
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean

SHA256 `7801deae1fa630bca3f1966f17b9005e0e9dfc86be62f7abd14e88bece1a26cc`

```lean
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

### FTC_off_countable_complete_proof

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean#L373-L398

```lean
theorem integral_eq_of_hasDerivAt_off_countable_of_le [CompleteSpace E] (f f' : ℝ → E)
    {a b : ℝ} (hle : a ≤ b) {s : Set ℝ} (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ Ioo a b \ s, HasDerivAt f (f' x) x) (Hi : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a := by
  set e : ℝ ≃L[ℝ] ℝ¹ := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  set F' : ℝ → ℝ →L[ℝ] E := fun x => smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  calc
    ∫ x in a..b, f' x = ∫ x in Icc a b, f' x := by
      rw [intervalIntegral.integral_of_le hle, setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∑ i : Fin 1,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e a i) x)) := by
      simp only [← interior_Icc] at Hd
      refine
        integral_divergence_of_hasFDerivAt_off_countable_of_equiv e ?_ ?_ (fun _ => f)
          (fun _ => F') s hs a b hle (fun _ => Hc) (fun x hx _ => Hd x hx) _ ?_ ?_
      · exact fun x y => (OrderIso.funUnique (Fin 1) ℝ).symm.le_iff_le
      · exact (volume_preserving_funUnique (Fin 1) ℝ).symm _
      · simp [F', e]
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at Hi
        exact Hi.congr_set_ae Ioc_ae_eq_Icc.symm
    _ = f b - f a := by
      simp [e, Subsingleton.elim (const (Fin 0) _) isEmptyElim, volume_pi,
        Measure.pi_of_empty fun _ : Fin 0 ↦ _]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean

SHA256 `e70ff0aea2f3cdc2a4aa519c999679132a3a0c3e79b1447e09a03af1c36fdc9d`

```lean
/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
```

### AbsolutelyContinuousOnInterval

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L154-L156

```lean
def _root_.AbsolutelyContinuousOnInterval (f : ℝ → X) (a b : ℝ) :=
  Tendsto (fun E ↦ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)
```

### AbsolutelyContinuousOnInterval.totalLengthFilter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L78-L79

```lean
def totalLengthFilter : Filter (ℕ × (ℕ → X × X)) := Filter.comap
  (fun E ↦ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝 0)
```

### AbsolutelyContinuousOnInterval.disjWithin

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L95-L97

```lean
def disjWithin (a b : ℝ) := {E : ℕ × (ℕ → ℝ × ℝ) |
  (∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i ↦ uIoc (E.2 i).1 (E.2 i).2)}
```

### AC_epsilon_delta_equivalence

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L163-L170

```lean
theorem _root_.absolutelyContinuousOnInterval_iff (f : ℝ → X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ disjWithin a b →
    ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
    ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))]
```

### AC_lipschitz_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L309-L324

```lean
theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval {f : ℝ → X} {K : ℝ≥0}
    (hfK : LipschitzOnWith K f (uIcc a b)) : AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun (n, I) hnI₁ hnI₂ ↦ ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have := hfK (hnI₁.left i hi).left (hnI₁.left i hi).right
      apply ENNReal.toReal_mono (Ne.symm (not_eq_of_beq_eq_false rfl)) at this
      rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at this
    _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by symm; exact Finset.mul_sum _ _ _
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field
```

### AC_ae_differentiability

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L442-L446

```lean
/-- If `f` is absolute continuous on `uIcc a b`, then `f'` exists a.e. on `uIcc a b`. -/
theorem ae_differentiableAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ uIcc a b → DifferentiableAt ℝ f x :=
  hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
```

### finite_disjoint_interval_AC_contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L158-L170

```lean
/-- The traditional `ε`-`δ` definition of absolutely continuous: A function `f` is
*absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such that for
any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where `a i`, `b i` are
all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`. -/
theorem _root_.absolutelyContinuousOnInterval_iff (f : ℝ → X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ disjWithin a b →
    ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
    ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))]
```

### AC_congruence_contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L184-L189

```lean
theorem congr (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : Set.EqOn f g (uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  apply hf.congr'
  rw [eventuallyEq_inf_principal_iff]
  filter_upwards with (n, I) hnI
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hfg (hnI.1 i hi).1, hfg (hnI.1 i hi).2]
```

### Lipschitz_composition_AC_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean#L328-L348

```lean
theorem _root_.LipschitzOnWith.comp_absolutelyContinuousOnInterval
    {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} {t : Set X}
    (hf : LipschitzOnWith K f t) {g : ℝ → X} {a b : ℝ} (hg : MapsTo g (uIcc a b) t)
    (h : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  apply squeeze_zero' ?_ ?_ (by simpa using Tendsto.const_mul (K : ℝ) h)
  · exact .of_forall fun _ ↦ by positivity
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦
    hf.dist_le_mul _ (hg (hnI.left i hi).left) _ (hg (hnI.left i hi).right)

/-- If `f` is Lipschitz and `g` is absolutely continuous on `uIcc a b`, then `f ∘ g` is absolutely
continuous on `uIcc a b`. -/
theorem _root_.LipschitzWith.comp_absolutelyContinuousOnInterval
    {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f)
    {g : ℝ → X} {a b : ℝ} (h : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b :=
  hf.lipschitzOnWith.comp_absolutelyContinuousOnInterval (mapsTo_univ _ _) h

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/OuterMeasure/AE.lean

SHA256 `de58d3b2aa42d801e9a268df285c32e5aa6ca7ffc5b42bf5eff8f12bda87a00d`

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
```

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

SHA256 `d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

### Filter.Eventually

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L281-L282

```lean
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/UnorderedInterval.lean

SHA256 `845a280c85d7c3e2fb9796ca1c0df9f7b6ad9174dba3fad74b5e8c26001bd9a8`

```lean
/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
```

### Set.uIcc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/UnorderedInterval.lean#L60-L60

```lean
def uIcc (a b : α) : Set α := Icc (a ⊓ b) (a ⊔ b)
```

### Set.uIoc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/UnorderedInterval.lean#L243-L243

```lean
def uIoc : α → α → Set α := fun a b => Ioc (min a b) (max a b)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean

SHA256 `3fb58136643c88bd7bf3dfd55eb22bc46237f995799ea7dbfafeda49d523b572`

```lean
/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
```

### AC_derivative_integrability

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean#L159-L163

```lean
/-- If `f` is absolutely continuous on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem AbsolutelyContinuousOnInterval.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.boundedVariationOn.intervalIntegrable_deriv
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean

SHA256 `65f3d7028d8d7c1b36830a2a0a3002acbd4cc59deac2aaba986a6e3e3db5a630`

```lean
/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
```

### AC_genuine_FTC

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean#L223-L242

```lean
/-- *Fundamental Theorem of Calculus* for absolutely continuous functions: if `f` is absolutely
continuous on `uIcc a b`, then `∫ (x : ℝ) in a..b, deriv f x = f b - f a`. -/
theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ (x : ℝ) in a..b, deriv f x = f b - f a := by
  have f_deriv_integral_ac :=
    hf.intervalIntegrable_deriv.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp)
  let g (x : ℝ) := f x - ∫ (t : ℝ) in a..x, deriv f t
  have g_ac : AbsolutelyContinuousOnInterval g a b := hf.sub (f_deriv_integral_ac)
  have g_ae_deriv_zero : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g 0 x := by
    filter_upwards [hf.ae_differentiableAt, hf.intervalIntegrable_deriv.ae_hasDerivAt_integral]
      with x hx₁ hx₂ hx₃
    convert! (hx₁ hx₃).hasDerivAt.sub (hx₂ hx₃ a (by simp))
    abel
  obtain ⟨C, hC⟩ := g_ac.const_of_ae_hasDerivAt_zero g_ae_deriv_zero
  have : f a = g a := by simp [g]
  have := hC a (by simp)
  have := hC b (by simp)
  grind
```

### AC_constancy_from_ae_zero_derivative

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean#L166-L221

```lean

/-- If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc a b`, then `f`
is constant on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero {f : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hf₀ : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f 0 x) :
    ∃ C, ∀ x ∈ uIcc a b, f x = C := by
  -- Proof idea : Assume wlog `a < b`. We need to show that `f d = f b` for any `d ∈ [a, b]`.
  -- Fix `d`. It suffices to show that `dist (f d) (f b) ≤ r` for any `r > 0`. Fix `r`.
  -- Use `exists_dist_slope_lt_pairwiseDisjoint_hasSum` with `η = r / (b - d)` to
  -- get a cover of `[d, b]` consisting of closed subintervals with total length `b - d` such that
  -- the slope of `f` on each subinterval has absolute value `≤ η`. The sum of `dist (f x) (f y)`
  -- for `[x, y]` in the cover must therefore be `≤ (b - d) * η = r`. Use
  -- `AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum` to conclude that
  -- `dist (f d) (f b) ≤ r`.
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ this (a := b) (b := a) hf.symm (uIcc_comm a b ▸ hf₀) (by linarith)
  suffices ∀ x ∈ uIcc a b, f x = f b by use f b
  rw [uIcc_of_le hab] at hf₀ ⊢
  intro d hd
  suffices ∀ r > 0, dist (f d) (f b) ≤ r by
    contrapose! this
    exact exists_between (dist_pos.mpr this)
  intro r hr
  rw [mem_Icc] at hd
  have had : a ≤ d := by linarith
  rcases hd.right.eq_or_lt with rfl | hdb
  · simp [hr.le]
  replace hf₀ : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f 0 x := by
    filter_upwards [hf₀] with x _ _ using by grind
  have hfdb' : 0 < r / (b - d) := by apply div_pos <;> linarith
  have ⟨u, hu₁, hu₂, hu₃⟩ :=
    exists_dist_slope_lt_pairwiseDisjoint_hasSum hd.right hf₀ hfdb'
  let g := fun (z : u) ↦ dist (f z.val.1) (f z.val.2)
  have g_nonneg : 0 ≤ g := by intro; simp [g]
  have g_finsum_bound (s : Finset u) : ∑ z ∈ s, g z ≤ r := by
    have (z : u) (hz : z ∈ s) : g z ≤ r / (b - d) * (z.val.2 - z.val.1) := by
      have slope_bound := hu₁ z (by simp) |>.right |>.le
      have : 0 < z.val.2 - z.val.1 := by linarith [hu₁ z (by simp)]
      grw [← slope_bound]
      simp only [dist_eq_norm, slope, vsub_eq_sub, sub_zero, g, mul_comm]
      nth_rw 1 [← Real.norm_of_nonneg this.le]
      simp only [norm_smul, Real.norm_eq_abs, norm_inv]
      field_simp
      rw [norm_sub_rev]
    grw [Finset.sum_le_sum this]
    rw [← Finset.mul_sum]
    have : ∑ z ∈ s, (z.val.2 - z.val.1) ≤ b - d :=
      hu₃.tsum_eq ▸ Summable.sum_le_tsum _ (by grind) hu₃.summable
    grw [this]
    field_simp
    grind
  have hu₄ := summable_of_sum_le g_nonneg g_finsum_bound |>.hasSum
  have g_sum_bound := Real.tsum_le_of_sum_le g_nonneg g_finsum_bound
  have := (hf.mono (by grind [uIcc_of_le])).dist_le_of_pairwiseDisjoint_hasSum hd.right
    (fun s hs ↦ hu₁ s hs |>.left) hu₂ hu₃ hu₄
  linarith
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean

SHA256 `53970116254a7e705eb85f92c9236be431966dbd61c1c1315a914a6d05e39b7b`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Set.Ioo

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L50-L51

```lean
@[to_dual self (reorder := a b)]
def Ioo (a b : α) := { x | a < x ∧ x < b }
```

### Set.Ioc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L62-L63

```lean
@[to_dual existing (reorder := a b)]
def Ioc (a b : α) := { x | a < x ∧ x ≤ b }
```

### Set.Icc

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L75-L76

```lean
@[to_dual self (reorder := a b)]
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Interval.lean

SHA256 `5e6aaccb81e007169bb3095781731808b1d5cbed0ecf0b637e85adedc33f0c08`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### closed_halfopen_interval_ae_equality

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Interval.lean#L81-L88

```lean
theorem Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter .rfl

theorem Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
  (Ioi_ae_eq_Ici' ha).inter .rfl

theorem Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Circle.lean

SHA256 `9e86cf381c989d2f768d771973cfca8c606a91f4b1d56b522d2b49db0f54e086`

```lean
/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
```

### Circle

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Circle.lean#L51-L55

```lean

/-- The unit circle in `ℂ`. -/
@[wikidata Q203425]
def Circle : Type := Submonoid.unitSphere ℂ
deriving TopologicalSpace
```

### Circle.exp

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Circle.lean#L120-L127

```lean
/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def exp : C(ℝ, Circle) where
  toFun t := ⟨(t * I).exp, by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I]⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop)
    (by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I])

@[simp, norm_cast]
theorem coe_exp (t : ℝ) : exp t = Complex.exp (t * Complex.I) := rfl
```

### unit_circle_coercion_norm

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Circle.lean#L58-L78

```lean
variable {x y : Circle}

instance instCoeOut : CoeOut Circle ℂ := subtypeCoe

instance instCommGroup : CommGroup Circle := inferInstanceAs <| CommGroup (sphere _ _)
instance : HasDistribNeg Circle := inferInstanceAs <| HasDistribNeg (sphere _ _)
instance : ContinuousNeg Circle := inferInstanceAs <| ContinuousNeg (sphere _ _)
instance instMetricSpace : MetricSpace Circle := inferInstanceAs <| MetricSpace (sphere _ _)

@[ext] lemma ext : (x : ℂ) = y → x = y := Subtype.ext

lemma coe_injective : Injective ((↑) : Circle → ℂ) := fun _ _ ↦ ext

-- Not simp because `SetLike.coe_eq_coe` already proves it
lemma coe_inj : (x : ℂ) = y ↔ x = y := coe_injective.eq_iff

@[simp] lemma norm_coe (z : Circle) : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.1 z.2
@[simp] lemma nnnorm_coe (z : Circle) : ‖(z : ℂ)‖₊ = 1 := NNReal.coe_injective z.norm_coe
@[simp] lemma enorm_coe (z : Circle) : ‖(z : ℂ)‖ₑ = 1 := by simp [enorm_eq_nnnorm]

@[simp] lemma normSq_coe (z : Circle) : normSq z = 1 := by simp [normSq_eq_norm_sq]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Field/UnitBall.lean

SHA256 `a672f0dd0e7fe37dbea5ef2b33e36c454e6f945314660066e3bc20af50a6e0d4`

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
```

### Submonoid.unitSphere

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Field/UnitBall.lean#L183-L192

```lean
/-- Unit sphere in a seminormed ring (with strictly multiplicative norm) as a bundled
`Submonoid`. -/
@[simps]
def Submonoid.unitSphere (𝕜 : Type*) [SeminormedRing 𝕜] [NormMulClass 𝕜] [NormOneClass 𝕜] :
    Submonoid 𝕜 where
  carrier := sphere (0 : 𝕜) 1
  mul_mem' hx hy := by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

SHA256 `13cd9bc80e44bf7b61a55b5b1c2993058ac995f8803a6fb58c230c23a1d0fa35`

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

### Metric.sphere

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L431-L432

```lean
/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere (x : α) (ε : ℝ) := { y | dist y x = ε }
```

### metric_uniform_continuity_contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L762-L765

```lean
theorem uniformContinuousOn_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, dist x y < δ → dist (f x) (f y) < ε :=
  uniformity_basis_dist.uniformContinuousOn_iff uniformity_basis_dist
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean

SHA256 `d63cf63b6eea1b5fe73a314d61f18056d7b3fcaa419b298a28e6a8ebc614214a`

```lean
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

### AddCircle.toCircle

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L377-L384

```lean

/-- The canonical map `fun x => exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circle in `ℂ`.
If `T = 0` we understand this as the constant function 1. -/
noncomputable def toCircle : AddCircle T → Circle :=
  (@scaled_exp_map_periodic T).lift

theorem toCircle_apply_mk (x : ℝ) : @toCircle T x = Circle.exp (2 * π / T * x) :=
  rfl
```

### canonical_scaled_period_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L371-L376

```lean

theorem scaled_exp_map_periodic : Function.Periodic (fun x => Circle.exp (2 * π / T * x)) T := by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · simp
  · intro x; simp_rw [mul_add]; rw [div_mul_cancel₀ _ hT, Circle.periodic_exp]
```

### canonical_map_continuity_injectivity

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L405-L418

```lean
@[fun_prop, continuity]
theorem continuous_toCircle : Continuous (@toCircle T) :=
  continuous_coinduced_dom.mpr (Circle.exp.continuous.comp <| by fun_prop)

theorem injective_toCircle (hT : T ≠ 0) : Function.Injective (@toCircle T) := by
  intro a b h
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  simp_rw [toCircle_apply_mk] at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h.symm
  rw [QuotientAddGroup.eq]; simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp at hm
  linarith
```

### circle_exponential_period

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L71-L82

```lean
lemma surjOn_exp_neg_pi_pi : SurjOn exp (Ioc (-π) π) univ := argPartialEquiv.symm.surjOn

set_option backward.isDefEq.respectTransparency false in
lemma exp_eq_exp {x y : ℝ} : exp x = exp y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff, coe_exp, coe_exp, exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero]
  norm_cast

lemma periodic_exp : Periodic exp (2 * π) := fun z ↦ exp_eq_exp.2 ⟨1, by rw [Int.cast_one, one_mul]⟩

@[simp] lemma exp_two_pi : exp (2 * π) = 1 := periodic_exp.eq.trans exp_zero
```

### AddCircle.homeomorphCircle'

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L421-L430

```lean
@[simps] noncomputable def homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle where
  toFun := Angle.toCircle
  invFun := fun x ↦ arg x
  left_inv := Angle.arg_toCircle
  right_inv := Circle.exp_arg
  continuous_toFun := continuous_coinduced_dom.mpr Circle.exp.continuous
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_arg_coe_angle x.coe_ne_zero).comp continuousAt_subtype_val
```

### AddCircle.homeomorphCircle

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L435-L436

```lean
noncomputable def homeomorphCircle (hT : T ≠ 0) : AddCircle T ≃ₜ Circle :=
  (homeomorphAddCircle T (2 * π) hT (by positivity)).trans homeomorphCircle'
```

### actual_circle_homeomorphism_formula

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L438-L443

```lean
theorem homeomorphCircle_apply (hT : T ≠ 0) (x : AddCircle T) :
    homeomorphCircle hT x = toCircle x := by
  cases x using QuotientAddGroup.induction_on
  rw [homeomorphCircle, Homeomorph.trans_apply,
    homeomorphAddCircle_apply_mk, homeomorphCircle'_apply_mk, toCircle_apply_mk]
  ring_nf
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean

SHA256 `744eb1d57d32044612ab388aa45e69fae15c87f84bb966c909d2c5cf55d03115`

```lean
/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
```

### Complex

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean#L32-L40

```lean

/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
@[wikidata Q11567]
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ

```

### Complex.ofReal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean#L82-L86

```lean
@[coe, instance_reducible]
def ofReal (r : ℝ) : ℂ :=
  ⟨r, 0⟩
instance : Coe ℝ ℂ :=
  ⟨ofReal⟩
```

### Complex.I

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean#L239-L241

```lean
/-- The imaginary unit. -/
def I : ℂ :=
  ⟨0, 1⟩
```

### Complex.normSq

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean#L506-L517

```lean
/-- The norm squared function. -/
@[pp_nodot]
def normSq : ℂ →*₀ ℝ where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    simp only [mul_re, mul_im]
    ring

theorem normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl
```

### Complex.star_def

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean#L499-L501

```lean
@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl
```

### complex_star_instance

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Complex/Basic.lean#L453-L471

```lean
/-! ### Complex conjugation -/


/-- This defines the complex conjugate as the `star` operation of the `StarRing ℂ`. It
is recommended to use the ring endomorphism version `starRingEnd`, available under the
notation `conj` in the scope `ComplexConjugate`. -/
instance : StarRing ℂ where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]
theorem conj_re (z : ℂ) : (conj z).re = z.re :=
  rfl

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Norm.lean

SHA256 `7f719d7b3ba3ba8b4667a8f79e7efd5d8fb4da2b82dcca011e64129113a63eba`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

### Complex.instNorm

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Norm.lean#L26-L34

```lean

@[no_expose]
instance instNorm : Norm ℂ where
  norm z := √(normSq z)

theorem norm_def (z : ℂ) : ‖z‖ = √(normSq z) := (rfl)

theorem norm_mul_self_eq_normSq (z : ℂ) : ‖z‖ * ‖z‖ = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)
```

### complex_norm_of_real

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Norm.lean#L102-L107

```lean
@[simp] lemma nnnorm_I : ‖I‖₊ = 1 := by simp [nnnorm]

@[simp 1100, norm_cast]
lemma norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := by
  simp [norm_def, Real.sqrt_mul_self_eq_abs]

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Star/Basic.lean

SHA256 `4ce946e9ba0306d69fdafda4b218702fc69f9bd0abca2e35eb194ee0a2f387f0`

```lean
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
```

### starRingEnd

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Star/Basic.lean#L335-L348

```lean
/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the scope `ComplexConjugate`.

Note that this is the preferred form (over `starRingAut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[starRingEnd R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑starRingAut : R →* R)`. -/
@[implicit_reducible]
def starRingEnd : R →+* R where
  toFun := star
  __ := (@starRingAut R _ _).toRingHom

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean

SHA256 `581fefd0139417fa56ef95b54103e415ae252d9d120f9da1cfe8039ff3d46bff`

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
```

### Complex.exp

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean#L60-L63

```lean
/-- The complex exponential function, defined via its Taylor series -/
@[pp_nodot]
irreducible_def exp (z : ℂ) : ℂ :=
  CauSeq.lim (exp' z)
```

### Complex.exp'

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean#L54-L59

```lean
/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot]
def exp' (z : ℂ) : CauSeq ℂ (‖·‖) :=
  ⟨fun n => ∑ m ∈ range n, z ^ m / m.factorial, isCauSeq_exp z⟩

```

### complex_exponential_Taylor_convergence

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean#L35-L53

```lean
namespace Complex

theorem isCauSeq_norm_exp (z : ℂ) :
    IsCauSeq abs fun n => ∑ m ∈ range n, ‖z ^ m / m.factorial‖ :=
  let ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (norm_nonneg _) hn
  IsCauSeq.series_ratio_test n (‖z‖ / n) (div_nonneg (norm_nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_norm, abs_norm, Nat.factorial_succ, pow_succ', mul_comm m.succ, Nat.cast_mul,
        ← div_div, mul_div_assoc, mul_div_right_comm, Complex.norm_mul, Complex.norm_div,
        norm_natCast]
      gcongr
      exact le_trans hm (Nat.le_succ _)

noncomputable section

theorem isCauSeq_exp (z : ℂ) : IsCauSeq (‖·‖) fun n => ∑ m ∈ range n, z ^ m / m.factorial :=
  (isCauSeq_norm_exp z).of_abv

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean

SHA256 `c8933a580347acc3ee7cf731a9034cff1d6e818be36d9323876d1f12a7b25ee4`

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
```

### Real.pi

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean#L124-L129

```lean
see `Mathlib/Analysis/Real/Pi/Bounds.lean`.

Denoted `π`, once the `Real` namespace is opened. -/
@[wikidata Q167]
protected noncomputable def pi : ℝ :=
  2 * Classical.choose exists_cos_eq_zero
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean

SHA256 `f4e96c735ead60a8983bcf8eb6e38dfd05d8102c3f741094f73639858605bb6a`

```lean
/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
```

### Real.sqrt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L112-L113

```lean
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
```

### NNReal.sqrt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L46-L47

```lean
noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
  OrderIso.symm <| powOrderIso 2 two_ne_zero
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean

SHA256 `ce7d6a512c82ac79452e80ef3ce19de86a55ee0976ba5a2abd0aa889cab9894c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### MeasureTheory.NullSingletonClass

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean#L30-L32

```lean
/-- Measure `μ` has value zero on singletons. -/
class NullSingletonClass {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_singleton : ∀ x, μ {x} = 0
```

### open_halfopen_interval_ae

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean#L111-L115

```lean
theorem Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
  Ioi_ae_eq_Ici' (measure_singleton a)

theorem Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
  Ioo_ae_eq_Ioc' (measure_singleton b)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean

SHA256 `b319b64a0eca5685d88d313b70eb5588d1708112101e4625f72aec199e43624f`

```lean
/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Fabrizio Barroero, Christopher Hoskin
-/
```

### circleMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean#L31-L43

```lean
/-- The exponential map $θ ↦ c + R e^{θi}$. The range of this map is the circle in `ℂ` with center
`c` and radius `|R|`. -/
def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)

@[simp]
theorem circleMap_sub_center (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ - c = circleMap 0 R θ := by
  simp [circleMap]

theorem circleMap_zero (R θ : ℝ) : circleMap 0 R θ = R * exp (θ * I) := zero_add _

@[simp]
theorem norm_circleMap_zero (R : ℝ) (θ : ℝ) : ‖circleMap 0 R θ‖ = |R| := by simp [circleMap]

```

### circle_map_literal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean#L31-L43

```lean
/-- The exponential map $θ ↦ c + R e^{θi}$. The range of this map is the circle in `ℂ` with center
`c` and radius `|R|`. -/
def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)

@[simp]
theorem circleMap_sub_center (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ - c = circleMap 0 R θ := by
  simp [circleMap]

theorem circleMap_zero (R θ : ℝ) : circleMap 0 R θ = R * exp (θ * I) := zero_add _

@[simp]
theorem norm_circleMap_zero (R : ℝ) (θ : ℝ) : ‖circleMap 0 R θ‖ = |R| := by simp [circleMap]

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/CircleIntegral.lean

SHA256 `5cc119be08835972728856dbf40aef4a614c5eabd775ec2d66bbe758816557ce`

```lean
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

### circle_map_actual_derivative

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Integral/CircleIntegral.lean#L98-L102

```lean
theorem hasDerivAt_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) :
    HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ := by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using! (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : ℂ)).const_add c

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Comp.lean

SHA256 `16a41715830ec582c91cb5262e2defab08052d7e749bb91ee059905c0b0e1847`

```lean
/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Yuyang Zhao
-/
```

### real_scalar_chain_rule

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/Deriv/Comp.lean#L99-L102

```lean
/-- The chain rule. -/
theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  HasDerivAtFilter.scomp hg hh <| hh.continuousAt.tendsto.prodMap <| tendsto_pure_pure _ _
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean

SHA256 `d73b5159fee4d0c7ed3f7ff31ffd091f13cfbaf0e0006cba696bb2413a16b597`

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
```

### complex_exponential_actual_derivative

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean#L88-L96

```lean
/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
theorem hasDerivAt_exp (x : ℂ) : HasDerivAt exp (exp x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have : (1 : ℕ) < 2 := by simp
  refine (IsBigO.of_bound ‖exp x‖ ?_).trans_isLittleO (isLittleO_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => exp_bound_sq x z hz.le

```

### complex_exponential_chain_rule

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean#L135-L137

```lean
theorem HasDerivAt.cexp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasDerivAt_exp (f x)).comp x hf
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/RealDeriv.lean

SHA256 `a9ca5646135c0b940b16184412c0d5cb16e6cfc7b455a534e3794ac30be27097`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yourong Zang
-/
```

### complex_real_embedding_derivative

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/RealDeriv.lean#L95-L105

```lean
/-- If a complex function `e` is differentiable at a real point, then its restriction to `ℝ` is
differentiable there as a function `ℝ → ℂ`, with the same derivative. -/
theorem HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : ℝ => e ↑y) e' z := by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using! hf.comp z ofRealCLM.hasDerivAt

/-- If a function `f : ℝ → ℝ` is differentiable at a (real) point `x`, then it is also
differentiable as a function `ℝ → ℂ`. -/
theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using!
    ofRealCLM.hasDerivAt.scomp z hf
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Basic.lean

SHA256 `36c55b3cf65b410972ed631abef1cb74c397327c8ccb30952dc5941c59c0d930`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

### conjugate_norm_square

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Basic.lean#L355-L357

```lean
-- TODO: Replace `mul_conj` and `conj_mul` once `norm` has replaced `abs`
lemma mul_conj' (z : ℂ) : z * conj z = ‖z‖ ^ 2 := RCLike.mul_conj z
lemma conj_mul' (z : ℂ) : conj z * z = ‖z‖ ^ 2 := RCLike.conj_mul z
```

### complex_real_embedding_CLM

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Basic.lean#L316-L322

```lean
/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealCLM : ℝ →L[ℝ] ℂ :=
  ofRealLI.toContinuousLinearMap

@[simp]
theorem ofRealCLM_coe : (ofRealCLM : ℝ →ₗ[ℝ] ℂ) = ofRealAm.toLinearMap :=
  rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean

SHA256 `0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

### UniformContinuous

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L633-L634

```lean
def UniformContinuous (f : α → β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)
```

### UniformContinuousOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L644-L645

```lean
def UniformContinuousOn (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean

SHA256 `4d27914014d20e4b9a6af97ebd7e7bea7451cc37a96dbd102b6d21c9a3f0eb72`

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

### Homeomorph

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L43-L50

```lean
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
```

### Homeomorph.symm

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L79-L82

```lean
protected def symm (h : X ≃ₜ Y) : Y ≃ₜ X where
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm
```

### Homeomorph.trans

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L114-L117

```lean
protected def trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) : X ≃ₜ Z where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
```

### actual_homeomorphism_inverse_laws

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L145-L151

```lean
@[simp]
theorem apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/HeineCantor.lean

SHA256 `bfb79da59c3164cc81af57221eaeb6c9abd25bb635e97ee810f2a1bac58f36c0`

```lean
/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
```

### compact_real_lift_uniformity_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/HeineCantor.lean#L49-L54

```lean
theorem IsCompact.uniformContinuousOn_of_continuous {s : Set α} {f : α → β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact CompactSpace.uniformContinuous_of_continuous hf
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Trigonometric.lean

SHA256 `b63dc0d49ca3deb88ffb47292745448b2611bf2d43b4ea05931628f8aa286b3b`

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
```

### actual_complex_chord_formula

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Trigonometric.lean#L973-L981

```lean
theorem norm_exp_I_mul_ofReal_sub_one (x : ℝ) : ‖exp (I * x) - 1‖ = ‖2 * Real.sin (x / 2)‖ := by
  rw [show ‖2 * Real.sin (x / 2)‖ = ‖2 * sin (x / 2)‖ by norm_cast, two_sin]
  nth_rw 2 [← one_mul (_ - _), ← exp_zero]
  rw [← neg_add_cancel (x / 2 * I), exp_add, mul_assoc _ _ (_ - _), mul_sub, ← exp_add, ← exp_add,
    ← add_mul, ← add_mul]; norm_cast
  rw [add_neg_cancel, ofReal_zero, zero_mul, exp_zero, add_halves, ← neg_mul, Complex.norm_mul,
    norm_I, mul_one, Complex.norm_mul,
    show -(ofReal (x / 2)) = ofReal (-x / 2) by norm_cast; exact neg_div' 2 x,
    norm_exp_ofReal_mul_I, one_mul, ← norm_neg, neg_sub, mul_comm]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean

SHA256 `6d0415d3eea2e529909a2f786ab3bf99d6082f63e50377c7d807667fbc3dd67a`

```lean
/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Yaël Dillies, Bhavik Mehta
-/
```

### jordan_and_global_sine_bounds

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean#L37-L117

```lean
open Set

namespace Real
variable {x : ℝ}

/-- For 0 < x, we have sin x < x. -/
theorem sin_lt (h : 0 < x) : sin x < x := by
  rcases lt_or_ge 1 x with h' | h'
  · exact (sin_le_one x).trans_lt h'
  have hx : |x| = x := abs_of_nonneg h.le
  have := le_of_abs_le (sin_bound <| show |x| ≤ 1 by rwa [hx])
  rw [sub_le_iff_le_add', hx] at this
  apply this.trans_lt
  rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
  refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
  apply pow_le_pow_of_le_one h.le h'
  simp

lemma sin_le (hx : 0 ≤ x) : sin x ≤ x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (sin_lt hx).le

lemma lt_sin (hx : x < 0) : x < sin x := by simpa using sin_lt <| neg_pos.2 hx
lemma le_sin (hx : x ≤ 0) : x ≤ sin x := by simpa using sin_le <| neg_nonneg.2 hx

theorem lt_sin_mul {x : ℝ} (hx : 0 < x) (hx' : x < 1) : x < sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩ ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
      pi_div_two_pos.ne (sub_pos.2 hx') hx

theorem le_sin_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : x ≤ sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, pi_pos.le⟩
      ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx

theorem mul_lt_sin {x : ℝ} (hx : 0 < x) (hx' : x < π / 2) : 2 / π * x < sin x := by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @lt_sin_mul ((π / 2)⁻¹ * x)
    (mul_pos (inv_pos.2 pi_div_two_pos) hx) (by rwa [← div_eq_inv_mul, div_lt_one pi_div_two_pos])

/-- One half of **Jordan's inequality**.

In the range `[0, π / 2]`, we have a linear lower bound on `sin`. The other half is given by
`Real.sin_le`.
-/
theorem mul_le_sin {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) : 2 / π * x ≤ sin x := by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @le_sin_mul ((π / 2)⁻¹ * x)
    (mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx)
    (by rwa [← div_eq_inv_mul, div_le_one pi_div_two_pos])

/-- Half of **Jordan's inequality** for negative values. -/
lemma sin_le_mul (hx : -(π / 2) ≤ x) (hx₀ : x ≤ 0) : sin x ≤ 2 / π * x := by
  simpa using mul_le_sin (neg_nonneg.2 hx₀) (neg_le.2 hx)

/-- Half of **Jordan's inequality** for absolute values. -/
lemma mul_abs_le_abs_sin (hx : |x| ≤ π / 2) : 2 / π * |x| ≤ |sin x| := by
  wlog hx₀ : 0 ≤ x
  case isFalse => simpa using this (by rwa [abs_neg]) <| neg_nonneg.2 <| le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx ⊢
  exact (mul_le_sin hx₀ hx).trans (le_abs_self _)

lemma sin_sq_lt_sq (hx : x ≠ 0) : sin x ^ 2 < x ^ 2 := by
  wlog! hx₀ : 0 < x
  case isFalse =>
    simpa using this (neg_ne_zero.2 hx) <| neg_pos_of_neg <| hx.lt_of_le hx₀
  rcases le_or_gt x 1 with hxπ | hxπ
  case inl =>
    exact pow_lt_pow_left₀ (sin_lt hx₀)
      (sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith [two_le_pi])) (by simp)
  case inr =>
    exact (sin_sq_le_one _).trans_lt (by rwa [one_lt_sq_iff₀ hx₀.le])

lemma sin_sq_le_sq : sin x ^ 2 ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (sin_sq_lt_sq hx).le

lemma abs_sin_lt_abs (hx : x ≠ 0) : |sin x| < |x| := sq_lt_sq.1 (sin_sq_lt_sq hx)
lemma abs_sin_le_abs : |sin x| ≤ |x| := sq_le_sq.1 sin_sq_le_sq
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/SpecificFunctions/Deriv.lean

SHA256 `7e34650b84e2cc7eeb4f0037b99ede1a6cfd4e07fb2b081a16584a4f3d5475a2`

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
```

### sine_concavity_producer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/SpecificFunctions/Deriv.lean#L162-L165

```lean
theorem strictConcaveOn_sin_Icc : StrictConcaveOn ℝ (Icc 0 π) sin := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  rw [interior_Icc] at hx
  simp [sin_pos_of_mem_Ioo hx]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/ProjIcc.lean

SHA256 `c9381ad59b712957a877a217b75cb1ea688c2dba511ae88907acb3dcf15c8e7b`

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
```

### actual_clamp_continuity

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/ProjIcc.lean#L30-L33

```lean
variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

@[continuity, fun_prop]
theorem continuous_projIcc : Continuous (projIcc a b h) := Continuous.subtype_mk (by fun_prop) _
```
