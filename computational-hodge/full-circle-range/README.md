# Full circle differential range and computational paths

For every positive C¹ coordinate density ρ on the real period-one circle and every real μ, this project proves

`(∃ u : C2Coefficient, Δρ u − μu = f) ↔ ∀ v : C2Coefficient, Δρ v − μv = 0 → ∫ ρfv = 0`.

Both quantifiers range over actual unrestricted C² circle coefficients. The geometer-sign Laplacian is the literal operator `−ρ⁻¹(ρ⁻¹u′)′`; no differential equation or bridge is assumed.

The predecessor PR78 constructs the actual Green operator and proves the normalized resonant range using a closed invariant subspace of the C⁰ forcing space. This extension projects arbitrary forcing to weighted mean zero, transfers its homogeneous-mode orthogonality, and reconstructs a solution with the negative constant correction `u0 − constantC2((weightedMean f / meanρ) / μ)` when μ is nonzero. Normalization commutes with the shifted operator and forcing projection.

At zero shift, solvability is equivalent to vanishing ordinary integrals along every actual finite computational trace, and to the corresponding finite harmonic-cochain periods. Traces use the user's indexed binary composition and reversal definitions, their actual path realization and covering lift. All corners, AC regularity, chain rule and integrability proofs remain. These are actual projected-curve integrals, not assigned period values.

Off zero, the constant coefficient `−1/μ` solves constant forcing 1, whose genuine weighted unit-trace period is strictly positive. Thus vanishing path periods is not a necessary condition for the unrestricted shifted problem off zero. This does not assert that every forcing is solvable off zero: nonconstant resonant modes may obstruct it.

The result concerns a real scalar weighted circle. It proves no canonical orthogonal representative or uniqueness, spectral basis/completeness, uniform near-resonance bound, Hilbert completion or unbounded self-adjoint realization, general manifold/Kähler Hodge theorem, de Rham identification, ambient cotangent construction, numerical algorithm or mathematical novelty.

Exact published predecessor fragments and final statement-preserving proof changes are recorded in `base-provenance.json` and `proof-refactors.json`. New source is in `FullRange.lean`. The three literal upstream computational-path excerpts and license remain unchanged. Exact toolchain and dependency commits are pinned.

`scripts/make_surface.py` includes all retained statements and complete proofs in both entrypoints. It keeps the 1,000-line/100-KiB source guards, removes no proof content, and joins no proof-body or open-command lines. Thirty-seven explanatory docstrings retain their original per-declaration associations through lossless header placement after ordinary signature layout; modular docstrings remain unchanged. Original-renderer raw/sanitized visibility, metadata associations and browser readability require their own checks. The 8-MiB page cap remains unchanged.

Native compilation, imported-definition semantic expansion, axiom audits, exact interfaces with negative controls, independent kernels, unchanged canonical validation, original rendering, browser review and final release evidence are separate mandatory local gates. Author-hosted CI is disabled by repository policy. Internal AI mathematical review is not human/external peer review or registry acceptance. No registry submission is authorized by this development package.
