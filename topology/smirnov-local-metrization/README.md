# Smirnov's local-to-global metrization theorem

A space is metrizable if and only if it is Hausdorff, paracompact and locally
metrizable. Here locally metrizable means that every point belongs to an open
subset whose inherited topology is metrizable. There is no countability,
separability, local compactness or nonemptiness assumption.

`PointFiniteBasis.lean` proves the reusable intermediate result: an arbitrary
point-finite open cover by metrizable subspaces in a paracompact space yields a
sigma locally finite basis. It globally refines the covers of all local balls
at each reciprocal radius, then uses finite patch membership and the triangle
inequality to prove the basis property. This intermediate theorem needs no
separation assumption. `Smirnov.lean` refines arbitrary open covers and applies
the previously registered Nagata–Smirnov theorem after deriving regularity.

Build from this directory with `lake build`. Exact toolchain:
`leanprover/lean4:v4.35.0-rc2`; Mathlib:
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The four registered Nagata–Smirnov
support modules from commit `6aa68b2cb67719a187e64de29567443575eb560e`,
`topology/nagata-smirnov`, are vendored in `NagataSmirnovSupport/` with credited,
unchanged declarations and adapted module import paths. Provenance hashes are
in `verification/registered-support-provenance.json`. This layout builds within
the fixed sandbox, which cannot write a nested Git dependency's build directory.
`SmirnovChallenge.lean` includes that attributed source and
the new construction with canonical Mathlib imports; `SmirnovSolution.lean` exports
the reusable modules. The Comparator selects six new results only.

The verification module identities are unique. The original Git dependency
exposed generic `Challenge.lean` and `Solution.lean` names that could shadow this
project during source lookup; the unique names remain after the portable layout repair.

Sources: Munkres, *Topology*, second edition, Theorem 42.1, pp.261–262; Sakai,
*Geometric Aspects of General Topology*, second-edition author manuscript dated
November 2, 2023, Proposition 2.6.8(4), p.63, with the Hausdorff convention in
Section 2.6, footnote 10, p.56. Complete metrizability is outside this project.
This formalizes classical mathematics without claiming new mathematics or
first formalization priority.

Authors and responsible maintainers: Arthur Freitas Ramos, David Barros Hulak,
and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex authored substantive proofs
and packaging under Arthur's authorization. Independent internal AI reviews
and mechanical checks are disclosed separately from human review; no human
review is claimed. Licensed under Apache-2.0.

Verification evidence is recorded in `AUDIT.md`, `REVIEW.md`, and
`verification/`. The parent campaign owns Palomar submission and registration.
