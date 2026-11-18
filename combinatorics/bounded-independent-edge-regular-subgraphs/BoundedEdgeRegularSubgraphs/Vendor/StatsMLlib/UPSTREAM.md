# StatsMLlib Gaussian concentration proof

The source files in this directory are the imports needed by the Gaussian
Lipschitz concentration theorem at StatsMLlib commit
`edcd3104f1eaf6b2eba9d2fc7ecb0f09aa7f606f`. The original author notices
and Apache 2.0 licence accompany the port.
[Pinned upstream concentration module](https://github.com/Lean-MoDS/StatsMLlib/blob/edcd3104f1eaf6b2eba9d2fc7ecb0f09aa7f606f/StatsMLlib/Probability/Gaussian/LipschitzConcentrationEuclidean.lean).

The port adds Lean module headers and rewrites imports to the local paths.
In `Poincare/LevyContinuity.lean`, two moment monotonicity arguments use the
corresponding Mathlib lemmas directly. The definition of `phi` in
`LogSobolev/GaussianOneDim.lean` is exported because a public theorem
mentions it. The package uses its existing Lean and Mathlib pins.
