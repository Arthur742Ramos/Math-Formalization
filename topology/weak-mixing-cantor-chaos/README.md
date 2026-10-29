# Weak mixing and Cantor scrambled families

A continuous self-map f of a nontrivial perfect Polish metric space has the
following property when its square map (x,y) ↦ (f x,f y) is open-set
transitive. There is one δ > 0 such that every nonempty open U contains a
closed embedded copy e of Cantor space ℕ → Bool. For each pair of distinct
Cantor codes s,t, every ε > 0 and every N, there are times n,m ≥ N such that

* dist(f^[n](e s), f^[n](e t)) < ε;
* δ < dist(f^[m](e s), f^[m](e t)).

The embedding is fixed for U; δ is fixed before U is chosen. The witness times
may depend on the pair, threshold and lower bound. The theorem constructs the
embedding and δ; neither is a premise. A stronger intermediate theorem gives
a Cantor family whose distinct ordered pairs have dense square orbit.

The exact Lean hypotheses are [MetricSpace X], [PolishSpace X],
[PerfectSpace X], [Nontrivial X], continuity of f and open-set transitivity
of the square. A Polish topology is second countable and admits a compatible
complete metric; the displayed metric need not itself be complete.
Perfectness excludes isolated points, and nontriviality supplies distinct
points. Compactness, surjectivity and invariance are not assumed. The
open-set transitivity definition permits time zero; a separate lemma proves
arbitrarily late visits. The closed embedding gives continuity, injectivity
and a closed image.

Blanchard, Glasner, Kolyada and Maass, “On Li–Yorke pairs”,
https://www.imath.kiev.ua/~skolyada/LY.pdf, discuss weak mixing and
independent transitive sets. The present result is a localized binary
consequence and makes no claim of the stronger all-arity independence or a
single dense σ-Cantor scrambled union. See RESEARCH-NOTES.md for the bounded
duplicate search and the scope of independent internal AI review.

The three Mycielski modules are credited proof dependencies copied from the
existing Mycielski package, not new selected results. The protected Challenge
contains their full proof sections inline and imports only pinned Mathlib; the
Solution uses the separately built local modules. The Challenge is generated
from the credited sources and checked for exact textual agreement.
ATTRIBUTION.md records origin, license, campaign roles and inherited IP proof
credits. Mathlib and Lean retain their own authorship.

Comparator selects the two CantorChaos theorems. Its definition-hole list is empty; the local definitions OpenTransitive, pairMap and DenseOrbit remain fixed, subject to definition-mutation controls. Separate semantic modules
check the Challenge and Solution interfaces. When performed, source-bound verification,
dependency authentication, independent kernels, axiom audits and rendering
are recorded in external receipts identifying their tested source; a local Lean build
alone is not a release or registration result.
