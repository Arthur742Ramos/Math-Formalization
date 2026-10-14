# Scope and verification audit

The full theorem includes both directions and explicit Hausdorffness. Local
patches, cover indices and basis layers have arbitrary cardinality. The new
point-finite-cover construction has independently generalized universes for
the space and cover index. The empty-space case is allowed.

Current Mathlib master `a63713524b66f0b5681eaa2bfa83e7218c5cdbe5` was audited
separately from the selected supported build pin. The audit examined all 9,223
Lean files, all metrizable/paracompact declaration contexts, and relevant
manifold results. No full local-to-global criterion was found. The manifold
result uses second countability through additional chart and sigma-compactness
assumptions. Palomar registry revision 262, including all math.GN entries, and
all repository branches and pull requests were checked; no competing target
was found. Registered Nagata–Smirnov and existing metric paracompactness are
explicit prerequisites, not new claims.

The toolchain and all dependencies are pinned. Local compiler checks cover
the library, standalone canonical Challenge, exports, ten declaration axiom
closures and semantic tests. Empty spaces, arbitrary discrete spaces, independent
index universes, explicit separation and exact topology equality are tested.
Permitted foundational axioms are only `propext`, `Classical.choice`, `Quot.sound`.
There are no proof holes or added axioms.

The canonical Challenge exceeds the preferred 300-line presentation size
because it includes the credited prerequisite. It remains below the hard
1,000-line and 100 KiB bounds. Exact-commit Comparator, NanoDa, con-ron and
renderer results must accompany the final packet; local verification alone is
not presented as those hosted checks. No Palomar receipt is claimed here.
