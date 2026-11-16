# Automatic coherence: stopped-campaign source checkpoints

**Preservation-only draft. Not a complete formalization, verified release, or
Palomar-ready package. Do not merge on the strength of the historical checks.**

This directory preserves existing source checkpoints after proof development was
stopped. No proof was changed, completed, or rebuilt to prepare this archive.
It is deliberately separate from the repository's audited project catalog and
contains no new Lake configuration, CI workflow, Comparator, or registry metadata.

## What is preserved

- `core04/`: the exact finite relative-last-vertex certificate source checked by
  ordinary Lean 4.35.0. Its 94 public checks cover only dimensions 0, 1, 2, and 3,
  including 70 explicit finite horn steps. This is a finite combinatorial result,
  not an identification with actual simplicial-set horn pushouts, a theorem in
  all dimensions, or the geometric reflection theorem.
- `geometry31/`: exact sources from the historical ordinary-native geometry
  checkpoint, including its audit driver. The checked geometric scope concerns
  double mapping cylinders and ordinary pushouts under the hypotheses displayed
  in those sources. It is not the manuscript's full geometric interpretation.
- `MANIFEST.json`: byte counts, SHA-256 and Git blob identities, preserved source
  provenance, exact toolchain/dependency pins, and the limits of the historical
  evidence. These hashes identify source; hashes alone are not proof verification.

Some original comments say `SOURCE ONLY / UNCOMPILED`. Those comments predate the
historical runs and are intentionally preserved byte-for-byte. The manifest
separately records the later ordinary-native outcome and does not imply a new
run on this repository commit. An audit driver is not an independently checked
kernel and does not by itself establish protected verification.

## Historical evidence and missing release gates

The accepted historical checkpoints are core04 and geometry31. Their original
run and internal AI review digests are recorded in the manifest. Those internal
reviews were not human peer review. Original private operational evidence and
compiled objects remain in their recovery backups; they are not published here.

A later geometry36 attempt failed and was not accepted; its source and outputs
are not substituted for geometry31. Subsequent uncompiled drafts also remain
outside this archive. Earlier campaign checkpoints are not all represented by
these two snapshots. This is not a complete backup of every campaign artifact.

No current-source native build, complete transitive audit of the full manuscript,
canonical protected comparison, required independent-kernel check, complete
negative-control suite, or Challenge rendering is established by this archive.
The manuscript's global geometric fullness/reflection and other unfinished
connections remain open. No full-paper readiness or registry acceptance is claimed.

The root `AGENTS.md` and `LOCAL-VALIDATION.md` remain unchanged and apply before
any future merge or verified handoff. Their narrow status-only carry-forward
exception does not apply to adding these new source files. This draft does not
request or authorize restarting proof development or running those missing gates.

## Provenance and attribution

The source bytes and existing headers are unchanged. This is AI-assisted
formalization work undertaken for Arthur Freitas Ramos, with internal AI source
and evidence reviews as specifically recorded. No human review is invented and
no claim of novelty is made. The source imports Lean and Mathlib at the pinned
versions in the manifest; their library sources are not vendored here.

The repository license governs this contribution. No manuscript is reproduced
or relicensed, and this archive does not change manuscript author attribution.
