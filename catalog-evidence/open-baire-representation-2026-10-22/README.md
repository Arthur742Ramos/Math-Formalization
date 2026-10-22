# Exact-source canonical verification

Frozen submitted source: `87652c909a92afded15aad86a901d8c11dd75ed8`,
project `topology/open-baire-representation`, package tree
`8a233f6d76e86f877c61c20af15e337daa9d6bd2`.

The initial native preparation checkpoint remains historical. Both later
canonical runs used caller `bd5c522367f64c871c2cc3c5b5b21551b81217a7` and
pipeline `ad5db9e7ff8b17523d73aeb244aaeabcde810c64`, on attempt 1:

- [Full 39811305855](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39811305855): pass. The protected comparator, Lean and NanoDa accepted. The pinned con-ron replay accepted 12,676 declarations with `--verified`; this was complete acceptance, with no capacity decline.
- [Rendering 39811305165](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39811305165): pass. All six contracts and all 14 bundle files, including the manifest, were checked against the downloaded original artifact. The tree digest was recomputed using the pinned renderer algorithm.

Original report bytes, GitHub artifact digests, the exact-source archive binding
and result summary are retained here. The release guard requires actual
three-kernel acceptance in the current report format; it preserves legacy
checks and rejects missing, declined, mismatched or incomplete evidence. All
189 root regressions passed. The source package was not edited after these runs.

Browser visual inspection was not performed. Mechanical success and internal
independent AI review do not establish human review, editorial acceptance or
public registration. No registry submission or merge was performed. The one
approved runner pair is consumed; no reruns are authorized.
