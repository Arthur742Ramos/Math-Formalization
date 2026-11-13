# Reproducing validation

Use Isabelle2026 and the external AFP source pin in `AFP_DEPENDENCY.md`.
The proof build checks the seven entry theories, including the selected-fact
transitive oracle audit and SML code-generation check.

```sh
isabelle build -c -j 1 -o threads=2 -o parallel_proofs=0 -o document=pdf \
  -o document_build=pdflatex \
  -d "$AFP/thys" -D Computational_Path_Presentations \
  Computational_Path_Presentations
```

The explicit pdfLaTeX engine is supported by Isabelle2026 and avoids requiring
a LuaLaTeX format on systems that only provide pdfLaTeX. Point TEXMFVAR,
TEXMFCONFIG and TEXMFCACHE to writable local cache directories when necessary.

For AFP's proof-outline document variant, additionally pass
`-o 'document_variants=document:outline=/proof,/ML'`.

The official Isabelle linter must match Isabelle2026. With its `linter_base`
component registered in an isolated user configuration:

```sh
isabelle lint -j 1 -o threads=2 -o parallel_proofs=0 -o document=false \
  -o lint_bundles=afp_mandatory -f error -r json -O mandatory-lint.json \
  -d "$AFP/thys" -D Computational_Path_Presentations \
  Computational_Path_Presentations
```

The default lint bundle provides additional advisory findings. Its advisories
must not be represented as mandatory failures or silently discarded.

A complete release receipt should preserve exact source hashes, toolchain and
AFP pins, commands, exits, full-build and lint logs, generated PDF hash and
visual inspection scope, generated-code tests, and independent review of the
same final source. A successful previous build is not evidence for later edits.
The audit inside `CP_Audit` checks recorded proof oracles, not all logical
axioms; ordinary Isabelle/HOL foundations remain in use. Forbidden proof gaps
and custom axiom declarations should also be scanned in the new source.

No command in this guide submits the entry or contacts AFP editors.
