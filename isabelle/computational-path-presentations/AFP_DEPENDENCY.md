# External AFP dependency

Target: Isabelle2026, distribution source identifier `096842708b28`.
The session imports `Free-Groups.FreeGroups` from the official AFP snapshot
`afp-2026-11-12`. The dependency remains external and is not republished here.

- Entry: https://isa-afp.org/entries/Free-Groups.html
- Author: Joachim Breitner. License: BSD.
- Snapshot: https://isa-afp.org/release/afp-2026-11-12.tar.gz
- Historically verified archive SHA256:
  `7d1c36b42ce9ba65a0b38f576324038a2d682a44f36f3a8e53ce8a2dc3d97583`.

The archive was obtained in the preceding dependent-HIT campaign. This campaign
freshly inspected and hashed the extracted Free-Groups and Applicative_Lifting
source files, listed in `AFP_DEPENDENCY_SHA256SUMS`; it does not describe the
old download as a fresh download. The installed Isabelle2026 source files and
standard parent heaps are likewise reused, while the new entry is freshly
built. No previous entry's proof log serves as evidence for this source.

Run from the AFP root to check the source pins:

```sh
sha256sum -c /path/to/this-repository/AFP_DEPENDENCY_SHA256SUMS
```

Build this entry with the AFP root supplied explicitly:

```sh
isabelle build -j 1 -o threads=2 -d "$AFP/thys" \
  -D Computational_Path_Presentations Computational_Path_Presentations
```

Only the selected entry and required dependencies are built; this does not
select the entire AFP. The global AFP components and security settings need
not change.
