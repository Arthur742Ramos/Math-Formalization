# Math-Formalization

Lean formalizations organized by subject and target. Each target is a separate
Lake project with its own toolchain, dependency lock, Challenge, Solution,
Comparator configuration, metadata and checks.

See [the project index](PROJECTS.md). Build a target from its own directory.
There is no root Lake project or shared toolchain. Existing standalone
repositories remain available at their original locations.

New targets belong under `<subject>/<descriptive-target>/`. Commit their
source, pins, definition evidence and verification scripts. Give each target
a workflow with exact path filters and working directory. Keep dependencies
within the target or pinned public dependencies; another target folder must
not supply ambient imports. The root Apache-2.0 license covers project code;
retained source evidence keeps its original attribution and license.
