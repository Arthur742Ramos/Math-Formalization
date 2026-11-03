# Draft registry contract

`Challenge.lean` is a self-contained proof-bearing statement surface with only
Std imported. It contains 990 physical lines and 53,701 bytes. Its principal
theorem excludes an original sixth-column extension of each of the seventeen
literal representatives. `Solution.lean` separately imports the full modular
implementation. Neither source assumes exhaustive classification or unrestricted
order-nine nonexistence.

The Challenge was extracted from the implementation by omitting unused
declarations, removing duplicate module/import/option wrappers, merging the
seventeen repeated profile-check namespace wrappers, and retaining every
required proof and literal data table. It does not pack unrelated commands on
one line to conceal its size. `challenge-extraction.json` lists selected
declarations and input hashes. The complete modular implementation remains
available alongside it.

The Comparator draft selects only
`CyclicDigitTransport.no_representative_extension`. Its `definition_names` list
is empty intentionally: representative data and the mathematical extension
predicate are fixed dependencies of the theorem, not replaceable definition
holes. Exact protected dependency comparison still requires execution.

The standalone Challenge passed ordinary Lean4.35.0-rc2 elaboration/kernel
checking with only propext, Classical.choice and Quot.sound. This is not a
protected Comparator, independent-kernel, rendering or canonical full pass.
Those gates remain outstanding; host capacity is below the published canonical
minimum. Author/maintainer attribution must be finalized before formalization
metadata is written or any registry handoff is made.
