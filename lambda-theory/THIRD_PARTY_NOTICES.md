# Source and license notices

The Challenge reuses the concrete syntax model and canonical term-encoding construction from the authors’ Lean lambda/Turing development at public commit c695e9a1b47f0c9cb7031f5c13b8494180b7b948, under Apache-2.0. It copies the model, code-tree encoding, decoder, valid-code recognizer and proofs needed to construct the exact `Primcodable Term` instance. The theorem obligations themselves are isolated in the Challenge.

The Solution depends on that pinned project and Mathlib. The dependency retains its own license and third-party notices, including notices for its CSLib and Isabelle adaptations and Mathlib material. This package does not bundle the dependencies. See the pinned dependency’s `lambda-turing/THIRD_PARTY_NOTICES.md` for its full notices.

The authors’ earlier Isabelle lambda/Turing development was reviewed locally at 6fed1b6e77514ec161a8fd4718fde1587f2cf624 and submitted to AFP. That local snapshot is not asserted to be publicly available. Its BSD-3-Clause license is separate from this Apache-2.0 package.
