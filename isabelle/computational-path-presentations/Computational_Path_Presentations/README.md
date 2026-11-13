# Computational Path Presentations

This standalone Isabelle/HOL development formalizes the algebraic results below.
No AFP submission, acceptance, worldwide mathematical novelty, or human review
is claimed. Validation receipts must identify the exact source bytes they checked.

## Introduction

A computational path records an equality witness rather than merely asserting
that two endpoints agree. This Isabelle/HOL development studies its free
structural fragment: generators with specified endpoints, identities, reversal
and composition. It relates parenthesized witnesses to composable signed words
and examines changes of presentation obtained by interpreting generators as
words.

The motivation comes from the explicit equality witnesses in
[Ramos, de Queiroz and de Oliveira (2017)](https://doi.org/10.1093/jigpal/jzx015)
and the broader rewriting treatment of
[de Veras et al. (version 4, 2021)](https://arxiv.org/html/1906.09105v4).
The literal-word and abbreviation constructions correspond to algebraic aspects
of [Ramos et al., *Topological Computational Paths: Presentation Invariance and
Observable Quotients*, version 4 (2026)](https://arxiv.org/html/2608.04228v4),
especially Sections 3.2 and 4. The present scope does not include that paper's
topological comparison theorems.

The core cancellation mathematics is reused from Joachim Breitner's AFP entry
[Free Groups](https://isa-afp.org/entries/Free-Groups.html). Its source supplies
signed letters, adjacent inverse cancellation, termination, confluence and
unique normal forms. Here an executable reducer is related to that existing
normal form; endpoint and presentation arguments are layered over it. These
classical results and their existing formalization are not new claims.

## Theorem contracts

- **Executable free normalization.** Given executable equality on generator
  labels, `cp_reduce` computes the free normal form. `cp_reduce_eq_normalize` identifies
  `cp_reduce` with AFP's uniquely specified `normalize`.
  `cp_reduce_complete` characterizes the independently inductively generated
  cancellation equivalence `cp_word_eq` by equality of reduced words.
- **Endpoints and witnesses.** `cp_flat_typed`, `cp_flat_quote`,
  `cp_quote_typed`, and `cp_typed_tree_word_correspondence` connect typed binary
  witnesses with signed composable words. Quoting and then flattening recovers
  the literal word. The reverse operation returns a right-associated witness,
  not the original syntax. The identity's endpoint is explicit, including for
  an empty word.
- **Typed confluence.** `cp_typed_reduction_diamond` joins two finite cancellation
  reductions while retaining both endpoints. It transfers AFP's confluence;
  it does not assert a strict one-step diamond or confluence of arbitrary
  additional equations.
- **Canonical representatives.** `cp_normal_tree_complete` characterizes
  equality of the quoted normal forms by free equivalence of the flattened
  words. It is not a theorem that distinct binary syntax trees are literally
  equal, or an independent completeness theorem for a tree rewrite calculus.
- **Presentation interpretation.** `cp_interpretation_sound` permits a vertex
  map and arbitrary finite generator codes, including empty codes, provided
  codes have the required endpoints and every admitted named equation is
  preserved.
- **Conservative abbreviation.** `cp_conservative_abbreviation` adjoins one
  fresh generator with specified endpoints and its defining equation to an
  existing typed word. Inclusion preserves and reflects equality between old
  words. The existing relation set is arbitrary; no termination or decision
  procedure for those relations is assumed. `cp_abbreviation_roundtrip` also
  proves every extended typed word equivalent to its embedded elimination.
- **Exact decision scope.** `cp_empty_presentation` specializes presentation
  equality to typed words with identical free normal forms when the named
  relation set is empty. It does not extend the normalizer's completeness to
  arbitrary presentations.

## Scope and prior work

This is an algebraic formalization in Isabelle/HOL. It does not identify HOL
propositional equality with an intensional identity type. It does not formalize
the full 39-rule LND_EQ-TRS, dependent identity elimination, higher coherence,
univalence, geometric realization, fundamental-group completeness, quotient
topologies or homeomorphisms. In particular, flattening syntax is not equality
of binary and equal-slot parametrizations of geometric paths.

The preceding dependent-HIT development also contains typed paths, presented
hom-set quotients and path-valued maps. Those are acknowledged overlap, not
newly discovered concepts. This standalone entry does not import or silently
identify that development's `dart`, typing judgments or presentation relation.
A later integration needs an explicit interpretation and preservation theorems;
reflection or equivalence requires additional proof. No such HoTT bridge is
claimed here.

Executable use of the word reducer requires executable equality on generator
labels. Evaluating endpoint typing additionally requires executable vertex
equality. The abstract HOL correctness theorems do not impose these code
execution constraints.

All vertex and generator carriers are HOL types and therefore nonempty. The
current graph interface does not have a separate admitted-generator subset; no
empty-generator graph generality is claimed. Named equations not well typed at
their recorded endpoints do not supply a rule.

The current extension theorem is algebraic conservativity on old words. By
itself it does not assert a quotient-space homeomorphism or invariance of an
observable topology. The cited 2026 paper makes precisely that distinction.

## Dependencies and validation boundary

Target: **Isabelle2026**, with the external AFP **afp-2026-11-12** snapshot and
its `Free-Groups` session. Keep the AFP checkout outside this entry and retain
its license and attribution. The audit identifies the exact inspected sources;
build, document, lint and review receipts must identify the exact source bytes
they checked. See the repository-level validation guide for reproducible commands.

Bibliographic metadata is in `document/root.bib`. Build, PDF inspection, mandatory
lint, internal review and external editorial review are separate checks; none
should be inferred from another.

## Attribution and review status

Prepared author metadata follows the owner's established AFP order: Arthur
Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz. This preparation
does not certify coauthor consent, individual human proof contributions, or
human mathematical review. Arthur is the intended maintainer. No submission
has been authorized or performed.

AI assistance was used for proof engineering. Internal AI review is distinct
from human peer review and from the machine checks, whose exact scope must be
reported separately.
