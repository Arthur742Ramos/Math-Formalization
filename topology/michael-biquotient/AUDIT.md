# Source, scope, and overlap audit

Audit performed 2026-10-09 in an isolated clone of
`Arthur742Ramos/Math-Formalization`, based on
`375929156f88029fe6b6088bb61c409d98bfe9cb`.
No applicable AGENTS.md was present in the task's ancestors or this checkout.
The available local skill catalog contained no specialized Lean formalization
skill. Other packages and concurrent Poincaré/Isabelle activity were untouched.

The paper's convention on printed p.287 makes all maps continuous and onto.
Theorem 1.2 on p.288 is for finite or infinite products without separation
hypotheses. Theorem 1.3 on p.288 assumes only Hausdorffness of the target and
quantifies over every space, or every paracompact space. Proposition 2.2 on
p.290 is the adherence bridge. Section 5 on p.295 gives a Hausdorff paracompact
topology on underlying Y and the deleted-diagonal obstruction. Michael's p.287
footnote credits Hájek's priority. The formal development changes the proof
route, not these conclusions.

The alternate route preserves the whole original fiber-cover family in
`finiteCoverFilter`. No cover member is discarded. Ultrafilter refinement and
Hausdorff uniqueness yield a pullback filter with no cluster point anywhere.
Its one-point topology has isolated points outside the distinguished point.
The paracompact proof uses one chosen cover member and singletons outside it,
and indexes the large member only once. The witness's first product factor
retains the original topology of Y via `WithTopology` on the second factor.

The pinned Mathlib source/cache reports revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55` and the matching Lean toolchain.
An all-source ASCII search for `biquotient`, `bi-quotient`, `biQuotient`,
`limit lifting`, and `universally quotient` returned no matches. A subsequent
topology search inspected the quotient and product declarations, including:

- `Topology.IsOpenQuotientMap.piMap` and `.prodMap`: open quotient maps;
- `Topology.IsQuotientMap.continuous_lift_prod_left/right`: locally compact factors;
- `Topology.IsQuotientMap.of_surjective_continuous`: compact-domain/Hausdorff-target;
- the basic quotient, filter, ultrafilter, and filter-product APIs.

None supplies the full fiber-cover characterization or arbitrary biquotient
product theorem. This is a pinned-source overlap assessment, not a claim that
no other formalization exists anywhere. The cache was read without security
configuration changes; hosted reconstruction provides the independent check
against canonical dependencies.

[Clementino–Hofmann, *On limit stability of special classes of continuous maps*](https://sweet.ua.pt/dirk/artigos/2002/limstab.pdf),
introduction and §6, places biquotient product stability in categorical topology
and descent theory. Its Corollary 6.8 recovers the classical product stability
through a broader ultrafilter framework.

[Brazas–Gillespie, *Infinitary commutativity and fundamental groups of topological monoids*](https://arxiv.org/pdf/2001.09500),
printed p.22 after Proposition 5.10, invokes Michael 1.2 to prove quotientness of
products of James-stage maps and continuity of concatenation. The published
version is Topology and its Applications 317 (2022), 108193. These uses support
a specialist research audience and the centrality of the classical result.

Palomar policy at `96b034cc31a72a63d4f4041911dce337a85c9a04` requires intrinsic
paper-worthiness and a credible research audience, both provisionally supported
here by the primary theorem and later research uses. This does not guarantee
editorial acceptance. Current PalomarSubmission `toolchains.json` was checked
online and requires at least `v4.35.0-rc2`; the selected pin meets that minimum.
