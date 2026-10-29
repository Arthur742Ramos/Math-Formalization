# Attribution and provenance

This development package retains Apache-2.0; see LICENSE.

The files Mycielski/FusionStep.lean, Mycielski/Scheme.lean and
Mycielski/Independent.lean are copied from
topology/mycielski-cantor-independent at repository commit
a6fd933f00c83a82c4d7ab510d17ae62e87dc75f. Their respective Git blob IDs are
591ff7b153df18577ad593a3280e532444882dbe,
a545c2c68c03a24ad60014562d3eaa850e1b1b3e, and
c0c0615effc8abd76b78470a6e61261d0aad8b94. The source package credits campaign
authors and responsible maintainers Arthur Freitas Ramos, David Barros Hulak,
and Ruy Jose Guerra Barretto de Queiroz; material Lean proof work was by
OpenAI Codex, without inferred human proof contributions. The construction
credits Mathlib's CantorScheme infrastructure and the classical Mycielski
theorem: Jan Mycielski, “Independent sets in topological algebras”,
https://eudml.org/doc/213780. The original scan was not inspected because
access returned 403. ChaosChallenge.lean includes these full proof sections
inline for protected compilation; scripts/build_challenge.py reconstructs and
checks their source text. CantorChaos.lean and the Solution retain the local
module structure. This repackaging does not change their attribution.

The new draft adapts the generic orbit construction and late-return,
square-punctured and iteration fragments of
topology/ip-transitive-points/IPTransitive.lean at the same commit, blob
40afb48ddf57a1f7a35e2706d346ae6baaed9a54, whose header credits OpenAI Codex
for material Lean proof authorship and its research source Jian Li,
“Transitive points via Furstenberg family”, Topology and its Applications 158
(2011), Theorem 3.2. It also identifies adapted fragments from
topology/strongly-transitive-sequences/StrongTransitive.lean at
b507c8fd789af8ac5dee356ea2a85444209e401d (blob
e47bf442d60d9fc11e4fa6e37c603d5ee4fc2b3a), and pair iteration from
topology/furstenberg-weak-mixing/WeakMixingPower.lean at
9e5b57dba2ba9423cc8f12ff934bd07d86394c47 (blob
ab52eda9215fa04e01e03417f9e3b87cba90dc99). The IP source also credits
topology/kuratowski-ulam/KuratowskiUlam.lean at
0e3676798fe19b23d17defe9d732977d9f913f11 (blob
a16038480bc2f517fcdcf77efe7c9bfd26a1e06d), with original-file copyright
2026 Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto
de Queiroz; material Lean proof by OpenAI Codex.
