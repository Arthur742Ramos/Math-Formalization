# Exact beta-step cost of call-by-name CPS translation

For a closed untyped lambda term, exactly `n` weak call-by-name head beta contractions reach an abstraction if and only if the CPS translation applied to the identity continuation reaches a weak call-by-value value in exactly `4*n + 2` beta contractions. The same statement holds for the existing explicitly translated tests of source contexts when the hole term and the plugged source are closed; fixed context syntax may itself be open under binders.

The counted big-step simulation also gives the translated source abstraction as exact target readback and takes `4*n + 1` steps before applying an arbitrary abstraction continuation. These are beta-step counts with capture-avoiding substitution treated atomically, not bounds on time, space or implementation cost. The theorem does not assert full abstraction for arbitrary target contexts or a divergence equivalence.

The source builds on the public CPS adequacy and translated-context formalizations and adapts the classical CPS setting of Plotkin, cited in the metadata. Challenge fixes the syntax, weak strategies, translations, context grammar and counted relations; its isolated theorem holes are not imported by Solution. Independent integrated review and hosted checks are pending.
