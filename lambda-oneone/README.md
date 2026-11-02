# Injective padding and one-one completeness for closed lambda programs

The package defines a primitive-recursive syntax padding operation that is injective in its natural-number tag and original term. It reduces to the original term and preserves all partial numerical observations under full beta reduction, including for open terms; closed inputs produce closed padded terms.

Every recursively enumerable predicate on a `Primcodable` domain has an injective primitive-recursive reduction to the concrete language of closed terms whose application to Church zero can reach Church zero. A uniform one-one reduction is also given for recursive-code halting. The construction selects a fixed code for each r.e. predicate by existence; it does not claim an extractor from a proof of r.e. membership. The package includes a productive-complement theorem. Absence of a numerical result is not identified with divergence.

The Challenge fixes the syntax, coding, numerical semantics, recognizer, padding and reductions. Its theorem holes are comparator obligations and are not imported by the Solution. This is a formalization of classical computability ideas for the stated concrete lambda model. Independent integrated review, protected comparison and hosted verification remain pending.
