# Selected definitions

`PerfectImage.upperImage f U` is `(f '' Uᶜ)ᶜ`: the set of values whose entire
fiber is contained in `U`. It does not assume surjectivity. In particular, a
value outside the range belongs to every upper image; all final image theorems
assume surjectivity explicitly.

`PerfectImage.fiberNeighborhood f r y` is
`upperImage f (Metric.thickening r (f ⁻¹' {y}))`. It uses the source metric;
the general shrinking estimate assumes `MetricSpace X`. The image-basis theorem
chooses a metric compatible with the domain's supplied topology. The definition
does not assume the source is compact, the map is continuous or closed, or its
fibers are compact. Those hypotheses appear where needed in the theorems.

Both definitions have identical values in the canonical Challenge and modular
Solution. Their names are included in Comparator's `definition_names`.
The compatible metric conclusion states equality of induced and supplied
topologies, rather than merely providing an unrelated metric on the same type.
