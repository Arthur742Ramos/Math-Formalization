# Selected definition

`HMP.row e d c i = d i (c.2 (fun k : Fin c.1 => e i k))`.

Here `e : ι → ℕ → Bool` codes coordinates, `d : ∀ i, ℕ → X i` are factor
sequences, and `c : HMP.RowCode` is a finite table. The definition itself does
not assume injection, density, topology, cardinal bounds or nonemptiness and
uses no axioms. Those hypotheses belong to the separately selected theorems.
`RowCode` is a transparent type abbreviation, not an additional selected value.
The table decoder is literal and exposed across module imports; definition
comparison must verify its value as well as its type.
