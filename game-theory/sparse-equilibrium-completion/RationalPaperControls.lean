/- AI-assisted formalization under the repository Apache-2.0 license.
Executable controls for canonical boundaries and actual sharp compression. -/
module
public import RationalPaperWitness
public meta import RationalPaperWitness
public meta import RationalCanonicalGrid
public meta import RationalGrid
public meta import RationalFeatureDeletion
@[expose] public section
open SparseCompletion
open scoped BigOperators

#guard rationalCeilSqrt (0 : ℚ) = 0
#guard rationalCeilSqrt (1 : ℚ) = 1
#guard rationalCeilSqrt (4 : ℚ) = 2
#guard rationalCeilSqrt (9/4 : ℚ) = 2
#guard rationalCeilSqrt (17/4 : ℚ) = 3
#guard rationalCanonicalGridSize 1 1 1 = 1
#guard rationalGridSize 1 1 1 = 2

private def D0 : Fin 2 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
private def E0 : Fin 0 → Fin 2 → ℚ := fun a => Fin.elim0 a
private def p0 : Fin 0 → ℚ := fun a => Fin.elim0 a
private def q2 : Fin 2 → ℚ := fun _ => 1/2
private def qsharp : Fin 2 → ℚ := rationalPaperExact D0 E0 p0 q2 1 1 1

-- At H=1, the exact compressor has only its single mass row. It actually
-- deletes one of two positive input weights, rather than taking a fallback.
#guard (rationalWeightSupport qsharp).card = 1
#guard (∑ i, qsharp i) = 1
#guard ∀ i, 0 ≤ qsharp i

private def qzero : Fin 2 → ℚ := rationalPaperExact D0 E0 p0 (fun _ => 0) 1 0 1
#guard ∀ i, qzero i=0
#guard (rationalWeightSupport qzero).card = 0

private def D3 : Fin 3 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
private def E3 : Fin 0 → Fin 3 → ℚ := fun a => Fin.elim0 a
private def q3 : Fin 3 → ℚ := fun i => if i=0 then 0 else 1/2
private def qoriginal : Fin 3 → ℚ := rationalPaperExact D3 E3 p0 q3 1 1 1
#guard qoriginal 0=0
#guard (rationalWeightSupport qoriginal).card=1
#guard (∑ i, qoriginal i)=1

private def Emoment : Fin 1 → Fin 3 → ℚ := fun _ i => i.val
private def qmoment : Fin 3 → ℚ :=
  rationalPaperExact D3 Emoment p0 (fun _ => 1/3) 1 1 1
#guard (rationalWeightSupport qmoment).card ≤ 2
#guard (∑ i, qmoment i*Emoment 0 i)=1
#guard (∑ i, qmoment i)=1
