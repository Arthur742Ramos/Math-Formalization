module
import RationalGaussianPaperEncoding
meta import RationalGaussianPaperFlow
meta import RationalGaussianPaperFeatures
meta import RationalGaussianCompress
meta import RationalFlowEncodingBounds
open SparseCompletion

private def toyD {m : ℕ} : Fin m → Fin 0 → ℚ := fun _ a => Fin.elim0 a
private def toyE {m : ℕ} : Fin 0 → Fin m → ℚ := fun a => Fin.elim0 a
private def toyP : Fin 0 → ℚ := fun a => Fin.elim0 a

#guard List.ofFn (rationalGaussianPaperGeneralFlow toyD toyE toyP
  (![1/3, 2/3] : Fin 2 → ℚ) 1 1 0 1).1.get = [1/3, 2/3]
#guard List.ofFn (rationalGaussianPaperExactFlow toyD toyE toyP
  (![1/3, 2/3] : Fin 2 → ℚ) 1 1 1).1.get = [1, 0]
#guard List.ofFn (rationalGaussianPaperGeneralFlow toyD toyE toyP
  (![0, 0] : Fin 2 → ℚ) 1 0 0 1).1.get = [0, 0]
#guard List.ofFn (rationalGaussianPaperExactFlow toyD toyE toyP
  (![0, 0] : Fin 2 → ℚ) 1 0 1).1.get = [0, 0]
#guard List.ofFn (rationalGaussianPaperExactFlow toyD toyE toyP
  (fun i : Fin 0 => Fin.elim0 i) 1 0 1).1.get = []
#guard rationalCanonicalEncodingBits ((rationalGaussianPaperExactFlow toyD toyE toyP
  (![1/3, 2/3] : Fin 2 → ℚ) 1 1 1).1.get 0) = 3
