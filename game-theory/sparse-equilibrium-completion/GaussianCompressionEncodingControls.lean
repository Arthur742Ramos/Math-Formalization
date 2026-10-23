module
import RationalGaussianCompressionEncoding
meta import RationalGaussianCompress
meta import RationalFlowEncodingBounds
open SparseCompletion

#guard List.ofFn (rationalGaussianCompressVector
  (fun _ : Fin 1 => fun _ : Fin 2 => (1 : ℚ)) (![1/3, 2/3] : Fin 2 → ℚ)).get = [1, 0]
#guard List.ofFn (rationalGaussianCompressVector
  (fun _ : Fin 1 => fun _ : Fin 2 => (1 : ℚ)) (![0, 0] : Fin 2 → ℚ)).get = [0, 0]
#guard List.ofFn (rationalGaussianCompressVector
  (fun i : Fin 0 => Fin.elim0 i) (![1/3, 2/3] : Fin 2 → ℚ)).get = [1, 0]
#guard List.ofFn (rationalGaussianCompressVector
  (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℚ)) (![1/3] : Fin 1 → ℚ)).get = [1/3]
#guard List.ofFn (rationalGaussianCompressVector
  (fun _ : Fin 1 => fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)).get = []
#guard rationalCanonicalEncodingBits ((rationalGaussianCompressVector
  (fun _ : Fin 1 => fun _ : Fin 2 => (1 : ℚ)) (![1/3, 2/3] : Fin 2 → ℚ)).get 0) = 3
