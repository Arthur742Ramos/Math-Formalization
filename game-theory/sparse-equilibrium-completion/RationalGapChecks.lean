/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalGap
public meta import RationalGap
@[expose] public section
namespace SparseCompletion
#guard checkRationalGap (fun _ _ : Fin 1 => (0 : ℚ)) (fun (_ : Fin 0) (_ : Fin 1) => (0 : ℚ))
  (fun _ : Fin 1 => (1 : ℚ)) (fun _ : Fin 0 => (0 : ℚ)) 1 0 0 (1/100) = true
#guard checkRationalGap (fun _ _ : Fin 1 => (0 : ℚ)) (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ))
  (fun _ : Fin 1 => (1 : ℚ)) (fun _ : Fin 1 => (0 : ℚ)) 1 0 0 (1/100) = false
end SparseCompletion
