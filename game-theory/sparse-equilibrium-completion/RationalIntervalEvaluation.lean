/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalPoint
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem interval_q_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (i : Fin m) :
    rationalFormEval (intervalQForm k m H i) x=intervalQ x i := by
  exact interval_basis_eval _ x

theorem interval_q_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (i : Fin m) :
    rationalFormRealEval (intervalQForm k m H i) x=intervalQ x i := by
  exact interval_basis_real_eval _ x

theorem interval_v_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (i : Fin m) (a : Fin k) :
    rationalFormEval (intervalVForm k m H i a) x=intervalV x i a := by
  exact interval_basis_eval _ x

theorem interval_v_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (i : Fin m) (a : Fin k) :
    rationalFormRealEval (intervalVForm k m H i a) x=intervalV x i a := by
  exact interval_basis_real_eval _ x

theorem interval_k_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (a b : Fin k) :
    rationalFormEval (intervalKForm k m H a b) x=intervalK x a b := by
  exact interval_basis_eval _ x

theorem interval_k_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (a b : Fin k) :
    rationalFormRealEval (intervalKForm k m H a b) x=intervalK x a b := by
  exact interval_basis_real_eval _ x

theorem interval_aux_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (l : Fin H) (i : Fin m) :
    rationalFormEval (intervalAuxForm k m H l i) x=intervalAux x l i := by
  exact interval_basis_eval _ x

theorem interval_aux_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (l : Fin H) (i : Fin m) :
    rationalFormRealEval (intervalAuxForm k m H l i) x=intervalAux x l i := by
  exact interval_basis_real_eval _ x

end SparseCompletion
