/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalGap
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalVariable (k m H : ℕ) :=
  Fin m ⊕ ((Fin m × Fin k) ⊕ ((Fin k × Fin k) ⊕ (Fin H × Fin m)))

def rationalIntervalVariableEquiv (k m H : ℕ) :
    RationalIntervalVariable k m H ≃ Fin (m+(m*k+(k*k+H*m))) :=
  (Equiv.sumCongr (Equiv.refl (Fin m))
    ((Equiv.sumCongr (finProdFinEquiv (m := m) (n := k))
      ((Equiv.sumCongr (finProdFinEquiv (m := k) (n := k))
        (finProdFinEquiv (m := H) (n := m))).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
          finSumFinEquiv

def intervalVariableDecode {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (v : RationalIntervalVariable k m H) : α :=
  x (rationalIntervalVariableEquiv k m H v)

def intervalVariableEncode {α : Type*} {k m H : ℕ}
    (f : RationalIntervalVariable k m H → α) (u : Fin (m+(m*k+(k*k+H*m)))) : α :=
  f ((rationalIntervalVariableEquiv k m H).symm u)

theorem interval_variable_decode_encode {α : Type*} {k m H : ℕ}
    (f : RationalIntervalVariable k m H → α) :
    intervalVariableDecode (intervalVariableEncode f)=f := by
  funext v
  exact congrArg f ((rationalIntervalVariableEquiv k m H).symm_apply_apply v)

theorem interval_variable_encode_decode {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) :
    intervalVariableEncode (intervalVariableDecode x)=x := by
  funext u
  exact congrArg x ((rationalIntervalVariableEquiv k m H).apply_symm_apply u)

end SparseCompletion
