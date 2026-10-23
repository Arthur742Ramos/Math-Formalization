/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalVariables
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def intervalBasis {k m H : ℕ} (v : RationalIntervalVariable k m H)
    (u : Fin (m+(m*k+(k*k+H*m)))) : ℚ :=
  if u=rationalIntervalVariableEquiv k m H v then 1 else 0

def intervalQ {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (i : Fin m) : α := intervalVariableDecode x (.inl i)
def intervalV {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (i : Fin m) (a : Fin k) : α :=
  intervalVariableDecode x (.inr (.inl (i,a)))
def intervalK {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (a b : Fin k) : α :=
  intervalVariableDecode x (.inr (.inr (.inl (a,b))))
def intervalAux {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) (l : Fin H) (i : Fin m) : α :=
  intervalVariableDecode x (.inr (.inr (.inr (l,i))))

theorem interval_basis_eval {k m H : ℕ} (v : RationalIntervalVariable k m H)
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) :
    (∑ u, intervalBasis v u*x u)=intervalVariableDecode x v := by
  simp only [intervalBasis,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    intervalVariableDecode]

theorem interval_basis_real_eval {k m H : ℕ} (v : RationalIntervalVariable k m H)
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) :
    (∑ u, (intervalBasis v u : ℝ)*x u)=intervalVariableDecode x v := by
  calc
    _ = ∑ u, if u=rationalIntervalVariableEquiv k m H v then x u else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : u=rationalIntervalVariableEquiv k m H v <;> simp [intervalBasis,h]
    _ = _ := by
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,intervalVariableDecode]

end SparseCompletion
