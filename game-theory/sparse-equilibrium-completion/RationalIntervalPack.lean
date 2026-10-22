/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalSystemPoint
@[expose] public section
namespace SparseCompletion

def intervalPack {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    Fin (m+(m*k+(k*k+H*m))) → α :=
  intervalVariableEncode (Sum.elim q (Sum.elim (fun v => V v.1 v.2)
    (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))))

theorem interval_pack_q {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalQ (intervalPack q V K A)=q := by
  funext i
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

theorem interval_pack_v {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalV (intervalPack q V K A)=V := by
  funext i a
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

theorem interval_pack_k {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalK (intervalPack q V K A)=K := by
  funext a b
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

theorem interval_pack_aux {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalAux (intervalPack q V K A)=A := by
  funext l i
  exact congrArg
    (fun v : RationalIntervalVariable k m H =>
      Sum.elim q (Sum.elim (fun v => V v.1 v.2)
        (Sum.elim (fun v => K v.1 v.2) (fun v => A v.1 v.2))) v)
    ((rationalIntervalVariableEquiv k m H).symm_apply_apply _)

end SparseCompletion
