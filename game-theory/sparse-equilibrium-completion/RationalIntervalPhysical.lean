/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalRealSolver
@[expose] public section
namespace SparseCompletion

def intervalPhysicalEmbed {k m H : ℕ} :
    RationalIntervalVariable k m 0 → RationalIntervalVariable k m H :=
  Sum.elim Sum.inl (Sum.elim (fun v => Sum.inr (Sum.inl v))
    (Sum.elim (fun v => Sum.inr (Sum.inr (Sum.inl v))) (fun v => Fin.elim0 v.1)))

def intervalPhysicalVector {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) : Fin (m+(m*k+(k*k+0*m))) → α :=
  fun j => intervalVariableDecode x (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm j))

def intervalPhysicalForm (k m H : ℕ) (j : Fin (m+(m*k+(k*k+0*m)))) :
    Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm j))

theorem interval_physical_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℚ) (j : Fin (m+(m*k+(k*k+0*m)))) :
    rationalFormEval (intervalPhysicalForm k m H j) x=intervalPhysicalVector x j :=
  interval_basis_eval _ x

theorem interval_physical_real_form_eval {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → ℝ) (j : Fin (m+(m*k+(k*k+0*m)))) :
    rationalFormRealEval (intervalPhysicalForm k m H j) x=intervalPhysicalVector x j :=
  interval_basis_real_eval _ x

theorem interval_physical_pack {α : Type*} {k m H : ℕ} (q : Fin m → α)
    (V : Fin m → Fin k → α) (K : Fin k → Fin k → α) (A : Fin H → Fin m → α) :
    intervalPhysicalVector (intervalPack q V K A)=intervalPack q V K (H := 0) Fin.elim0 := by
  funext j
  obtain ⟨v,rfl⟩ := (rationalIntervalVariableEquiv k m 0).surjective j
  change intervalVariableDecode (intervalPack q V K A)
    (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm
      ((rationalIntervalVariableEquiv k m 0) v)))=
    intervalVariableDecode (intervalPack q V K (H := 0) Fin.elim0) v
  refine (congrArg
    (fun w : RationalIntervalVariable k m 0 => intervalVariableDecode (intervalPack q V K A)
      (intervalPhysicalEmbed w))
    ((rationalIntervalVariableEquiv k m 0).symm_apply_apply v)).trans ?_
  rcases v with i | v
  · exact congrFun (interval_pack_q q V K A) i |>.trans
      (congrFun (interval_pack_q q V K (H := 0) Fin.elim0) i).symm
  · rcases v with v | v
    · exact congrFun (congrFun (interval_pack_v q V K A) v.1) v.2 |>.trans
        (congrFun (congrFun (interval_pack_v q V K (H := 0) Fin.elim0) v.1) v.2).symm
    · rcases v with v | v
      · exact congrFun (congrFun (interval_pack_k q V K A) v.1) v.2 |>.trans
          (congrFun (congrFun (interval_pack_k q V K (H := 0) Fin.elim0) v.1) v.2).symm
      · exact Fin.elim0 v.1

end SparseCompletion
