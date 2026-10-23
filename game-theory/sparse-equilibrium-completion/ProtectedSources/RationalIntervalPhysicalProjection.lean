/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalRepertoireGame
@[expose] public section
namespace SparseCompletion

theorem interval_physical_projection {α : Type*} {k m H : ℕ}
    (x : Fin (m+(m*k+(k*k+H*m))) → α) :
    intervalPhysicalVector x=intervalPack (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0 := by
  funext j
  obtain ⟨v,rfl⟩ := (rationalIntervalVariableEquiv k m 0).surjective j
  change intervalVariableDecode x
    (intervalPhysicalEmbed ((rationalIntervalVariableEquiv k m 0).symm
      ((rationalIntervalVariableEquiv k m 0) v)))=
    intervalVariableDecode (intervalPack (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) v
  refine (congrArg
    (fun w : RationalIntervalVariable k m 0 => intervalVariableDecode x
      (intervalPhysicalEmbed w))
    ((rationalIntervalVariableEquiv k m 0).symm_apply_apply v)).trans ?_
  rcases v with i | v
  · exact (congrFun (interval_pack_q (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) i).symm
  · rcases v with v | v
    · exact (congrFun (congrFun (interval_pack_v (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) v.1) v.2).symm
    · rcases v with v | v
      · exact (congrFun (congrFun (interval_pack_k (intervalQ x) (intervalV x) (intervalK x) (H := 0) Fin.elim0) v.1) v.2).symm
      · exact Fin.elim0 v.1

end SparseCompletion
