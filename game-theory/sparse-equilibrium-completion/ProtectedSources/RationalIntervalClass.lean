/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalModel
public import ProtectedSources.RationalRepertoire
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

abbrev IntervalGameData (k m : ℕ) := (Fin m → ℝ) ×
  ((Fin m → Fin k → ℝ) × ((Fin k → Fin k → ℝ) × (Fin m → Fin m → ℝ)))

def intervalGamePhysical {k m : ℕ} (z : IntervalGameData k m) :
    Fin (m+(m*k+(k*k+0*m))) → ℝ :=
  intervalPack z.1 (fun i a => z.1 i*z.2.1 i a) z.2.2.1 (H := 0) Fin.elim0

theorem interval_game_physical_continuous {k m : ℕ}
    (j : Fin (m+(m*k+(k*k+0*m)))) :
    Continuous (fun z : IntervalGameData k m => intervalGamePhysical z j) := by
  unfold intervalGamePhysical intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with i | v
  · dsimp only [Sum.elim_inl]
    fun_prop
  · rcases v with v | v
    · dsimp only [Sum.elim_inr,Sum.elim_inl]
      fun_prop
    · rcases v with v | v
      · dsimp only [Sum.elim_inr,Sum.elim_inl]
        fun_prop
      · exact Fin.elim0 v.1

def intervalGameBox {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I) :
    Set (IntervalGameData k m) :=
  Set.Icc (fun _ => 0) (fun _ => (d.r : ℝ)) ×ˢ
    (Set.Icc (fun i a => (d.lo i a : ℝ)) (fun i a => (d.hi i a : ℝ)) ×ˢ
      (Set.Icc (fun a b => (d.loK a b : ℝ)) (fun a b => (d.hiK a b : ℝ)) ×ˢ skewBox d.M))

def intervalGameClass {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I) :
    Set (IntervalGameData k m) :=
  intervalGameBox d ∩ {z | (∑ i, z.1 i)=(d.r : ℝ) ∧ IsSkew z.2.2.1 ∧
    d.R.RealSatisfies (intervalGamePhysical z)}

theorem interval_game_class_compact {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) : IsCompact (intervalGameClass d) := by
  have hc : IsCompact (intervalGameBox d) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (skewBox_compact d.M)))
  apply hc.inter_right
  have he : {z : IntervalGameData k m | (∑ i, z.1 i)=(d.r : ℝ) ∧ IsSkew z.2.2.1 ∧
      d.R.RealSatisfies (intervalGamePhysical z)}=
    {z | (∑ i, z.1 i)=(d.r : ℝ)} ∩
      ((⋂ a, ⋂ b, {z | z.2.2.1 a b= -z.2.2.1 b a}) ∩
        (⋂ row, {z | (∑ j, (d.R.coefficient row j : ℝ)*intervalGamePhysical z j) ≤ (d.R.rightSide row : ℝ)})) := by
    ext z
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter,IsSkew,RationalLinearSystem.RealSatisfies]
  rw [he]
  exact (isClosed_eq (by fun_prop) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (by fun_prop) (by fun_prop)).inter
      (isClosed_iInter fun row => isClosed_le
        (continuous_finsetSum _ fun j _ => continuous_const.mul (interval_game_physical_continuous j)) continuous_const))

theorem interval_game_class_nonempty {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) : (intervalGameClass d).Nonempty := by
  obtain ⟨q,K,D,B,hq,hr,hK,hKb,hD,hB,hBb,hR⟩ := d.compatibleNonempty
  refine ⟨(q,D,K,B),⟨⟨hq,?_⟩,⟨fun i a => (hD i a).1,fun i a => (hD i a).2⟩,
    ⟨fun a b => (hKb a b).1,fun a b => (hKb a b).2⟩,hB,hBb⟩,hr,hK,hR⟩
  intro i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hq j)
    (Finset.mem_univ i)
  rwa [hr] at hi

end
end SparseCompletion
