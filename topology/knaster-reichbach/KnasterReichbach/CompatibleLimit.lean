module
public import KnasterReichbach.Cylinders
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Maps.Proper.Basic

public section

namespace KnasterReichbach

/-- Finite matched clopen partitions will supply these closed approximating
relations. Bi-totality and control in both directions are required explicitly. -/
structure CompatibleRelations where
  relation : ℕ → Set (CantorSpace × CantorSpace)
  closed : ∀ n, IsClosed (relation n)
  nested : Antitone relation
  total : ∀ n x, ∃ y, (x, y) ∈ relation n
  onto : ∀ n y, ∃ x, (x, y) ∈ relation n
  right_prefix : ∀ n x y z, (x, y) ∈ relation n → (x, z) ∈ relation n →
    ∀ i < n, y i = z i
  left_prefix : ∀ n x y z, (y, x) ∈ relation n → (z, x) ∈ relation n →
    ∀ i < n, y i = z i

namespace CompatibleRelations

def symm (R : CompatibleRelations) : CompatibleRelations where
  relation n := Prod.swap ⁻¹' R.relation n
  closed n := (R.closed n).preimage continuous_swap
  nested := fun _ _ h _ hz => R.nested h hz
  total := R.onto
  onto := R.total
  right_prefix := R.left_prefix
  left_prefix := R.right_prefix

theorem exists_limit (R : CompatibleRelations) (x : CantorSpace) :
    ∃ y, ∀ n, (x, y) ∈ R.relation n := by
  let F : ℕ → Set CantorSpace := fun n => {y | (x, y) ∈ R.relation n}
  have hclosed (n : ℕ) : IsClosed (F n) :=
    (R.closed n).preimage (continuous_const.prodMk continuous_id)
  have hnonempty (n : ℕ) : (F n).Nonempty := R.total n x
  have hnested : Antitone F := fun _ _ h _ hz => R.nested h hz
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F (fun n => hnested (Nat.le_succ n)) hnonempty (hclosed 0).isCompact hclosed
  exact ⟨y, fun n => Set.mem_iInter.mp hy n⟩

noncomputable def limit (R : CompatibleRelations) (x : CantorSpace) : CantorSpace :=
  Classical.choose (R.exists_limit x)

theorem limit_mem (R : CompatibleRelations) (x : CantorSpace) (n : ℕ) :
    (x, R.limit x) ∈ R.relation n :=
  Classical.choose_spec (R.exists_limit x) n

theorem limit_unique (R : CompatibleRelations) {x y : CantorSpace}
    (hy : ∀ n, (x, y) ∈ R.relation n) : y = R.limit x := by
  funext i
  exact R.right_prefix (i + 1) x y (R.limit x) (hy _) (R.limit_mem x _) i
    (Nat.lt_succ_self i)

theorem left_inverse (R : CompatibleRelations) :
    Function.LeftInverse R.symm.limit R.limit := by
  intro x
  exact (R.symm.limit_unique (fun n => R.limit_mem x n)).symm

theorem continuous_limit (R : CompatibleRelations) : Continuous R.limit := by
  apply continuous_of_isClosed_graph
  have heq : R.limit.graph = ⋂ n, R.relation n := by
    ext p
    constructor
    · intro hp
      have hp' : R.limit p.1 = p.2 := hp
      apply Set.mem_iInter.mpr
      intro n
      simpa only [hp'] using R.limit_mem p.1 n
    · intro hp
      exact (R.limit_unique (Set.mem_iInter.mp hp)).symm
  rw [heq]
  exact isClosed_iInter R.closed

/-- The inverse-limit step of the extension construction. This does not assert
that relations extending a prescribed partial homeomorphism already exist. -/
noncomputable def homeomorph (R : CompatibleRelations) : CantorSpace ≃ₜ CantorSpace where
  toFun := R.limit
  invFun := R.symm.limit
  left_inv := R.left_inverse
  right_inv := by
    intro y
    exact (R.limit_unique (fun n => R.symm.limit_mem y n)).symm
  continuous_toFun := R.continuous_limit
  continuous_invFun := R.symm.continuous_limit

theorem homeomorph_agrees (R : CompatibleRelations) {A B : Set CantorSpace}
    (h : A ≃ₜ B) (hR : ∀ n (a : A), (a.val, (h a).val) ∈ R.relation n) (a : A) :
    R.homeomorph a.val = (h a).val :=
  (R.limit_unique (fun n => hR n a)).symm

end CompatibleRelations
end KnasterReichbach
