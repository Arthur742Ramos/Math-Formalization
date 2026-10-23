module
public import KnasterReichbach.MatchedPartitions

public section
namespace KnasterReichbach

open MatchedPartition

noncomputable def partitions {A B : Set CantorSpace} (h : A ≃ₜ B)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B) :
    ℕ → MatchedPartition h
  | 0 => MatchedPartition.trivial h
  | n + 1 => ((partitions h hA hnA hB hnB n).step hA hnA hB hnB n).partition

theorem partitions_prefix {A B : Set CantorSpace} (h : A ≃ₜ B)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B)
    (n : ℕ) :
    (partitions h hA hnA hB hnB n).LeftPrefix n ∧
    (partitions h hA hnA hB hnB n).RightPrefix n := by
  induction n with
  | zero =>
    exact (partitions h hA hnA hB hnB 0).prefix_zero
  | succ n ih =>
    exact (partitions h hA hnA hB hnB n).step_prefix hA hnA hB hnB ih.1 ih.2

/-- Construct the compatible relations by alternating source and target
coordinate splits. No refinement-existence hypothesis is supplied externally. -/
noncomputable def extensionRelations {A B : Set CantorSpace} (h : A ≃ₜ B)
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B) :
    CompatibleRelations where
  relation n := (partitions h hA hnA hB hnB n).relation
  closed n := (partitions h hA hnA hB hnB n).relation_closed
  nested := antitone_nat_of_succ_le (fun n =>
    ((partitions h hA hnA hB hnB n).step hA hnA hB hnB n).relation_subset)
  total n := (partitions h hA hnA hB hnB n).relation_total
  onto n := (partitions h hA hnA hB hnB n).relation_onto
  right_prefix n _ _ _ hy hz := (partitions h hA hnA hB hnB n).relation_right_prefix
    (partitions_prefix h hA hnA hB hnB n).2 hy hz
  left_prefix n _ _ _ hy hz := (partitions h hA hnA hB hnB n).relation_left_prefix
    (partitions_prefix h hA hnA hB hnB n).1 hy hz

/-- **Knaster–Reichbach extension theorem for Cantor space.** Every prescribed
homeomorphism between closed nowhere-dense subsets extends to an ambient
homeomorphism. No nonemptiness assumption is imposed on either subset. -/
theorem exists_homeomorph_extension {A B : Set CantorSpace}
    (hA : IsClosed A) (hnA : IsNowhereDense A) (hB : IsClosed B) (hnB : IsNowhereDense B)
    (h : A ≃ₜ B) :
    ∃ H : CantorSpace ≃ₜ CantorSpace, ∀ a : A, H a.val = (h a).val := by
  let R := extensionRelations h hA hnA hB hnB
  refine ⟨R.homeomorph, ?_⟩
  exact R.homeomorph_agrees h (fun n a =>
    (partitions h hA hnA hB hnB n).relation_trace a)

end KnasterReichbach
