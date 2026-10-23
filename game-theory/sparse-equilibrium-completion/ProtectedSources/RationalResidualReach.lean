/- AI-assisted formalization under the repository Apache-2.0 license.
Finite executable reachability layers on a Boolean adjacency function.
No stored-array representation or access-cost theorem is asserted. Correctness does not assume a reachability oracle. Predecessor/path
recovery and max-flow augmentation/complexity remain separate. -/
module
public import ProtectedSources.RationalSaturatedFlow
public import Mathlib.Logic.Relation
@[expose] public section
namespace SparseCompletion

/-- C-F is the residual bound for a net-flow representation. A raw nonnegative
arc-flow matrix must first be antisymmetrized; that bridge is separate. -/
def rationalResidualAdj {n : ℕ} (C F : Fin n → Fin n → ℚ) (u v : Fin n) : Bool :=
  decide (0 < C u v-F u v)

def residualReachStep {n : ℕ} (A : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ Finset.univ.filter (fun v => ∃ u ∈ S, A u v=true)

def residualReachLayers {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n)
    (k : ℕ) : Finset (Fin n) :=
  Nat.rec {s} (fun _ seen => residualReachStep A seen) k

theorem residual_reach_layers_zero {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n) :
    residualReachLayers A s 0={s} := rfl

theorem residual_reach_layers_succ {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n) (k : ℕ) :
    residualReachLayers A s (k+1)=residualReachStep A (residualReachLayers A s k) := rfl

theorem residual_reach_step_extensive {n : ℕ} (A : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) : S ⊆ residualReachStep A S := Finset.subset_union_left

theorem residual_reach_layers_mono {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n)
    {k l : ℕ} (hkl : k ≤ l) : residualReachLayers A s k ⊆ residualReachLayers A s l := by
  induction hkl with
  | refl => exact Finset.Subset.refl _
  | @step l h ih =>
    exact ih.trans (residual_reach_step_extensive A (residualReachLayers A s l))

theorem residual_reach_stable_or_large {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n)
    (k : ℕ) : residualReachStep A (residualReachLayers A s k)=residualReachLayers A s k ∨
      k+1 ≤ (residualReachLayers A s k).card := by
  induction k with
  | zero =>
    right
    simpa only [residual_reach_layers_zero,Finset.card_singleton] using (Nat.le_refl 1)
  | succ k ih =>
    by_cases hstable : residualReachStep A (residualReachLayers A s (k+1))=residualReachLayers A s (k+1)
    · exact Or.inl hstable
    · right
      have hprev : residualReachStep A (residualReachLayers A s k) ≠ residualReachLayers A s k := by
        intro he
        apply hstable
        rw [residual_reach_layers_succ,he]
        exact he
      have hlarge : k+1 ≤ (residualReachLayers A s k).card := ih.resolve_left hprev
      have hsub : residualReachLayers A s k ⊆ residualReachLayers A s (k+1) :=
        residual_reach_step_extensive A _
      have hne : residualReachLayers A s k ≠ residualReachLayers A s (k+1) := by
        intro he
        apply hprev
        exact he.symm
      have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
      omega

theorem residual_reach_layers_stable {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n) :
    residualReachStep A (residualReachLayers A s n)=residualReachLayers A s n := by
  rcases residual_reach_stable_or_large A s n with hs | hl
  · exact hs
  · have hb := (residualReachLayers A s n).card_le_univ
    simp only [Fintype.card_fin] at hb
    omega

theorem residual_reach_layers_closed {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n)
    (u v : Fin n) (hu : u ∈ residualReachLayers A s n) (he : A u v=true) :
    v ∈ residualReachLayers A s n := by
  rw [← residual_reach_layers_stable A s]
  apply Finset.mem_union_right
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,he⟩

theorem residual_reach_layers_sound {n : ℕ} (A : Fin n → Fin n → Bool) (s : Fin n)
    (k : ℕ) (v : Fin n) (hv : v ∈ residualReachLayers A s k) :
    Relation.ReflTransGen (fun u v => A u v=true) s v := by
  induction k generalizing v with
  | zero =>
    have he := Finset.mem_singleton.mp hv
    subst v
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    rcases Finset.mem_union.mp hv with hold | hnew
    · exact ih v hold
    · rcases (Finset.mem_filter.mp hnew).2 with ⟨u,hu,he⟩
      exact Relation.ReflTransGen.tail (ih u hu) he

theorem residual_reach_layers_complete {n : ℕ} (A : Fin n → Fin n → Bool) (s v : Fin n)
    (hv : Relation.ReflTransGen (fun u v => A u v=true) s v) :
    v ∈ residualReachLayers A s n := by
  have hs : s ∈ residualReachLayers A s n :=
    residual_reach_layers_mono A s (Nat.zero_le n) (Finset.mem_singleton_self s)
  induction hv with
  | refl => exact hs
  | @tail u v _ he ih => exact residual_reach_layers_closed A s u v ih he

theorem residual_reach_layers_iff {n : ℕ} (A : Fin n → Fin n → Bool) (s v : Fin n) :
    v ∈ residualReachLayers A s n ↔ Relation.ReflTransGen (fun u v => A u v=true) s v :=
  ⟨residual_reach_layers_sound A s n v,residual_reach_layers_complete A s v⟩

end SparseCompletion
