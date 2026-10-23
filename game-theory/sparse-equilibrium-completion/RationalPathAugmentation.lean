/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Actual rational edge updates composed along a
simple finite path, with exact divergence and a genuine nonempty minimum.
No augmentation finder, termination, complexity or compiled-proof claim. -/
module
public import RationalEdgePush
public import CachedResidualSimplePaths
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Execute the tail updates first, then the head edge. Public eliminators
avoid new private matcher helpers. Each branch still executes the actual edge
update; commutativity is not assumed in the definition. -/
def rationalNetPushPath {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) : Fin n → Fin n → ℚ :=
  List.rec (motive := fun _ => Fin n → Fin n → Fin n → ℚ)
    (fun _ => F)
    (fun b _ ih start => rationalNetPushEdge (ih b) start b δ) tail a

def rationalPathEnd {n : ℕ} (a : Fin n) (tail : List (Fin n)) : Fin n :=
  List.rec (motive := fun _ => Fin n → Fin n) (fun start => start)
    (fun b _ ih _ => ih b) tail a

/-- One original residual value for every actual consecutive edge. -/
def rationalPathResiduals {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) : List ℚ :=
  List.rec (motive := fun _ => Fin n → List ℚ) (fun _ => [])
    (fun b _ ih start => (C start b - F start b) :: ih b) tail a

theorem rational_net_push_path_nil {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a : Fin n) (δ : ℚ) : rationalNetPushPath F a [] δ = F := rfl

theorem rational_net_push_path_cons {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (tail : List (Fin n)) (δ : ℚ) :
    rationalNetPushPath F a (b :: tail) δ =
      rationalNetPushEdge (rationalNetPushPath F b tail δ) a b δ := rfl

theorem rational_path_end_nil {n : ℕ} (a : Fin n) : rationalPathEnd a [] = a := rfl

theorem rational_path_end_cons {n : ℕ} (a b : Fin n) (tail : List (Fin n)) :
    rationalPathEnd a (b :: tail) = rationalPathEnd b tail := rfl

theorem rational_path_residuals_nil {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (a : Fin n) : rationalPathResiduals C F a [] = [] := rfl

theorem rational_path_residuals_cons {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (a b : Fin n) (tail : List (Fin n)) :
    rationalPathResiduals C F a (b :: tail) =
      (C a b - F a b) :: rationalPathResiduals C F b tail := rfl

theorem rational_path_end_getLast {n : ℕ} (a : Fin n) (tail : List (Fin n)) :
    (a :: tail).getLast? = some (rationalPathEnd a tail) := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    simpa only [List.getLast?_cons_cons, rational_path_end_cons] using ih b

/-- An update cannot touch a row whose label never occurs in the path. This
earns the capacity induction's noninterference, rather than assuming disjoint
edge effects or a special orientation of the capacity matrix. -/
theorem rational_net_push_path_away_left {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) (u v : Fin n)
    (hu : u ∉ a :: tail) : rationalNetPushPath F a tail δ u v = F u v := by
  revert hu
  induction tail generalizing a with
  | nil => intro hu; rfl
  | cons b tail ih =>
    intro hu
    have hua : u ≠ a := by
      intro h
      exact hu (List.mem_cons.mpr (Or.inl h))
    have hub : u ≠ b := by
      intro h
      exact hu (List.mem_cons_of_mem a (List.mem_cons.mpr (Or.inl h)))
    have hut : u ∉ b :: tail := by
      intro h
      exact hu (List.mem_cons_of_mem a h)
    rw [rational_net_push_path_cons,
      rational_net_push_edge_other _ a b δ u v
        (fun h => hua h.1) (fun h => hub h.1)]
    exact ih b hut

theorem rational_net_push_path_skew {n : ℕ} (F : Fin n → Fin n → ℚ)
    (hF : ∀ u v, F u v = -F v u) (a : Fin n)
    (tail : List (Fin n)) (δ : ℚ) :
    ∀ u v, rationalNetPushPath F a tail δ u v =
      -rationalNetPushPath F a tail δ v u := by
  induction tail generalizing a with
  | nil => exact hF
  | cons b tail ih =>
    rw [rational_net_push_path_cons]
    exact rational_net_push_edge_skew _ (ih b) a b δ

/-- All original capacities are preserved. Simplicity ensures that the
already executed tail cannot have consumed the current head edge's room. -/
theorem rational_net_push_path_capacity {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (hF : ∀ u v, F u v ≤ C u v) (a : Fin n) (tail : List (Fin n))
    (δ : ℚ) (hδ : 0 ≤ δ) (hnd : (a :: tail).Nodup)
    (hroom : ∀ z ∈ rationalPathResiduals C F a tail, δ ≤ z) :
    ∀ u v, rationalNetPushPath F a tail δ u v ≤ C u v := by
  revert hnd hroom
  induction tail generalizing a with
  | nil => intro hnd hroom; exact hF
  | cons b tail ih =>
    intro hnd hroom
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    have hab : a ≠ b := by
      intro h
      exact ha (List.mem_cons.mpr (Or.inl h))
    have htail : ∀ z ∈ rationalPathResiduals C F b tail, δ ≤ z := by
      intro z hz
      exact hroom z (List.mem_cons_of_mem _ hz)
    have hhead : δ ≤ C a b - F a b := hroom _ List.mem_cons_self
    have hG := ih b ht htail
    have hunused : rationalNetPushPath F b tail δ a b = F a b :=
      rational_net_push_path_away_left F b tail δ a b ha
    rw [rational_net_push_path_cons]
    apply rational_net_push_edge_capacity C _ hG a b hab δ hδ
    rw [hunused]
    exact hhead

/-- Cancellation of internal incidences is exact, even for a nonsimple list.
Simplicity is needed for capacity, not for this algebraic telescoping law. -/
theorem rational_net_push_path_divergence {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) (u : Fin n) :
    (∑ v, rationalNetPushPath F a tail δ u v) =
      (∑ v, F u v) + (if u = a then δ else 0) -
        (if u = rationalPathEnd a tail then δ else 0) := by
  induction tail generalizing a with
  | nil =>
    by_cases hua : u = a <;> simp [rational_net_push_path_nil, rational_path_end_nil, hua]
  | cons b tail ih =>
    rw [rational_net_push_path_cons, rational_net_push_edge_divergence,
      ih b, rational_path_end_cons]
    ring

theorem rational_net_push_path_conservation {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) (u : Fin n)
    (hua : u ≠ a) (hut : u ≠ rationalPathEnd a tail) :
    (∑ v, rationalNetPushPath F a tail δ u v) = ∑ v, F u v := by
  rw [rational_net_push_path_divergence]
  simp only [ite_eq_right hua, ite_eq_right hut, add_zero, sub_zero]

theorem rational_net_push_path_source_value {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ)
    (hat : a ≠ rationalPathEnd a tail) :
    (∑ v, rationalNetPushPath F a tail δ a v) = (∑ v, F a v) + δ := by
  rw [rational_net_push_path_divergence]
  simp [hat]

/-- The minimum of an empty collection is absent. No artificial cap such as
min(1,residual) is inserted: Some δ is an attained original residual value. -/
def rationalNonemptyMinimum (xs : List ℚ) : Option ℚ :=
  List.rec none (fun z _ ih => some (Option.rec z (fun b => min z b) ih)) xs

theorem rational_nonempty_minimum_none_iff (xs : List ℚ) :
    rationalNonemptyMinimum xs = none ↔ xs = [] := by
  cases xs with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons z zs =>
    constructor
    · intro h
      change some _ = none at h
      cases h
    · intro h
      cases h

theorem rational_nonempty_minimum_exists (xs : List ℚ) (hne : xs ≠ []) :
    ∃ δ, rationalNonemptyMinimum xs = some δ := by
  cases hm : rationalNonemptyMinimum xs with
  | none => exact False.elim (hne ((rational_nonempty_minimum_none_iff xs).mp hm))
  | some δ => exact ⟨δ, rfl⟩

theorem rational_nonempty_minimum_some (xs : List ℚ) (δ : ℚ)
    (ho : rationalNonemptyMinimum xs = some δ) :
    δ ∈ xs ∧ ∀ z ∈ xs, δ ≤ z := by
  revert ho
  induction xs generalizing δ with
  | nil => intro ho; cases ho
  | cons z zs ih =>
    intro ho
    cases ht : rationalNonemptyMinimum zs with
    | none =>
      change some (Option.rec z (fun b => min z b) (rationalNonemptyMinimum zs)) = some δ at ho
      rw [ht] at ho
      have hz : z = δ := Option.some.inj ho
      have hnil : zs = [] := (rational_nonempty_minimum_none_iff zs).mp ht
      subst zs
      subst δ
      exact ⟨List.mem_cons_self, by simp⟩
    | some b =>
      obtain ⟨hbmem, hble⟩ := ih b ht
      change some (Option.rec z (fun b => min z b) (rationalNonemptyMinimum zs)) = some δ at ho
      rw [ht] at ho
      have he : min z b = δ := Option.some.inj ho
      by_cases hzb : z ≤ b
      · rw [min_eq_left hzb] at he
        subst δ
        constructor
        · exact List.mem_cons_self
        · intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst w; exact le_rfl
          · exact le_trans hzb (hble w hw)
      · have hbz : b ≤ z := le_of_lt (lt_of_not_ge hzb)
        rw [min_eq_right hbz] at he
        subst δ
        constructor
        · exact List.mem_cons_of_mem z hbmem
        · intro w hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst w; exact hbz
          · exact hble w hw

theorem rational_nonempty_minimum_positive (xs : List ℚ) (δ : ℚ)
    (ho : rationalNonemptyMinimum xs = some δ)
    (hpos : ∀ z ∈ xs, 0 < z) : 0 < δ := by
  exact hpos δ (rational_nonempty_minimum_some xs δ ho).1

def rationalPathBottleneck {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) : Option ℚ :=
  rationalNonemptyMinimum (rationalPathResiduals C F a tail)

/-- A positive-residual simple path supplies an actual positive executable
push preserving all capacities and internal divergences. This is a local
augmentation theorem, not existence or termination of a complete flow finder. -/
theorem rational_path_bottleneck_augmentation {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (hF : ∀ u v, F u v ≤ C u v)
    (hskew : ∀ u v, F u v = -F v u) (a : Fin n) (tail : List (Fin n))
    (hnd : (a :: tail).Nodup) (δ : ℚ)
    (ho : rationalPathBottleneck C F a tail = some δ)
    (hpos : ∀ z ∈ rationalPathResiduals C F a tail, 0 < z) :
    0 < δ ∧
    (∀ u v, rationalNetPushPath F a tail δ u v =
      -rationalNetPushPath F a tail δ v u) ∧
    (∀ u v, rationalNetPushPath F a tail δ u v ≤ C u v) ∧
    (∀ u, u ≠ a → u ≠ rationalPathEnd a tail →
      (∑ v, rationalNetPushPath F a tail δ u v) = ∑ v, F u v) := by
  have hmin := rational_nonempty_minimum_some
    (rationalPathResiduals C F a tail) δ ho
  have hδ : 0 < δ := hpos δ hmin.1
  exact ⟨hδ, rational_net_push_path_skew F hskew a tail δ,
    rational_net_push_path_capacity C F hF a tail δ (le_of_lt hδ) hnd hmin.2,
    fun u hua hut => rational_net_push_path_conservation F a tail δ u hua hut⟩

end SparseCompletion
