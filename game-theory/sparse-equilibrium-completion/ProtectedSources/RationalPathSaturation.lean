/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Exact incidence of a simple path update and
saturation of an edge attaining its genuine bottleneck. This does not assert
termination or an iteration count for repeated augmentations. -/
module
public import ProtectedSources.RationalPathAugmentation
@[expose] public section
namespace SparseCompletion

def rationalPathEdges {n : ℕ} (a : Fin n) (tail : List (Fin n)) :
    List (Fin n × Fin n) :=
  List.rec (motive := fun _ => Fin n → List (Fin n × Fin n)) (fun _ => [])
    (fun b _ ih start => (start, b) :: ih b) tail a

theorem rational_path_edges_nil {n : ℕ} (a : Fin n) : rationalPathEdges a [] = [] := rfl

theorem rational_path_edges_cons {n : ℕ} (a b : Fin n) (tail : List (Fin n)) :
    rationalPathEdges a (b :: tail) = (a, b) :: rationalPathEdges b tail := rfl

theorem rational_path_edges_endpoints {n : ℕ} (a : Fin n) (tail : List (Fin n))
    (u v : Fin n) (he : (u, v) ∈ rationalPathEdges a tail) :
    u ∈ a :: tail ∧ v ∈ a :: tail := by
  revert he
  induction tail generalizing a with
  | nil => intro he; cases he
  | cons b tail ih =>
    intro he
    rcases List.mem_cons.mp he with he | he
    · have hu : u = a := congrArg Prod.fst he
      have hv : v = b := congrArg Prod.snd he
      subst u
      subst v
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem a List.mem_cons_self⟩
    · obtain ⟨hu, hv⟩ := ih b he
      exact ⟨List.mem_cons_of_mem a hu, List.mem_cons_of_mem a hv⟩

theorem rational_path_residuals_map {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) :
    rationalPathResiduals C F a tail =
      (rationalPathEdges a tail).map (fun e => C e.1 e.2 - F e.1 e.2) := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    simp only [rational_path_residuals_cons, rational_path_edges_cons, List.map_cons, ih b]

/-- A simple path has exactly one forward update on each of its directed
edges. Neither another forward occurrence nor a reverse occurrence can cancel
it, since the head vertex is absent from the tail. -/
theorem rational_net_push_path_edge_forward {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ) (hnd : (a :: tail).Nodup)
    (u v : Fin n) (he : (u, v) ∈ rationalPathEdges a tail) :
    rationalNetPushPath F a tail δ u v = F u v + δ := by
  revert hnd he
  induction tail generalizing a with
  | nil => intro hnd he; cases he
  | cons b tail ih =>
    intro hnd he
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp he with he | he
    · have hu : u = a := congrArg Prod.fst he
      have hv : v = b := congrArg Prod.snd he
      subst u
      subst v
      have hab : a ≠ b := by
        intro h
        exact ha (List.mem_cons.mpr (Or.inl h))
      rw [rational_net_push_path_cons, rational_net_push_edge_forward _ a b hab δ,
        rational_net_push_path_away_left F b tail δ a b ha]
    · obtain ⟨hu, hv⟩ := rational_path_edges_endpoints b tail u v he
      have hua : u ≠ a := by
        intro h
        exact ha (h ▸ hu)
      have hva : v ≠ a := by
        intro h
        exact ha (h ▸ hv)
      rw [rational_net_push_path_cons,
        rational_net_push_edge_other _ a b δ u v
          (fun h => hua h.1) (fun h => hva h.2)]
      exact ih b ht he

/-- The computed minimum is attained by an actual path edge, and executing the
entire simple-path update saturates that same original capacity inequality. -/
theorem rational_path_bottleneck_saturates {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) (hnd : (a :: tail).Nodup) (δ : ℚ)
    (ho : rationalPathBottleneck C F a tail = some δ) :
    ∃ u v, (u, v) ∈ rationalPathEdges a tail ∧
      C u v - F u v = δ ∧ rationalNetPushPath F a tail δ u v = C u v := by
  have hmem := (rational_nonempty_minimum_some
    (rationalPathResiduals C F a tail) δ ho).1
  rw [rational_path_residuals_map] at hmem
  obtain ⟨e, he, hres⟩ := List.mem_map.mp hmem
  refine ⟨e.1, e.2, he, hres, ?_⟩
  rw [rational_net_push_path_edge_forward F a tail δ hnd e.1 e.2 he]
  linarith

end SparseCompletion
