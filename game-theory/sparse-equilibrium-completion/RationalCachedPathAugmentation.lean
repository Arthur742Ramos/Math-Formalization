/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Connect the actual cached BFS result to a
positive bottleneck and the executed simple-path edge updates. This is one
augmentation, with no flow-finder termination or complexity claim. -/
module
public import RationalPathAugmentation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalWalkResiduals {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (path : List (Fin n)) : List ℚ :=
  List.rec [] (fun a tail _ => rationalPathResiduals C F a tail) path

theorem rational_walk_residuals_cons {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (a : Fin n) (tail : List (Fin n)) :
    rationalWalkResiduals C F (a :: tail) = rationalPathResiduals C F a tail := rfl

theorem rational_path_residuals_append_one {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (a : Fin n) (tail : List (Fin n)) (v : Fin n) :
    rationalPathResiduals C F a (tail ++ [v]) =
      rationalPathResiduals C F a tail ++
        [C (rationalPathEnd a tail) v - F (rationalPathEnd a tail) v] := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih =>
    simp only [List.cons_append, rational_path_residuals_cons,
      rational_path_end_cons, ih b]

/-- Every residual on a walk certified by the actual cached adjacency is
strictly positive. The source singleton has an empty residual list. -/
theorem cached_residual_walk_residuals_positive {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (s t : Fin n) (path : List (Fin n))
    (hw : CachedResidualWalk (cacheResidualAdj C F) s t path) :
    ∀ z ∈ rationalWalkResiduals C F path, 0 < z := by
  induction hw with
  | start =>
    intro z hz
    change z ∈ ([] : List ℚ) at hz
    cases hz
  | @extend u v walkPrefix hwalk hedge ih =>
    have hends := cached_residual_walk_endpoints (cacheResidualAdj C F) s u
      walkPrefix hwalk
    cases walkPrefix with
    | nil =>
      have he : (none : Option (Fin n)) = some s := hends.1
      cases he
    | cons a tail =>
      have hend : rationalPathEnd a tail = u := by
        have hlast : some (rationalPathEnd a tail) = some u := by
          rw [← rational_path_end_getLast]
          exact hends.2
        exact Option.some.inj hlast
      have hedge' : rationalResidualAdj C F u v = true := by
        change cachedBFSAdjFunction (cacheResidualAdj C F) u v = true at hedge
        rwa [cached_residual_adjacency_coherence] at hedge
      have hres : 0 < C u v - F u v := by
        simpa only [rationalResidualAdj, decide_eq_true_eq] using hedge'
      intro z hz
      change z ∈ rationalPathResiduals C F a (tail ++ [v]) at hz
      rw [rational_path_residuals_append_one] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact ih z hz
      · have hz : z = C (rationalPathEnd a tail) v -
            F (rationalPathEnd a tail) v := by
          simpa only [List.mem_singleton] using hz
        rw [hz, hend]
        exact hres

theorem rational_path_residuals_nonempty {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (a : Fin n) (tail : List (Fin n))
    (hat : a ≠ rationalPathEnd a tail) : rationalPathResiduals C F a tail ≠ [] := by
  cases tail with
  | nil => exact False.elim (hat rfl)
  | cons b tail =>
    change (C a b - F a b) :: rationalPathResiduals C F b tail ≠ []
    simp

/-- Actual source and sink labels, original residual capacities, and the
original cached path are retained. A distinct sink earns nonempty edges and
therefore a genuinely positive minimum; it is not an extra feasibility oracle.
The result executes one update, preserving all original capacity inequalities
and exactly the original internal conservation equations. -/
theorem cached_rational_path_augmentation {n : ℕ}
    (C F : Fin n → Fin n → ℚ)
    (hcap : ∀ u v, F u v ≤ C u v) (hskew : ∀ u v, F u v = -F v u)
    (s t : Fin n) (hst : s ≠ t) (tail : List (Fin n))
    (ho : cachedBFSPath (cacheResidualAdj C F) s t = some (s :: tail)) :
    ∃ δ, rationalPathBottleneck C F s tail = some δ ∧ 0 < δ ∧
      rationalPathEnd s tail = t ∧
      (∀ u v, rationalNetPushPath F s tail δ u v =
        -rationalNetPushPath F s tail δ v u) ∧
      (∀ u v, rationalNetPushPath F s tail δ u v ≤ C u v) ∧
      (∀ u, u ≠ s → u ≠ t →
        (∑ v, rationalNetPushPath F s tail δ u v) = ∑ v, F u v) ∧
      (∑ v, rationalNetPushPath F s tail δ s v) = (∑ v, F s v) + δ := by
  have hw := (cached_bfs_path_some_walk (cacheResidualAdj C F) s t (s :: tail) ho).1
  have hends := cached_residual_walk_endpoints (cacheResidualAdj C F) s t
    (s :: tail) hw
  have hend : rationalPathEnd s tail = t := by
    have he : some (rationalPathEnd s tail) = some t := by
      rw [← rational_path_end_getLast]
      exact hends.2
    exact Option.some.inj he
  have hat : s ≠ rationalPathEnd s tail := by simpa only [hend] using hst
  have hnd := cached_bfs_path_nodup (cacheResidualAdj C F) s t (s :: tail) ho
  have hpos : ∀ z ∈ rationalPathResiduals C F s tail, 0 < z :=
    cached_residual_walk_residuals_positive C F s t (s :: tail) hw
  obtain ⟨δ, hδ⟩ := rational_nonempty_minimum_exists
    (rationalPathResiduals C F s tail) (rational_path_residuals_nonempty C F s tail hat)
  have hbot : rationalPathBottleneck C F s tail = some δ := hδ
  obtain ⟨hpositive, hnewskew, hnewcap, hconserve⟩ :=
    rational_path_bottleneck_augmentation C F hcap hskew s tail hnd δ hbot hpos
  refine ⟨δ, hbot, hpositive, hend, hnewskew, hnewcap, ?_, ?_⟩
  · intro u hus hut
    apply hconserve u hus
    simpa only [hend] using hut
  · exact rational_net_push_path_source_value F s tail δ hat

end SparseCompletion
