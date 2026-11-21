module

public import UniformEdits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.OpenProblems

open Edit Finset Filter Residues
open scoped Classical Topology

set_option maxHeartbeats 700000 in
/-- Lemma 11. With probability tending to one, every admissible choice of target
rows and counts can be realized while preserving all registered exterior counts. -/
theorem simultaneous_adjustment : SimultaneousAdjustment := by
  classical
  intro u τ c θ hu hτ hc hθ hθ'
  obtain ⟨L₀,L₁,hL,ltL,short,long⟩ := two_lengths u τ c θ hu hτ hc hθ
  obtain ⟨β,w,bp,wp,w1,uniform⟩ := uniform_rows _ _ _ _ _ _ ltL short long
  obtain ⟨n₁,edits⟩ := editable_draws _ _ hL ltL θ hθ hθ'
  obtain ⟨a,ap,a1,rates⟩ := edit_rates L₁ w β wp w1 bp
  refine ⟨L₀,L₁,a,n₁,hL,ltL,ap,?_⟩
  intro power ε ep
  filter_upwards [uniform,total_failure_rate power β ε bp ep] with r estimate err
  intro N G B Y n ℓ core polynomial linear Xs ex data nshort nlong
  let len := fun i => (Xs i).length
  let F := fun i => tupleSpace (Xs i)
  let d := fun P y => tupleDegree (adj G) y P
  let pool := fun i ref => registered (F i) d (ex i) ref
  let cut := fun i => Real.exp (-budget (len i)*r)*(F i).card
  let lists := Fintype.piFinset fun _ : Fin ℓ => Y
  let init := fun i ref (ys : Fin ℓ → Fin N) =>
    ((profileFiber (pool i ref) (rowValues d ys) (rowValues d ys ref)).card:ℝ) < cut i/w^ℓ
  let bad := fun i ref (ys : Fin ℓ → Fin N) => ¬GoodRows (pool i ref) d (len i) θ w (cut i) (requiredTests L₀ (len i)) ys
  have bound (i x) (hx : x ∈ F i) (y) : d x y ≤ len i := (List.countP_le_length ..).trans (tuple_len hx).le
  have fpos (i) : 0 < ((F i).card:ℝ) := by
    have bp' := pos_of_mul_pos_left ((Real.exp_pos _).trans_le core.1) (Real.exp_pos _).le
    apply Nat.cast_pos.mpr
    apply card_pos.mpr
    apply tuples_nonempty (Xs i)
    intro X hx
    apply card_pos.mp
    exact_mod_cast (mul_pos bp' (Real.exp_pos _)).trans_le ((data i).1.2 X hx).1.2
  have term (i) := rates (len i) (ex i).length ℓ r
    (by rcases (data i).2.1 with h|h <;> dsimp [len] <;> omega) (data i).2.2 linear
  have pW := pow_pos wp ℓ
  have first (i ys) (_ : ys ∈ lists) :
      (((F i).filter (fun x => init i x ys)).card:ℝ) ≤ Real.exp (-(r:ℝ))*(F i).card := by
    have v := initial_profile_bound (F i) d (len i) (ex i) ys (bound i) (cut i/w^ℓ)
      (div_nonneg (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) pW.le)
    apply v.trans
    have h := mul_le_mul_of_nonneg_right (term i).1 (Nat.cast_nonneg (F i).card : (0:ℝ)≤_)
    dsimp [cut]
    convert h using 1; ring
  have second (i ref) (_ : ref ∈ F i) : ((lists.filter (bad i ref)).card:ℝ) ≤
      ((r:ℝ)*Real.exp (-(β/2)*r))*lists.card := by
    have sub : pool i ref ⊆ F i := registered_subset ..
    have prob := other_profile_bound (pool i ref) Y d (len i) ℓ θ w (cut i) (Real.exp (-β*r))
      (requiredTests L₀ (len i)) (mul_pos (Real.exp_pos _) (fpos i)) (Real.exp_pos _).le
      (fun x hx => bound i x (sub hx)) (fun Q hQ mass => estimate N G B Y (Xs i) Q core (data i).1
        (data i).2.1 (hQ.trans sub) mass)
    have rate' : ℓ*((len i:ℝ)+1)^ℓ*Real.exp (-β*r) ≤ r*Real.exp (-(β/2)*r) := by
      rw [mul_assoc]
      exact mul_le_mul (linear.trans (mul_le_of_le_one_left (Nat.cast_nonneg r) a1)) (term i).2
        (by positivity) (Nat.cast_nonneg _)
    apply le_trans _ (mul_le_mul_of_nonneg_right rate' (Nat.cast_nonneg lists.card))
    exact prob
  have joint := simultaneous_sample_bound F lists init bad (Adjustable G θ Xs ex)
    (Real.exp (-(r:ℝ))) ((r:ℝ)*Real.exp (-(β/2)*r)) (Real.exp_pos _).le (by positivity)
    first (by
      intro i ref hr
      convert second i ref hr using 1
      apply congrArg Nat.cast
      apply congrArg Finset.card
      ext ys
      simp) (by
      intro ref href ys _ good₁ good₂
      apply edits G Xs ex ref ys cut w (fun i => (data i).2.1) nshort nlong wp w1
        (fun i => mul_pos (Real.exp_pos _) (fpos i)) (Fintype.mem_piFinset.mp href)
      · intro i
        have h := (div_le_iff₀ pW).mp (le_of_not_gt (good₁ i))
        simpa only [mul_comm] using h
      · exact fun i => not_not.mp (good₂ i))
  have final := (mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ (r:ℝ)^power by exact_mod_cast polynomial)
    (show 0 ≤ Real.exp (-(r:ℝ)) + r*Real.exp (-(β/2)*r) by positivity)).trans err
  apply le_trans _ (mul_le_mul_of_nonneg_right final (Nat.cast_nonneg _))
  exact joint

end InducedDegreeRepetition.OpenProblems
