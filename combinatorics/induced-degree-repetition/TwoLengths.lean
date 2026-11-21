module

public import AdjustmentWitnesses
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Edit

open Filter Finset OpenProblems
open scoped Topology Classical

@[expose] noncomputable def moduli (L : ℕ) :=
  ((range (max 4 L+1)).filter (TestModulus L)).toList

theorem mem_moduli (L q : ℕ) : q ∈ moduli L ↔ TestModulus L q := by
  simp only [moduli,mem_toList,mem_filter,mem_range]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  rcases h with h|h <;> omega

theorem append_moduli (u τ c θ : ℝ) (L : ℕ) (qs : List ℕ)
    (base : RowEstimate u τ c θ L [none]) (each : ∀ q ∈ qs, RowEstimate u τ c θ L [some q]) :
    RowEstimate u τ c θ L (qs.map some ++ [none]) := by
  induction qs with
  | nil => exact base
  | cons q qs ih =>
    exact combine_rows _ _ _ _ _ [some q] _ (each q (by simp))
      (ih fun z hz => each z (by simp [hz]))

/-- Choose the shorter length before deciding which residue tests govern the
longer length. All witnesses share an exponential mass threshold for each length. -/
theorem two_lengths (u τ c θ : ℝ) (hu : 0 < u) (hτ : 0 < τ) (hc : 0 < c) (hθ : 0 < θ) :
    ∃ L₀ L₁ : ℕ, 0 < L₀ ∧ L₀ < L₁ ∧ RowEstimate u τ c θ L₀ [none] ∧
      RowEstimate u τ c θ L₁ ((moduli L₀).map some ++ [none]) := by
  classical
  choose b limits body using fun q : ℕ => conditional_residues (max 3 q) (le_max_left ..) u τ c hu hτ hc
  let k := θ*(u/16)/10
  obtain ⟨j₀,j₁,j0,j01,short,long,mods⟩ := choose_lengths k (by dsimp [k]; positivity) b (fun q _ => limits q)
  have rearr (j : ℕ) : k*(2:ℝ)^j = θ*(u/16)*(2^j:ℕ)/10 := by dsimp [k]; push_cast; ring
  refine ⟨2^j₀,2^j₁,by positivity,Nat.pow_lt_pow_right (by decide) j01,?_,?_⟩
  · exact range_rows _ _ _ _ hu hτ hθ _ (short.trans_eq (rearr j₀))
  apply append_moduli _ _ _ _ _ _ (range_rows _ _ _ _ hu hτ hθ _ (long.trans_eq (rearr j₁)))
  intro q hq
  have test := (mem_moduli _ _).mp hq
  have qp : 3 ≤ q := by rcases test with z|z <;> omega
  obtain ⟨β,w,hβ,hw,prob⟩ := body q j₁ (by omega) _ (budget_pos _) (mods q test)
  refine ⟨β,w,hβ,hw,?_⟩
  filter_upwards [prob] with r hr
  intro N G B Y Xs Q core pos len sub mass
  obtain ⟨E,ey,e,out⟩ := hr N G B Y Xs Q core pos len sub mass
  refine ⟨E,ey,e,?_⟩
  intro y hy good t ht
  obtain rfl := List.mem_singleton.mp ht
  simpa only [Witnesses,Meets,max_eq_right qp] using out y hy good

end InducedDegreeRepetition.Edit
