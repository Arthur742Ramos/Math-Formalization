module

public import Gallai
public import Ramsey
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

open Finset

variable {V : Type*} (G : SimpleGraph V)

/-- Relate the finite count used in the statements to Mathlib's graph invariant. -/
theorem degreeOn_eq_induced_degree (S : Finset V) (x : S) :
    degreeOn G S x = @SimpleGraph.degree _ (G.induce (S : Set V)) x (by classical infer_instance) := by
  classical
  let H := G.induce (S : Set V)
  change (S.filter (G.Adj x)).card = (H.neighborFinset x).card
  rw [← Finset.card_map (Function.Embedding.subtype (· ∈ S)) (s := H.neighborFinset x)]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_map, SimpleGraph.mem_neighborFinset,
    Function.Embedding.subtype_apply, H, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨hy, hxy⟩
    exact ⟨⟨y,hy⟩, hxy, rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.property,hz⟩

/-- For K log 4 ≤ 1, an exactly regular witness of order r is available in every host N ≥ 2. -/
theorem logScale_ramsey_range (K : ℝ) (hK : 0 < K) (hsmall : K * Real.log 4 ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) (G : SimpleGraph (Fin N)) :
    ∃ S : Finset (Fin N), S.card = ⌈K * Real.log N⌉₊ ∧ ∃ d, degreeClass G S d = S := by
  let r := ⌈K * Real.log N⌉₊
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hr : 1 ≤ r := Nat.one_le_ceil_iff.mpr (mul_pos hK hlog)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : 4 ^ (r - 1) ≤ N := by
    suffices h : (4 : ℝ) ^ (r - 1) ≤ N by exact_mod_cast h
    apply (Real.log_le_log_iff (by positivity) hn).mp
    rw [Real.log_pow, Nat.cast_sub hr, Nat.cast_one]
    have hceil := Nat.ceil_lt_add_one (mul_pos hK hlog).le
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    calc
      (r - 1 : ℝ) * Real.log 4 ≤ (K * Real.log N) * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right _ hlog4.le
        dsimp [r]
        linarith
      _ = (K * Real.log 4) * Real.log N := by ring
      _ ≤ Real.log N := by simpa using mul_le_mul_of_nonneg_right hsmall hlog.le
  obtain ⟨S, _, hc, hd⟩ := ramsey_regular_witness G (r - 1) univ (by simpa using hpow)
  exact ⟨S, by change S.card = r; omega, hd⟩

/-- Choose the larger even part inside a prescribed sample U. -/
theorem large_even_part (U : Finset V) :
    ∃ E ⊆ U, U.card ≤ 2 * E.card ∧ ∀ x ∈ E, Even (degreeOn G E x) := by
  classical
  let H := G.induce (U : Set V)
  obtain ⟨T, hT, hC⟩ := gallai_even_partition H
  have hsel : ∃ P : Finset U, U.card ≤ 2 * P.card ∧ ∀ x ∈ P, Even (degreeOn H P x) := by
    have hc := T.card_add_card_compl
    change T.card + Tᶜ.card = Fintype.card U at hc
    rw [Fintype.card_coe] at hc
    by_cases h : U.card ≤ 2 * T.card
    · exact ⟨T, h, hT⟩
    · exact ⟨Tᶜ, by omega, hC⟩
  obtain ⟨P, hp, he⟩ := hsel
  let f := Function.Embedding.subtype (· ∈ U)
  refine ⟨P.map f, ?_, by simpa using hp, ?_⟩
  · intro y hy
    obtain ⟨z, _, rfl⟩ := mem_map.mp hy
    exact z.property
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
    unfold degreeOn
    rw [Finset.filter_map, card_map]
    exact he z hz

/-- Select the common initial parity and leave exactly enough room for the auxiliaries. -/
theorem parity_core (W : Finset V) (r t : ℕ) (hW : 4 * r ≤ W.card) (ht : t < r)
    (initial : V → ℕ) :
    ∃ E ⊆ W, r ≤ E.card + t ∧ E.card + t < 2 * r ∧ ∃ ε < 2,
      ∀ x ∈ E, (degreeOn G E x + initial x) % 2 = ε := by
  classical
  let Z := W.filter fun x => initial x % 2 = 0
  let O := W.filter fun x => ¬initial x % 2 = 0
  have hsum : Z.card + O.card = W.card := card_filter_add_card_filter_not ..
  have chooseClass : ∃ P ⊆ W, 2 * r ≤ P.card ∧ ∃ ε < 2, ∀ x ∈ P, initial x % 2 = ε := by
    by_cases hZ : 2 * r ≤ Z.card
    · exact ⟨Z, filter_subset .., hZ, 0, by decide, fun _ hx => (mem_filter.mp hx).2⟩
    · refine ⟨O, filter_subset .., by omega, 1, by decide, fun x hx => ?_⟩
      have hx' := (mem_filter.mp hx).2
      omega
  obtain ⟨P,hP,hc,ε,hε,he⟩ := chooseClass
  obtain ⟨U,hU,hu⟩ := exists_subset_card_eq (show 2 * (r - t) - 1 ≤ P.card by omega)
  obtain ⟨E,hE,hl,hev⟩ := large_even_part G U
  have hu' := card_le_card hE
  refine ⟨E, (hE.trans hU).trans hP, by omega, by omega, ε, hε, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := hev x hx
  rw [hn, ← he x (hU (hE hx))]
  omega

/-- The last count in §6, in the induced graph on the retained vertices and edited auxiliaries. -/
theorem equalized_witness [DecidableEq V] (E P good : Finset V) (r d : ℕ) (η : ℝ)
    (hd : Disjoint E P) (hg : good ⊆ E) (hlo : r ≤ E.card + P.card)
    (hhi : E.card + P.card < 2*r)
    (hexc : ((E.card - good.card + P.card : ℕ) : ℝ) ≤ η * (E.card + P.card))
    (hedit : ∀ x ∈ good, degreeOn G E x + degreeOn G P x = d) :
    r ≤ (E ∪ P).card ∧ (E ∪ P).card < 2*r ∧
      (1-η) * (E ∪ P).card ≤ ((degreeClass G (E ∪ P) d).card : ℝ) := by
  classical
  have hsub : good ⊆ degreeClass G (E ∪ P) d := by
    intro x hx
    apply mem_filter.mpr
    refine ⟨mem_union_left _ (hg hx), ?_⟩
    simpa [degreeOn, filter_union, card_union_of_disjoint
      (hd.mono (filter_subset ..) (filter_subset ..))] using hedit x hx
  rw [card_union_of_disjoint hd]
  refine ⟨hlo, hhi, ?_⟩
  push_cast [Nat.cast_sub (card_le_card hg)] at hexc ⊢
  have hcount : (good.card : ℝ) ≤ (degreeClass G (E ∪ P) d).card := by exact_mod_cast card_le_card hsub
  linarith

end InducedDegreeRepetition
