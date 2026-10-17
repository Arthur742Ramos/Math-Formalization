module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Countable-density Hewitt–Marczewski–Pondiczery theorem

Finite binary prefixes code a countable collection of rows that interpolates
arbitrary natural-number labels on finitely many distinct binary sequences.
Applying these labels to dense sequences in the factors gives a dense set in
any product with at most continuum many separable factors.
-/

public section

open Set Function TopologicalSpace
open scoped Cardinal

namespace HMP

universe u v

/-- A finite binary table with natural-number entries. There are countably many. -/
abbrev RowCode := Σ n : ℕ, (Fin n → Bool) → ℕ

/-- The row selected by a finite binary table and a sequence in every factor. -/
@[expose] def row {ι : Type u} {X : ι → Type v} (e : ι → ℕ → Bool)
    (d : ∀ i, ℕ → X i) (c : RowCode) (i : ι) : X i :=
  d i (c.2 (fun k => e i k))

private theorem finite_prefix_separates {F : Type*} [Fintype F]
    (e : F → ℕ → Bool) (he : Injective e) :
    ∃ n : ℕ, Injective (fun i => fun k : Fin n => e i k) := by
  classical
  have hp : ∀ i j : F, ∃ n : ℕ,
      (fun k : Fin n => e i k) = (fun k : Fin n => e j k) → i = j := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun _ => hij⟩
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp (fun h => hij (he h))
      exact ⟨k + 1, fun h => False.elim (hk (congrFun h ⟨k, Nat.lt_succ_self k⟩))⟩
  choose n hn using hp
  let N := Finset.univ.sup (fun p : F × F => n p.1 p.2)
  refine ⟨N, fun i j h => hn i j ?_⟩
  funext k
  exact congrFun h ⟨k, lt_of_lt_of_le k.isLt
    (Finset.le_sup (f := fun p : F × F => n p.1 p.2) (Finset.mem_univ (i, j)))⟩

/-- A single finite table realizes any labels on a finite set of coordinates. -/
theorem finite_interpolation {ι : Type u} (e : ι ↪ (ℕ → Bool))
    (s : Finset ι) (v : s → ℕ) :
    ∃ c : RowCode, ∀ i : s, c.2 (fun k => e i k) = v i := by
  classical
  obtain ⟨n, hn⟩ := finite_prefix_separates (fun i : s => e i)
    (e.injective.comp Subtype.val_injective)
  exact ⟨⟨n, Function.extend (fun i : s => fun k : Fin n => e i k) v (fun _ => 0)⟩,
    fun i => hn.extend_apply v (fun _ => 0) i⟩

/-- The coded rows are dense if each factor sequence is dense. No separation
or countability hypothesis on the factors' bases is used. -/
theorem denseRange_rows {ι : Type u} {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] (e : ι ↪ (ℕ → Bool))
    (d : ∀ i, ℕ → X i) (hd : ∀ i, DenseRange (d i)) :
    DenseRange (row e d) := by
  classical
  apply dense_iff_inter_open.mpr
  intro o ho hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, U, hU, hs⟩ := isOpen_pi_iff.mp ho x hx
  have hlabels : ∀ i : s, ∃ n, d i n ∈ U i :=
    fun i => (hd i).exists_mem_open (hU i i.2).1 ⟨x i, (hU i i.2).2⟩
  choose v hv using hlabels
  obtain ⟨c, hc⟩ := finite_interpolation e s v
  refine ⟨row e d c, hs ?_, ⟨c, rfl⟩⟩
  intro i hi
  change d i (c.2 (fun k => e i k)) ∈ U i
  rw [hc ⟨i, hi⟩]
  exact hv ⟨i, hi⟩

/-- At most continuum means exactly that binary-sequence coordinate codes exist,
including for index types in an arbitrary universe. -/
theorem continuum_bound_iff {ι : Type u} :
    #ι ≤ 𝔠 ↔ Nonempty (ι ↪ (ℕ → Bool)) := by
  rw [← Cardinal.lift_mk_le']
  simp only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.two_power_aleph0, Cardinal.lift_continuum, Cardinal.lift_le_continuum]

/-- Countable-density HMP for nonempty separable factors. -/
theorem separable_product_of_embedding {ι : Type u} {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, SeparableSpace (X i)]
    [∀ i, Nonempty (X i)] (e : ι ↪ (ℕ → Bool)) :
    SeparableSpace (∀ i, X i) :=
  (denseRange_rows e (fun i => denseSeq (X i))
    (fun i => denseRange_denseSeq (X i))).separableSpace' _

/-- The Hewitt–Marczewski–Pondiczery theorem at countable density. Empty factors
are allowed: an empty product space is separable as well. -/
theorem separable_product {ι : Type u} {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, SeparableSpace (X i)]
    (hι : #ι ≤ 𝔠) : SeparableSpace (∀ i, X i) := by
  classical
  by_cases h : Nonempty (∀ i, X i)
  · have : ∀ i, Nonempty (X i) := fun i => h.map (fun f => f i)
    exact separable_product_of_embedding (continuum_bound_iff.mp hι).some
  · have : IsEmpty (∀ i, X i) := not_nonempty_iff.mp h
    infer_instance

/-- A dense sequence in a discrete Boolean cube distinguishes its coordinates.
This is the converse obstruction behind the sharp continuum bound. -/
theorem coordinate_patterns_injective {ι : Type u} (d : ℕ → ι → Bool)
    (hd : DenseRange d) : Injective (fun i => fun n => d n i) := by
  classical
  intro i j h
  by_contra hij
  let U : Set (ι → Bool) := (fun f => f i) ⁻¹' {false} ∩ (fun f => f j) ⁻¹' {true}
  have hU : IsOpen U :=
    ((isOpen_discrete _).preimage (continuous_apply i)).inter
      ((isOpen_discrete _).preimage (continuous_apply j))
  have hne : U.Nonempty := ⟨Function.update (fun _ => false) j true, by simp [U, hij]⟩
  obtain ⟨n, hn⟩ := hd.exists_mem_open hU hne
  have hni : d n i = false := hn.1
  have hnj : d n j = true := hn.2
  have hfalse : (false : Bool) = true := hni.symm.trans ((congrFun h n).trans hnj)
  cases hfalse

/-- The continuum bound is sharp: a discrete Boolean cube is separable exactly
when its index set has cardinality at most continuum. -/
theorem boolean_cube_separable_iff {ι : Type u} :
    SeparableSpace (ι → Bool) ↔ #ι ≤ 𝔠 := by
  constructor
  · intro h
    have := h
    exact continuum_bound_iff.mpr
      ⟨⟨_, coordinate_patterns_injective (denseSeq (ι → Bool))
        (denseRange_denseSeq (ι → Bool))⟩⟩
  · intro h
    exact separable_product h

end HMP
