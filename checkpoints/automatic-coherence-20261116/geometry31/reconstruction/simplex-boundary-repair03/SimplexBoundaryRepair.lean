module
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! SOURCE ONLY / UNCOMPILED. A geometric retraction of the actual finite standard-simplex
cylinder onto its bottom and whole lateral boundary. No independently prescribed
final interior, approximation, simplicial retraction or reflection is asserted. -/
@[expose] public noncomputable section
open scoped BigOperators
open unitInterval Convexity
namespace AutomaticCoherence.SimplexBoundaryRepair01

abbrev Simplex (n : Nat) := StdSimplex ℝ (Fin (n + 1))
abbrev Cylinder (n : Nat) := I × Simplex n

def count (n : Nat) : ℝ := (n + 1 : Nat)

lemma count_pos (n : Nat) : 0 < count n := by
  change (0 : ℝ) < ((n + 1 : Nat) : ℝ)
  exact_mod_cast Nat.succ_pos n

lemma count_ne (n : Nat) : count n ≠ 0 := ne_of_gt (count_pos n)

variable {n : Nat}

def minimum (x : Simplex n) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
    (fun i => x.weights i)

lemma minimum_nonneg (x : Simplex n) : 0 ≤ minimum x := by
  exact Finset.le_inf' Finset.univ_nonempty _ (fun i _ => x.weights_nonneg i)

lemma minimum_le (x : Simplex n) (i : Fin (n + 1)) : minimum x ≤ x.weights i := by
  exact Finset.inf'_le _ (Finset.mem_univ i)

lemma minimum_attained (x : Simplex n) : ∃ i, minimum x = x.weights i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
    (fun i => x.weights i)
  exact ⟨i, hi⟩

lemma continuous_minimum : Continuous (minimum (n := n)) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => StdSimplex.continuous_weights_apply ℝ i)

def Boundary (x : Simplex n) : Prop := ∃ i, x.weights i = 0
def BottomSides (p : Cylinder n) : Prop := p.1 = 0 ∨ Boundary p.2

def den (p : Cylinder n) : ℝ := max (1 - (p.1 : ℝ) / 2) (1 - count n * minimum p.2)
def rt (p : Cylinder n) : ℝ := 2 - (2 - (p.1 : ℝ)) / den p
def coord (p : Cylinder n) (i : Fin (n + 1)) : ℝ :=
  1 / count n + (p.2.weights i - 1 / count n) / den p

lemma den_bounds (p : Cylinder n) : 1 / 2 ≤ den p ∧ den p ≤ 1 := by
  have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.property.1
  have ht1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
  have hm := mul_nonneg (le_of_lt (count_pos n)) (minimum_nonneg p.2)
  constructor
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact max_le (by linarith) (by linarith)

lemma den_pos (p : Cylinder n) : 0 < den p :=
  lt_of_lt_of_le (by norm_num) (den_bounds p).1

lemma rt_mem (p : Cylinder n) : rt p ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := den_pos p
  have hl : 1 - (p.1 : ℝ) / 2 ≤ den p := le_max_left _ _
  have hu := (den_bounds p).2
  have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.property.1
  have ht1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
  have hq0 : (2 - (p.1 : ℝ)) / den p ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
  have hq1 : 1 ≤ (2 - (p.1 : ℝ)) / den p := (le_div_iff₀ hd).mpr (by linarith)
  exact ⟨by dsimp [rt]; linarith, by dsimp [rt]; linarith⟩

lemma coord_as_quotient (p : Cylinder n) (i : Fin (n + 1)) :
    coord p i = (den p - 1 + count n * p.2.weights i) / (count n * den p) := by
  have hc := count_ne n
  have hd : den p ≠ 0 := ne_of_gt (den_pos p)
  unfold coord
  field_simp [hc, hd]
  <;> ring

lemma coord_nonneg (p : Cylinder n) (i : Fin (n + 1)) : 0 ≤ coord p i := by
  have hm := mul_le_mul_of_nonneg_left (minimum_le p.2 i) (le_of_lt (count_pos n))
  have hl : 1 - count n * minimum p.2 ≤ den p := le_max_right _ _
  rw [coord_as_quotient]
  exact div_nonneg (by linarith) (le_of_lt (mul_pos (count_pos n) (den_pos p)))

lemma sum_coord (p : Cylinder n) : ∑ i, coord p i = 1 := by
  have hc := count_ne n
  simp only [coord, div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_sub_distrib, StdSimplex.total_of_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change count n * 1 * (count n)⁻¹ +
    (1 - count n * 1 * (count n)⁻¹) * (den p)⁻¹ = 1
  simp [hc]

def spatial (p : Cylinder n) : Simplex n where
  weights := Finsupp.equivFunOnFinite.symm (coord p)
  nonneg i := by simpa using coord_nonneg p i
  total := by simpa [Finsupp.sum_fintype] using sum_coord p

@[simp] lemma spatial_weights (p : Cylinder n) (i : Fin (n + 1)) :
    (spatial p).weights i = coord p i := by simp [spatial]

def retractPoint (p : Cylinder n) : Cylinder n := (⟨rt p, rt_mem p⟩, spatial p)

lemma retractPoint_mem (p : Cylinder n) : BottomSides (retractPoint p) := by
  have hd : den p ≠ 0 := ne_of_gt (den_pos p)
  rcases le_total (1 - count n * minimum p.2) (1 - (p.1 : ℝ) / 2) with h | h
  · left
    apply Subtype.ext
    change rt p = 0
    have he : den p = 1 - (p.1 : ℝ) / 2 := max_eq_left h
    dsimp [rt]
    apply sub_eq_zero.mpr
    apply (eq_div_iff hd).mpr
    rw [he]
    ring
  · right
    obtain ⟨i, hi⟩ := minimum_attained p.2
    refine ⟨i, ?_⟩
    change (spatial p).weights i = 0
    rw [spatial_weights]
    have he : den p = 1 - count n * p.2.weights i := by
      exact (max_eq_right h).trans (by rw [hi])
    rw [coord_as_quotient]
    have hz : den p - 1 + count n * p.2.weights i = 0 := by linarith [he]
    rw [hz, zero_div]

lemma den_boundary (p : Cylinder n) (h : BottomSides p) : den p = 1 := by
  rcases h with h | ⟨i, hi⟩
  · have hv : (p.1 : ℝ) = 0 := congrArg Subtype.val h
    have hm := mul_nonneg (le_of_lt (count_pos n)) (minimum_nonneg p.2)
    simp only [den, hv, zero_div, sub_zero]
    exact max_eq_left (by linarith)
  · have hm : minimum p.2 = 0 :=
      le_antisymm ((minimum_le p.2 i).trans_eq hi) (minimum_nonneg p.2)
    have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.property.1
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
    simp only [den, hm, mul_zero, sub_zero]
    exact max_eq_right (by linarith)

lemma retractPoint_fixed (p : Cylinder n) (h : BottomSides p) : retractPoint p = p := by
  apply Prod.ext
  · apply Subtype.ext
    change rt p = (p.1 : ℝ)
    rw [rt, den_boundary p h, div_one]
    ring
  · apply StdSimplex.ext
    ext i
    change (spatial p).weights i = p.2.weights i
    rw [spatial_weights, coord, den_boundary p h, div_one]
    ring

lemma continuous_den : Continuous (den (n := n)) := by
  unfold den
  exact (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (continuous_const.sub (continuous_const.mul (continuous_minimum.comp continuous_snd)))

lemma continuous_spatial : Continuous (spatial (n := n)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  apply continuous_pi
  intro i
  change Continuous (fun p : Cylinder n => coord p i)
  unfold coord
  exact continuous_const.add ((((StdSimplex.continuous_weights_apply ℝ i).comp
    continuous_snd).sub continuous_const).div continuous_den
    (fun p => ne_of_gt (den_pos p)))

lemma continuous_retractPoint : Continuous (retractPoint (n := n)) := by
  have ht : Continuous (rt (n := n)) := by
    unfold rt
    exact continuous_const.sub ((continuous_const.sub
      (continuous_subtype_val.comp continuous_fst)).div continuous_den
      (fun p => ne_of_gt (den_pos p)))
  exact (ht.subtype_mk _).prodMk continuous_spatial

/-- Supplied continuous data on the whole bottom and lateral boundary. Corner
and edge agreement is encoded in this single map's domain, not an assumed
filling. The final simplex interior is not independently prescribed. -/
def extendBoundary {Y : Type*} [TopologicalSpace Y]
    (a : C({p : Cylinder n // BottomSides p}, Y)) : C(Cylinder n, Y) :=
  a.comp ⟨fun p => ⟨retractPoint p, retractPoint_mem p⟩,
    continuous_retractPoint.subtype_mk _⟩

lemma extendBoundary_restrict {Y : Type*} [TopologicalSpace Y]
    (a : C({p : Cylinder n // BottomSides p}, Y))
    (p : {p : Cylinder n // BottomSides p}) : extendBoundary a p.val = a p := by
  change a ⟨retractPoint p.val, retractPoint_mem p.val⟩ = a p
  congr 1
  exact Subtype.ext (retractPoint_fixed p.val p.property)

/-- In dimension zero the whole boundary is empty; the cylinder retracts only
onto its bottom. This case is included, not excluded by a positivity premise. -/
lemma boundary_zero_empty (x : Simplex 0) : ¬ Boundary x := by
  letI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  rintro ⟨i, hi⟩
  have h := StdSimplex.weights_apply_eq_one x i
  rw [h] at hi
  norm_num at hi

lemma retractPoint_zero_dim_time (p : Cylinder 0) : (retractPoint p).1 = 0 := by
  exact (retractPoint_mem p).resolve_right (boundary_zero_empty _)

end AutomaticCoherence.SimplexBoundaryRepair01
