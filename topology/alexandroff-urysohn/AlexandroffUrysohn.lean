/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0 license.
Substantive formalization: OpenAI Codex, under Arthur's authorization.
-/
module

public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Alexandroff–Urysohn metrization by open covers

The intersecting-pair absorption criterion is Theorem 2.4.1(a) iff (b) of
K. Sakai, Geometric Aspects of General Topology, second-edition author
manuscript, November 2, 2023, pp. 47–48. We construct the compatible
countably generated uniformity from co-membership relations, and use
Mathlib's metrization of countably generated uniformities.
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology Uniformity SetRel

namespace AlexandroffUrysohn

variable {X : Type*}

section Topological
variable [TopologicalSpace X]

/-- The point-star is the union of all members of `C` that contain `x`. -/
def pointStar (C : Set (Set X)) (x : X) : Set X :=
  {y | ∃ U ∈ C, x ∈ U ∧ y ∈ U}

/-- A cover consists of open sets, and every point belongs to a member.
The empty family covers the empty space. No cardinality bound is imposed. -/
def IsOpenCover (C : Set (Set X)) : Prop :=
  (∀ U ∈ C, IsOpen U) ∧ ∀ x, ∃ U ∈ C, x ∈ U

/-- Alexandroff–Urysohn's cover criterion: successive intersecting members
are jointly contained in one member of the preceding cover, and the
point-stars are cofinal among open neighborhoods at every point. -/
def IsMetrizingSequence (C : ℕ → Set (Set X)) : Prop :=
  (∀ n, IsOpenCover (C n)) ∧
  (∀ n, ∀ U ∈ C (n + 1), ∀ V ∈ C (n + 1), (U ∩ V).Nonempty →
    ∃ W ∈ C n, U ∪ V ⊆ W) ∧
  ∀ x O, IsOpen O → x ∈ O → ∃ n, pointStar (C n) x ⊆ O

theorem isOpen_pointStar {C : Set (Set X)} (hC : IsOpenCover C) (x : X) :
    IsOpen (pointStar C x) := by
  have heq : pointStar C x = ⋃ (U ∈ C) (_ : x ∈ U), U := by
    ext y
    simp only [pointStar, mem_ofPred_eq, mem_iUnion]
    aesop
  rw [heq]
  exact isOpen_iUnion fun U => isOpen_iUnion fun hU => isOpen_iUnion fun _ => hC.1 U hU

theorem mem_pointStar {C : Set (Set X)} (hC : IsOpenCover C) (x : X) :
    x ∈ pointStar C x := by
  obtain ⟨U, hU, hx⟩ := hC.2 x
  exact ⟨U, hU, hx, hx⟩

theorem IsMetrizingSequence.nhds_basis {C : ℕ → Set (Set X)}
    (hC : IsMetrizingSequence C) (x : X) :
    (𝓝 x).HasBasis (fun _ : ℕ => True) (fun n => pointStar (C n) x) := by
  refine ⟨fun {s} => ⟨?_, ?_⟩⟩
  · intro hs
    obtain ⟨O, hOs, hO, hx⟩ := mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := hC.2.2 x O hO hx
    exact ⟨n, trivial, hn.trans hOs⟩
  · rintro ⟨n, -, hn⟩
    exact mem_of_superset ((isOpen_pointStar (hC.1 n) x).mem_nhds
      (mem_pointStar (hC.1 n) x)) hn

/-- Two points are related exactly when they belong to one cover member. -/
def coverRelation (C : Set (Set X)) : Set (X × X) :=
  {p | p.2 ∈ pointStar C p.1}

theorem IsMetrizingSequence.comp_subset {C : ℕ → Set (Set X)}
    (hC : IsMetrizingSequence C) (n : ℕ) :
    coverRelation (C (n + 1)) ○ coverRelation (C (n + 1)) ⊆ coverRelation (C n) := by
  rintro ⟨x, z⟩ ⟨y, ⟨U, hU, hx, hy⟩, ⟨V, hV, hy', hz⟩⟩
  obtain ⟨W, hW, hUV⟩ := hC.2.1 n U hU V hV ⟨y, hy, hy'⟩
  exact ⟨W, hW, hUV (Or.inl hx), hUV (Or.inr hz)⟩

theorem IsMetrizingSequence.relation_antitone {C : ℕ → Set (Set X)}
    (hC : IsMetrizingSequence C) : Antitone (fun n => coverRelation (C n)) := by
  apply antitone_nat_of_succ_le
  intro n p hp
  exact hC.comp_subset n ⟨p.2, hp, mem_pointStar (hC.1 (n + 1)) p.2⟩

/-- A metrizing sequence supplies a countably generated uniformity inducing
exactly the given topology. Its basic entourages are cover co-membership. -/
theorem IsMetrizingSequence.exists_uniformity {C : ℕ → Set (Set X)}
    (hC : IsMetrizingSequence C) :
    ∃ u : UniformSpace X, u.toTopologicalSpace = ‹TopologicalSpace X› ∧
      (𝓤[u]).HasBasis (fun _ : ℕ => True) (fun n => coverRelation (C n)) := by
  let F : Filter (X × X) := ⨅ n, 𝓟 (coverRelation (C n))
  have hB : F.HasBasis (fun _ : ℕ => True) (fun n => coverRelation (C n)) :=
    hasBasis_iInf_principal hC.relation_antitone.directed_ge
  let core : UniformSpace.Core X := .mk' F
    (by
      intro r hr x
      obtain ⟨n, -, hn⟩ := hB.mem_iff.mp hr
      exact hn (mem_pointStar (hC.1 n) x))
    (by
      intro r hr
      obtain ⟨n, -, hn⟩ := hB.mem_iff.mp hr
      apply hB.mem_iff.mpr
      refine ⟨n, trivial, ?_⟩
      rintro ⟨x, y⟩ ⟨U, hU, hx, hy⟩
      exact hn ⟨U, hU, hy, hx⟩)
    (by
      intro r hr
      obtain ⟨n, -, hn⟩ := hB.mem_iff.mp hr
      exact ⟨coverRelation (C (n + 1)), hB.mem_of_mem trivial,
        (hC.comp_subset n).trans hn⟩)
  have htop : ‹TopologicalSpace X› = core.toTopologicalSpace := by
    apply TopologicalSpace.ext_nhds
    intro x
    rw [core.nhds_toTopologicalSpace]
    exact (hC.nhds_basis x).eq_of_same_basis (hB.comap (Prod.mk x))
  exact ⟨UniformSpace.ofCoreEq core _ htop, rfl, hB⟩

/-- The sufficiency direction requires no separation: it yields a compatible
pseudometric on arbitrary spaces, including empty and non-T₀ spaces. -/
theorem IsMetrizingSequence.pseudoMetrizableSpace {C : ℕ → Set (Set X)}
    (hC : IsMetrizingSequence C) : PseudoMetrizableSpace X := by
  obtain ⟨u, hu, hB⟩ := hC.exists_uniformity
  exact ⟨u, hu, hB.isCountablyGenerated⟩

/-- Alexandroff–Urysohn sufficiency, with T₀ as the explicit separation
assumption needed to turn a compatible pseudometric into a metric. -/
theorem IsMetrizingSequence.metrizableSpace [T0Space X]
    {C : ℕ → Set (Set X)} (hC : IsMetrizingSequence C) : MetrizableSpace X := by
  have := hC.pseudoMetrizableSpace
  infer_instance

end Topological

/-- Shrinking metric ball covers give the converse, even for pseudometrics. -/
theorem metric_ball_covers [PseudoMetricSpace X] :
    IsMetrizingSequence (fun n => range (fun x : X => Metric.ball x ((1 / 8 : ℝ) ^ n))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · rintro U ⟨x, rfl⟩
      exact Metric.isOpen_ball (α := X)
    · intro x
      exact ⟨Metric.ball x ((1 / 8 : ℝ) ^ n), ⟨x, rfl⟩,
        Metric.mem_ball_self (pow_pos (by norm_num) n)⟩
  · intro n U hU V hV hUV
    obtain ⟨a, rfl⟩ := hU
    obtain ⟨b, rfl⟩ := hV
    obtain ⟨y, hya, hyb⟩ := hUV
    refine ⟨Metric.ball a ((1 / 8 : ℝ) ^ n), ⟨a, rfl⟩, ?_⟩
    have hr : 0 < (1 / 8 : ℝ) ^ n := pow_pos (by norm_num) n
    rw [Metric.mem_ball, pow_succ] at hya hyb
    intro z hz
    rcases hz with hz | hz
    · rw [Metric.mem_ball, pow_succ] at hz
      rw [Metric.mem_ball]
      linarith
    · rw [Metric.mem_ball, pow_succ] at hz
      have hby : dist b y < (1 / 8 : ℝ) ^ n * (1 / 8) := by
        simpa only [dist_comm] using hyb
      have htri := dist_triangle z y a
      have htri' := dist_triangle z b y
      rw [Metric.mem_ball]
      linarith
  · intro x O hO hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO x hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 8 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rintro z ⟨U, ⟨a, rfl⟩, hxa, hza⟩
    apply hball
    rw [Metric.mem_ball] at hxa hza ⊢
    have htri := dist_triangle z a x
    have hax : dist a x < (1 / 8 : ℝ) ^ n := by simpa only [dist_comm] using hxa
    linarith

section Topological
variable [TopologicalSpace X]

/-- Every pseudometrizable topology admits the open covers of the criterion. -/
theorem exists_metrizingSequence [PseudoMetrizableSpace X] :
    ∃ C : ℕ → Set (Set X), IsMetrizingSequence C := by
  let := pseudoMetrizableSpacePseudoMetric X
  exact ⟨_, metric_ball_covers⟩

/-- The separation-free version characterizes pseudometrizability. -/
theorem pseudoMetrizable_iff :
    PseudoMetrizableSpace X ↔ ∃ C : ℕ → Set (Set X), IsMetrizingSequence C := by
  constructor
  · intro h
    exact exists_metrizingSequence
  · rintro ⟨C, hC⟩
    exact hC.pseudoMetrizableSpace

/-- Alexandroff–Urysohn's full intersecting-pair cover criterion for T₀
spaces. Cover members can have arbitrary cardinality. -/
theorem metrizable_iff [T0Space X] :
    MetrizableSpace X ↔ ∃ C : ℕ → Set (Set X), IsMetrizingSequence C := by
  constructor
  · intro h
    exact exists_metrizingSequence
  · rintro ⟨C, hC⟩
    exact hC.metrizableSpace

/-- The criterion produces an actual metric inducing the exact original topology. -/
theorem exists_compatibleMetric [T0Space X] {C : ℕ → Set (Set X)}
    (hC : IsMetrizingSequence C) :
    ∃ m : MetricSpace X, m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace X› := by
  have := hC.metrizableSpace
  exact ⟨metrizableSpaceMetric X, rfl⟩

end Topological

end AlexandroffUrysohn
