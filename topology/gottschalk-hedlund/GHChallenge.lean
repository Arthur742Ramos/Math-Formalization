/-
Scalar Gottschalk–Hedlund theorem. Apache-2.0; see ATTRIBUTION.md.
Material Lean proof developed by OpenAI Codex.
-/
module
public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Order.Zorn

@[expose] public section

/-!
Bounded-orbit cohomological equations: authoring development.
These sections provide supporting lemmas and the existence proof.
-/

open Function Set

namespace GottschalkHedlund

variable {X : Type*} [TopologicalSpace X]

def ForwardMinimal (T : X → X) : Prop :=
  ∀ x, DenseRange (fun n : ℕ => (T^[n]) x)

def BoundedOrbitSums (T : X → X) (g : X → ℝ) : Prop :=
  ∃ x : X, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |birkhoffSum T g n x| ≤ C

def HasTransfer (T : X → X) (g : X → ℝ) : Prop :=
  ∃ h : X → ℝ, Continuous h ∧ ∀ x, h (T x) - h x = g x

def skew (T : X → X) (g : X → ℝ) : X × ℝ → X × ℝ :=
  fun p => (T p.1, p.2 + g p.1)

def fiberTranslation (h : X → ℝ) : X × ℝ → X × ℝ :=
  fun p => (p.1, p.2 - h p.1)

theorem fiber_translation_homeomorph (h : X → ℝ) (hh : Continuous h) :
    ∃ H : X × ℝ ≃ₜ X × ℝ, ∀ p, H p = fiberTranslation h p := by
  let H : X × ℝ ≃ₜ X × ℝ := {
    toFun := fiberTranslation h
    invFun := fun p => (p.1, p.2 + h p.1)
    left_inv := by intro p; simp [fiberTranslation]
    right_inv := by intro p; simp [fiberTranslation]
    continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (hh.comp continuous_fst))
    continuous_invFun := continuous_fst.prodMk (continuous_snd.add (hh.comp continuous_fst))
  }
  exact ⟨H, fun _ => rfl⟩

omit [TopologicalSpace X] in
theorem fiber_translation_conjugates (T : X → X) (g h : X → ℝ)
    (hgh : ∀ x, h (T x) - h x = g x) :
    ∀ p, fiberTranslation h (skew T g p) = (T p.1, (fiberTranslation h p).2) := by
  intro p
  simp only [fiberTranslation, skew]
  congr 1
  have := hgh p.1
  linarith

omit [TopologicalSpace X] in
theorem birkhoffSum_eq_transfer (T : X → X) (g h : X → ℝ)
    (hgh : ∀ x, h (T x) - h x = g x) (n : ℕ) (x : X) :
    birkhoffSum T g n x = h ((T^[n]) x) - h x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [birkhoffSum_succ_apply, ih]
      rw [← hgh ((T^[n]) x)]
      simp only [Function.iterate_succ_apply']
      ring

/-- Continuity of the real additive skew product. -/
theorem skew_continuous (T : X → X) (g : X → ℝ)
    (hT : Continuous T) (hg : Continuous g) : Continuous (skew T g) := by
  exact (hT.comp continuous_fst).prodMk (continuous_snd.add (hg.comp continuous_fst))

omit [TopologicalSpace X] in
/-- The vertical coordinate of an iterated skew product is a Birkhoff sum. -/
theorem skew_iterate (T : X → X) (g : X → ℝ) (n : ℕ) (x : X) (t : ℝ) :
    (skew T g)^[n] (x,t) = ((T^[n]) x, t + birkhoffSum T g n x) := by
  induction n with
  | zero => simp [birkhoffSum_zero_apply]
  | succ n ih =>
      simp only [Function.iterate_succ_apply', ih, skew, birkhoffSum_succ_apply]
      simp only [add_assoc]

/-- A continuous transfer on a compact nonempty space gives bounded orbit sums. -/
theorem bounded_sums_of_transfer [CompactSpace X] [Nonempty X]
    (T : X → X) (g : X → ℝ) (h : X → ℝ) (hh : Continuous h)
    (hgh : ∀ x, h (T x) - h x = g x) : BoundedOrbitSums T g := by
  let x : X := Classical.choice inferInstance
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp (isCompact_range hh).isBounded
  have hC0 : 0 ≤ C := by
    have hc := hC x x
    simpa using hc
  refine ⟨x, C, hC0, ?_⟩
  intro n
  rw [birkhoffSum_eq_transfer T g h hgh]
  simpa [Real.dist_eq] using hC ((T^[n]) x) x

end GottschalkHedlund

/-! Authoring development for compact minimal invariant sets. -/

open Set

namespace GottschalkHedlund

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

theorem exists_minimal_closed_invariant (F : Y → Y) (K₀ : Set Y)
    (hcompact : IsCompact K₀) (hne : K₀.Nonempty)
    (hinv : ∀ y ∈ K₀, F y ∈ K₀) :
    ∃ K : Set Y, K.Nonempty ∧ IsClosed K ∧ K ⊆ K₀ ∧
      (∀ y ∈ K, F y ∈ K) ∧
      ∀ L : Set Y, L.Nonempty → IsClosed L → L ⊆ K →
        (∀ y ∈ L, F y ∈ L) → L = K := by
  let S : Set (Set Y) := {s | s.Nonempty ∧ IsClosed s ∧ s ⊆ K₀ ∧ ∀ y ∈ s, F y ∈ s}
  have hmin : ∃ K, Minimal (· ∈ S) K := by
    refine zorn_superset S ?_
    intro C hCS hC
    obtain rfl | hCne := C.eq_empty_or_nonempty
    · exact ⟨K₀, ⟨hne, hcompact.isClosed, Subset.rfl, hinv⟩, fun _ h => False.elim h⟩
    refine ⟨⋂₀ C, ⟨?_, isClosed_sInter (fun s hs => (hCS hs).2.1), ?_, ?_⟩,
      fun s hs => sInter_subset_of_mem hs⟩
    · have : Nonempty (↥C) := hCne.to_subtype
      rw [sInter_eq_iInter]
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun s t => ?_)
        (fun s => (hCS s.mem).1)
        (fun s => hcompact.of_isClosed_subset (hCS s.mem).2.1 (hCS s.mem).2.2.1)
        (fun s => (hCS s.mem).2.1)
      obtain hst | hts := hC.total s.mem t.mem
      exacts [⟨s, Subset.rfl, hst⟩, ⟨t, hts, Subset.rfl⟩]
    · obtain ⟨s, hs⟩ := hCne
      exact (sInter_subset_of_mem hs).trans (hCS hs).2.2.1
    · intro y hy
      apply mem_sInter.2
      intro s hs
      exact (hCS hs).2.2.2 y (mem_sInter.1 hy s hs)
  obtain ⟨K, hK⟩ := hmin
  refine ⟨K, hK.prop.1, hK.prop.2.1, hK.prop.2.2.1, hK.prop.2.2.2, ?_⟩
  intro L hLne hLclosed hLK hLF
  exact hK.eq_of_subset ⟨hLne, hLclosed, hLK.trans hK.prop.2.2.1, hLF⟩ hLK

omit [T2Space Y] in
/-- Continuity makes the closure of a forward orbit forward-invariant. -/
theorem orbit_closure_invariant (F : Y → Y) (hF : Continuous F) (y : Y) :
    ∀ z ∈ closure (range (fun n : ℕ => (F^[n]) y)),
      F z ∈ closure (range (fun n : ℕ => (F^[n]) y)) := by
  let O : Set Y := range (fun n : ℕ => (F^[n]) y)
  have hclosed : IsClosed (F ⁻¹' closure O) := isClosed_closure.preimage hF
  have hsub : O ⊆ F ⁻¹' closure O := by
    rintro z ⟨n, rfl⟩
    apply subset_closure
    refine ⟨n + 1, ?_⟩
    simp only [Function.iterate_succ_apply']
  exact closure_minimal hsub hclosed

end GottschalkHedlund

/-! Compact orbit closure for bounded real skew products. -/

open Set Function

namespace GottschalkHedlund

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- A bounded additive cocycle gives a nonempty compact forward-invariant set. -/
theorem exists_compact_skew_orbit (T : X → X) (g : X → ℝ)
    (hT : Continuous T) (hg : Continuous g) (x : X) (C : ℝ)
    (hsum : ∀ n : ℕ, |birkhoffSum T g n x| ≤ C) :
    ∃ K : Set (X × ℝ), K.Nonempty ∧ IsCompact K ∧
      ∀ z ∈ K, skew T g z ∈ K := by
  let F := skew T g
  let O : Set (X × ℝ) := range (fun n : ℕ => (F^[n]) (x, 0))
  let B : Set (X × ℝ) := univ ×ˢ Icc (-C) C
  have hB : IsCompact B := isCompact_univ.prod isCompact_Icc
  have hOB : O ⊆ B := by
    rintro z ⟨n, rfl⟩
    change (skew T g)^[n] (x, 0) ∈ univ ×ˢ Icc (-C) C
    rw [skew_iterate]
    simp only [mem_prod, mem_univ, true_and, mem_Icc, zero_add]
    exact abs_le.mp (hsum n)
  have hOcomp : IsCompact (closure O) :=
    hB.of_isClosed_subset isClosed_closure (closure_minimal hOB hB.isClosed)
  have hOne : O.Nonempty := ⟨(x, 0), ⟨0, by simp⟩⟩
  refine ⟨closure O, hOne.mono subset_closure, hOcomp, ?_⟩
  exact orbit_closure_invariant F (skew_continuous T g hT hg) (x, 0)

end GottschalkHedlund

/-! Vertical translations and compact skew-product fibers. -/

open Set Function

namespace GottschalkHedlund

variable {X : Type*} [TopologicalSpace X]

def verticalShift (c : ℝ) (p : X × ℝ) : X × ℝ := (p.1, p.2 + c)

theorem continuous_verticalShift (c : ℝ) : Continuous (verticalShift (X := X) c) := by
  exact continuous_fst.prodMk (continuous_snd.add continuous_const)

omit [TopologicalSpace X] in
theorem skew_verticalShift_commute (T : X → X) (g : X → ℝ) (c : ℝ) (p : X × ℝ) :
    skew T g (verticalShift c p) = verticalShift c (skew T g p) := by
  simp only [skew, verticalShift]
  congr 1
  ring

/-- A nonempty compact set cannot be contained in a nontrivial vertical translate. -/
theorem compact_subset_verticalShift_eq_zero (K : Set (X × ℝ))
    (hcompact : IsCompact K) (hne : K.Nonempty) (c : ℝ)
    (hsub : K ⊆ verticalShift c '' K) : c = 0 := by
  by_contra hc
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hne continuous_snd.continuousOn
    obtain ⟨q, hq, hqp⟩ := hsub hp
    have hcoord : q.2 + c = p.2 := by
      simpa [verticalShift] using congrArg Prod.snd hqp
    have hbound := hmax hq
    change q.2 ≤ p.2 at hbound
    linarith
  · obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨q, hq, hqp⟩ := hsub hp
    have hcoord : q.2 + c = p.2 := by
      simpa [verticalShift] using congrArg Prod.snd hqp
    have hbound := hmin hq
    change p.2 ≤ q.2 at hbound
    linarith

end GottschalkHedlund

/-! At-most-one-point fibers of minimal compact additive skew-product sets. -/

open Set Function

namespace GottschalkHedlund

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Minimality and compactness make each vertical fiber a subsingleton. -/
theorem minimal_skew_fibers_subsingleton (T : X → X) (g : X → ℝ)
    (K : Set (X × ℝ)) (hcompact : IsCompact K) (hne : K.Nonempty)
    (hinv : ∀ z ∈ K, skew T g z ∈ K)
    (hmin : ∀ L : Set (X × ℝ), L.Nonempty → IsClosed L → L ⊆ K →
      (∀ z ∈ L, skew T g z ∈ L) → L = K) :
    ∀ x : X, ∀ a b : ℝ, (x, a) ∈ K → (x, b) ∈ K → a = b := by
  intro x a b ha hb
  let c : ℝ := b - a
  let L : Set (X × ℝ) := K ∩ verticalShift c '' K
  have hLne : L.Nonempty := by
    refine ⟨(x, b), hb, ⟨(x, a), ha, ?_⟩⟩
    simp [verticalShift, c]
  have hLclosed : IsClosed L :=
    hcompact.isClosed.inter ((hcompact.image (continuous_verticalShift c)).isClosed)
  have hLsub : L ⊆ K := inter_subset_left
  have hLinv : ∀ z ∈ L, skew T g z ∈ L := by
    rintro z ⟨hz, y, hy, rfl⟩
    refine ⟨hinv _ hz, ⟨skew T g y, hinv _ hy, ?_⟩⟩
    exact (skew_verticalShift_commute T g c y).symm
  have heq : L = K := hmin L hLne hLclosed hLsub hLinv
  have hsub : K ⊆ verticalShift c '' K := by
    intro z hz
    have hz' : z ∈ L := heq.symm ▸ hz
    exact hz'.2
  have hc : c = 0 := compact_subset_verticalShift_eq_zero K hcompact hne c hsub
  dsimp [c] at hc
  linarith

end GottschalkHedlund

/-! Projection of a minimal skew-product set and continuous graph. -/

open Set Function

namespace GottschalkHedlund

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
/-- A nonempty closed forward-invariant subset of a forward-minimal system is all of X. -/
theorem closed_forward_invariant_eq_univ (T : X → X) (hminimal : ForwardMinimal T)
    (A : Set X) (hclosed : IsClosed A) (hne : A.Nonempty)
    (hinv : ∀ x ∈ A, T x ∈ A) : A = univ := by
  obtain ⟨x, hx⟩ := hne
  have horbit : range (fun n : ℕ => (T^[n]) x) ⊆ A := by
    rintro y ⟨n, rfl⟩
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hinv _ ih
  have hcover : univ ⊆ A := by
    rw [← (hminimal x).closure_eq]
    exact closure_minimal horbit hclosed
  exact eq_univ_iff_forall.mpr (fun x => hcover (mem_univ x))

/-- A compact nonempty forward-invariant skew set projects onto a minimal base. -/
theorem minimal_base_projection (T : X → X) (g : X → ℝ)
    (hminimal : ForwardMinimal T) (K : Set (X × ℝ))
    (hcompact : IsCompact K) (hne : K.Nonempty)
    (hinv : ∀ z ∈ K, skew T g z ∈ K) : Prod.fst '' K = univ := by
  have hclosed : IsClosed (Prod.fst '' K) := (hcompact.image continuous_fst).isClosed
  have hne' : (Prod.fst '' K).Nonempty := hne.image Prod.fst
  have hinv' : ∀ x ∈ Prod.fst '' K, T x ∈ Prod.fst '' K := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨skew T g z, hinv z hz, rfl⟩
  exact closed_forward_invariant_eq_univ T hminimal (Prod.fst '' K) hclosed hne' hinv'

/-- A compact invariant graph with one point per fiber is a continuous transfer. -/
theorem transfer_of_compact_graph (T : X → X) (g : X → ℝ)
    (K : Set (X × ℝ)) (hcompact : IsCompact K)
    (hinv : ∀ z ∈ K, skew T g z ∈ K) (hproj : Prod.fst '' K = univ)
    (huniq : ∀ x : X, ∀ a b : ℝ, (x, a) ∈ K → (x, b) ∈ K → a = b) :
    HasTransfer T g := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let π : K → X := fun z => z.val.1
  have hπ : Continuous π := continuous_fst.comp continuous_subtype_val
  have hsurj : Function.Surjective π := by
    intro x
    have hx : x ∈ Prod.fst '' K := by rw [hproj]; exact mem_univ x
    obtain ⟨z, hz, hzx⟩ := hx
    exact ⟨⟨z, hz⟩, hzx⟩
  have hinj : Function.Injective π := by
    intro u v huv
    obtain ⟨⟨x, a⟩, hu⟩ := u
    obtain ⟨⟨y, b⟩, hv⟩ := v
    dsimp [π] at huv
    subst y
    have hab : a = b := huniq x a b hu hv
    subst b
    rfl
  let e : K ≃ₜ X := (Equiv.ofBijective π ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed hπ hπ.isClosedMap
  let h : X → ℝ := fun x => ((e.symm x : K).val).2
  have hh : Continuous h := continuous_snd.comp (continuous_subtype_val.comp e.symm.continuous)
  have hmem : ∀ x, (x, h x) ∈ K := by
    intro x
    have hfst : ((e.symm x : K).val).1 = x := by
      exact e.apply_symm_apply x
    have hpair : (x, h x) = (e.symm x : K).val := by
      apply Prod.ext
      · exact hfst.symm
      · rfl
    exact hpair.symm ▸ (e.symm x).property
  refine ⟨h, hh, ?_⟩
  intro x
  have hm : (T x, h x + g x) ∈ K := by
    simpa [skew] using hinv (x, h x) (hmem x)
  have heq := huniq (T x) (h x + g x) (h (T x)) hm (hmem (T x))
  linarith

end GottschalkHedlund

/-! Scalar Gottschalk–Hedlund theorem and skew-product consequence. -/

open Set Function

namespace GottschalkHedlund

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- Bounded sums along one orbit produce a continuous transfer function. -/
theorem transfer_of_bounded_sums (T : X → X) (g : X → ℝ)
    (hT : Continuous T) (hg : Continuous g) (hminimal : ForwardMinimal T)
    (hbounded : BoundedOrbitSums T g) : HasTransfer T g := by
  obtain ⟨x, C, _, hsum⟩ := hbounded
  obtain ⟨K₀, hne₀, hcompact₀, hinv₀⟩ :=
    exists_compact_skew_orbit T g hT hg x C hsum
  obtain ⟨K, hne, hclosed, hsub, hinv, hmin⟩ :=
    exists_minimal_closed_invariant (skew T g) K₀ hcompact₀ hne₀ hinv₀
  have hcompact : IsCompact K := hcompact₀.of_isClosed_subset hclosed hsub
  exact transfer_of_compact_graph T g K hcompact hinv
    (minimal_base_projection T g hminimal K hcompact hne hinv)
    (minimal_skew_fibers_subsingleton T g K hcompact hne hinv hmin)

omit [T2Space X] [CompactSpace X] in
/-- Two continuous transfer functions differ by a constant on a minimal system. -/
theorem transfer_difference_constant (T : X → X) (g h₁ h₂ : X → ℝ)
    (hminimal : ForwardMinimal T) (hh₁ : Continuous h₁) (hh₂ : Continuous h₂)
    (heq₁ : ∀ x, h₁ (T x) - h₁ x = g x)
    (heq₂ : ∀ x, h₂ (T x) - h₂ x = g x) (x₀ : X) :
    ∀ x, h₁ x - h₂ x = h₁ x₀ - h₂ x₀ := by
  let A : Set X := {x | h₁ x - h₂ x = h₁ x₀ - h₂ x₀}
  have hclosed : IsClosed A := isClosed_eq (hh₁.sub hh₂) continuous_const
  have horbit : range (fun n : ℕ => (T^[n]) x₀) ⊆ A := by
    rintro x ⟨n, rfl⟩
    induction n with
    | zero => simp [A]
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      change h₁ (T ((T^[n]) x₀)) - h₂ (T ((T^[n]) x₀)) = _
      have h₁n := heq₁ ((T^[n]) x₀)
      have h₂n := heq₂ ((T^[n]) x₀)
      change h₁ ((T^[n]) x₀) - h₂ ((T^[n]) x₀) = _ at ih
      linarith
  have hall : univ ⊆ A := by
    rw [← (hminimal x₀).closure_eq]
    exact closure_minimal horbit hclosed
  exact fun x => hall (mem_univ x)

/-- The scalar Gottschalk–Hedlund equivalence for a nonempty compact base. -/
theorem bounded_sums_iff_transfer [Nonempty X] (T : X → X) (g : X → ℝ)
    (hT : Continuous T) (hg : Continuous g) (hminimal : ForwardMinimal T) :
    BoundedOrbitSums T g ↔ HasTransfer T g := by
  constructor
  · exact transfer_of_bounded_sums T g hT hg hminimal
  · rintro ⟨h, hh, heq⟩
    exact bounded_sums_of_transfer T g h hh heq

/-- Bounded sums give a fiber homeomorphism conjugating the skew product to T × id. -/
theorem bounded_sums_skew_conjugacy (T : X → X) (g : X → ℝ)
    (hT : Continuous T) (hg : Continuous g) (hminimal : ForwardMinimal T)
    (hbounded : BoundedOrbitSums T g) :
    ∃ h : X → ℝ, Continuous h ∧ (∀ x, h (T x) - h x = g x) ∧
      ∃ H : X × ℝ ≃ₜ X × ℝ, (∀ p, H p = fiberTranslation h p) ∧
        ∀ p, H (skew T g p) = (T (H p).1, (H p).2) := by
  obtain ⟨h, hh, heq⟩ := transfer_of_bounded_sums T g hT hg hminimal hbounded
  obtain ⟨H, hH⟩ := fiber_translation_homeomorph h hh
  refine ⟨h, hh, heq, H, hH, ?_⟩
  intro p
  simpa only [hH, fiberTranslation, Prod.fst, Prod.snd] using fiber_translation_conjugates T g h heq p

end GottschalkHedlund
