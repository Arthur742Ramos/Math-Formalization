module
public import DeterminationPatterns.Witness
@[expose] public section
namespace DeterminationPatterns
universe u

theorem contextual_fixed_carrier {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (ctx : Sub U (Roots C D)) (fixed : Fixed (Step C D f U) X) : Sub X C := by
  intro x hx
  have hf : Step C D f U X x := by rw [fixed]; exact hx
  rcases hf with hu | ⟨hc, _, _⟩
  · exact (ctx hu).1
  · exact hc

theorem contextual_fixed_roots {α : Type u} {C U X : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (_ctx : Sub U (Roots C D)) (fixed : Fixed (Step C D f U) X) :
    ∀ x, Roots C D x → (X x ↔ U x) := by
  intro x root
  constructor
  · intro hx
    have hf : Step C D f U X x := by rw [fixed]; exact hx
    rcases hf with hu | ⟨_, ⟨y, hy⟩, _⟩
    · exact hu
    · exact False.elim (root.2 y hy)
  · intro hu
    have hf : Step C D f U X x := Or.inl hu
    rw [fixed] at hf
    exact hf

theorem contextual_greatest_internal_zero_paths {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (ctx : Sub U (Roots C D)) :
    InternalReach (fun x => C x ∧ ¬ Greatest (Step C D f U) x) D
      (fun x => Roots C D x ∧ ¬ U x) =
      (fun x => C x ∧ ¬ Greatest (Step C D f U) x) := by
  classical
  let F := Step C D f U
  let G := Greatest F
  let Z : Region α := fun x => C x ∧ ¬ G x
  let R := InternalReach Z D (fun x => Roots C D x ∧ ¬ U x)
  let Y : Region α := fun x => C x ∧ ¬ R x
  have hm : Monotone F := step_monotone adm U
  have gf : Fixed F G := greatest_fixed hm
  have gc : Sub G C := contextual_fixed_carrier ctx gf
  have rz : Sub R Z := by intro x h; obtain ⟨_, _, hp⟩ := h; exact path_target hp
  have gy : Sub G Y := by
    intro x hx
    refine ⟨gc hx, ?_⟩
    intro hr
    exact (rz hr).2 hx
  have post : Sub Y (F Y) := by
    intro x ⟨hxC, hxNotR⟩
    by_cases hxG : G x
    · have hFG : F G x := by rw [gf]; exact hxG
      exact hm G Y gy hFG
    · have hxZ : Z x := ⟨hxC, hxG⟩
      have hxNotU : ¬ U x := by
        intro hu
        have hFG : F G x := Or.inl hu
        rw [gf] at hFG
        exact hxG hFG
      have hparent : ∃ y, Parents C D x y := by
        apply Classical.byContradiction
        intro hnone
        have root : Roots C D x := ⟨hxC, fun y hy => hnone ⟨y, hy⟩⟩
        have rx : R x := ⟨x, ⟨root, hxNotU⟩, InternalPath.refl x hxZ⟩
        exact hxNotR rx
      have noR : ∀ y, Parents C D x y → ¬ R y := by
        intro y hyP hyR
        obtain ⟨b, hb, path⟩ := hyR
        have rx : R x := ⟨b, hb, InternalPath.step path hxZ hyP.2⟩
        exact hxNotR rx
      have inputs : (fun y => Y y ∧ Parents C D x y) = Parents C D x := by
        funext y
        apply propext
        constructor
        · intro h; exact h.2
        · intro hp; exact ⟨⟨hp.1, noR y hp⟩, hp⟩
      apply Or.inr
      refine ⟨hxC, hparent, ?_⟩
      rw [inputs]
      exact (adm x hxC).2.2
  have yz : Sub Y G := le_greatest F Y post
  apply funext
  intro x
  apply propext
  constructor
  · intro hr; exact rz hr
  · intro hx
    apply Classical.byContradiction
    intro hn
    exact hx.2 (yz ⟨hx.1, hn⟩)

theorem ambiguity_has_ambiguous_parent {α : Type u} {C U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (adm : Mechanism C D f) (_ctx : Sub U (Roots C D)) {x : α}
    (hxG : Greatest (Step C D f U) x) (hxNotL : ¬ Least (Step C D f U) x) :
    ∃ y, Parents C D x y ∧ Greatest (Step C D f U) y ∧
      ¬ Least (Step C D f U) y := by
  classical
  let F := Step C D f U
  let L := Least F
  let G := Greatest F
  have hm : Monotone F := step_monotone adm U
  have lf : Fixed F L := least_fixed hm
  have gf : Fixed F G := greatest_fixed hm
  have lg : Sub L G := (fixed_bounds gf).1
  apply Classical.byContradiction
  intro hn
  have eq : (fun y => L y ∧ Parents C D x y) = (fun y => G y ∧ Parents C D x y) := by
    funext y
    apply propext
    constructor
    · intro h; exact ⟨lg h.1, h.2⟩
    · intro h
      have hyL : L y := by
        apply Classical.byContradiction
        intro hnot
        exact hn ⟨y, h.2, h.1, hnot⟩
      exact ⟨hyL, h.2⟩
  have hfg : F G x := by rw [gf]; exact hxG
  have hfl : F L x := by
    rcases hfg with hu | ⟨hc, hp, hf⟩
    · exact Or.inl hu
    · apply Or.inr
      refine ⟨hc, hp, ?_⟩
      rw [eq]
      exact hf
  rw [lf] at hfl
  exact hxNotL hfl

theorem realized_pattern_necessary {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop}
    (part : StatusPartition C L Z Q) (ctx : Sub U (Roots C D))
    (adm : Mechanism C D f) (low : Least (Step C D f U) = L)
    (high : Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x)) :
    PatternConditions C D U L Z Q := by
  classical
  let F := Step C D f U
  have lf : Fixed F L := by
    have h := least_fixed (step_monotone adm U)
    rw [low] at h
    exact h
  have gf : Fixed F (fun x => C x ∧ ¬ Z x) := by
    have h := greatest_fixed (step_monotone adm U)
    rw [high] at h
    exact h
  have zc : Sub Z C := by intro x hz; exact (part.1 x).mpr (Or.inr (Or.inl hz))
  have qc : Sub Q C := by intro x hq; exact (part.1 x).mpr (Or.inr (Or.inr hq))
  have ul : Sub U L := by
    intro x hu
    have h : F L x := Or.inl hu
    rw [lf] at h
    exact h
  have rootZ : Sub (fun x => Roots C D x ∧ ¬ U x) Z := by
    intro x ⟨hroot, hnot⟩
    have iff := contextual_fixed_roots ctx gf x hroot
    apply Classical.byContradiction
    intro hnz
    exact hnot (iff.mp ⟨hroot.1, hnz⟩)
  have lpath : InternalReach L D U = L := by
    have h := contextual_least_internal_paths adm ctx
    rw [low] at h
    exact h
  have zpath : InternalReach Z D (fun x => Roots C D x ∧ ¬ U x) = Z := by
    have h := contextual_greatest_internal_zero_paths adm ctx
    rw [high] at h
    have zform : (fun x => C x ∧ ¬ (C x ∧ ¬ Z x)) = Z := by
      funext x
      apply propext
      constructor
      · intro ⟨hc, hn⟩
        apply Classical.byContradiction
        intro hnz
        exact hn ⟨hc, hnz⟩
      · intro hz
        exact ⟨zc hz, fun h => h.2 hz⟩
    rw [zform] at h
    exact h
  have qp : ∀ x, Q x → ∃ y, Parents C D x y ∧ Q y := by
    intro x hxQ
    have hxNotL : ¬ L x := by intro hl; exact (part.2.2.1 x) ⟨hl, hxQ⟩
    have hxNotZ : ¬ Z x := by intro hz; exact (part.2.2.2 x) ⟨hz, hxQ⟩
    have hxG : Greatest F x := by rw [high]; exact ⟨qc hxQ, hxNotZ⟩
    have hxNotLeast : ¬ Least F x := by rw [low]; exact hxNotL
    obtain ⟨y, hyP, hyG, hyNotLeast⟩ := ambiguity_has_ambiguous_parent adm ctx hxG hxNotLeast
    have hyNotL : ¬ L y := by rw [← low]; exact hyNotLeast
    have hyNotZ : ¬ Z y := by rw [high] at hyG; exact hyG.2
    have hyQ : Q y := by
      rcases (part.1 y).mp hyP.1 with hyL | hyZ | hyQ
      · exact False.elim (hyNotL hyL)
      · exact False.elim (hyNotZ hyZ)
      · exact hyQ
    exact ⟨y, hyP, hyQ⟩
  exact ⟨ul, rootZ, lpath, zpath, qp⟩

/-- Exact realization of a forced-on / forced-off / ambiguous partition. -/
theorem exact_relevant_pattern_realization {α : Type u} {C L Z Q U : Region α}
    {D : α → α → Prop} (part : StatusPartition C L Z Q)
    (ctx : Sub U (Roots C D)) :
    (∃ f, Mechanism C D f ∧ Relevant C D f ∧ Least (Step C D f U) = L ∧
      Greatest (Step C D f U) = (fun x => C x ∧ ¬ Z x)) ↔
      PatternConditions C D U L Z Q := by
  constructor
  · rintro ⟨f, adm, _, low, high⟩
    exact realized_pattern_necessary part ctx adm low high
  · intro cond
    exact ⟨StatusMechanism C D L Z Q, pattern_witness_extrema part cond ctx⟩

end DeterminationPatterns
