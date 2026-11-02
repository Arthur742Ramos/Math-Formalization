/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.ClosedProductive
public meta import LambdaTuring.ClosedProductive

@[expose] public section

namespace LambdaTuring

/-- Bounded membership in a finite list of natural codes is primitive recursive. -/
theorem natListMem_primrecRel : PrimrecRel (fun (xs : List Nat) (x : Nat) => x ∈ xs) := by
  have h := (Primrec.eq : PrimrecRel (fun a b : Nat => a = b)).exists_mem_list
  exact h.of_eq (fun xs x => by simp)

/-- Two self-referential behaviors, selected by a Boolean parameter. The
finite list contains project syntax codes, not arbitrary lambda terms. -/
def avoidanceSimulation (g : Nat.Partrec.Code → Term) (p : Nat.Partrec.Code × Nat) : Part Nat :=
  let a := (Nat.unpair p.2).1
  let param := (Encodable.decode a : Option ((Nat.Partrec.Code × List Nat) × Bool)).getD
    ((.zero, []), false)
  let self := Nat.Partrec.Code.curry p.1 a
  let hit := decide (executableTermEncode (g self) ∈ param.1.2)
  bif param.2 then (bif hit then Part.some 0 else Part.none)
  else (bif hit then Part.none else Nat.Partrec.Code.eval param.1.1 0)

theorem avoidanceSimulation_partrec (g : Nat.Partrec.Code → Term) (hg : Computable g) :
    Partrec (avoidanceSimulation g) := by
  let P := Nat.Partrec.Code × Nat
  let T := (Nat.Partrec.Code × List Nat) × Bool
  have ha : Primrec (fun p : P => (Nat.unpair p.2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hparam : Primrec (fun p : P =>
      (Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const _)).comp ha
  have hlist : Primrec (fun p : P =>
      ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).1.2) :=
    Primrec.snd.comp (Primrec.fst.comp hparam)
  have hcode : Primrec (fun p : P =>
      ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).1.1) :=
    Primrec.fst.comp (Primrec.fst.comp hparam)
  have hmode : Primrec (fun p : P =>
      ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).2) :=
    Primrec.snd.comp hparam
  have hself : Primrec (fun p : P => Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1) :=
    Nat.Partrec.Code.primrec₂_curry.comp Primrec.fst ha
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have htarget : Computable (fun p : P =>
      executableTermEncode (g (Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1))) :=
    henc.comp (hg.comp hself.to_comp)
  have hhit : Computable (fun p : P => decide
      (executableTermEncode (g (Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1)) ∈
        ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).1.2)) :=
    natListMem_primrecRel.decide.to_comp.comp hlist.to_comp htarget
  have heval : Partrec (fun p : P => Nat.Partrec.Code.eval
      ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).1.1 0) :=
    Nat.Partrec.Code.eval_part.comp hcode.to_comp (Computable.const 0)
  have hone : Partrec (fun _ : P => Part.some 0) := Partrec.some.comp (Computable.const 0)
  have ht : Partrec (fun p : P => bif
      decide (executableTermEncode (g (Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1)) ∈
        ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).1.2)
      then Part.some 0 else Part.none) := Partrec.cond hhit hone Partrec.none
  have hf : Partrec (fun p : P => bif
      decide (executableTermEncode (g (Nat.Partrec.Code.curry p.1 (Nat.unpair p.2).1)) ∈
        ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).1.2)
      then Part.none else Nat.Partrec.Code.eval
        ((Encodable.decode ((Nat.unpair p.2).1) : Option T).getD ((.zero, []), false)).1.1 0) :=
    Partrec.cond hhit Partrec.none heval
  exact Partrec.cond hmode.to_comp ht hf

/-- The fixed-point theorem gives primitive-recursive program families for
the two complementary avoidance tests. -/
theorem avoidance_fixed_codes (g : Nat.Partrec.Code → Term) (hg : Computable g) :
    ∃ left right : Nat.Partrec.Code × List Nat → Nat.Partrec.Code,
      Primrec left ∧ Primrec right ∧ ∀ e xs,
        ((Nat.Partrec.Code.eval (left (e, xs)) 0).Dom ↔
          executableTermEncode (g (left (e, xs))) ∉ xs ∧ (Nat.Partrec.Code.eval e 0).Dom) ∧
        ((Nat.Partrec.Code.eval (right (e, xs)) 0).Dom ↔
          executableTermEncode (g (right (e, xs))) ∈ xs) := by
  have hp : Partrec₂ (fun u z => avoidanceSimulation g (u, z)) :=
    (avoidanceSimulation_partrec g hg).to₂
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.fixed_point₂ hp
  let q : ((Nat.Partrec.Code × List Nat) × Bool) → Nat.Partrec.Code :=
    fun p => Nat.Partrec.Code.curry u (Encodable.encode p)
  have hq : Primrec q := Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode
  let left : Nat.Partrec.Code × List Nat → Nat.Partrec.Code := fun p => q (p, false)
  let right : Nat.Partrec.Code × List Nat → Nat.Partrec.Code := fun p => q (p, true)
  refine ⟨left, right, hq.comp (Primrec.id.pair (Primrec.const false)),
    hq.comp (Primrec.id.pair (Primrec.const true)), ?_⟩
  intro e xs
  have heval (mode : Bool) : Nat.Partrec.Code.eval (q ((e, xs), mode)) 0 =
      (bif mode then
        (bif decide (executableTermEncode (g (q ((e, xs), mode))) ∈ xs) then Part.some 0 else Part.none)
       else
        (bif decide (executableTermEncode (g (q ((e, xs), mode))) ∈ xs) then Part.none else Nat.Partrec.Code.eval e 0)) := by
    change Nat.Partrec.Code.eval (Nat.Partrec.Code.curry u (Encodable.encode ((e, xs), mode))) 0 = _
    rw [Nat.Partrec.Code.eval_curry, hu]
    simp only [avoidanceSimulation, Nat.unpair_pair, Encodable.encodek, Option.getD_some, q]
  constructor
  · change (Nat.Partrec.Code.eval (q ((e, xs), false)) 0).Dom ↔ _
    rw [heval]
    by_cases h : executableTermEncode (g (q ((e, xs), false))) ∈ xs <;> simp [h, left]
  · change (Nat.Partrec.Code.eval (q ((e, xs), true)) 0).Dom ↔ _
    rw [heval]
    by_cases h : executableTermEncode (g (q ((e, xs), true))) ∈ xs <;> simp [h, right]

/-- Uniformly avoid any finite homogeneous list while preserving the
halting status of the input code. This uses no extensionality assumption on
`A`; list entries are encoded syntax values. -/
theorem finite_homogeneous_avoidance (A : Term → Prop) (g : Nat.Partrec.Code → Term)
    (hg : Computable g) (hred : ∀ c, (Nat.Partrec.Code.eval c 0).Dom ↔ A (g c)) :
    ∃ select : Nat.Partrec.Code × List Nat → Nat.Partrec.Code, Computable select ∧
      ∀ e xs,
        (∀ t, executableTermEncode t ∈ xs → (A t ↔ (Nat.Partrec.Code.eval e 0).Dom)) →
        executableTermEncode (g (select (e, xs))) ∉ xs ∧
          ((Nat.Partrec.Code.eval (select (e, xs)) 0).Dom ↔ (Nat.Partrec.Code.eval e 0).Dom) := by
  obtain ⟨left, right, hl, hr, hfixed⟩ := avoidance_fixed_codes g hg
  let P := Nat.Partrec.Code × List Nat
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have hhit : Computable (fun p : P =>
      decide (executableTermEncode (g (left p)) ∈ p.2)) :=
    natListMem_primrecRel.decide.to_comp.comp Computable.snd (henc.comp (hg.comp hl.to_comp))
  let select : P → Nat.Partrec.Code := fun p =>
    bif decide (executableTermEncode (g (left p)) ∈ p.2) then right p else left p
  have hselect : Computable select := Computable.cond hhit hr.to_comp hl.to_comp
  refine ⟨select, hselect, ?_⟩
  intro e xs homogeneous
  by_cases h : executableTermEncode (g (left (e, xs))) ∈ xs
  · have hleft : ¬ (Nat.Partrec.Code.eval (left (e, xs)) 0).Dom := by
      rw [(hfixed e xs).1]
      simp [h]
    have he : ¬ (Nat.Partrec.Code.eval e 0).Dom := by
      intro he
      have ha : A (g (left (e, xs))) := (homogeneous _ h).2 he
      exact hleft ((hred _).2 ha)
    have hright : executableTermEncode (g (right (e, xs))) ∉ xs := by
      intro hmem
      have hrightdom := (hfixed e xs).2.2 hmem
      have ha : A (g (right (e, xs))) := (hred _).1 hrightdom
      exact he ((homogeneous _ hmem).1 ha)
    constructor
    · simpa [select, h] using hright
    · have hrightnone : ¬ (Nat.Partrec.Code.eval (right (e, xs)) 0).Dom :=
        fun hd => hright ((hfixed e xs).2.1 hd)
      simp [select, h, hrightnone, he]
  · have hleft : (Nat.Partrec.Code.eval (left (e, xs)) 0).Dom ↔
        (Nat.Partrec.Code.eval e 0).Dom := by
      rw [(hfixed e xs).1]
      simp [h]
    constructor
    · simp [select, h]
    · simpa [select, h] using hleft

/-- Record a newly selected code and all syntax codes produced so far. -/
def avoidanceChain (select : Nat.Partrec.Code × List Nat → Nat.Partrec.Code)
    (g : Nat.Partrec.Code → Term) (e : Nat.Partrec.Code) : Nat → Nat.Partrec.Code × List Nat
  | 0 => (e, [executableTermEncode (g e)])
  | n + 1 =>
    let prev := avoidanceChain select g e n
    let next := select (e, prev.2)
    (next, executableTermEncode (g next) :: prev.2)

theorem avoidanceChain_computable (select : Nat.Partrec.Code × List Nat → Nat.Partrec.Code)
    (g : Nat.Partrec.Code → Term) (hs : Computable select) (hg : Computable g) :
    Computable (fun p : Nat.Partrec.Code × Nat => avoidanceChain select g p.1 p.2) := by
  let P := Nat.Partrec.Code × Nat
  let S := Nat.Partrec.Code × List Nat
  let X := P × (Nat × S)
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have hbase : Computable (fun p : P => (p.1, [executableTermEncode (g p.1)])) :=
    Computable.fst.pair (Computable.list_cons.comp (henc.comp (hg.comp Computable.fst))
      (Computable.const []))
  have he : Computable (fun p : X => p.1.1) := Computable.fst.comp Computable.fst
  have hlist : Computable (fun p : X => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hn : Computable (fun p : X => select (p.1.1, p.2.2.2)) := hs.comp (he.pair hlist)
  have hstep : Computable (fun p : X =>
      (select (p.1.1, p.2.2.2), executableTermEncode (g (select (p.1.1, p.2.2.2))) :: p.2.2.2)) :=
    hn.pair (Computable.list_cons.comp (henc.comp (hg.comp hn)) hlist)
  have h := Computable.nat_rec (α := P) (σ := S) Computable.snd hbase hstep.to₂
  exact h.of_eq (fun p => by induction p.2 <;> simp_all [avoidanceChain])

/-- Every accumulated syntax code has the same target-language status as
the starting computation, and every earlier output remains in the list. -/
theorem avoidanceChain_invariant (A : Term → Prop) (g : Nat.Partrec.Code → Term)
    (hred : ∀ c, (Nat.Partrec.Code.eval c 0).Dom ↔ A (g c))
    (select : Nat.Partrec.Code × List Nat → Nat.Partrec.Code)
    (hselect : ∀ e xs,
      (∀ t, executableTermEncode t ∈ xs → (A t ↔ (Nat.Partrec.Code.eval e 0).Dom)) →
      executableTermEncode (g (select (e, xs))) ∉ xs ∧
        ((Nat.Partrec.Code.eval (select (e, xs)) 0).Dom ↔ (Nat.Partrec.Code.eval e 0).Dom))
    (e : Nat.Partrec.Code) :
    ∀ k, ((Nat.Partrec.Code.eval (avoidanceChain select g e k).1 0).Dom ↔
        (Nat.Partrec.Code.eval e 0).Dom) ∧
      (∀ t, executableTermEncode t ∈ (avoidanceChain select g e k).2 →
        (A t ↔ (Nat.Partrec.Code.eval e 0).Dom)) ∧
      (∀ i, i ≤ k → executableTermEncode (g (avoidanceChain select g e i).1) ∈
        (avoidanceChain select g e k).2) := by
  intro k
  induction k with
  | zero =>
    constructor
    · rfl
    constructor
    · intro t ht
      have he : executableTermEncode t = executableTermEncode (g e) := by
        simpa [avoidanceChain] using ht
      have ht' : t = g e := by
        apply Encodable.encode_injective
        simpa only [executableTermEncode_eq] using he
      rw [ht']
      exact (hred e).symm
    · intro i hi
      have hi' : i = 0 := by omega
      subst i
      simp [avoidanceChain]
  | succ k ih =>
    let prev := avoidanceChain select g e k
    let next := select (e, prev.2)
    have hn := hselect e prev.2 ih.2.1
    have hA : A (g next) ↔ (Nat.Partrec.Code.eval e 0).Dom := (hred next).symm.trans hn.2
    constructor
    · simpa [avoidanceChain, prev, next] using hn.2
    constructor
    · intro t ht
      have hmem : executableTermEncode t = executableTermEncode (g next) ∨
          executableTermEncode t ∈ prev.2 := by
        simpa [avoidanceChain, prev, next] using ht
      rcases hmem with heq | hmem
      · have ht' : t = g next := by
          apply Encodable.encode_injective
          simpa only [executableTermEncode_eq] using heq
        simpa [ht'] using hA
      · exact ih.2.1 t hmem
    · intro i hi
      by_cases heq : i = k + 1
      · subst i
        simp [avoidanceChain]
      · have hi' : i ≤ k := by omega
        have hmem := ih.2.2 i hi'
        simpa [avoidanceChain, prev, next] using Or.inr
          (a := executableTermEncode (g (avoidanceChain select g e i).1) =
            executableTermEncode (g next)) hmem

/-- Repeated finite avoidance yields infinitely many distinct syntax outputs
with the same halting status, uniformly in the starting code. -/
theorem manyOne_reduction_has_injective_fibers (A : Term → Prop)
    (g : Nat.Partrec.Code → Term) (hg : Computable g)
    (hred : ∀ c, (Nat.Partrec.Code.eval c 0).Dom ↔ A (g c)) :
    ∃ h : Nat.Partrec.Code × Nat → Nat.Partrec.Code, Computable h ∧
      ∀ e, Function.Injective (fun n => g (h (e, n))) ∧
        ∀ n, ((Nat.Partrec.Code.eval (h (e, n)) 0).Dom ↔ (Nat.Partrec.Code.eval e 0).Dom) := by
  obtain ⟨select, hs, hselect⟩ := finite_homogeneous_avoidance A g hg hred
  let h : Nat.Partrec.Code × Nat → Nat.Partrec.Code :=
    fun p => (avoidanceChain select g p.1 p.2).1
  have hh : Computable h := Computable.fst.comp (avoidanceChain_computable select g hs hg)
  refine ⟨h, hh, ?_⟩
  intro e
  have inv := avoidanceChain_invariant A g hred select hselect e
  have hdistinct : ∀ i j, i < j →
      executableTermEncode (g (h (e, i))) ≠ executableTermEncode (g (h (e, j))) := by
    intro i j hij heq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hmem := (inv k).2.2 i (by omega)
    have hnot := (hselect e (avoidanceChain select g e k).2 (inv k).2.1).1
    apply hnot
    change executableTermEncode (g (h (e, k + 1))) ∈ (avoidanceChain select g e k).2
    rw [← heq]
    exact hmem
  constructor
  · intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact False.elim ((hdistinct i j hlt) (congrArg executableTermEncode hij))
    · exact heq
    · exact False.elim ((hdistinct j i hgt) (congrArg executableTermEncode hij.symm))
  · intro n
    exact (inv n).1

#print axioms manyOne_reduction_has_injective_fibers
#print axioms finite_homogeneous_avoidance
#print axioms avoidance_fixed_codes
end LambdaTuring
