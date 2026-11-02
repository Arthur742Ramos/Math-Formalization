/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ChurchPredecessor
public meta import LambdaTuring.ChurchPredecessor

@[expose] public section

/- This strict two-stage continuation construction follows the related
   Isabelle Lambda_CPS_Binary_Composition development and its Norrish credit. -/

namespace LambdaTuring

theorem liftFrom_duplicate (t : Term) (depth : Nat) :
    liftFrom depth (liftFrom depth t) = liftFrom (depth + 1) (liftFrom depth t) := by
  induction t generalizing depth with
  | var i =>
    by_cases h : i < depth
    · have h' : i < depth + 1 := by omega
      simp [liftFrom, h, h']
    · have h0 : ¬ i + 1 < depth := by omega
      have h1 : ¬ i + 1 < depth + 1 := by omega
      simp [liftFrom, h, h0, h1]
  | abs t ih =>
    change Term.abs (liftFrom (depth + 1) (liftFrom (depth + 1) t)) =
      Term.abs (liftFrom ((depth + 1) + 1) (liftFrom (depth + 1) t))
    rw [ih (depth + 1)]
  | app f x ihf ihx =>
    simp only [liftFrom, ihf, ihx]

theorem substAt_liftBy_two (t value : Term) :
    substAt 1 value (liftBy 2 t) = liftFrom 0 t := by
  change substAt 1 value (liftFrom 0 (liftFrom 0 t)) = liftFrom 0 t
  rw [liftFrom_duplicate t 0]
  exact substAt_liftFrom (liftFrom 0 t) 1 value

def cpsPair (F G : Term) : Term :=
  .abs (.abs (.app (.app F (.var 1))
    (.abs (.app (.app G (.var 2))
      (.abs (.app (.var 2) (.app (.app churchNatPair (.var 1)) (.var 0))))))))

def cpsPairCont1 (G : Term) (n : Nat) (K : Term) : Term :=
  .abs (.app (.app G (church n))
    (.abs (.app (liftBy 2 K) (.app (.app churchNatPair (.var 1)) (.var 0)))))

def cpsPairCont2 (a : Nat) (K : Term) : Term :=
  .abs (.app (liftFrom 0 K) (.app (.app churchNatPair (church a)) (.var 0)))

theorem cpsPair_closed {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) : Scoped 0 (cpsPair F G) := by
  have hf2 := scoped_mono hf (Nat.zero_le 2)
  have hg3 := scoped_mono hg (Nat.zero_le 3)
  have hp4 := scoped_mono churchNatPair_closed (Nat.zero_le 4)
  simp [cpsPair, Scoped, hf2, hg3, hp4]

theorem cpsPair_run {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) (n : Nat) (K : Term) :
    Reaches (.app (.app (cpsPair F G) (church n)) K)
      (.app (.app F (church n)) (cpsPairCont1 G n K)) := by
  have hf1 := substAt_scoped F 1 (church n) (scoped_mono hf (Nat.zero_le 1))
  have hg2 := substAt_scoped G 2 (church n) (scoped_mono hg (Nat.zero_le 2))
  have hp3 := substAt_scoped churchNatPair 3 (church n) (scoped_mono churchNatPair_closed (Nat.zero_le 3))
  have hn1 : liftBy 1 (church n) = church n := liftBy_closed 1 (church_closed n)
  have hn2 : liftBy 2 (church n) = church n := liftBy_closed 2 (church_closed n)
  have h1 : Beta (.app (cpsPair F G) (church n))
      (.abs (.app (.app F (church n))
        (.abs (.app (.app G (church n))
          (.abs (.app (.var 2) (.app (.app churchNatPair (.var 1)) (.var 0)))))))) := by
    simpa [cpsPair, substAt, hf1, hg2, hp3, hn1, hn2] using
      (Beta.contract (.abs (.app (.app F (.var 1))
        (.abs (.app (.app G (.var 2))
          (.abs (.app (.var 2) (.app (.app churchNatPair (.var 1)) (.var 0)))))))) (church n))
  have hf0 := substAt_scoped F 0 K hf
  have hg1 := substAt_scoped G 1 K (scoped_mono hg (Nat.zero_le 1))
  have hp2 := substAt_scoped churchNatPair 2 K (scoped_mono churchNatPair_closed (Nat.zero_le 2))
  have hn0 := substAt_scoped (church n) 0 K (church_closed n)
  have hn1' := substAt_scoped (church n) 1 K (scoped_mono (church_closed n) (Nat.zero_le 1))
  have h2 : Beta
      (.app (.abs (.app (.app F (church n))
        (.abs (.app (.app G (church n))
          (.abs (.app (.var 2) (.app (.app churchNatPair (.var 1)) (.var 0)))))))) K)
      (.app (.app F (church n)) (cpsPairCont1 G n K)) := by
    simpa [cpsPairCont1, substAt, hf0, hg1, hp2, hn0, hn1'] using
      (Beta.contract (.app (.app F (church n))
        (.abs (.app (.app G (church n))
          (.abs (.app (.var 2) (.app (.app churchNatPair (.var 1)) (.var 0))))))) K)
  exact .step (.appLeft h1) (.step h2 (.refl _))

theorem cpsPairCont1_run {G : Term} (hg : Scoped 0 G) (n a : Nat) (K : Term) :
    Reaches (.app (cpsPairCont1 G n K) (church a)) (.app (.app G (church n)) (cpsPairCont2 a K)) := by
  have hg0 := substAt_scoped G 0 (church a) hg
  have hn0 := substAt_scoped (church n) 0 (church a) (church_closed n)
  have hp1 := substAt_scoped churchNatPair 1 (church a) (scoped_mono churchNatPair_closed (Nat.zero_le 1))
  have ha1 : liftBy 1 (church a) = church a := liftBy_closed 1 (church_closed a)
  have hk := substAt_liftBy_two K (church a)
  have hb : Beta (.app (cpsPairCont1 G n K) (church a)) (.app (.app G (church n)) (cpsPairCont2 a K)) := by
    simpa [cpsPairCont1, cpsPairCont2, substAt, hg0, hn0, hp1, ha1, hk] using
      (Beta.contract (.app (.app G (church n))
        (.abs (.app (liftBy 2 K) (.app (.app churchNatPair (.var 1)) (.var 0))))) (church a))
  exact .step hb (.refl _)

theorem cpsPairCont2_run (a b : Nat) (K : Term) :
    Reaches (.app (cpsPairCont2 a K) (church b)) (.app K (church (Nat.pair a b))) := by
  have hp0 := substAt_scoped churchNatPair 0 (church b) churchNatPair_closed
  have ha0 := substAt_scoped (church a) 0 (church b) (church_closed a)
  have hk := substAt_liftFrom K 0 (church b)
  have hb : Beta (.app (cpsPairCont2 a K) (church b))
      (.app K (.app (.app churchNatPair (church a)) (church b))) := by
    simpa [cpsPairCont2, substAt, liftBy, hp0, ha0, hk] using
      (Beta.contract (.app (liftFrom 0 K) (.app (.app churchNatPair (church a)) (.var 0))) (church b))
  exact .step hb (reaches_appRight K (churchNatPair_run a b))

def numericalPairBind (f g : Nat →. Nat) : Nat →. Nat :=
  fun n => (f n).bind fun a => (g n).bind fun b => Part.some (Nat.pair a b)

/-- Pair the results of two CPS computations strictly, preserving absence of
    normal forms if either computation is undefined. -/
theorem cpsPair_represents {F G : Term} {f g : Nat →. Nat}
    (hf : CPSRepresents F f) (hg : CPSRepresents G g) :
    CPSRepresents (cpsPair F G) (numericalPairBind f g) := by
  constructor
  · exact cpsPair_closed hf.1 hg.1
  · intro n K
    have hprefix := cpsPair_run hf.1 hg.1 n K
    have hsecond : ∀ a, a ∈ f n →
        Reaches (.app (.app (cpsPair F G) (church n)) K)
          (.app (.app G (church n)) (cpsPairCont2 a K)) := by
      intro a ha
      exact reaches_trans hprefix
        (reaches_trans ((hf.2 n (cpsPairCont1 G n K)).1 a ha) (cpsPairCont1_run hg.1 n a K))
    have hresult : ∀ a b, a ∈ f n → b ∈ g n →
        Reaches (.app (.app (cpsPair F G) (church n)) K) (.app K (church (Nat.pair a b))) := by
      intro a b ha hb
      exact reaches_trans (hsecond a ha)
        (reaches_trans ((hg.2 n (cpsPairCont2 a K)).1 b hb) (cpsPairCont2_run a b K))
    constructor
    · intro m hm
      change m ∈ (f n).bind (fun a => (g n).bind fun b => Part.some (Nat.pair a b)) at hm
      obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.1 hm
      obtain ⟨b, hb, hm⟩ := Part.mem_bind_iff.1 hm
      have heq : m = Nat.pair a b := by simpa using hm
      subst m
      exact hresult a b ha hb
    · intro hnone
      change (f n).bind (fun a => (g n).bind fun b => Part.some (Nat.pair a b)) = Part.none at hnone
      by_cases hfd : (f n).Dom
      · obtain ⟨a, ha⟩ := Part.dom_iff_mem.1 hfd
        by_cases hgd : (g n).Dom
        · obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 hgd
          have hm : Nat.pair a b ∈ (f n).bind (fun a => (g n).bind fun b => Part.some (Nat.pair a b)) :=
            Part.mem_bind_iff.2 ⟨a, ha, Part.mem_bind_iff.2 ⟨b, hb, by simp⟩⟩
          rw [hnone] at hm
          simp at hm
        · have hgNone : g n = Part.none := by
            apply Part.eq_none_iff.2
            intro b hb
            exact hgd (Part.dom_iff_mem.2 ⟨b, hb⟩)
          exact noNormal_backward (hsecond a ha) ((hg.2 n (cpsPairCont2 a K)).2 hgNone)
      · have hfNone : f n = Part.none := by
          apply Part.eq_none_iff.2
          intro a ha
          exact hfd (Part.dom_iff_mem.2 ⟨a, ha⟩)
        exact noNormal_backward hprefix ((hf.2 n (cpsPairCont1 G n K)).2 hfNone)

theorem codePair_eval (f g : Nat.Partrec.Code) :
    Nat.Partrec.Code.eval (.pair f g) = numericalPairBind (Nat.Partrec.Code.eval f) (Nat.Partrec.Code.eval g) := by
  funext n
  apply Part.ext
  intro m
  simp only [Nat.Partrec.Code.eval, Seq.seq, Part.map_eq_map, Part.bind_map,
    Part.mem_bind_iff, Part.mem_map_iff, numericalPairBind, Part.mem_some_iff]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, h.symm⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, h.symm⟩

theorem primrec_cpsPair : Primrec₂ cpsPair := by
  let P := Term × Term
  let inner : Term := .abs (.app (.var 2) (.app (.app churchNatPair (.var 1)) (.var 0)))
  have hf : Primrec (fun p : P => p.1) := Primrec.fst
  have hg : Primrec (fun p : P => p.2) := Primrec.snd
  have ho : Primrec (fun p : P => Term.abs (.app (.app p.2 (.var 2)) inner)) :=
    primrec_abs.comp (primrec_app.comp (primrec_app.comp hg (Primrec.const (Term.var 2))) (Primrec.const inner))
  exact primrec_abs.comp (primrec_abs.comp (primrec_app.comp
    (primrec_app.comp hf (Primrec.const (Term.var 1))) ho))

#print axioms cpsPair_run
#print axioms cpsPairCont1_run
#print axioms cpsPairCont2_run
#print axioms cpsPair_represents
#print axioms codePair_eval
#print axioms primrec_cpsPair

end LambdaTuring
