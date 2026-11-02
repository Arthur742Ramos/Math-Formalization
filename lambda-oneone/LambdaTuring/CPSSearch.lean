/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSRecursion
public meta import LambdaTuring.CPSRecursion

@[expose] public section

/- The search body follows the related Isabelle Lambda_CPS_Search construction,
   with the test input encoded using Mathlib's numeric pairing. -/

namespace LambdaTuring

def fixDelta (F : Term) : Term := .abs (.app F (.app (.var 0) (.var 0)))
def lambdaFix (F : Term) : Term := .app (fixDelta F) (fixDelta F)

theorem fixDelta_closed {F : Term} (hf : Scoped 0 F) : Scoped 0 (fixDelta F) := by
  have hf1 := scoped_mono hf (Nat.zero_le 1)
  simp [fixDelta, Scoped, hf1]

theorem lambdaFix_closed {F : Term} (hf : Scoped 0 F) : Scoped 0 (lambdaFix F) :=
  ⟨fixDelta_closed hf, fixDelta_closed hf⟩

theorem lambdaFix_unfold {F : Term} (hf : Scoped 0 F) :
    Beta (lambdaFix F) (.app F (lambdaFix F)) := by
  have hF := substAt_scoped F 0 (fixDelta F) hf
  have hb := Beta.contract (.app F (.app (.var 0) (.var 0))) (fixDelta F)
  simp only [substAt, hF] at hb
  exact hb

/-- The search loop calls the test strictly, branching only on its result. -/
def cpsSearchBody (G : Term) : Term :=
  .abs (.abs (.abs (.abs
    (.app (.app G (.app (.app churchNatPair (.var 2)) (.var 1)))
      (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
        (.app (.app (.app (.var 4) (.var 3)) (.app churchSuccessor (.var 2))) (.var 1))))))))

theorem cpsSearchBody_closed {G : Term} (hg : Scoped 0 G) : Scoped 0 (cpsSearchBody G) := by
  have hg4 := scoped_mono hg (Nat.zero_le 4)
  have hp4 := scoped_mono churchNatPair_closed (Nat.zero_le 4)
  have hz5 := scoped_mono churchIsZero_closed (Nat.zero_le 5)
  have hs5 := scoped_mono churchSuccessor_closed (Nat.zero_le 5)
  simp [cpsSearchBody, Scoped, hg4, hp4, hz5, hs5]

def cpsSearchLoop (G : Term) : Term := lambdaFix (cpsSearchBody G)

theorem cpsSearchLoop_closed {G : Term} (hg : Scoped 0 G) : Scoped 0 (cpsSearchLoop G) :=
  lambdaFix_closed (cpsSearchBody_closed hg)

def cpsSearchCont (G : Term) (a i : Nat) (K : Term) : Term :=
  .abs (.app (.app (.app churchIsZero (.var 0)) (.app (liftFrom 0 K) (church i)))
    (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor (church i))) (liftFrom 0 K)))

theorem pairFirstSelector_any (a b : Term) :
    Reaches (.app (.app pairFirstSelector a) b) a := by
  have h1 : Beta (.app pairFirstSelector a) (.abs (liftFrom 0 a)) := by
    simpa [pairFirstSelector, substAt, liftBy] using (Beta.contract (.abs (.var 1)) a)
  have h2 : Beta (.app (.abs (liftFrom 0 a)) b) a := by
    simpa [substAt_liftFrom] using (Beta.contract (liftFrom 0 a) b)
  exact .step (.appLeft h1) (.step h2 (.refl _))

theorem cpsSearchCont_run {G : Term} (hg : Scoped 0 G) (a i v : Nat) (K : Term) :
    Reaches (.app (cpsSearchCont G a i K) (church v))
      (if v = 0 then .app K (church i)
       else .app (.app (.app (cpsSearchLoop G) (church a)) (church (i + 1))) K) := by
  have hz := substAt_scoped churchIsZero 0 (church v) churchIsZero_closed
  have hs := substAt_scoped churchSuccessor 0 (church v) churchSuccessor_closed
  have hl := substAt_scoped (cpsSearchLoop G) 0 (church v) (cpsSearchLoop_closed hg)
  have ha := substAt_scoped (church a) 0 (church v) (church_closed a)
  have hi := substAt_scoped (church i) 0 (church v) (church_closed i)
  have hk := substAt_liftFrom K 0 (church v)
  have hb : Beta (.app (cpsSearchCont G a i K) (church v))
      (.app (.app (.app churchIsZero (church v)) (.app K (church i)))
        (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor (church i))) K)) := by
    simpa [cpsSearchCont, substAt, liftBy, hz, hs, hl, ha, hi, hk] using
      (Beta.contract (.app (.app (.app churchIsZero (.var 0)) (.app (liftFrom 0 K) (church i)))
        (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor (church i))) (liftFrom 0 K))) (church v))
  apply Reaches.step hb
  have htest := churchIsZero_run v
  have hsucc := churchSuccessor_run i
  apply reaches_trans (reaches_appLeft (reaches_appLeft htest _) _)
  by_cases hv : v = 0
  · simp only [hv, ite_true]
    exact pairFirstSelector_any _ _
  · simp only [hv, ite_false]
    apply reaches_trans (pairSecondSelector_run _ _)
    exact reaches_appLeft (reaches_appRight (.app (cpsSearchLoop G) (church a)) hsucc) K

theorem cpsSearchLoop_dispatch {G : Term} (hg : Scoped 0 G) (a i : Nat) (K : Term) :
    Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K)
      (.app (.app G (church (Nat.pair a i))) (cpsSearchCont G a i K)) := by
  let L := cpsSearchLoop G
  have hL : Scoped 0 L := cpsSearchLoop_closed hg
  have sG (d : Nat) (t : Term) := substAt_scoped G d t (scoped_mono hg (Nat.zero_le d))
  have sL (d : Nat) (t : Term) := substAt_scoped L d t (scoped_mono hL (Nat.zero_le d))
  have sP (d : Nat) (t : Term) := substAt_scoped churchNatPair d t (scoped_mono churchNatPair_closed (Nat.zero_le d))
  have sZ (d : Nat) (t : Term) := substAt_scoped churchIsZero d t (scoped_mono churchIsZero_closed (Nat.zero_le d))
  have sS (d : Nat) (t : Term) := substAt_scoped churchSuccessor d t (scoped_mono churchSuccessor_closed (Nat.zero_le d))
  have sA (d : Nat) (t : Term) := substAt_scoped (church a) d t (scoped_mono (church_closed a) (Nat.zero_le d))
  have sI (d : Nat) (t : Term) := substAt_scoped (church i) d t (scoped_mono (church_closed i) (Nat.zero_le d))
  have lL (d : Nat) := liftBy_closed d hL
  have lA (d : Nat) := liftBy_closed d (church_closed a)
  have lI (d : Nat) := liftBy_closed d (church_closed i)
  let T1 : Term := .abs (.abs (.abs
    (.app (.app G (.app (.app churchNatPair (.var 2)) (.var 1)))
      (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
        (.app (.app (.app L (.var 3)) (.app churchSuccessor (.var 2))) (.var 1)))))))
  let T2 : Term := .abs (.abs
    (.app (.app G (.app (.app churchNatPair (church a)) (.var 1)))
      (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
        (.app (.app (.app L (church a)) (.app churchSuccessor (.var 2))) (.var 1))))))
  let T3 : Term := .abs
    (.app (.app G (.app (.app churchNatPair (church a)) (church i)))
      (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (church i)))
        (.app (.app (.app L (church a)) (.app churchSuccessor (church i))) (.var 1)))))
  have h0 : Beta L (.app (cpsSearchBody G) L) := lambdaFix_unfold (cpsSearchBody_closed hg)
  have h1 : Beta (.app (cpsSearchBody G) L) T1 := by
    simpa [cpsSearchBody, T1, substAt, sG, sP, sZ, sS, lL] using
      (Beta.contract (.abs (.abs (.abs
        (.app (.app G (.app (.app churchNatPair (.var 2)) (.var 1)))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
            (.app (.app (.app (.var 4) (.var 3)) (.app churchSuccessor (.var 2))) (.var 1)))))))) L)
  have h2 : Beta (.app T1 (church a)) T2 := by
    simpa [T1, T2, substAt, sG, sL, sP, sZ, sS, lA] using
      (Beta.contract (.abs (.abs
        (.app (.app G (.app (.app churchNatPair (.var 2)) (.var 1)))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
            (.app (.app (.app L (.var 3)) (.app churchSuccessor (.var 2))) (.var 1))))))) (church a))
  have h3 : Beta (.app T2 (church i)) T3 := by
    simpa [T2, T3, substAt, sG, sL, sP, sZ, sS, sA, lI] using
      (Beta.contract (.abs
        (.app (.app G (.app (.app churchNatPair (church a)) (.var 1)))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
            (.app (.app (.app L (church a)) (.app churchSuccessor (.var 2))) (.var 1)))))) (church i))
  have h4 : Beta (.app T3 K)
      (.app (.app G (.app (.app churchNatPair (church a)) (church i))) (cpsSearchCont G a i K)) := by
    simpa [T3, cpsSearchCont, substAt, liftBy, sG, sL, sP, sZ, sS, sA, sI] using
      (Beta.contract
        (.app (.app G (.app (.app churchNatPair (church a)) (church i)))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (church i)))
            (.app (.app (.app L (church a)) (.app churchSuccessor (church i))) (.var 1))))) K)
  apply Reaches.step (.appLeft (.appLeft (.appLeft h0)))
  apply Reaches.step (.appLeft (.appLeft (.appLeft h1)))
  apply Reaches.step (.appLeft (.appLeft h2))
  apply Reaches.step (.appLeft h3)
  apply Reaches.step h4
  exact reaches_appLeft (reaches_appRight G (churchNatPair_run a i)) _

theorem cpsSearchLoop_zero {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g)
    (a i : Nat) (K : Term) (hzero : 0 ∈ g (Nat.pair a i)) :
    Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K) (.app K (church i)) := by
  apply reaches_trans (cpsSearchLoop_dispatch hg.1 a i K)
  apply reaches_trans ((hg.2 _ (cpsSearchCont G a i K)).1 0 hzero)
  simpa using cpsSearchCont_run hg.1 a i 0 K

theorem cpsSearchLoop_positive {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g)
    (a i v : Nat) (K : Term) (hpos : v + 1 ∈ g (Nat.pair a i)) :
    Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K)
      (.app (.app (.app (cpsSearchLoop G) (church a)) (church (i + 1))) K) := by
  apply reaches_trans (cpsSearchLoop_dispatch hg.1 a i K)
  apply reaches_trans ((hg.2 _ (cpsSearchCont G a i K)).1 (v + 1) hpos)
  simpa using cpsSearchCont_run hg.1 a i (v + 1) K

theorem cpsSearchLoop_blocked {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g)
    (a i : Nat) (K : Term) (hnone : g (Nat.pair a i) = Part.none) :
    ¬ ∃ N, Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K) N ∧
      ¬ ∃ u, Beta N u :=
  noNormal_backward (cpsSearchLoop_dispatch hg.1 a i K)
    ((hg.2 _ (cpsSearchCont G a i K)).2 hnone)

theorem cpsSearchLoop_advance {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g)
    (a i d : Nat) (K : Term)
    (hpositive : ∀ j, j < d → ∃ v, v + 1 ∈ g (Nat.pair a (i + j))) :
    Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K)
      (.app (.app (.app (cpsSearchLoop G) (church a)) (church (i + d))) K) := by
  induction d generalizing i with
  | zero => simpa using Reaches.refl (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K)
  | succ d ih =>
    obtain ⟨v, hv⟩ := hpositive 0 (by omega)
    have hv' : v + 1 ∈ g (Nat.pair a i) := by simpa using hv
    have hp : ∀ j, j < d → ∃ v, v + 1 ∈ g (Nat.pair a ((i + 1) + j)) := by
      intro j hj
      have h := hpositive (j + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have htail := ih (i + 1) hp
    have hstep := cpsSearchLoop_positive hg a i v K hv'
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reaches_trans hstep htail

theorem cpsSearchLoop_finite_success {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g)
    (a i d : Nat) (K : Term)
    (hpositive : ∀ j, j < d → ∃ v, v + 1 ∈ g (Nat.pair a (i + j)))
    (hzero : 0 ∈ g (Nat.pair a (i + d))) :
    Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K)
      (.app K (church (i + d))) :=
  reaches_trans (cpsSearchLoop_advance hg a i d K hpositive) (cpsSearchLoop_zero hg a (i + d) K hzero)

theorem cpsSearchLoop_finite_blocked {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g)
    (a i d : Nat) (K : Term)
    (hpositive : ∀ j, j < d → ∃ v, v + 1 ∈ g (Nat.pair a (i + j)))
    (hnone : g (Nat.pair a (i + d)) = Part.none) :
    ¬ ∃ N, Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K) N ∧
      ¬ ∃ u, Beta N u :=
  noNormal_backward (cpsSearchLoop_advance hg a i d K hpositive)
    (cpsSearchLoop_blocked hg a (i + d) K hnone)

theorem cpsSearchLoop_code_success {G : Term} {f : Nat.Partrec.Code}
    (hg : CPSRepresents G (Nat.Partrec.Code.eval f)) (a i m : Nat) (K : Term)
    (hm : m ∈ Nat.Partrec.Code.eval (.rfind' f) (Nat.pair a i)) :
    Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church i)) K) (.app K (church m)) := by
  rw [Nat.Partrec.Code.eval, Nat.unpaired, Nat.unpair_pair] at hm
  obtain ⟨d, hd, heq⟩ := (Part.mem_map_iff (fun d => d + i)).mp hm
  obtain ⟨hz, hp⟩ := Nat.mem_rfind.mp hd
  have hzero : 0 ∈ Nat.Partrec.Code.eval f (Nat.pair a (i + d)) := by
    simp only [Part.map_eq_map, Part.mem_map_iff] at hz
    obtain ⟨v, hv, hv0⟩ := hz
    have : v = 0 := by simpa using hv0
    simpa [Nat.add_comm, this] using hv
  have hpositive : ∀ j, j < d → ∃ v, v + 1 ∈ Nat.Partrec.Code.eval f (Nat.pair a (i + j)) := by
    intro j hj
    have hj' := hp hj
    simp only [Part.map_eq_map, Part.mem_map_iff] at hj'
    obtain ⟨v, hv, hv0⟩ := hj'
    have hne : v ≠ 0 := by simpa using hv0
    cases v with
    | zero => contradiction
    | succ v => exact ⟨v, by simpa [Nat.add_comm] using hv⟩
  have hr := cpsSearchLoop_finite_success hg a i d K hpositive hzero
  simpa [Nat.add_comm, ← heq] using hr

/-- The candidate minimizer reads the parameter and initial offset from the
    encoded input. Infinite successful-but-positive search is treated separately. -/
def cpsMinimize (G : Term) : Term :=
  .abs (.abs (.app (.app (.app (cpsSearchLoop G)
    (.app churchNumericLeft (.var 1))) (.app churchNumericRight (.var 1))) (.var 0)))

theorem cpsMinimize_closed {G : Term} (hg : Scoped 0 G) : Scoped 0 (cpsMinimize G) := by
  have hl := scoped_mono (cpsSearchLoop_closed hg) (Nat.zero_le 2)
  have ha := scoped_mono churchNumericLeft_closed (Nat.zero_le 2)
  have hi := scoped_mono churchNumericRight_closed (Nat.zero_le 2)
  simp [cpsMinimize, Scoped, hl, ha, hi]

theorem cpsMinimize_run {G : Term} (hg : Scoped 0 G) (x : Nat) (K : Term) :
    Reaches (.app (.app (cpsMinimize G) (church x)) K)
      (.app (.app (.app (cpsSearchLoop G) (church x.unpair.1)) (church x.unpair.2)) K) := by
  let L := cpsSearchLoop G
  have hl : Scoped 0 L := cpsSearchLoop_closed hg
  have hl1 := substAt_scoped L 1 (church x) (scoped_mono hl (Nat.zero_le 1))
  have ha1 := substAt_scoped churchNumericLeft 1 (church x) (scoped_mono churchNumericLeft_closed (Nat.zero_le 1))
  have hi1 := substAt_scoped churchNumericRight 1 (church x) (scoped_mono churchNumericRight_closed (Nat.zero_le 1))
  have hx1 := liftBy_closed 1 (church_closed x)
  have hb1 : Beta (.app (cpsMinimize G) (church x))
      (.abs (.app (.app (.app L (.app churchNumericLeft (church x)))
        (.app churchNumericRight (church x))) (.var 0))) := by
    change Beta (.app (.abs (.abs (.app (.app (.app L (.app churchNumericLeft (.var 1)))
      (.app churchNumericRight (.var 1))) (.var 0)))) (church x)) _
    simpa [substAt, hl1, ha1, hi1, hx1] using
      (Beta.contract (.abs (.app (.app (.app L (.app churchNumericLeft (.var 1)))
        (.app churchNumericRight (.var 1))) (.var 0))) (church x))
  have hl0 := substAt_scoped L 0 K hl
  have ha0 := substAt_scoped churchNumericLeft 0 K churchNumericLeft_closed
  have hi0 := substAt_scoped churchNumericRight 0 K churchNumericRight_closed
  have hx0 := substAt_scoped (church x) 0 K (church_closed x)
  have hb2 : Beta (.app (.abs (.app (.app (.app L (.app churchNumericLeft (church x)))
      (.app churchNumericRight (church x))) (.var 0))) K)
      (.app (.app (.app L (.app churchNumericLeft (church x))) (.app churchNumericRight (church x))) K) := by
    simpa [substAt, liftBy, hl0, ha0, hi0, hx0] using
      (Beta.contract (.app (.app (.app L (.app churchNumericLeft (church x)))
        (.app churchNumericRight (church x))) (.var 0)) K)
  apply Reaches.step (.appLeft hb1)
  apply Reaches.step hb2
  have hleft := churchNumericLeft_run x
  have hright := churchNumericRight_run x
  exact reaches_trans (reaches_appLeft (reaches_appLeft (reaches_appRight L hleft) _) K)
    (reaches_appLeft (reaches_appRight (.app L (church x.unpair.1)) hright) K)

theorem cpsMinimize_code_success {G : Term} {f : Nat.Partrec.Code}
    (hg : CPSRepresents G (Nat.Partrec.Code.eval f)) (x m : Nat) (K : Term)
    (hm : m ∈ Nat.Partrec.Code.eval (.rfind' f) x) :
    Reaches (.app (.app (cpsMinimize G) (church x)) K) (.app K (church m)) := by
  have hm' : m ∈ Nat.Partrec.Code.eval (.rfind' f) (Nat.pair x.unpair.1 x.unpair.2) := by
    simpa [Nat.pair_unpair] using hm
  exact reaches_trans (cpsMinimize_run hg.1 x K)
    (cpsSearchLoop_code_success hg x.unpair.1 x.unpair.2 m K hm')

theorem cpsMinimize_finite_blocked {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g)
    (x d : Nat) (K : Term)
    (hpositive : ∀ j, j < d → ∃ v, v + 1 ∈ g (Nat.pair x.unpair.1 (x.unpair.2 + j)))
    (hnone : g (Nat.pair x.unpair.1 (x.unpair.2 + d)) = Part.none) :
    ¬ ∃ N, Reaches (.app (.app (cpsMinimize G) (church x)) K) N ∧ ¬ ∃ u, Beta N u :=
  noNormal_backward (cpsMinimize_run hg.1 x K)
    (cpsSearchLoop_finite_blocked hg x.unpair.1 x.unpair.2 d K hpositive hnone)

#print axioms lambdaFix_unfold
#print axioms cpsSearchCont_run
#print axioms cpsSearchLoop_dispatch
#print axioms cpsSearchLoop_finite_success
#print axioms cpsSearchLoop_finite_blocked
#print axioms cpsSearchLoop_code_success
#print axioms cpsMinimize_code_success
#print axioms cpsMinimize_finite_blocked

end LambdaTuring
