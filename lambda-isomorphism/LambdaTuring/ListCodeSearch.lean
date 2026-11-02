/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The connection to Mathlib's list-code search follows the `rfind` case of
Mathlib/Computability/TuringMachine/Config.lean, copyright 2020 Mario Carneiro,
released under Apache 2.0. The proof below handles partial tests explicitly.
-/
module

public import LambdaTuring.ListCodeRecursionBridge
public meta import LambdaTuring.ListCodeRecursionBridge

@[expose] public section

namespace LambdaTuring

def listSearchStep (F : Turing.ToPartrec.Code) (w : List Nat) :
    Part (List Nat ⊕ List Nat) :=
  (F.eval w).bind fun y =>
    Part.some (if y.headI = 0 then Sum.inl (w.headI.succ :: w.tail)
      else Sum.inr (w.headI.succ :: w.tail))

set_option backward.isDefEq.respectTransparency false in
theorem listSearchStep_stop (F : Turing.ToPartrec.Code) (f : Nat →. Nat)
    (v : List Nat) (hf : ∀ a, F.eval (a :: v) = (f a).map (fun r => [r]))
    (n : Nat) (out : List Nat) :
    Sum.inl out ∈ listSearchStep F (n :: v) ↔ 0 ∈ f n ∧ out = (n+1) :: v := by
  simp only [listSearchStep, List.headI_cons, List.tail_cons, hf, Part.bind_map,
    Part.mem_bind_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨a, ha, he⟩
    split_ifs at he with hz
    · subst a
      simpa using And.intro ha (Sum.inl.inj he)
  · rintro ⟨ha, rfl⟩
    exact ⟨0, ha, by simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem listSearchStep_continue (F : Turing.ToPartrec.Code) (f : Nat →. Nat)
    (v : List Nat) (hf : ∀ a, F.eval (a :: v) = (f a).map (fun r => [r]))
    (n : Nat) (next : List Nat) :
    Sum.inr next ∈ listSearchStep F (n :: v) ↔
      (∃ r, r ∈ f n ∧ r ≠ 0) ∧ next = (n+1) :: v := by
  simp only [listSearchStep, List.headI_cons, List.tail_cons, hf, Part.bind_map,
    Part.mem_bind_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨a, ha, he⟩
    split_ifs at he with hz
    exact ⟨⟨a, ha, hz⟩, Sum.inr.inj he⟩
  · rintro ⟨⟨a, ha, hz⟩, rfl⟩
    exact ⟨a, ha, by simp [hz]⟩

set_option backward.isDefEq.respectTransparency false in
theorem listSearchFix_forward (F : Turing.ToPartrec.Code) (f : Nat →. Nat)
    (v : List Nat) (hf : ∀ a, F.eval (a :: v) = (f a).map (fun r => [r]))
    (out state : List Nat) (hout : out ∈ PFun.fix (listSearchStep F) state) :
    ∀ n, state = n :: v → ∃ k, n ≤ k ∧ 0 ∈ f k ∧
      (∀ j, n ≤ j → j < k → ∃ r, r ∈ f j ∧ r ≠ 0) ∧ out = (k+1) :: v := by
  refine PFun.fixInduction' hout ?_ ?_
  · intro state hstop n hs
    subst state
    obtain ⟨hz, heq⟩ := (listSearchStep_stop F f v hf n out).1 hstop
    refine ⟨n, le_rfl, hz, ?_, heq⟩
    intro j hj hj'
    omega
  · intro state next hrest hstep ih n hs
    subst state
    obtain ⟨hn, hnext⟩ := (listSearchStep_continue F f v hf n next).1 hstep
    subst next
    obtain ⟨k, hk, hz, hp, heq⟩ := ih (n+1) rfl
    refine ⟨k, by omega, hz, ?_, heq⟩
    intro j hj hj'
    by_cases hjn : j = n
    · subst j
      exact hn
    · exact hp j (by omega) hj'

set_option backward.isDefEq.respectTransparency false in
theorem listSearchFix_from (F : Turing.ToPartrec.Code) (f : Nat →. Nat)
    (v : List Nat) (hf : ∀ a, F.eval (a :: v) = (f a).map (fun r => [r]))
    (n d : Nat) (hzero : 0 ∈ f (n+d))
    (hprev : ∀ j, n ≤ j → j < n+d → ∃ r, r ∈ f j ∧ r ≠ 0) :
    (n+d+1) :: v ∈ PFun.fix (listSearchStep F) (n :: v) := by
  induction d generalizing n with
  | zero =>
    apply PFun.mem_fix_iff.2
    left
    apply (listSearchStep_stop F f v hf n _).2
    simpa using hzero
  | succ d ih =>
    apply PFun.mem_fix_iff.2
    right
    refine ⟨(n+1) :: v, ?_, ?_⟩
    · apply (listSearchStep_continue F f v hf n _).2
      exact ⟨hprev n (le_refl n) (by omega), rfl⟩
    · have hzero' : 0 ∈ f ((n+1)+d) := by
        convert hzero using 1
        congr 1
        omega
      have hprev' : ∀ j, n+1 ≤ j → j < (n+1)+d → ∃ r, r ∈ f j ∧ r ≠ 0 := by
        intro j hj hj'
        exact hprev j (by omega) (by omega)
      have h := ih (n+1) hzero' hprev'
      convert h using 1
      congr 1
      omega

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some in
set_option backward.isDefEq.respectTransparency false in
theorem listCode_rfind_partial (F : Turing.ToPartrec.Code) (f : Nat →. Nat)
    (v : List Nat) (hf : ∀ a, F.eval (a :: v) = (f a).map (fun r => [r])) :
    (Turing.ToPartrec.Code.rfind F).eval v =
      (Nat.rfind (fun a => (f a).map (fun r => r = 0))).map (fun r => [r]) := by
  apply Part.ext
  intro out
  simp only [Turing.ToPartrec.Code.rfind, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some,
    Turing.ToPartrec.Code.cons_eval, Turing.ToPartrec.Code.comp_eval,
    Turing.ToPartrec.Code.fix_eval, Turing.ToPartrec.Code.tail_eval,
    Turing.ToPartrec.Code.succ_eval, Turing.ToPartrec.Code.zero'_eval,
    List.headI_cons, Turing.ToPartrec.Code.pred_eval, Part.map_some,
    Part.mem_bind_iff, Part.mem_map_iff, Nat.mem_rfind, List.tail_cons,
    Part.mem_some_iff, Part.map_bind]
  change (∃ a, a ∈ PFun.fix (listSearchStep F) (0 :: v) ∧ out = [a.headI.pred]) ↔ _
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, exists_eq_right]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hz, hp, rfl⟩ := listSearchFix_forward F f v hf w (0 :: v) hw 0 rfl
    refine ⟨k, ⟨hz, ?_⟩, ?_⟩
    · intro m hm
      exact hp m (Nat.zero_le _) hm
    · simp
  · rintro ⟨k, ⟨hz, hp⟩, rfl⟩
    refine ⟨(k+1) :: v, ?_, ?_⟩
    · have h := listSearchFix_from F f v hf 0 k (by simpa using hz)
        (by intro j hj hj'; exact hp (by simpa using hj'))
      simpa using h
    · simp

#print axioms listCode_rfind_partial
end LambdaTuring
