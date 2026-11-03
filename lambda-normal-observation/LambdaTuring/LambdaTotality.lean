/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.NumeralReduction
public import LambdaTuring.CPSBottom

@[expose] public section

namespace LambdaTuring

def CodeTotal (c : Nat.Partrec.Code) : Prop := ∀ n, (Nat.Partrec.Code.eval c n).Dom

def ClosedNumericalTotal (t : Term) : Prop :=
  Scoped 0 t ∧ ∀ n, (numericalValue t n).Dom

def closedTotalityCode (u : Nat.Partrec.Code) (t : Term) : Nat.Partrec.Code :=
  if requiredDepth t ≤ 0 then Nat.Partrec.Code.curry u (executableTermEncode t) else bottomCode

theorem closedTotalityCode_primrec (u : Nat.Partrec.Code) : Primrec (closedTotalityCode u) := by
  have henc : Primrec executableTermEncode := Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)
  unfold closedTotalityCode
  exact Primrec.ite (Primrec.nat_le.comp primrec_requiredDepth (Primrec.const 0))
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) henc)
    (Primrec.const bottomCode)

theorem closedTotalityCode_correct (u : Nat.Partrec.Code) (hu : UniformLambdaCode u) (t : Term) :
    ClosedNumericalTotal t ↔ CodeTotal (closedTotalityCode u t) := by
  by_cases h : requiredDepth t ≤ 0
  · have hs : Scoped 0 t := (scoped_iff_requiredDepth_le t 0).2 h
    have he (n : Nat) : Nat.Partrec.Code.eval (closedTotalityCode u t) n = numericalValue t n := by
      rw [closedTotalityCode, if_pos h, Nat.Partrec.Code.eval_curry, hu]
    simp only [ClosedNumericalTotal, CodeTotal, hs, true_and, he]
  · have hs : ¬ Scoped 0 t := fun hs => h ((scoped_iff_requiredDepth_le t 0).1 hs)
    have hd : ¬ CodeTotal (closedTotalityCode u t) := by
      intro htotal
      have hzero := htotal 0
      rw [closedTotalityCode, if_neg h, bottomCode_eval] at hzero
      exact hzero
    simp [ClosedNumericalTotal, hs, hd]

theorem codeTotal_manyOne_closedNumericalTotal : ManyOneReducible CodeTotal ClosedNumericalTotal := by
  refine ⟨compileLambdaTotal, primrec_compileLambdaTotal.to_comp, ?_⟩
  intro c
  constructor
  · intro ht
    refine ⟨(compileLambdaTotal_sound c).1, ?_⟩
    intro n
    rw [(compileLambdaTotal_sound c).2 n]
    exact ht n
  · intro ht n
    rw [← (compileLambdaTotal_sound c).2 n]
    exact ht.2 n

theorem closedNumericalTotal_manyOne_codeTotal : ManyOneReducible ClosedNumericalTotal CodeTotal := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  exact ⟨closedTotalityCode u, (closedTotalityCode_primrec u).to_comp, closedTotalityCode_correct u hu⟩

theorem closedNumericalTotal_manyOne_equiv : ManyOneEquiv CodeTotal ClosedNumericalTotal :=
  ⟨codeTotal_manyOne_closedNumericalTotal, closedNumericalTotal_manyOne_codeTotal⟩

#print axioms closedNumericalTotal_manyOne_equiv

end LambdaTuring
