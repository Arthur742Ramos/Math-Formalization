module

public import SampleCount
public import LabelSamples
public import RestrictionRates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Restriction

open Finset Filter
open scoped Classical Topology
variable {Z : Type} {X Y : Finset Z}

theorem agreement_moment (ok : Z → Z → Prop) (cut p b : ℝ) (hc : 0 ≤ cut) (hp : 0 ≤ p)
    (hb : 0 ≤ b) (cx : cut ≤ p*X.card) (cy : cut ≤ p*Y.card)
    (sparse : ∀ V ⊆ Y, cut ≤ V.card →
      ((X.filter fun x => b*V.card < ((V.filter (ok x)).card:ℝ)).card:ℝ) ≤ cut)
    (I J : Type) [Fintype I] [Fintype J] :
    samples I J (fun (x : X) (y : Y) => ok x y) ≤
      ((p+b^(Fintype.card J))^(Fintype.card I) + p^(Fintype.card J)) *
        Fintype.card (I → X) * Fintype.card (J → Y) := by
  classical
  let ok' := fun (x:X) (y:Y) => ok x y
  have spars (V : Finset Y) (_ : V ⊆ univ) (large : cut ≤ V.card) :
      ((univ.filter (fun x : X => b*V.card < ((V.filter (ok' x)).card:ℝ))).card:ℝ) ≤ p*Fintype.card X := by
    have h := (sparse (labels V) (labels_subset V) (by simpa using large)).trans cx
    have cnt (x : X) : (V.filter (ok' x)).card = ((labels V).filter (ok x)).card := by
      rw [← labels_filter,card_labels]
    have e : (labels (univ.filter (fun x : X => b*V.card < ((V.filter (ok' x)).card:ℝ)))) =
        X.filter (fun x => b*(labels V).card < (((labels V).filter (ok x)).card:ℝ)) := by
      simp only [card_labels]
      let P (x : Z) := b*V.card < (((labels V).filter (ok x)).card:ℝ)
      have e' : (univ.filter (fun x : X => b*V.card < ((V.filter (ok' x)).card:ℝ))) =
          univ.filter (fun x : X => P x) := by ext i; simp only [mem_filter,cnt]; rfl
      rw [e',labels_filter,labels_univ]
    rw [← e,card_labels] at h
    simpa using h
  rw [samples_moment]
  have bound := moment_bound ok' (Fintype.card J) (Fintype.card I) univ cut p b hc hp hb spars _ Subset.rfl
  apply bound.trans
  have ce := pow_le_pow_left₀ hc cy (Fintype.card J)
  rw [mul_pow] at ce
  simp only [card_univ,Fintype.card_coe,Fintype.card_fun,Nat.cast_pow]
  nlinarith only [mul_le_mul_of_nonneg_left ce (by positivity : (0:ℝ)≤(X.card:ℝ)^Fintype.card I)]

end InducedDegreeRepetition.Restriction
