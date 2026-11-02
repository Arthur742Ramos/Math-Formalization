/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang

Adapted from CSLib PR #475, commit cd9bd6ba0537764eb422532400e99b2c90f34256:
the final closure argument uses the pinned Mathlib Relation.church_rosser lemma.
-/
module

public import LambdaTuring.Upstream.Parallel
public meta import LambdaTuring.Upstream.Parallel

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open Relation

theorem beta_reaches_par {a b : Term} (h : ReflTransGen Beta a b) :
    ReflTransGen Par a b := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (beta_subset_par h)

theorem par_reaches_beta {a b : Term} (h : ReflTransGen Par a b) :
    ReflTransGen Beta a b := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.trans (par_subset_betaStar h)

theorem churchRosser_beta {a b c : Term} (hab : ReflTransGen Beta a b)
    (hac : ReflTransGen Beta a c) :
    ∃ d, ReflTransGen Beta b d ∧ ReflTransGen Beta c d := by
  have localDiamond : ∀ a b c, Par a b → Par a c →
      ∃ d, ReflGen Par b d ∧ ReflTransGen Par c d := by
    intro a b c hab hac
    exact ⟨a.dev, .single (par_to_dev hab), .single (par_to_dev hac)⟩
  obtain ⟨d, hbd, hcd⟩ := Relation.church_rosser localDiamond
    (beta_reaches_par hab) (beta_reaches_par hac)
  exact ⟨d, par_reaches_beta hbd, par_reaches_beta hcd⟩

#print axioms churchRosser_beta

end Cslib.LambdaCalculus.Unscoped.Untyped
