/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.CodedIsomorphism
public meta import LambdaTuring.CodedIsomorphism

@[expose] public section
namespace LambdaTuring

/-- If every edge in an increasing computable matching sequence has relation
`R`, its computable limit retains `R`. No decision procedure for `R` is used. -/
theorem computable_equiv_of_matching_relation (R : Nat → Nat → Prop)
    (forward backward : Nat → Nat → Option Nat)
    (hf : Computable₂ forward) (hb : Computable₂ backward)
    (hinv : ∀ n x y, forward n x = some y ↔ backward n y = some x)
    (hmono : ∀ m n x y, m ≤ n → forward m x = some y → forward n x = some y)
    (hcoverF : ∀ x, ∃ n y, forward n x = some y)
    (hcoverB : ∀ y, ∃ n x, backward n y = some x)
    (hrel : ∀ n x y, forward n x = some y → R x y) :
    ∃ f g : Nat → Nat, Computable f ∧ Computable g ∧
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) ∧ (∀ x, R x (f x)) := by
  let pf : Nat → Part Nat := fun x => Nat.rfindOpt (fun n => forward n x)
  let pb : Nat → Part Nat := fun y => Nat.rfindOpt (fun n => backward n y)
  have hpf : Partrec pf := Partrec.rfindOpt (hf.comp Computable.snd Computable.fst).to₂
  have hpb : Partrec pb := Partrec.rfindOpt (hb.comp Computable.snd Computable.fst).to₂
  have hdomf (x : Nat) : (pf x).Dom := by
    apply Nat.rfindOpt_dom.mpr
    obtain ⟨n, y, h⟩ := hcoverF x
    exact ⟨n, y, Option.mem_def.mpr h⟩
  have hdomb (y : Nat) : (pb y).Dom := by
    apply Nat.rfindOpt_dom.mpr
    obtain ⟨n, x, h⟩ := hcoverB y
    exact ⟨n, x, Option.mem_def.mpr h⟩
  let f : Nat → Nat := fun x => (pf x).get (hdomf x)
  let g : Nat → Nat := fun y => (pb y).get (hdomb y)
  have hfc : Computable f := hpf.of_eq_tot (fun x => Part.get_mem (hdomf x))
  have hgc : Computable g := hpb.of_eq_tot (fun y => Part.get_mem (hdomb y))
  have hbm (m n y x : Nat) (hmn : m ≤ n) (h : backward m y = some x) :
      backward n y = some x :=
    (hinv n x y).1 (hmono m n x y hmn ((hinv m x y).2 h))
  have hgf (x : Nat) : g (f x) = x := by
    have hmem : f x ∈ pf x := Part.get_mem (hdomf x)
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hmem
    have hback : backward n (f x) = some x := (hinv n x (f x)).1 (Option.mem_def.mp hn)
    have hx : x ∈ pb (f x) := (Nat.rfindOpt_mono (fun {a m n} hmn h => by
      exact Option.mem_def.mpr (hbm m n (f x) a hmn (Option.mem_def.mp h)))).2
      ⟨n, Option.mem_def.mpr hback⟩
    exact Part.mem_unique (Part.get_mem (hdomb (f x))) hx
  have hfg (y : Nat) : f (g y) = y := by
    have hmem : g y ∈ pb y := Part.get_mem (hdomb y)
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hmem
    have hfor : forward n (g y) = some y := (hinv n (g y) y).2 (Option.mem_def.mp hn)
    have hy : y ∈ pf (g y) := (Nat.rfindOpt_mono (fun {a m n} hmn h => by
      exact Option.mem_def.mpr (hmono m n (g y) a hmn (Option.mem_def.mp h)))).2
      ⟨n, Option.mem_def.mpr hfor⟩
    exact Part.mem_unique (Part.get_mem (hdomf (g y))) hy
  refine ⟨f, g, hfc, hgc, hgf, hfg, ?_⟩
  intro x
  have hmem : f x ∈ pf x := Part.get_mem (hdomf x)
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hmem
  exact hrel n x (f x) (Option.mem_def.mp hn)


/-- The old finite matching stages preserve any equality-valued semantics.
This uses equality's symmetry and transitivity, without deciding equality. -/
theorem matchingStages_preserve_labels {σ : Type} (left right : Nat → σ) (f g : Nat → Nat)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfr : ∀ x, left x = right (f x)) (hgr : ∀ y, right y = left (g y))
    (n x y : Nat) (hxy : (x, y) ∈ matchingStages f g n) : left x = right y := by
  let A : Nat → Prop := fun i => left i = left x
  let B : Nat → Prop := fun j => right j = left x
  have hf : ∀ i, A i ↔ B (f i) := by
    intro i
    change (left i = left x) ↔ (right (f i) = left x)
    rw [hfr i]
  have hg : ∀ j, B j ↔ A (g j) := by
    intro j
    change (right j = left x) ↔ (left (g j) = left x)
    rw [hgr j]
  have hv := matchingStages_valid A B f g hfi hgi hf hg n
  have he : A x ↔ B y := hv.2.2 x y hxy
  exact (he.1 rfl).symm

/-- Computable injections that preserve equality of labels in both directions
can be extended to a computable permutation preserving all labels. -/
theorem computable_permutation_of_label_injections {σ : Type} (left right : Nat → σ)
    (f g : Nat → Nat) (hfc : Computable f) (hgc : Computable g)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfr : ∀ x, left x = right (f x)) (hgr : ∀ y, right y = left (g y)) :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧ ∀ x, left x = right (e x) := by
  let stages := matchingStages f g
  let forward : Nat → Nat → Option Nat := fun n x => edgeForward (stages n) x
  let backward : Nat → Nat → Option Nat := fun n y => edgeBackward (stages n) y
  have hs : Computable stages := matchingStages_computable f g hfc hgc
  have hforward : Computable₂ forward := by
    have h : Computable (fun p : Nat × Nat => edgeForward (stages p.1) p.2) :=
      edgeLookup_primrec.to_comp.comp (hs.comp Computable.fst) Computable.snd
    exact h.to₂
  have hbackward : Computable₂ backward := by
    have h : Computable (fun p : Nat × Nat => edgeBackward (stages p.1) p.2) :=
      edgeBackward_primrec.to_comp.comp (hs.comp Computable.fst) Computable.snd
    exact h.to₂
  let A : Nat → Prop := fun _ => True
  let B : Nat → Prop := fun _ => True
  have htriv : ∀ x, A x ↔ B (f x) := fun _ => Iff.rfl
  have htriv' : ∀ y, B y ↔ A (g y) := fun _ => Iff.rfl
  have hv (n : Nat) : edgeMatching A B (stages n) :=
    matchingStages_valid A B f g hfi hgi htriv htriv' n
  have hi : ∀ n x y, forward n x = some y ↔ backward n y = some x := by
    intro n
    exact edgeMatching_inverse A B (stages n) (hv n)
  have hm : ∀ m n x y, m ≤ n → forward m x = some y → forward n x = some y := by
    intro m n x y hmn h
    apply edgeLookup_complete (stages n) (hv n).1
    exact matchingStages_mono A B f g hfi hgi htriv htriv' m n x y hmn
      (edgeLookup_sound (stages m) x y h)
  have hcF : ∀ x, ∃ n y, forward n x = some y := by
    intro x
    obtain ⟨y, hy⟩ := (matchingStages_step A B f g hfi hgi htriv htriv' x).2.1
    exact ⟨x + 1, y, edgeLookup_complete (stages (x + 1)) (hv (x + 1)).1 x y hy⟩
  have hcB : ∀ y, ∃ n x, backward n y = some x := by
    intro y
    obtain ⟨x, hx⟩ := (matchingStages_step A B f g hfi hgi htriv htriv' y).2.2
    have hfor := edgeLookup_complete (stages (y + 1)) (hv (y + 1)).1 x y hx
    exact ⟨y + 1, x, (hi (y + 1) x y).1 hfor⟩
  have hr : ∀ n x y, forward n x = some y → left x = right y := by
    intro n x y h
    exact matchingStages_preserve_labels left right f g hfi hgi hfr hgr n x y
      (edgeLookup_sound (stages n) x y h)
  obtain ⟨u, v, huc, hvc, huv, hvu, hrel⟩ :=
    computable_equiv_of_matching_relation (fun x y => left x = right y)
      forward backward hforward hbackward hi hm hcF hcB hr
  let e : Nat ≃ Nat := ⟨u, v, huv, hvu⟩
  exact ⟨e, huc, hvc, hrel⟩

#print axioms computable_equiv_of_matching_relation
#print axioms matchingStages_preserve_labels
#print axioms computable_permutation_of_label_injections
end LambdaTuring
