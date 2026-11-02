/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.SearchComputable
public meta import LambdaTuring.SearchComputable

@[expose] public section

namespace LambdaTuring

/-- Once capture-avoiding contraction is primitive recursive, so is the
    finite list of root redex results. -/
theorem primrec_rootReductions_of_subst
    (hsub : Primrec₂ (fun value body => substAt 0 value body)) :
    Primrec₂ rootReductions := by
  have harg : Primrec₂ (fun (p : Term × Term) body => substAt 0 p.2 body) :=
    hsub.comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  have hopt : Primrec (fun p : Term × Term => (termAbs? p.1).map (fun body => substAt 0 p.2 body)) :=
    Primrec.option_map (primrec_termAbs.comp Primrec.fst) harg
  have hlist := Primrec.optionToList.comp hopt
  apply hlist.of_eq
  intro p
  rcases p with ⟨f, x⟩
  cases f <;> simp [termAbs?, rootReductions]


/-- Assemble all reducts of an application from its children's reduct lists. -/
def combineReductions (p : Term × Term × List Term × List Term) : List Term :=
  rootReductions p.1 p.2.1 ++
    p.2.2.1.map (fun g => .app g p.2.1) ++
    p.2.2.2.map (Term.app p.1)

theorem primrec_combineReductions_of_subst
    (hsub : Primrec₂ (fun value body => substAt 0 value body)) :
    Primrec combineReductions := by
  let P := Term × Term × List Term × List Term
  have hr : Primrec (fun p : P => rootReductions p.1 p.2.1) :=
    (primrec_rootReductions_of_subst hsub).comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hm1 : Primrec (fun p : P => p.2.2.1.map (fun g => Term.app g p.2.1)) := by
    apply Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    exact (primrec_app.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to₂
  have hm2 : Primrec (fun p : P => p.2.2.2.map (Term.app p.1)) := by
    apply Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact (primrec_app.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp hr hm1) hm2


open Nat.Partrec

def combineCode (p : Code × Code × List Term × List Term) : List Term :=
  ((decodeTerm p.1).bind fun f => (decodeTerm p.2.1).map fun x =>
    combineReductions (f, x, p.2.2.1, p.2.2.2)).getD []

theorem primrec_combineCode_of_subst
    (hsub : Primrec₂ (fun value body => substAt 0 value body)) :
    Primrec combineCode := by
  let P := Code × Code × List Term × List Term
  let Q := P × Term
  let R := Q × Term
  have hp : Primrec (fun r : R => r.1.1) := Primrec.fst.comp Primrec.fst
  have hf : Primrec (fun r : R => r.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun r : R => r.2) := Primrec.snd
  have hfs : Primrec (fun r : R => r.1.1.2.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp hp
  have hxs : Primrec (fun r : R => r.1.1.2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp hp
  have hbuild : Primrec (fun r : R => combineReductions (r.1.2, r.2, r.1.1.2.2.1, r.1.1.2.2.2)) :=
    (primrec_combineReductions_of_subst hsub).comp (hf.pair (hx.pair (hfs.pair hxs)))
  have hmap : Primrec (fun q : Q => (decodeTerm q.1.2.1).map fun x =>
      combineReductions (q.2, x, q.1.2.2.1, q.1.2.2.2)) :=
    Primrec.option_map (primrec_decodeTerm.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) hbuild.to₂
  have hbind : Primrec (fun p : P => (decodeTerm p.1).bind fun f => (decodeTerm p.2.1).map fun x =>
      combineReductions (f, x, p.2.2.1, p.2.2.2)) :=
    Primrec.option_bind (primrec_decodeTerm.comp Primrec.fst) hmap.to₂
  exact Primrec.option_getD.comp hbind (Primrec.const [])


/-- Structural fold computing all one-step reducts from a canonical term code. -/
def foldReductions (c : Code) : List Term :=
  Code.recOn c [] [] [] []
    (fun f x rf rx => combineCode (f, x, rf, rx))
    (fun _ _ _ _ => []) (fun _ _ _ _ => [])
    (fun _ rec => rec.map Term.abs)

theorem primrec_foldReductions_of_subst
    (hsub : Primrec₂ (fun value body => substAt 0 value body)) : Primrec foldReductions := by
  have hpr : Primrec₂ (fun (_ : Code) (p : Code × Code × List Term × List Term) =>
      combineCode p) := (primrec_combineCode_of_subst hsub).comp Primrec.snd
  have hrf : Primrec₂ (fun (_ : Code) (p : Code × List Term) => p.2.map Term.abs) := by
    apply Primrec.list_map (Primrec.snd.comp Primrec.snd)
    exact (primrec_abs.comp Primrec.snd).to₂
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => [])
    (s := fun _ : Code => []) (l := fun _ : Code => []) (r := fun _ : Code => [])
    (pr := fun _ p => combineCode p) (co := fun _ _ => []) (pc := fun _ _ => [])
    (rf := fun _ p => p.2.map Term.abs)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) (Primrec₂.const _) hrf
  exact h.of_eq (fun _ => rfl)

theorem foldReductions_encodeTerm (t : Term) : foldReductions (encodeTerm t) = betaSteps t := by
  induction t with
  | var n => rfl
  | abs t ih =>
    change (foldReductions (encodeTerm t)).map Term.abs = betaSteps (.abs t)
    simp [ih, betaSteps]
  | app f x ihf ihx =>
    change combineCode (encodeTerm f, encodeTerm x, foldReductions (encodeTerm f), foldReductions (encodeTerm x)) =
      betaSteps (.app f x)
    simp [ihf, ihx, combineCode, decodeTerm_encodeTerm, combineReductions, betaSteps]

theorem primrec_betaSteps_of_subst
    (hsub : Primrec₂ (fun value body => substAt 0 value body)) : Primrec betaSteps :=
  ((primrec_foldReductions_of_subst hsub).comp primrec_encodeTerm).of_eq foldReductions_encodeTerm

theorem numericalValue_partrec_of_subst
    (hsub : Primrec₂ (fun value body => substAt 0 value body)) (t : Term) :
    Nat.Partrec (numericalValue t) :=
  numericalValue_partrec_of_steps (primrec_betaSteps_of_subst hsub) t

#print axioms primrec_betaSteps_of_subst
#print axioms numericalValue_partrec_of_subst
#print axioms primrec_combineCode_of_subst
#print axioms primrec_combineReductions_of_subst
#print axioms primrec_rootReductions_of_subst

end LambdaTuring
