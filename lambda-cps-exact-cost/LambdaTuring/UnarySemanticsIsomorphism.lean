/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.UnaryCodePadding
public meta import LambdaTuring.UnaryCodePadding
public import LambdaTuring.SemanticMatching
public meta import LambdaTuring.SemanticMatching

@[expose] public section
namespace LambdaTuring

/-- The closed term at an index of the effective canonical-code enumeration. -/
noncomputable def closedTermAt (i : Nat) : Term := closedCodeDecode (closedCodeEnum i)

theorem closedTermAt_computable : Computable closedTermAt :=
  closedCodeDecode_primrec.to_comp.comp closedCodeEnum_computable

theorem closedTermAt_closed (i : Nat) : Scoped 0 (closedTermAt i) :=
  closedCodeEnum_decode_closed i

theorem closedTermAt_rank (t : Term) (ht : Scoped 0 t) :
    closedTermAt (closedCodeRank (Encodable.encode t)) = t := by
  have hv := (closedCodeTest_encode t).2 ht
  change closedCodeDecode (closedCodeEnum (closedCodeRank (Encodable.encode t))) = t
  rw [closedCodeEnum_rank _ hv, closedCodeDecode_encode]

theorem closedTermAt_encode (i : Nat) : Encodable.encode (closedTermAt i) = closedCodeEnum i :=
  closedCodeEnum_code i

theorem closedTermAt_rank_index (i : Nat) : closedCodeRank (Encodable.encode (closedTermAt i)) = i := by
  rw [closedTermAt_encode, closedCodeRank_enum]

/-- A code index is compiled to a closed term and tagged to guarantee a
syntactic injection before conversion to a closed-term index. -/
noncomputable def codeToClosedIndex (i : Nat) : Nat :=
  closedCodeRank (Encodable.encode
    (syntaxPadding (i, compileLambdaTotal (Denumerable.ofNat Nat.Partrec.Code i))))

theorem codeToClosedIndex_computable : Computable codeToClosedIndex := by
  have hterm : Computable (fun i : Nat =>
      syntaxPadding (i, compileLambdaTotal (Denumerable.ofNat Nat.Partrec.Code i))) :=
    syntaxPadding_primrec.to_comp.comp (Computable.id.pair
      (primrec_compileLambdaTotal.to_comp.comp (Computable.ofNat Nat.Partrec.Code)))
  exact closedCodeRank_computable.comp (Computable.encode.comp hterm)

theorem codeToClosedIndex_injective : Function.Injective codeToClosedIndex := by
  intro a b hab
  let t : Nat → Term := fun i => syntaxPadding (i, compileLambdaTotal (Denumerable.ofNat Nat.Partrec.Code i))
  have ht (i : Nat) : Scoped 0 (t i) :=
    syntaxPadding_closed i (compileLambdaTotal_sound (Denumerable.ofNat Nat.Partrec.Code i)).1
  have ha := (closedCodeTest_encode (t a)).2 (ht a)
  have hb := (closedCodeTest_encode (t b)).2 (ht b)
  have he := congrArg closedCodeEnum hab
  change closedCodeEnum (closedCodeRank (Encodable.encode (t a))) =
    closedCodeEnum (closedCodeRank (Encodable.encode (t b))) at he
  rw [closedCodeEnum_rank _ ha, closedCodeEnum_rank _ hb] at he
  have hterm : t a = t b := Encodable.encode_injective he
  have hpairs := syntaxPadding_injective hterm
  exact congrArg Prod.fst hpairs

theorem codeToClosedIndex_value (i x : Nat) :
    numericalValue (closedTermAt (codeToClosedIndex i)) x =
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code i) x := by
  let t := syntaxPadding (i, compileLambdaTotal (Denumerable.ofNat Nat.Partrec.Code i))
  have ht : Scoped 0 t := syntaxPadding_closed i (compileLambdaTotal_sound _).1
  change numericalValue (closedTermAt (closedCodeRank (Encodable.encode t))) x = _
  rw [closedTermAt_rank t ht]
  change numericalValue (syntaxPadding (i, compileLambdaTotal (Denumerable.ofNat Nat.Partrec.Code i))) x = _
  rw [syntaxPadding_numericalValue, (compileLambdaTotal_sound _).2 x]

/-- A fixed uniform evaluator code converts closed syntax to code; an explicit
code tag makes the index translation injective. -/
noncomputable def closedToCodeIndex (u : Nat.Partrec.Code) (j : Nat) : Nat :=
  Encodable.encode (unaryCodePadding (specializeLambdaCode u (closedTermAt j), j))

theorem closedToCodeIndex_computable (u : Nat.Partrec.Code) : Computable (closedToCodeIndex u) := by
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have hspec : Computable (fun j => specializeLambdaCode u (closedTermAt j)) :=
    Nat.Partrec.Code.primrec₂_curry.to_comp.comp (Computable.const u) (henc.comp closedTermAt_computable)
  exact Computable.encode.comp (unaryCodePadding_primrec.to_comp.comp (hspec.pair Computable.id))

theorem closedToCodeIndex_injective (u : Nat.Partrec.Code) : Function.Injective (closedToCodeIndex u) := by
  intro a b hab
  have hpad := Encodable.encode_injective hab
  have hpairs := unaryCodePadding_injective hpad
  exact congrArg Prod.snd hpairs

theorem closedToCodeIndex_value (u : Nat.Partrec.Code) (hu : UniformLambdaCode u) (j x : Nat) :
    Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (closedToCodeIndex u j)) x =
      numericalValue (closedTermAt j) x := by
  change Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code
    (Encodable.encode (unaryCodePadding (specializeLambdaCode u (closedTermAt j), j)))) x = _
  rw [Denumerable.ofNat_encode, unaryCodePadding_eval, specializeLambdaCode_eval u hu]

/-- Uniform computable injections in both directions preserve the entire
partial numerical function; the evaluator code is fixed once by existence. -/
theorem unary_numerical_injections :
    ∃ f g : Nat → Nat, Computable f ∧ Computable g ∧ Function.Injective f ∧ Function.Injective g ∧
      (∀ i x, numericalValue (closedTermAt (f i)) x = Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code i) x) ∧
      (∀ j x, Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (g j)) x = numericalValue (closedTermAt j) x) := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  exact ⟨codeToClosedIndex, closedToCodeIndex u, codeToClosedIndex_computable,
    closedToCodeIndex_computable u, codeToClosedIndex_injective, closedToCodeIndex_injective u,
    codeToClosedIndex_value, closedToCodeIndex_value u hu⟩

/-- The recursive-code and closed-term numberings are computably isomorphic
as numberings of partial numerical functions. -/
theorem unary_semantics_index_isomorphism :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧
      ∀ i x, numericalValue (closedTermAt (e i)) x =
        Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code i) x := by
  obtain ⟨f, g, hfc, hgc, hfi, hgi, hfr, hgr⟩ := unary_numerical_injections
  let left : Nat → Nat → Part Nat := fun i => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code i)
  let right : Nat → Nat → Part Nat := fun j => numericalValue (closedTermAt j)
  have hf : ∀ i, left i = right (f i) := fun i => funext (fun x => (hfr i x).symm)
  have hg : ∀ j, right j = left (g j) := fun j => funext (fun x => (hgr j x).symm)
  obtain ⟨e, he, hei, hlabels⟩ :=
    computable_permutation_of_label_injections left right f g hfc hgc hfi hgi hf hg
  exact ⟨e, he, hei, fun i x => (congrFun (hlabels i) x).symm⟩

/-- A computable bijection between recursive codes and all closed lambda
terms, preserving the whole partial numerical function. The reverse map is
total on all terms, and its inverse law is asserted for closed terms. -/
theorem code_closedTerm_unary_isomorphism :
    ∃ F : Nat.Partrec.Code → Term, ∃ G : Term → Nat.Partrec.Code,
      Computable F ∧ Computable G ∧
      (∀ c, Scoped 0 (F c)) ∧
      (∀ c, G (F c) = c) ∧
      (∀ t, Scoped 0 t → F (G t) = t) ∧
      (∀ c x, numericalValue (F c) x = Nat.Partrec.Code.eval c x) := by
  obtain ⟨e, he, hei, hvalue⟩ := unary_semantics_index_isomorphism
  let F : Nat.Partrec.Code → Term := fun c => closedTermAt (e (Encodable.encode c))
  let G : Term → Nat.Partrec.Code := fun t =>
    Denumerable.ofNat Nat.Partrec.Code (e.symm (closedCodeRank (Encodable.encode t)))
  have hF : Computable F := closedTermAt_computable.comp (he.comp Computable.encode)
  have hG : Computable G := (Computable.ofNat Nat.Partrec.Code).comp
    (hei.comp (closedCodeRank_computable.comp Computable.encode))
  refine ⟨F, G, hF, hG, ?_, ?_, ?_, ?_⟩
  · intro c
    exact closedTermAt_closed _
  · intro c
    change Denumerable.ofNat Nat.Partrec.Code
      (e.symm (closedCodeRank (Encodable.encode (closedTermAt (e (Encodable.encode c)))))) = c
    rw [closedTermAt_rank_index, e.symm_apply_apply, Denumerable.ofNat_encode]
  · intro t ht
    change closedTermAt (e (Encodable.encode
      (Denumerable.ofNat Nat.Partrec.Code (e.symm (closedCodeRank (Encodable.encode t)))))) = t
    rw [Denumerable.encode_ofNat, e.apply_symm_apply, closedTermAt_rank t ht]
  · intro c x
    change numericalValue (closedTermAt (e (Encodable.encode c))) x = Nat.Partrec.Code.eval c x
    rw [hvalue (Encodable.encode c) x, Denumerable.ofNat_encode]

/-- The isomorphism preserves every numerical result and the absence of
any numerical result, without identifying that absence with divergence. -/
theorem code_closedTerm_unary_observations :
    ∃ F : Nat.Partrec.Code → Term, ∃ G : Term → Nat.Partrec.Code,
      Computable F ∧ Computable G ∧
      (∀ c, Scoped 0 (F c)) ∧
      (∀ c, G (F c) = c) ∧
      (∀ t, Scoped 0 t → F (G t) = t) ∧
      (∀ c x m, NumericalResult (F c) x m ↔ m ∈ Nat.Partrec.Code.eval c x) ∧
      (∀ c x, (∀ m, ¬ NumericalResult (F c) x m) ↔ Nat.Partrec.Code.eval c x = Part.none) := by
  obtain ⟨F, G, hF, hG, hclosed, hleft, hright, hvalue⟩ := code_closedTerm_unary_isomorphism
  refine ⟨F, G, hF, hG, hclosed, hleft, hright, ?_, ?_⟩
  · intro c x m
    rw [← mem_numericalValue_iff, hvalue]
  · intro c x
    rw [← numericalValue_none_iff, hvalue]

#print axioms codeToClosedIndex_injective
#print axioms codeToClosedIndex_value
#print axioms closedToCodeIndex_injective
#print axioms closedToCodeIndex_value
#print axioms unary_numerical_injections
#print axioms unary_semantics_index_isomorphism
#print axioms code_closedTerm_unary_isomorphism
#print axioms code_closedTerm_unary_observations
end LambdaTuring
