module
public import KRChallenge
#check KnasterReichbach.exists_homeomorph_extension
example {A B : Set (ℕ → Bool)} (hA : IsClosed A) (hnA : IsNowhereDense A)
    (hB : IsClosed B) (hnB : IsNowhereDense B) (h : A ≃ₜ B) :
    ∃ H : (ℕ → Bool) ≃ₜ (ℕ → Bool), ∀ a : A, H a.val = (h a).val :=
  KnasterReichbach.exists_homeomorph_extension hA hnA hB hnB h

-- BEGIN material-imported-definition audit
example {A : Set KnasterReichbach.CantorSpace} :
    IsNowhereDense A ↔ interior (closure A) = ∅ := Iff.rfl
example {A : Set KnasterReichbach.CantorSpace} :
    IsClopen A ↔ IsClosed A ∧ IsOpen A := Iff.rfl
example : KnasterReichbach.CantorSpace = (ℕ → Bool) := rfl
example (n : ℕ) : Continuous (fun x : KnasterReichbach.CantorSpace => x n) :=
  continuous_apply n
example {A B : Set KnasterReichbach.CantorSpace} (h : A ≃ₜ B) :
    Function.LeftInverse h.symm h := h.symm_apply_apply
-- END material-imported-definition audit
