/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FoldCode
public meta import LambdaTuring.FoldCode

@[expose] public section

namespace LambdaTuring

/- The validity proof guarantees that the fallback is unreachable; using
the executable decoder avoids choosing a preimage from a proposition. -/
theorem executableTermCode_valid (t : Term) : validCode (encodeTerm t) = true :=
  (validCode_iff _).2 ⟨t, rfl⟩

theorem executableTermDecode_left (t : Term) :
    (decodeTerm (encodeTerm t)).getD (.var 0) = t := by
  rw [decodeTerm_encodeTerm]
  rfl

theorem executableTermDecode_right (c : ValidCode) :
    (⟨encodeTerm ((decodeTerm c.val).getD (.var 0)),
      executableTermCode_valid _⟩ : ValidCode) = c := by
  apply Subtype.ext
  obtain ⟨t, ht⟩ := (validCode_iff c.val).1 c.property
  change encodeTerm ((decodeTerm c.val).getD (.var 0)) = c.val
  rw [ht, decodeTerm_encodeTerm]
  rfl

def executableTermEquivValid : Term ≃ ValidCode where
  toFun t := ⟨encodeTerm t, executableTermCode_valid t⟩
  invFun c := (decodeTerm c.val).getD (.var 0)
  left_inv := executableTermDecode_left
  right_inv := executableTermDecode_right

@[instance_reducible]
def executableTermPrimcodable : Primcodable Term :=
  Primcodable.ofEquiv ValidCode executableTermEquivValid

theorem executableTermEquivValid_eq : executableTermEquivValid = termEquivValid := by
  apply Equiv.ext
  intro t
  rfl

theorem executableTermPrimcodable_eq :
    executableTermPrimcodable = (inferInstance : Primcodable Term) := by
  exact congrArg (Primcodable.ofEquiv ValidCode) executableTermEquivValid_eq

def executableTermEncode (t : Term) : Nat :=
  @Encodable.encode Term executableTermPrimcodable.toEncodable t

def executableTermDecode (n : Nat) : Option Term :=
  @Encodable.decode Term executableTermPrimcodable.toEncodable n

theorem executableTermDecode_encode (t : Term) :
    executableTermDecode (executableTermEncode t) = some t := by
  exact @Encodable.encodek Term executableTermPrimcodable.toEncodable t

theorem executableTermEncode_eq (t : Term) : executableTermEncode t = Encodable.encode t := by
  unfold executableTermEncode
  rw [executableTermPrimcodable_eq]

theorem executableTermDecode_eq (n : Nat) : executableTermDecode n = Encodable.decode n := by
  unfold executableTermDecode
  rw [executableTermPrimcodable_eq]

#eval executableTermEncode (.app (.abs (.var 0)) (.var 2))
#eval executableTermDecode (executableTermEncode (.app (.abs (.var 0)) (.var 2)))
#print axioms executableTermEquivValid
#print axioms executableTermPrimcodable
#print axioms executableTermEncode
#print axioms executableTermDecode
#print axioms executableTermDecode_encode
#print axioms executableTermPrimcodable_eq
end LambdaTuring
