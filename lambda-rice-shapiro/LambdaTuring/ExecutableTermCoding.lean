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
def executableTermEquivValid : Term ≃ ValidCode where
  toFun t := ⟨encodeTerm t, (validCode_iff _).2 ⟨t, rfl⟩⟩
  invFun c := (decodeTerm c.val).getD (.var 0)
  left_inv t := by simp [decodeTerm_encodeTerm]
  right_inv c := by
    apply Subtype.ext
    obtain ⟨t, ht⟩ := (validCode_iff c.val).1 c.property
    simp [ht, decodeTerm_encodeTerm]

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
