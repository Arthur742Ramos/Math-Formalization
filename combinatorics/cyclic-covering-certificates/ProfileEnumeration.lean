module
/- Completeness of a quota-based enumeration of ternary words.
   This is generic in the word length and all three multiplicities. -/
public import Std
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CoveringProfiles
abbrev Trit := Fin 3

@[expose] def count (d : Trit) : List Trit → Nat
  | [] => 0
  | a :: xs => (if a = d then 1 else 0) + count d xs

@[expose] def quotaWords : Nat → Nat → Nat → Nat → List (List Trit)
  | 0, z, o, t => if z = 0 ∧ o = 0 ∧ t = 0 then [[]] else []
  | n+1, z, o, t =>
    (if z > 0 then (quotaWords n (z-1) o t).map (0 :: ·) else []) ++
    (if o > 0 then (quotaWords n z (o-1) t).map (1 :: ·) else []) ++
    (if t > 0 then (quotaWords n z o (t-1)).map (2 :: ·) else [])

theorem trit_cases : ∀ a : Trit, a = 0 ∨ a = 1 ∨ a = 2 := by decide

theorem quota_complete (xs : List Trit) :
    xs ∈ quotaWords xs.length (count 0 xs) (count 1 xs) (count 2 xs) := by
  induction xs with
  | nil => decide
  | cons a xs ih =>
    rcases trit_cases a with rfl | rfl | rfl
    all_goals simp [quotaWords, count, Nat.add_sub_cancel_left, ih, List.mem_map]
    all_goals omega

@[expose] def balancedWords : List (List Trit) := quotaWords 10 4 3 3

theorem balanced_complete (xs : List Trit)
    (hlen : xs.length = 10) (hz : count 0 xs = 4)
    (ho : count 1 xs = 3) (ht : count 2 xs = 3) : xs ∈ balancedWords := by
  simpa [balancedWords, hlen, hz, ho, ht] using quota_complete xs

theorem balanced_words_count : balancedWords.length = 4200 := by decide

#print axioms quota_complete
#print axioms balanced_complete
#print axioms balanced_words_count
end CoveringProfiles
