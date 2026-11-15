module

public import ErdosOverlap.Native6Kernel
public import ErdosOverlap.Numerics.CachedTrig

/-! Fixed-point enclosures of the actual sinc-square Fourier return. -/

namespace ErdosOverlap.Numerics

open LeanCert.Core

@[expose] public section

def sincBox (q : ℚ) : FixedBox :=
  if q = 0 then FixedBox.ofRat 1
  else (FixedBox.ofRat q).sin32.mul (FixedBox.ofRat (1/q))

theorem sinc_mem_box (q : ℚ) : Real.sinc (q : ℝ) ∈ sincBox q := by
  unfold sincBox
  split_ifs with hq
  · subst q
    simpa using FixedBox.mem_ofRat (1 : ℚ)
  · have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    rw [Real.sinc_of_ne_zero hqr]
    convert! FixedBox.mem_mul (FixedBox.mem_sin32 (FixedBox.mem_ofRat q))
      (FixedBox.mem_ofRat (1/q)) using 1 <;> push_cast <;> ring

def sincTermBox (a : CosineTerm) : FixedBox :=
  let I := sincBox a.frequency
  (FixedBox.ofRat a.weight).mul (I.mul I)

theorem sincTerm_mem_box (a : CosineTerm) :
    (a.weight : ℝ)*Real.sinc (a.frequency : ℝ)^2 ∈ sincTermBox a := by
  simpa only [sincTermBox, pow_two] using
    FixedBox.mem_mul (FixedBox.mem_ofRat a.weight)
      (FixedBox.mem_mul (sinc_mem_box a.frequency) (sinc_mem_box a.frequency))

def sincSumBox : List CosineTerm → FixedBox
  | [] => FixedBox.ofRat 0
  | a :: rest => (sincTermBox a).add (sincSumBox rest)

theorem sincSum_mem_box (terms : List CosineTerm) :
    Native6.cosineLower terms ∈ sincSumBox terms := by
  induction terms with
  | nil => simpa only [Native6.cosineLower, sincSumBox, Rat.cast_zero] using FixedBox.mem_ofRat 0
  | cons a rest ih => exact FixedBox.mem_add (sincTerm_mem_box a) ih

theorem cosineLower_append (xs ys : List CosineTerm) :
    Native6.cosineLower (xs ++ ys) = Native6.cosineLower xs + Native6.cosineLower ys := by
  induction xs with
  | nil => simp [Native6.cosineLower]
  | cons x xs ih => simp only [List.cons_append, Native6.cosineLower, ih]; ring

theorem sincSum_lower_of_check (terms : List CosineTerm) (q : ℚ)
    (h : (sincSumBox terms).lowerBoundedBy q = true) :
    (q : ℝ) ≤ Native6.cosineLower terms :=
  FixedBox.lowerBoundedBy_sound (sincSum_mem_box terms) h

end
end ErdosOverlap.Numerics
