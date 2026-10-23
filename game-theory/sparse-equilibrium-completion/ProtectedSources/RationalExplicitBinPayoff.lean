/- AI-assisted formalization under the repository Apache-2.0 license.
Source explicit bin payoffs; this module does not yet prove global responses. -/
module
public import ProtectedSources.RationalCentralPayoff
public import ProtectedSources.BinnedWitness
@[expose] public section
namespace SparseCompletion

def rationalBinDecode {h : ℕ} (L : Fin h → ℕ) (j : Fin (∑ b,L b)) :
    (b : Fin h) × Fin (L b) := finSigmaFinEquiv.symm j

def rationalBinRepresentative {h : ℕ} (L : Fin h → ℕ) (j : Fin (∑ b,L b)) : Bool :=
  decide ((rationalBinDecode L j).2.val=(L (rationalBinDecode L j).1-1)/2 ∨
    (rationalBinDecode L j).2.val=L (rationalBinDecode L j).1/2)

def rationalOmittedCoefficient {m : ℕ} (j : Fin m) : ℚ :=
  -((m : ℚ)-((2 : ℕ) : ℚ)*(j.val : ℚ)-1)/(m : ℚ)

def rationalSupportedBinPayoff {h : ℕ} (L : Fin h → ℕ) (i j : Fin (∑ b,L b)) : ℚ :=
  if (rationalBinDecode L i).1.val < (rationalBinDecode L j).1.val then -1
  else if (rationalBinDecode L j).1.val < (rationalBinDecode L i).1.val then 1
  else if i.val < j.val then -(((2 : ℕ) : ℚ)/(L (rationalBinDecode L i).1 : ℚ))
  else if j.val < i.val then ((2 : ℕ) : ℚ)/(L (rationalBinDecode L i).1 : ℚ) else 0

def rationalExplicitBinPayoff {h : ℕ} (L : Fin h → ℕ) (i j : Fin (∑ b,L b)) : ℚ :=
  if rationalBinRepresentative L i then
    if rationalBinRepresentative L j then rationalSupportedBinPayoff L i j
    else -rationalOmittedCoefficient j
  else if rationalBinRepresentative L j then rationalOmittedCoefficient i else 0

theorem rational_supported_bin_payoff_skew {h : ℕ} (L : Fin h → ℕ)
    (i j : Fin (∑ b,L b)) : rationalSupportedBinPayoff L i j= -rationalSupportedBinPayoff L j i := by
  by_cases hij : (rationalBinDecode L i).1.val < (rationalBinDecode L j).1.val
  · have hji : ¬(rationalBinDecode L j).1.val < (rationalBinDecode L i).1.val := by omega
    simp only [rationalSupportedBinPayoff,hij,hji,ite_true,ite_false]
  · by_cases hji : (rationalBinDecode L j).1.val < (rationalBinDecode L i).1.val
    · simp only [rationalSupportedBinPayoff,hij,hji,ite_true,ite_false,neg_neg]
    · have he : (rationalBinDecode L i).1=(rationalBinDecode L j).1 :=
        Fin.ext (by omega)
      by_cases hi : i.val < j.val
      · have hj : ¬j.val < i.val := by omega
        simp only [rationalSupportedBinPayoff,he,lt_self_iff_false,hi,hj,ite_false,ite_true]
      · by_cases hj : j.val < i.val
        · simp only [rationalSupportedBinPayoff,he,lt_self_iff_false,hi,hj,ite_false,ite_true,neg_neg]
        · simp only [rationalSupportedBinPayoff,hij,hji,hi,hj,ite_false,neg_zero]

theorem rational_explicit_bin_payoff_skew {h : ℕ} (L : Fin h → ℕ)
    (i j : Fin (∑ b,L b)) : rationalExplicitBinPayoff L i j= -rationalExplicitBinPayoff L j i := by
  cases hi : rationalBinRepresentative L i <;> cases hj : rationalBinRepresentative L j <;>
    simp only [rationalExplicitBinPayoff,hi,hj,Bool.false_eq_true,ite_false,ite_true,neg_zero,neg_neg]
  exact rational_supported_bin_payoff_skew L i j

theorem rational_explicit_bin_payoff_diagonal {h : ℕ} (L : Fin h → ℕ)
    (i : Fin (∑ b,L b)) : rationalExplicitBinPayoff L i i=0 := by
  have h := rational_explicit_bin_payoff_skew L i i
  linarith

theorem rational_omitted_coefficient_bounds {m : ℕ} (j : Fin m) :
    -1 ≤ rationalOmittedCoefficient j ∧ rationalOmittedCoefficient j ≤ 1 := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hmQ : (0 : ℚ)<(m : ℚ) := by exact_mod_cast hm
  have hi : (j.val : ℚ)+1 ≤ (m : ℚ) := by exact_mod_cast j.isLt
  have hj : (0 : ℚ) ≤ (j.val : ℚ) := Nat.cast_nonneg _
  unfold rationalOmittedCoefficient
  norm_num only [Nat.cast_ofNat]
  constructor
  · apply (le_div_iff₀ hmQ).mpr
    linarith
  · apply (div_le_iff₀ hmQ).mpr
    linarith

theorem rational_bin_decode_val {h : ℕ} (L : Fin h → ℕ) (j : Fin (∑ b,L b)) :
    j.val=binStart L (rationalBinDecode L j).1+(rationalBinDecode L j).2.val := by
  have hh := binIndex_val L (rationalBinDecode L j).1 (rationalBinDecode L j).2
  have he : binIndex L (rationalBinDecode L j).1 (rationalBinDecode L j).2=j :=
    finSigmaFinEquiv.apply_symm_apply j
  rw [he] at hh
  exact hh

theorem rational_same_bin_length_two {h : ℕ} (L : Fin h → ℕ)
    (i j : Fin (∑ b,L b))
    (hb : (rationalBinDecode L i).1=(rationalBinDecode L j).1) (hij : i.val ≠ j.val) :
    (2 : ℕ) ≤ L (rationalBinDecode L i).1 := by
  have hi := (rationalBinDecode L i).2.isLt
  have hj := (rationalBinDecode L j).2.isLt
  have hvi := rational_bin_decode_val L i
  have hvj := rational_bin_decode_val L j
  have hlen : L (rationalBinDecode L j).1=L (rationalBinDecode L i).1 := congrArg L hb.symm
  have hj' : (rationalBinDecode L j).2.val < L (rationalBinDecode L i).1 :=
    lt_of_lt_of_eq hj hlen
  have hstart : binStart L (rationalBinDecode L j).1=binStart L (rationalBinDecode L i).1 :=
    congrArg (binStart L) hb.symm
  have hvj' : j.val=binStart L (rationalBinDecode L i).1+(rationalBinDecode L j).2.val :=
    hvj.trans (congrArg (fun n => n+(rationalBinDecode L j).2.val) hstart)
  omega

theorem rational_supported_bin_payoff_bounds {h : ℕ} (L : Fin h → ℕ)
    (i j : Fin (∑ b,L b)) :
    -1 ≤ rationalSupportedBinPayoff L i j ∧ rationalSupportedBinPayoff L i j ≤ 1 := by
  by_cases hij : (rationalBinDecode L i).1.val < (rationalBinDecode L j).1.val
  · simp only [rationalSupportedBinPayoff,hij,ite_true]
    norm_num
  · by_cases hji : (rationalBinDecode L j).1.val < (rationalBinDecode L i).1.val
    · simp only [rationalSupportedBinPayoff,hij,hji,ite_false,ite_true]
      norm_num
    · have hb : (rationalBinDecode L i).1=(rationalBinDecode L j).1 := Fin.ext (by omega)
      by_cases hi : i.val=j.val
      · have hi' : i=j := Fin.ext hi
        subst j
        simp only [rationalSupportedBinPayoff,lt_self_iff_false,ite_false]
        norm_num
      · have hL := rational_same_bin_length_two L i j hb hi
        have hLQ : ((2 : ℕ) : ℚ) ≤ (L (rationalBinDecode L i).1 : ℚ) := by exact_mod_cast hL
        have hpos : (0 : ℚ)<(L (rationalBinDecode L i).1 : ℚ) := by
          exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ)<2) hL)
        have hq : (0 : ℚ) ≤ ((2 : ℕ) : ℚ)/(L (rationalBinDecode L i).1 : ℚ) ∧
            ((2 : ℕ) : ℚ)/(L (rationalBinDecode L i).1 : ℚ) ≤ 1 :=
          ⟨div_nonneg (by norm_num) hpos.le,(div_le_one hpos).mpr hLQ⟩
        simp only [rationalSupportedBinPayoff,hij,hji,ite_false]
        split_ifs <;> constructor <;> linarith

theorem rational_explicit_bin_payoff_bounds {h : ℕ} (L : Fin h → ℕ)
    (i j : Fin (∑ b,L b)) :
    -1 ≤ rationalExplicitBinPayoff L i j ∧ rationalExplicitBinPayoff L i j ≤ 1 := by
  have hi := rational_omitted_coefficient_bounds i
  have hj := rational_omitted_coefficient_bounds j
  have hs := rational_supported_bin_payoff_bounds L i j
  unfold rationalExplicitBinPayoff
  split_ifs <;> constructor <;> linarith

end SparseCompletion
