/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.OuterPositiveBins
public import ErdosOverlap.Certificate.Outer90.Integral114
public import ErdosOverlap.Certificate.Outer90.Integral115
public import ErdosOverlap.Certificate.Outer90.Integral116
public import ErdosOverlap.Certificate.Outer90.Integral117
public import ErdosOverlap.Certificate.Outer90.Integral118
public import ErdosOverlap.Certificate.Outer90.Integral119
public import ErdosOverlap.Certificate.Outer90.Integral120
public import ErdosOverlap.Certificate.Outer90.Integral121
public import ErdosOverlap.Certificate.Outer90.Integral122
public import ErdosOverlap.Certificate.Outer90.Integral123
public import ErdosOverlap.Certificate.Outer90.Integral124
public import ErdosOverlap.Certificate.Outer90.Integral125
public import ErdosOverlap.Certificate.Outer90.Integral126
public import ErdosOverlap.Certificate.Outer90.Integral127
public import ErdosOverlap.Certificate.Outer90.Integral128
public import ErdosOverlap.Certificate.Outer90.Integral129
public import ErdosOverlap.Certificate.Outer90.Integral130
public import ErdosOverlap.Certificate.Outer90.Integral131
public import ErdosOverlap.Certificate.Outer90.Integral132
public import ErdosOverlap.Certificate.Outer90.Integral133
public import ErdosOverlap.Certificate.Outer90.Integral134
public import ErdosOverlap.Certificate.Outer90.Integral135
public import ErdosOverlap.Certificate.Outer90.Integral136
public import ErdosOverlap.Certificate.Outer90.Integral137
public import ErdosOverlap.Certificate.Outer90.Integral138
public import ErdosOverlap.Certificate.Outer90.Integral139
public import ErdosOverlap.Certificate.Outer90.Integral140
public import ErdosOverlap.Certificate.Outer90.Integral141
public import ErdosOverlap.Certificate.Outer90.Integral142
public import ErdosOverlap.Certificate.Outer90.Integral143
public import ErdosOverlap.Certificate.Outer90.Integral144
public import ErdosOverlap.Certificate.Outer90.Integral145
public import ErdosOverlap.Certificate.Outer90.Integral146
public import ErdosOverlap.Certificate.Outer90.Integral147
public import ErdosOverlap.Certificate.Outer90.Integral148
public import ErdosOverlap.Certificate.Outer90.Integral149
public import ErdosOverlap.Certificate.Outer90.Integral150
public import ErdosOverlap.Certificate.Outer90.Integral151
public import ErdosOverlap.Certificate.Outer90.Integral152
public import ErdosOverlap.Certificate.Outer90.Integral153
public import ErdosOverlap.Certificate.Outer90.Integral154
public import ErdosOverlap.Certificate.Outer90.Integral155
public import ErdosOverlap.Certificate.Outer90.Integral156
public import ErdosOverlap.Certificate.Outer90.Integral157
public import ErdosOverlap.Certificate.Outer90.Integral158
public import ErdosOverlap.Certificate.Outer90.Integral159
public import ErdosOverlap.Certificate.Outer90.Integral160
public import ErdosOverlap.Certificate.Outer90.Integral161
public import ErdosOverlap.Certificate.Outer90.Integral162
public import ErdosOverlap.Certificate.Outer90.Integral163
public import ErdosOverlap.Certificate.Outer90.Integral164
public import ErdosOverlap.Certificate.Outer90.Integral165
public import ErdosOverlap.Certificate.Outer90.Integral166
public import ErdosOverlap.Certificate.Outer90.Integral167
public import ErdosOverlap.Certificate.Outer90.Integral168
public import ErdosOverlap.Certificate.Outer90.Integral169
public import ErdosOverlap.Certificate.Outer90.Integral170
public import ErdosOverlap.Certificate.Outer90.Integral171
public import ErdosOverlap.Certificate.Outer90.Integral172
public import ErdosOverlap.Certificate.Outer90.Integral173

/-! # Actual checked denominator bounds for the sixty needed positive outer bins

Every numerical premise is supplied by the imported finite certificate.
Far mean bins are discharged by the separate cap-to-mean theorem.
Negative mean intervals follow by colour-complement reflection.
-/

namespace ErdosOverlap.OuterNumerics
open MeasureTheory Set
@[expose] public section

theorem positiveBins_denominator_upper {b : OuterBinData} (hb : b ∈ positiveBins) :
    signedKernelDenominator b.kernel ≤ (262723/100000 : ℝ) := by
  simp only [positiveBins, Outer180.bins09, Outer180.bins10, Outer180.bins11, Outer180.bins12, Outer180.bins13, Outer180.bins14, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bin114.denominator_upper
  · exact Bin115.denominator_upper
  · exact Bin116.denominator_upper
  · exact Bin117.denominator_upper
  · exact Bin118.denominator_upper
  · exact Bin119.denominator_upper
  · exact Bin120.denominator_upper
  · exact Bin121.denominator_upper
  · exact Bin122.denominator_upper
  · exact Bin123.denominator_upper
  · exact Bin124.denominator_upper
  · exact Bin125.denominator_upper
  · exact Bin126.denominator_upper
  · exact Bin127.denominator_upper
  · exact Bin128.denominator_upper
  · exact Bin129.denominator_upper
  · exact Bin130.denominator_upper
  · exact Bin131.denominator_upper
  · exact Bin132.denominator_upper
  · exact Bin133.denominator_upper
  · exact Bin134.denominator_upper
  · exact Bin135.denominator_upper
  · exact Bin136.denominator_upper
  · exact Bin137.denominator_upper
  · exact Bin138.denominator_upper
  · exact Bin139.denominator_upper
  · exact Bin140.denominator_upper
  · exact Bin141.denominator_upper
  · exact Bin142.denominator_upper
  · exact Bin143.denominator_upper
  · exact Bin144.denominator_upper
  · exact Bin145.denominator_upper
  · exact Bin146.denominator_upper
  · exact Bin147.denominator_upper
  · exact Bin148.denominator_upper
  · exact Bin149.denominator_upper
  · exact Bin150.denominator_upper
  · exact Bin151.denominator_upper
  · exact Bin152.denominator_upper
  · exact Bin153.denominator_upper
  · exact Bin154.denominator_upper
  · exact Bin155.denominator_upper
  · exact Bin156.denominator_upper
  · exact Bin157.denominator_upper
  · exact Bin158.denominator_upper
  · exact Bin159.denominator_upper
  · exact Bin160.denominator_upper
  · exact Bin161.denominator_upper
  · exact Bin162.denominator_upper
  · exact Bin163.denominator_upper
  · exact Bin164.denominator_upper
  · exact Bin165.denominator_upper
  · exact Bin166.denominator_upper
  · exact Bin167.denominator_upper
  · exact Bin168.denominator_upper
  · exact Bin169.denominator_upper
  · exact Bin170.denominator_upper
  · exact Bin171.denominator_upper
  · exact Bin172.denominator_upper
  · exact Bin173.denominator_upper

theorem positiveBin_cap_bound {h : ℝ → ℝ} {M : ℝ} (hh : Admissible h)
    (hcap : OverlapCap h M) {b : OuterBinData} (hb : b ∈ positiveBins)
    (hm : profileMean (overlapProfile h) ∈ Icc (b.lo : ℝ) (b.hi : ℝ)) :
    1 ≤ M * (262723/100000 : ℝ) := by
  have hp := Outer180.bin_cap_bound hh hcap b (positiveBins_mem hb) hm
  exact hp.trans (mul_le_mul_of_nonneg_left (positiveBins_denominator_upper hb)
    (hcap.nonneg hh))

end
end ErdosOverlap.OuterNumerics
