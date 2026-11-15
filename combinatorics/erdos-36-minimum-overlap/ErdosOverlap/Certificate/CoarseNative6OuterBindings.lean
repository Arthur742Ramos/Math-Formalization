/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.OuterPositiveBins
public import ErdosOverlap.Certificate.CoarseNative6OuterReduction

/-! # Exact source-bin bindings for the sixty needed outer mean rows

The lists and six rational field equalities are checked in the Lean kernel.
The final adapter accepts the actual positive-bin cap theorem; it does not
assume a row inequality for an unrelated or rounded mean interval.
-/

@[expose] public section

namespace ErdosOverlap.Certificate.CoarseNative6

open Set OuterNumerics

set_option maxHeartbeats 1000000

def neededOuterBindings : List (Row × OuterBinData) := [
  (outer114, Outer180.bin114),
  (outer115, Outer180.bin115),
  (outer116, Outer180.bin116),
  (outer117, Outer180.bin117),
  (outer118, Outer180.bin118),
  (outer119, Outer180.bin119),
  (outer120, Outer180.bin120),
  (outer121, Outer180.bin121),
  (outer122, Outer180.bin122),
  (outer123, Outer180.bin123),
  (outer124, Outer180.bin124),
  (outer125, Outer180.bin125),
  (outer126, Outer180.bin126),
  (outer127, Outer180.bin127),
  (outer128, Outer180.bin128),
  (outer129, Outer180.bin129),
  (outer130, Outer180.bin130),
  (outer131, Outer180.bin131),
  (outer132, Outer180.bin132),
  (outer133, Outer180.bin133),
  (outer134, Outer180.bin134),
  (outer135, Outer180.bin135),
  (outer136, Outer180.bin136),
  (outer137, Outer180.bin137),
  (outer138, Outer180.bin138),
  (outer139, Outer180.bin139),
  (outer140, Outer180.bin140),
  (outer141, Outer180.bin141),
  (outer142, Outer180.bin142),
  (outer143, Outer180.bin143),
  (outer144, Outer180.bin144),
  (outer145, Outer180.bin145),
  (outer146, Outer180.bin146),
  (outer147, Outer180.bin147),
  (outer148, Outer180.bin148),
  (outer149, Outer180.bin149),
  (outer150, Outer180.bin150),
  (outer151, Outer180.bin151),
  (outer152, Outer180.bin152),
  (outer153, Outer180.bin153),
  (outer154, Outer180.bin154),
  (outer155, Outer180.bin155),
  (outer156, Outer180.bin156),
  (outer157, Outer180.bin157),
  (outer158, Outer180.bin158),
  (outer159, Outer180.bin159),
  (outer160, Outer180.bin160),
  (outer161, Outer180.bin161),
  (outer162, Outer180.bin162),
  (outer163, Outer180.bin163),
  (outer164, Outer180.bin164),
  (outer165, Outer180.bin165),
  (outer166, Outer180.bin166),
  (outer167, Outer180.bin167),
  (outer168, Outer180.bin168),
  (outer169, Outer180.bin169),
  (outer170, Outer180.bin170),
  (outer171, Outer180.bin171),
  (outer172, Outer180.bin172),
  (outer173, Outer180.bin173)]

theorem neededOuterBindings_rows :
    neededOuterBindings.map Prod.fst = outerRowsNeedingIntegrals := rfl

theorem neededOuterBindings_bins :
    neededOuterBindings.map Prod.snd = positiveBins := rfl

def outerRowBinCheck (p : Row × OuterBinData) : Bool :=
  decide (p.1.lo = p.2.lo ∧ p.1.hi = p.2.hi ∧ p.1.a = 1 ∧
    p.1.b = 0 ∧ p.1.c = 0 ∧ p.1.d = (262723/100000 : ℚ))

theorem neededOuterBindings_checked : neededOuterBindings.all outerRowBinCheck = true := by
  decide +kernel

theorem neededOuterBindings_spec {r : Row} (hr : r ∈ outerRowsNeedingIntegrals) :
    ∃ b ∈ positiveBins, r.lo = b.lo ∧ r.hi = b.hi ∧ r.a = 1 ∧
      r.b = 0 ∧ r.c = 0 ∧ r.d = (262723/100000 : ℚ) := by
  rw [← neededOuterBindings_rows] at hr
  obtain ⟨p,hp,hpr⟩ := List.mem_map.mp hr
  have hs := of_decide_eq_true ((List.all_eq_true.mp neededOuterBindings_checked) p hp)
  have hb : p.2 ∈ positiveBins := by
    rw [← neededOuterBindings_bins]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  refine ⟨p.2,hb,?_⟩
  rw [← hpr]
  exact hs

/-- Insert the actual signed-kernel cap bound after its finite integral
receipts have been checked. All source and interval bindings are closed. -/
theorem outerRowsNeedingIntegrals_physical_of_positiveBin_cap_bound
    (hbound : ∀ {h : ℝ → ℝ} {M : ℝ}, Admissible h → OverlapCap h M →
      ∀ {b : OuterBinData}, b ∈ positiveBins →
      profileMean (overlapProfile h) ∈ Icc (b.lo : ℝ) (b.hi : ℝ) →
      1 ≤ M*(262723/100000 : ℝ)) :
    PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight := by
  intro r hr h hh hlo hhi hcap
  obtain ⟨b,hb,hloeq,hhieq,ha,hbzero,hczero,hd⟩ := neededOuterBindings_spec hr
  have hm : profileMean (overlapProfile h) ∈ Icc (b.lo : ℝ) (b.hi : ℝ) := by
    rw [← hloeq,← hhieq]
    exact ⟨hlo,hhi⟩
  have hhbound := hbound hh hcap hb hm
  simpa only [ha,hbzero,hczero,hd,Rat.cast_one,Rat.cast_zero,zero_mul,
    add_zero,Rat.cast_div,Rat.cast_ofNat] using hhbound

end ErdosOverlap.Certificate.CoarseNative6
