/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Hyperspace
public import Scalar

@[expose] public section

open Set Topology TopologicalSpace

namespace OrderArcs

/-- A maximal chain in a compact partial order with strict interpolation has a
full interval as the image of any continuous strictly increasing real scalar. -/
theorem exists_compact_chain_image {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [PartialOrder Y] (hclosed : IsClosed {p : Y × Y | p.1 ≤ p.2})
    (f : Y → ℝ) (hfc : Continuous f) (hfs : StrictMono f)
    (hbetween : ∀ x y : Y, x < y → ∃ z : Y, x < z ∧ z < y)
    (a b : Y) (hab : a < b) (ha : ∀ x : Y, a ≤ x) (hb : ∀ x : Y, x ≤ b) :
    ∃ M : Set Y, IsCompact M ∧ IsChain (· ≤ ·) M ∧ a ∈ M ∧ b ∈ M ∧
      Set.InjOn f M ∧ f '' M = Icc (f a) (f b) := by
  classical
  obtain ⟨M, hM, hpair⟩ := (IsChain.pair hab.le).exists_maxChain
  have hMa : a ∈ M := hpair (by simp)
  have hMb : b ∈ M := hpair (by simp)
  have hEq : M = closure M := hM.2 (isChain_closure hclosed hM.1) subset_closure
  have hMc : IsCompact M := (hEq ▸ isClosed_closure).isCompact
  have hreflect : ∀ {x y : Y}, x ∈ M → y ∈ M → f x ≤ f y → x ≤ y := by
    intro x y hx hy hxy
    rcases hM.1.total hx hy with h | h
    · exact h
    · rcases eq_or_lt_of_le h with heq | hlt
      · simp [heq]
      · exact False.elim ((not_lt_of_ge hxy) (hfs hlt))
  have hinj : Set.InjOn f M := by
    intro x hx y hy hxy
    exact le_antisymm (hreflect hx hy hxy.le) (hreflect hy hx hxy.ge)
  let S : Set ℝ := f '' M
  have hSc : IsCompact S := hMc.image hfc
  have hfa : f a ∈ S := ⟨a, hMa, rfl⟩
  have hfb : f b ∈ S := ⟨b, hMb, rfl⟩
  have hfull : S = Icc (f a) (f b) := by
    apply Subset.antisymm
    · rintro _ ⟨x, _, rfl⟩
      exact ⟨hfs.monotone (ha x), hfs.monotone (hb x)⟩
    · intro t ht
      by_contra htS
      obtain ⟨l, hl⟩ := (hSc.inter_right isClosed_Iic).exists_isGreatest
        (show (S ∩ Iic t).Nonempty from ⟨f a, hfa, ht.1⟩)
      obtain ⟨r, hr⟩ := (hSc.inter_right isClosed_Ici).exists_isLeast
        (show (S ∩ Ici t).Nonempty from ⟨f b, hfb, ht.2⟩)
      have hlt : l < t := lt_of_le_of_ne hl.1.2 (fun h => htS (h ▸ hl.1.1))
      have htr : t < r := lt_of_le_of_ne hr.1.2 (fun h => htS (h.symm ▸ hr.1.1))
      obtain ⟨K, hK, hfK⟩ := hl.1.1
      obtain ⟨L, hL, hfL⟩ := hr.1.1
      have hKL : K < L := by
        refine lt_of_le_of_ne (hreflect hK hL (by rw [hfK, hfL]; exact (hlt.trans htr).le)) ?_
        intro h
        have : l = r := hfK.symm.trans ((congrArg f h).trans hfL)
        exact (ne_of_lt (hlt.trans htr)) this
      obtain ⟨D, hKD, hDL⟩ := hbetween K L hKL
      have hcomparable : ∀ P ∈ M, D ≤ P ∨ P ≤ D := by
        intro P hP
        rcases le_total (f P) t with hPt | htP
        · have hPK : P ≤ K := hreflect hP hK (by
            rw [hfK]
            exact hl.2 ⟨⟨P, hP, rfl⟩, hPt⟩)
          exact Or.inr (hPK.trans hKD.le)
        · have hLP : L ≤ P := hreflect hL hP (by
            rw [hfL]
            exact hr.2 ⟨⟨P, hP, rfl⟩, htP⟩)
          exact Or.inl (hDL.le.trans hLP)
      have hinsert : IsChain (· ≤ ·) (insert D M) :=
        hM.1.insert fun P hP _ => hcomparable P hP
      have hMax : M = insert D M := hM.2 hinsert (subset_insert D M)
      have hDM : D ∈ M := by
        rw [hMax]
        exact mem_insert D M
      rcases le_total (f D) t with hDt | htD
      · have hle : f D ≤ l := hl.2 ⟨⟨D, hDM, rfl⟩, hDt⟩
        have hstrict := hfs hKD
        rw [hfK] at hstrict
        exact (not_lt_of_ge hle) hstrict
      · have hle : r ≤ f D := hr.2 ⟨⟨D, hDM, rfl⟩, htD⟩
        have hstrict := hfs hDL
        rw [hfL] at hstrict
        exact (not_lt_of_ge hle) hstrict
  exact ⟨M, hMc, hM.1, hMa, hMb, hinj, hfull⟩

end OrderArcs

#print axioms OrderArcs.exists_compact_chain_image
