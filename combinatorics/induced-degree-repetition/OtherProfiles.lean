module

public import RegisteredProfiles
public import LabelSamples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Edit

open Finset Restriction
open scoped Classical
variable {X V : Type*}

@[expose] def GoodRows {ℓ : ℕ} (S : Finset X) (d : X → V → ℕ) (L : ℕ)
    (θ w cut : ℝ) (tests : List (Option ℕ)) (ys : Fin ℓ → V) : Prop :=
  ∀ (s : Fin ℓ → ℤ) j, let Q := otherFiber S (rowValues d ys) s j
    cut ≤ Q.card → ∀ t ∈ tests, Witnesses Q (fun x => d x (ys j)) L θ w t

set_option maxHeartbeats 600000 in
/-- Count failures before choosing any current profile. The other-row family can
depend on all tester labels except the label whose witnesses are being checked. -/
theorem other_profile_bound (S : Finset X) (Y : Finset V) (d : X → V → ℕ) (L ℓ : ℕ)
    (θ w cut δ : ℝ) (tests : List (Option ℕ)) (hp : 0 < cut) (hd : 0 ≤ δ)
    (bound : ∀ x ∈ S, ∀ y, d x y ≤ L)
    (estimate : ∀ Q ⊆ S, cut ≤ Q.card → ∃ E ⊆ Y, (E.card:ℝ) ≤ δ*Y.card ∧
      ∀ y ∈ Y, y ∉ E → ∀ t ∈ tests, Witnesses Q (fun x => d x y) L θ w t) :
    (((Fintype.piFinset fun _ : Fin ℓ => Y).filter (fun ys => ¬GoodRows S d L θ w cut tests ys)).card:ℝ) ≤
      ℓ*((L:ℝ)+1)^ℓ*δ*(Fintype.piFinset fun _ : Fin ℓ => Y).card := by
  classical
  let Pos (j : Fin ℓ) := {k : Fin ℓ // k ≠ j}
  let Codes (j : Fin ℓ) := Pos j → Fin (L+1)
  let family (j : Fin ℓ) (rest : Pos j → Y) (z : Codes j) :=
    S.filter fun x => ∀ k, degreeCode L (d x (rest k)) = z k
  let bad (j : Fin ℓ) (rest : Pos j → Y) (z : Codes j) :=
    (univ : Finset Y).filter fun (y:Y) => cut ≤ (family j rest z).card ∧
      ∃ t ∈ tests, ¬Witnesses (family j rest z) (fun x => d x y) L θ w t
  have rare (j rest z) : ((bad j rest z).card:ℝ) ≤ δ*Fintype.card Y := by
    let Q := family j rest z
    by_cases small : cut ≤ Q.card
    · obtain ⟨E,ey,sz,out⟩ := estimate Q (filter_subset ..) small
      have sub : labels (bad j rest z) ⊆ E := by
        intro y hy
        obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
        obtain ⟨_,_,t,ht,no⟩ := mem_filter.mp hv
        by_contra h
        exact no (out v v.2 h t ht)
      have le := card_le_card sub
      rw [card_labels] at le
      exact (Nat.cast_le.mpr le).trans (by simpa using sz)
    · have eq : bad j rest z = ∅ := by ext y; simp [bad,Q,small]
      simpa [eq] using mul_nonneg hd (Nat.cast_nonneg (α:=ℝ) Y.card)
  have failure (ys : Fin ℓ → Y) (h : ¬GoodRows S d L θ w cut tests (forget ys)) :
      ∃ j z, ys j ∈ bad j (fun k => ys k) z := by
    simp only [GoodRows,not_forall] at h
    obtain ⟨s,j,hc,t,ht,no⟩ := h
    let Q := otherFiber S (rowValues d (forget ys)) s j
    have pos : 0 < Q.card := by exact_mod_cast hp.trans_le hc
    obtain ⟨x,hx⟩ := card_pos.mp pos
    have spec : x ∈ S ∧ ∀ k, k ≠ j → rowValues d (forget ys) x k = s k := by
      simpa only [Q,otherFiber,mem_filter] using hx
    let z : Codes j := fun k => degreeCode L (d x (ys k))
    have eq : family j (fun k => ys k) z = Q := by
      ext p
      simp only [family,Q,otherFiber,mem_filter,and_congr_right_iff]
      intro pm
      constructor
      · intro h k ne
        have h' := (code_eq (bound p pm _) (bound x spec.1 _)).mp (h ⟨k,ne⟩)
        exact (congrArg Int.ofNat h').trans (spec.2 k ne)
      · intro h k
        apply congrArg (degreeCode L)
        exact Int.ofNat_inj.mp ((h k k.2).trans (spec.2 k k.2).symm)
    exact ⟨j,z,mem_filter.mpr ⟨mem_univ _,by rw [eq]; exact ⟨hc,t,ht,no⟩⟩⟩
  let event := fun ys : Fin ℓ → Y => ∃ j z, ys j ∈ bad j (fun k => ys k) z
  have factor (j : Fin ℓ) : (Fintype.card (Codes j):ℝ) ≤ ((L:ℝ)+1)^ℓ := by
    simp only [Codes,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    apply pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) L])
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin ℓ)
  have sum := sum_le_sum (s:=(univ:Finset (Fin ℓ))) (fun j _ => factor j)
  have prob := exceptional_profile_lists (I:=Fin ℓ) (Y:=Y) Codes bad δ rare
  have direct := count_label_event (I:=Fin ℓ) Y (fun ys => ¬GoodRows S d L θ w cut tests ys)
  convert le_trans (le_of_eq direct) ?_ using 1
  · apply congrArg Nat.cast
    apply congrArg Finset.card
    ext v
    simp [Fintype.mem_piFinset]
  · trans (∑ ys : Fin ℓ → Y, if ¬GoodRows S d L θ w cut tests (forget ys) then (1:ℝ) else 0)
    · apply le_of_eq
      apply sum_congr (Finset.ext fun _ => by simp)
      intro ys _
      by_cases h : GoodRows S d L θ w cut tests (forget ys) <;> simp [h]
    apply le_trans (sum_le_sum (s:=univ) (g:=fun ys => if event ys then (1:ℝ) else 0) ?_)
    · rw [sum_boole]
      convert prob.trans ?_ using 1
      · apply congrArg Nat.cast
        apply congrArg Finset.card
        ext v
        simp [event]
        constructor <;> rintro ⟨j,z,hz⟩ <;> exact ⟨j,z,hz⟩
      · simpa [Fintype.card_piFinset] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right sum hd)
          (Nat.cast_nonneg (Fintype.card (Fin ℓ → Y)))
    · intro ys _
      by_cases h : GoodRows S d L θ w cut tests (forget ys)
      · simp [h]; split <;> norm_num
      · simp [h,show event ys from failure ys h]

end InducedDegreeRepetition.Edit
