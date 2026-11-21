module

public import DensityBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

public section
namespace InducedDegreeRepetition

open Finset Real OpenProblems
open scoped Classical

/-- The first, iterative half of Lemma 3. Each failed cut test supplies a saved block.
After four times J successful extractions the pigeonhole argument supplies a regular
union of J equal-sized blocks. -/
theorem regular_or_two_sided (c : ℝ) (hc : 0 < c) :
    ∃ (u τ : ℝ) (r₀ : ℕ), 0 < u ∧ 0 < τ ∧ ∀ r ≥ r₀,
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)), exp (c*r) ≤ N → (N:ℝ) ≤ exp (2*c*r) →
    (∃ (S : Finset (Fin N)) (d : ℕ), r ≤ S.card ∧ S.card < 2*r ∧ degreeClass G S d = S) ∨
    ∃ W : Finset (Fin N), exp (3*c*r/4) ≤ W.card ∧ CutBounds G W (W.card*exp (-u*r)) τ := by
  classical
  let J := ⌈8*log 4 / c⌉₊+1
  have jp : 0 < J := Nat.succ_pos _
  have jPos : (0:ℝ) < J := Nat.cast_pos.mpr jp
  have sc : 8*log 4 ≤ c*J := by
    rw [mul_comm c]
    apply (div_le_iff₀ hc).mp
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show ⌈8*log 4/c⌉₊ ≤ J by omega)
  let u := c/(64*(J:ℝ))
  let τ := (1-exp (-c/16384))/2
  have up : 0 < u := div_pos hc (by positivity)
  have uJ : u*(64*J) = c := div_mul_cancel₀ _ (by positivity)
  have taupos : 0 < τ := by
    have h := exp_lt_one_iff.mpr (show -c/16384 < 0 by linarith)
    dsimp [τ]; linarith
  have tau2 : 2*τ ≤ 1 := by dsimp [τ]; linarith [exp_pos (-c/16384)]
  let r₀ := max (J+1) ⌈8*log 8 / c⌉₊
  refine ⟨u,τ,r₀,up,taupos,?_⟩
  intro r hr N G en ne
  have jr : J < r := by have := (le_max_left ..).trans hr; omega
  have rp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have gr : log 8 ≤ c*r/8 := by
    have lb : 8*log 8/c ≤ (r:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right ..).trans hr))
    linarith [(div_le_iff₀ hc).mp lb]
  let s := r/J+1
  have sPos : 0 < s := Nat.succ_pos _
  by_cases success : ∃ W : Finset (Fin N), exp (3*c*r/4) ≤ W.card ∧ CutBounds G W (W.card*exp (-u*r)) τ
  · exact Or.inr success
  left
  let level := fun j : ℕ => exp (3*c*r/4 + j*(2*u*r))
  have grow (j : ℕ) : ∀ W : Finset (Fin N), level j ≤ W.card →
      ∃ L : List (SavedBlock (Fin N)), L.length = j ∧
        (∀ A ∈ L, A.vertices ⊆ W ∧ A.vertices.card = s ∧ Homogeneous G (A.inner = true) A.vertices) ∧
        L.Pairwise (Follows G) := by
    induction j with
    | zero => intro W _; exact ⟨[],rfl,by simp,by simp⟩
    | succ j ih =>
      intro W hW
      have base : exp (3*c*r/4) ≤ W.card := (exp_le_exp.mpr
        (le_add_of_nonneg_right (by positivity : 0 ≤ ((j+1:ℕ):ℝ)*(2*u*r)))).trans hW
      have fail : ¬CutBounds G W (W.card*exp (-u*r)) τ := fun hh => success ⟨W,base,hh⟩
      unfold CutBounds at fail
      push Not at fail
      obtain ⟨X,hX,Y,hY,dis,hx,hy,b,few⟩ := fail
      have xlow : exp (c*r/2) ≤ X.card := by
        apply le_trans _ ((mul_le_mul_of_nonneg_right base (exp_pos _).le).trans hx)
        rw [← exp_add,exp_le_exp]
        have ju : u ≤ c/64 := by
          have jle : (1:ℝ) ≤ J := by exact_mod_cast jp
          nlinarith [mul_le_mul_of_nonneg_left jle up.le]
        nlinarith [mul_le_mul_of_nonneg_right ju rp.le]
      have xhigh : (X.card : ℝ) ≤ exp (2*c*r) := (Nat.cast_le.mpr (by simpa using card_le_univ X)).trans ne
      have yPos : Y.Nonempty := card_pos.mp (Nat.cast_pos.mp (show (0:ℝ) < Y.card from
        (mul_pos ((exp_pos _).trans_le base) (exp_pos _)).trans_le hy))
      have budget := density_budget c J r hc jp jr.le sc gr X.card xlow xhigh
      have et : 1-2*τ = exp (-c/16384) := by dsimp [τ]; ring
      obtain ⟨A,Z,hAX,sz,hom,hZY,hZ,cross⟩ := dense_cut_step G X Y s (1024*r) b τ (exp (-u*r))
        taupos tau2 (exp_pos _).le sPos yPos few (by rw [et]; exact budget)
      have hlevel : level j ≤ Z.card := by
        apply le_trans _ hZ
        apply le_trans _ (mul_le_mul_of_nonneg_left hy (exp_pos _).le)
        apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW (exp_pos _).le) (exp_pos _).le)
        dsimp [level]
        rw [← exp_add, ← exp_add]
        apply exp_le_exp.mpr
        push_cast; linarith
      obtain ⟨L,len,valid,pair⟩ := ih Z hlevel
      refine ⟨A::L,by simp [len],?_,List.pairwise_cons.mpr ⟨?_,pair⟩⟩
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hB
        · exact ⟨hAX.trans hX,sz,hom⟩
        · obtain ⟨hz,hh⟩ := valid B hB
          exact ⟨hz.trans (hZY.trans hY),hh⟩
      · intro B hB
        have bz := (valid B hB).1
        exact ⟨dis.mono hAX (bz.trans hZY),fun x hx y hy => cross x hx y (bz hy)⟩
  have start : level (4*J) ≤ (univ : Finset (Fin N)).card := by
    simp only [level,card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    apply le_trans _ en
    apply exp_le_exp.mpr
    have H := congrArg (fun z : ℝ => z*(r:ℝ)) uJ
    nlinarith [mul_nonneg hc.le rp.le]
  obtain ⟨L,len,valid,pair⟩ := grow _ _ start
  obtain ⟨S,hS,d,hd⟩ := regular_block_union G L s J len.ge
    (fun A h => (valid A h).2.1) (fun A h => (valid A h).2.2) pair
  refine ⟨S,d,?_,?_,hd⟩
  · rw [hS]
    exact (Nat.lt_mul_div_succ r jp).le
  · rw [hS]
    dsimp [s]
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm J]
    have := Nat.div_mul_le_self r J
    omega

end InducedDegreeRepetition
