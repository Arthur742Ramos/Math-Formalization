module

public import SamplingPlan
public import HostScales
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Filter Finset OpenProblems
open scoped Classical
variable {r N g L₀ L₁ n₁ : ℕ} {u θ η a ε p : ℝ}

set_option maxHeartbeats 800000 in
theorem core_witness (G : SimpleGraph (Fin N)) (B : Finset (Fin N))
    (plan : SamplingPlan r B.card g L₀ L₁ n₁ u θ η a ε)
    (hp : 0 < θ) (ep : 0 ≤ η) (p₀ : 2*θ ≤ p) (p₁ : p ≤ 1-2*θ) (Ls : L₀ < L₁)
    (op : SpectralBound G B p ε)
    (δ : ℝ) (hd : 0 ≤ δ) (gδ : (g:ℝ)*δ ≤ 1/8)
    (adjust : ∀ (Y : Finset (Fin N)) (n ℓ : ℕ), n ≤ r^2 → (ℓ:ℝ) ≤ a*r →
      ∀ (Xs : Fin n → List (Finset (Fin N))) (ex : Fin n → List (Fin N)),
      (∀ i, Positional B Y (Xs i) r u ∧ ((Xs i).length=L₀ ∨ (Xs i).length=L₁) ∧ (ex i).length ≤ 4*r) →
      n₁ ≤ (univ.filter fun i => (Xs i).length=L₀).card → n₁ ≤ (univ.filter fun i => (Xs i).length=L₁).card →
      let draws := (Fintype.piFinset fun i => tupleSpace (Xs i)) ×ˢ (Fintype.piFinset fun _ : Fin ℓ => Y)
      ((draws.filter fun z => ¬Adjustable G θ Xs ex z.1 z.2).card:ℝ) ≤ δ*draws.card) :
    ∃ S : Finset (Fin N), ∃ d : ℕ, r ≤ S.card ∧ S.card < 2*r ∧ (1-η)*S.card ≤ ((degreeClass G S d).card:ℝ) := by
  classical
  let n := plan.k+plan.k
  let len := blockLength plan.k L₀ L₁
  obtain ⟨short,long,m⟩ := block_counts plan.k L₀ L₁ Ls.ne
  have sizes (i : Fin n) : len i=L₀ ∨ len i=L₁ := by dsimp [len,blockLength]; split <;> simp
  have cap (i : Fin n) : len i ≤ L₁ := by rcases sizes i with h|h <;> omega
  have length : ∑ i, len i = plan.m := m.trans plan.block
  let Pos := (z : Fin g × Fin n) × Fin (len z.2)
  have num : Fintype.card Pos=g*plan.m := by simp [Pos,Fintype.card_sigma,Fintype.sum_prod_type]; exact Or.inl length
  obtain ⟨T,tB,ts,P,allP,dis⟩ := reserve_pools (I:=Pos) B plan.b (by simpa [num] using plan.space)
  have tp : T.Nonempty := card_pos.mp (ts ▸ plan.testPos)
  let : Nonempty T := tp.to_subtype
  let U := fun (j : Fin g) (i : Fin n) (k : Fin (len i)) => P ⟨(j,i),k⟩
  let sets := fun j i => List.ofFn (U j i)
  have nempty (j : Fin g) (i : Fin n) : (tupleSpace (sets j i)).Nonempty := by
    apply tuples_nonempty
    intro X hx
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hx
    exact card_pos.mp ((allP _).2.1 ▸ plan.positive)
  let inst (j : Fin g) (i : Fin n) : Nonempty ↥(tupleSpace (sets j i)) := (nempty j i).to_subtype
  have tlarge : Large B T r u 16 := ⟨tB,plan.cutoff.trans (Nat.cast_le.mpr (ts ▸ plan.half))⟩
  have local_bound (j : Fin g) (o : {k : Fin g // k ≠ j} → Fin plan.s → T) :=
    adjust T n plan.s plan.poly plan.fresh (sets j) (fun _ => exteriorList j (fun k t => (o k t : Fin N))) (by
      intro i
      refine ⟨⟨tlarge,?_⟩,by simpa [sets] using sizes i,by simpa only [length_exterior] using plan.ext⟩
      intro X hx
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hx
      obtain ⟨xb,xsize,away⟩ := allP (⟨(j,i),k⟩ : Pos)
      exact ⟨⟨xb,xsize ▸ plan.cutoff⟩,away⟩)
      (by
        apply plan.enough.trans_eq
        rw [← short]
        apply congrArg Finset.card
        ext i
        simp [sets,len]) (by
        apply plan.enough.trans_eq
        rw [← long]
        apply congrArg Finset.card
        ext i
        simp [sets,len])
  have refBound (j : Fin g) := group_deviation G p ε B T tB tp op L₁ len cap (U j) plan.b plan.positive
    (fun i k => (allP (⟨(j,i),k⟩:Pos)).2.1) (fun i k => (allP (⟨(j,i),k⟩:Pos)).1)
    (fun a b ne => dis ⟨(j,a.1),a.2⟩ ⟨(j,b.1),b.2⟩ (by rintro e; apply ne; cases a; cases b; cases e; rfl))
  obtain ⟨ref,ys,inj,mom,few,edits⟩ := sample_selection (s:=plan.s) G T p θ sets plan.m plan.v plan.κ plan.count δ plan.D
    plan.vpos plan.κpos plan.cpos hd (by simpa [ts] using plan.collisions)
    ((tester_moment (I:=Fin g × Fin plan.s) G B T p ε tB (by linarith) (by linarith) op tp (by
      exact_mod_cast ts ▸ plan.testSize)).trans (by simpa [Fintype.card_prod] using plan.spectral))
    (fun j => by
      have h := refBound j
      rw [length,ts] at h
      apply h.trans
      simpa only [Fintype.card_fin,n] using plan.variance)
    plan.refErrors gδ local_bound
  apply sampled_witness G p θ η plan.v plan.κ plan.count T len U ref ys plan.m length dis
    (fun j i k => (allP (⟨(j,i),k⟩:Pos)).2.2) inj mom few edits hp ep plan.vpos plan.κpos.le
    p₀ p₁ plan.margin plan.nh plan.tail plan.exceptional

end InducedDegreeRepetition.Sampling
