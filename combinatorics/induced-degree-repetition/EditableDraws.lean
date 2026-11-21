module

public import TwoLengths
public import OtherProfiles
public import EditMargins
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Edit

open Finset OpenProblems Residues
open scoped Classical

@[expose] noncomputable def requiredTests (L₀ L : ℕ) : List (Option ℕ) :=
  if L=L₀ then [none] else (moduli L₀).map some ++ [none]

theorem editable_draws (L₀ L₁ : ℕ) (hL : 0 < L₀) (hLs : L₀ < L₁) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1/2) :
    ∃ n₁ : ℕ, ∀ {N n ℓ : ℕ} (G : SimpleGraph (Fin N)) (Xs : Fin n → List (Finset (Fin N)))
      (ex ref : Fin n → List (Fin N)) (ys : Fin ℓ → Fin N) (cut : Fin n → ℝ) (w : ℝ),
      (∀ i, (Xs i).length = L₀ ∨ (Xs i).length = L₁) →
      n₁ ≤ (univ.filter fun i => (Xs i).length=L₀).card → n₁ ≤ (univ.filter fun i => (Xs i).length=L₁).card →
      0 < w → w ≤ 1 → (∀ i, 0 < cut i) → (∀ i, ref i ∈ tupleSpace (Xs i)) →
      let d := fun P y => tupleDegree (adj G) y P
      let S := fun i => registered (tupleSpace (Xs i)) d (ex i) (ref i)
      (∀ i, cut i ≤ w^ℓ*(profileFiber (S i) (rowValues d ys) (rowValues d ys (ref i))).card) →
      (∀ i, GoodRows (S i) d (Xs i).length θ w (cut i) (requiredTests L₀ (Xs i).length) ys) →
      Adjustable G θ Xs ex ref ys := by
  classical
  obtain ⟨n₀,C,edit⟩ := simultaneous_edits L₀ L₁
  refine ⟨max n₀ ⌈2*C/θ⌉₊,?_⟩
  intro N n ℓ G Xs ex ref ys cut w lens short long hw w1 cp refs d S initial rows
  let len := fun i => (Xs i).length
  let A := univ.filter fun i => len i = L₀
  let B := univ.filter fun i => len i = L₁
  let entry := fun (_ : Fin n) => rowValues d ys
  let s₀ := fun i => entry i (ref i)
  have dis : Disjoint A B := disjoint_left.mpr fun i ha hb => by
    have h := (mem_filter.mp ha).2
    have h' := (mem_filter.mp hb).2
    exact hLs.ne (h.symm.trans h')
  have bound (i) (P) (hp : P ∈ tupleSpace (Xs i)) (y) : d P y ≤ len i :=
    (List.countP_le_length ..).trans (tuple_len hp).le
  have margin := length_margin len L₀ C θ hθ hL ((le_max_right ..).trans short)
  intro R target need
  obtain ⟨repl,pool,hit,keep⟩ := edit (univ : Finset (Fin n)) A B R S entry s₀ len
    (fun _ => w) cut (fun i => ⌊θ*len i/5⌋) (fun i => ⌈(1-θ/5)*len i⌉) (fun j => (target j:ℤ))
    (subset_univ _) (subset_univ _) dis ((le_max_left ..).trans short) ((le_max_left ..).trans long)
    (fun i _ => ⟨by rcases lens i with h|h <;> dsimp [len] <;> omega,hw,w1,cp i,(initial i).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hw.le w1 (by simpa using card_le_univ R)) (Nat.cast_nonneg _))⟩)
    (fun i _ j => mem_Icc.mpr ⟨by exact Int.natCast_nonneg _,by change (d (ref i) (ys j):ℤ) ≤ (len i:ℤ); exact_mod_cast bound i _ (refs i) (ys j)⟩)
    (fun i _ s j _ enough => by
      have data := rows i s j enough
      have ne : (otherFiber (S i) (entry i) s j).Nonempty := card_pos.mp (by exact_mod_cast (cp i).trans_le enough)
      have test := allowed_tests (S i) (fun x k => d x (ys k)) (len i) L₀ w θ hw
        (by rcases lens i with h|h <;> dsimp [len] <;> omega) hθ'
        (fun x hx k => bound i x (registered_subset _ _ _ _ hx) (ys k)) s j ne
        (data none (by simp [requiredTests]; split <;> simp))
        (fun diff q hq => data (some q) (by simp [requiredTests,show (Xs i).length ≠ L₀ from diff,mem_moduli,hq]))
      exact ⟨test.1,test.2.1,test.2.2.1,fun h => test.2.2.2.1 (mem_filter.mp h).2,
        fun h => test.2.2.2.2 (by have z := (mem_filter.mp h).2; change len i = L₁ at z; omega)⟩)
    (fun j hj => by
      obtain ⟨lo,hi,even⟩ := need j hj
      obtain ⟨p,q⟩ := target_margins len θ C (target j) margin lo hi
      exact ⟨p,q,by simpa [s₀,entry,rowValues,d,Nat.cast_sum] using even⟩)
  let repl' := fun i : Fin n => repl ⟨i,mem_univ i⟩
  have reg (i : Fin n) : repl' i ∈ tupleSpace (Xs i) ∧ ∀ y ∈ ex i, d (repl' i) y = d (ref i) y := by
    simpa only [S,registered,mem_filter,repl'] using pool ⟨i,mem_univ _⟩
  refine ⟨repl',fun i => (reg i).1,fun i => (reg i).2,?_,?_⟩
  · intro j hj
    have h := hit j hj
    have e : (∑ i : (univ : Finset (Fin n)), entry i.val (repl i) j) = ∑ i, (d (repl' i) (ys j):ℤ) := by
      change (∑ i : (univ : Finset (Fin n)), (d (repl' i.val) (ys j):ℤ)) = _
      simpa only [attach_eq_univ] using
        (Finset.sum_attach (univ : Finset (Fin n)) (fun i => (d (repl' i) (ys j):ℤ)))
    rw [e] at h
    exact_mod_cast h
  · intro j hj
    apply sum_congr rfl
    intro i _
    exact Int.ofNat_inj.mp (keep ⟨i,mem_univ i⟩ j hj)

end InducedDegreeRepetition.Edit
