module

public import GroupEdits
public import ParityTargets
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V : Type}

theorem group_total_close {g : ℕ} (f : Fin g → ℕ) (p v : ℝ) (m : ℕ)
    (h : ∀ j, |(f j:ℝ)-p*m| ≤ v) :
    |((∑ j, f j : ℕ):ℝ)-p*(g*m)| ≤ g*v := by
  push_cast
  have e := (abs_sum_le_sum_abs (fun j => (f j:ℝ)-p*m) univ).trans (sum_le_sum (s:=univ) fun j _ => h j)
  simpa [sum_sub_distrib,mul_left_comm,mul_assoc] using e

/-- Equalize the degrees on a chosen set of good rows in the actual induced
graph. Rows outside it are retained when all the degrees are counted. -/
theorem good_witness {g n s r : ℕ} (G : SimpleGraph V) (η p θ v : ℝ) (len : Fin n → ℕ)
    (pool : Fin g → (i : Fin n) → Fin (len i) → Finset V) (T E good : Finset V)
    (ys : Fin g → Fin s → V) (ref ex : Fin g → Fin n → List V) (m d : ℕ)
    (length : ∑ i, len i = m) (Esub : E ⊆ T) (goodsub : good ⊆ E)
    (labels : ∀ y ∈ good, ∃ j k, ys j k = y)
    (dis : ∀ a b : (z : Fin g × Fin n) × Fin (len z.2), a ≠ b →
      Disjoint (pool a.1.1 a.1.2 a.2) (pool b.1.1 b.1.2 b.2))
    (away : ∀ j i k, Disjoint (pool j i k) T)
    (edits : ∀ j, Adjustable G θ (fun i => List.ofFn (pool j i)) (ex j) (ref j) (ys j))
    (exts : ∀ j i k t, k ≠ j → ys k t ∈ ex j i)
    (lower : r ≤ E.card+g*m) (upper : E.card+g*m < 2*r)
    (exc : ((E.card-good.card+g*m:ℕ):ℝ) ≤ η*(E.card+g*m))
    (positive : 0 < θ) (p₀ : 2*θ ≤ p) (p₁ : p ≤ 1-2*θ) (margin : 2+((g:ℝ)+2)*v ≤ θ*m)
    (near : |(d:ℝ)-p*(E.card+g*m)| ≤ 2)
    (parity : ∀ x ∈ good, (degreeOn G E x + ∑ k, contribution G (ref k) x)%2 = d%2)
    (base : ∀ x ∈ good, |(degreeOn G E x:ℝ)-p*E.card| ≤ v)
    (initial : ∀ x ∈ good, ∀ j, |(contribution G (ref j) x:ℝ)-p*m| ≤ v) :
    ∃ S : Finset V, r ≤ S.card ∧ S.card < 2*r ∧ (1-η)*S.card ≤ ((degreeClass G S d).card:ℝ) := by
  classical
  let selected (j : Fin g) := univ.filter fun k => ys j k ∈ good
  have select (j t) (mem : t ∈ selected j) := (mem_filter.mp mem).2
  have choices (j t) (mem : t ∈ selected j) := adjustment_target g m (degreeOn G E (ys j t)) E.card
    (∑ k, contribution G (ref k) (ys j t)) (contribution G (ref j) (ys j t)) d p θ v positive p₀ p₁ margin near
    (base _ (select j t mem)) (initial _ (select j t mem) j)
    (group_total_close _ _ _ _ (initial _ (select j t mem))) (parity _ (select j t mem))
  have allChoices (j : Fin g) (t : Fin s) : ∃ c : ℕ, t ∈ selected j →
      θ*m ≤ c ∧ (c:ℝ) ≤ (1-θ)*m ∧ Even ((c:ℤ)-contribution G (ref j) (ys j t)) ∧
      (c:ℤ) = (contribution G (ref j) (ys j t):ℤ)+d-degreeOn G E (ys j t)-
        (∑ k, contribution G (ref k) (ys j t):ℕ) := by
    by_cases h : t ∈ selected j
    · obtain ⟨c,properties⟩ := choices j t h
      exact ⟨c,fun _ => properties⟩
    · exact ⟨0,fun ht => (h ht).elim⟩
  choose target spec using allChoices
  obtain ⟨repl,valid,hit⟩ := edit_groups G θ (fun j i => List.ofFn (pool j i)) ex ref ys selected target edits exts (by
    intro j t h
    simp only [List.length_ofFn,length]
    exact ⟨(spec j t h).1,(spec j t h).2.1,(spec j t h).2.2.1⟩)
  obtain ⟨A,disA,cardA,count⟩ := realize_auxiliary (I:=Fin g × Fin n) G (fun z => len z.2) T
    (fun z => pool z.1 z.2) (fun z => repl z.1 z.2) (fun z => valid z.1 z.2) dis (fun z => away z.1 z.2)
  have size : A.card=g*m := by simpa [Fintype.sum_prod_type,length] using cardA
  refine ⟨E∪A,equalized_witness G E A good r d η (disA.symm.mono_left Esub) goodsub
    (by simpa [size] using lower) (by simpa [size] using upper) (by simpa [size] using exc) ?_⟩
  intro y hy
  obtain ⟨j,t,rfl⟩ := labels y hy
  have h : t ∈ selected j := mem_filter.mpr ⟨mem_univ _,hy⟩
  have achieved := hit j t h
  have eq := (spec j t h).2.2.2
  have tally : degreeOn G A (ys j t) = ∑ k, contribution G (repl k) (ys j t) := by
    simpa only [Fintype.sum_prod_type,contribution] using count (ys j t)
  rw [tally]
  push_cast at eq
  rw [eq] at achieved
  exact_mod_cast (by push_cast; linarith only [eq,achieved] :
    ((degreeOn G E (ys j t):ℤ) + (∑ k, contribution G (repl k) (ys j t):ℕ)) = (d:ℤ))

end InducedDegreeRepetition.Sampling
