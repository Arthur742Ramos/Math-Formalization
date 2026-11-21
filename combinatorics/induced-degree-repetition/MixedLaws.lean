module

public import CosetProjection
public import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality.Law

open Finset
open scoped Classical
variable {G H : Type*} [Fintype G] [Fintype H]

@[expose] noncomputable def prodLaw (f : Law G) (g : Law H) : Law (G × H) where
  val z := f z.1*g z.2
  nonneg z := mul_nonneg (f.nonneg _) (g.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp only [← mul_sum,g.total,mul_one,f.total]

theorem eq_by_test {f g : Law G} (h : ∀ v : G → ℝ, (∑ z, f z*v z) = ∑ z, g z*v z) : f = g := by
  classical
  apply ext_law
  intro z
  simpa [mul_ite] using h (fun t => if t=z then (1:ℝ) else 0)

variable [AddCommGroup G] [AddCommGroup H]

theorem diff_product (f : Law G) (g : Law H) :
    (prodLaw f g).difference = prodLaw f.difference g.difference := by
  apply ext_law
  rintro ⟨x,y⟩
  change (∑ p : G × H, (f p.1*g p.2)*(f (p.1-x)*g (p.2-y))) =
    (∑ a, f a*f (a-x)) * ∑ b, g b*g (b-y)
  rw [Fintype.sum_prod_type,sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intros
  ring

@[expose] def plusHom : G × G →+ G := (AddMonoidHom.fst G G)+(AddMonoidHom.snd G G)

@[expose] noncomputable def plus (f g : Law G) := (prodLaw f g).push plusHom

theorem plus_test (f g : Law G) (v : G → ℝ) :
    (∑ t, plus f g t*v t) = ∑ x, f x*∑ y, g y*v (x+y) := by
  rw [plus,push_test,Fintype.sum_prod_type]
  simp only [prodLaw,plusHom,AddMonoidHom.add_apply,AddMonoidHom.coe_fst,AddMonoidHom.coe_snd,mul_sum,mul_assoc]

theorem plus_assoc (f g h : Law G) : (f.plus g).plus h = f.plus (g.plus h) := by
  apply eq_by_test
  intro v
  rw [plus_test,plus_test f (g.plus h)]
  rw [plus_test (v := fun t => ∑ y, h y * v (t+y))]
  apply sum_congr rfl
  intro x _
  rw [plus_test (v := fun t => v (x+t))]
  simp [add_assoc]

theorem diff_plus (f g : Law G) : (f.plus g).difference = f.difference.plus g.difference := by
  rw [plus,← push_difference,diff_product]
  rfl

theorem plus_apply (f g : Law G) (z : G) : f.plus g z = ∑ x, f x*g (z-x) := by
  have h := plus_test f g (fun t => if t = z then (1:ℝ) else 0)
  have iff' (x y : G) : x+y=z ↔ y=z-x := by
    constructor
    · rintro rfl; abel
    · rintro rfl; abel
  simpa [mul_ite,iff'] using h

theorem plus_sq (f g : Law G) (z : G) : (f.plus g z)^2 ≤ f.difference 0*g.difference 0 := by
  rw [plus_apply]
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset G) f.val (fun x => g (z-x))
  have e := (Equiv.subLeft z).sum_comp (fun x => g x^2)
  change (∑ x, g (z-x)^2) = _ at e
  rw [e] at h
  simpa [difference,diff,pow_two] using h

@[expose] noncomputable def point (z : G) : Law G where
  val x := if x=z then 1 else 0
  nonneg _ := by split <;> norm_num
  total := by simp

theorem point_left (f : Law G) : (point 0).plus f = f := by
  apply ext_law
  intro z
  simp [plus_apply,point,ite_mul]

@[expose] noncomputable def listSum : List (Law G) → Law G
  | [] => point 0
  | f::fs => f.plus (listSum fs)

theorem list_append (l s : List (Law G)) : listSum (l++s) = (listSum l).plus (listSum s) := by
  induction l with
  | nil => simp [listSum,point_left]
  | cons f l ih => simp only [List.cons_append,listSum,ih,plus_assoc]

theorem diff_point : (point (0:G)).difference = point 0 := by
  apply ext_law
  intro z
  simp [difference,diff,point,sub_eq_zero]

theorem diff_list (l : List (Law G)) : (listSum l).difference = listSum (l.map difference) := by
  induction l with
  | nil => exact diff_point
  | cons f l ih => simp [listSum,diff_plus,ih]

/-- Repeated Cauchy-Schwarz on the two halves of a dyadic list gives the
mixed-law atom estimate without choosing characters on a quotient. -/
theorem dyadic_mixed (l : List (Law G)) (j : ℕ) (b : ℝ) (hb : 0 ≤ b) (len : l.length = 2^j)
    (each : ∀ f ∈ l, ∀ z, f.iter j z ≤ b) : ∀ z, listSum l z ≤ b := by
  induction j generalizing l with
  | zero =>
    rcases l with _|⟨f,l⟩
    · simp at len
    · have e : l=[] := List.length_eq_zero_iff.mp (by simpa using len)
      subst l
      have one : f.plus (point 0) = f := by apply ext_law; intro z; simp [plus_apply,point,mul_ite,sub_eq_zero]
      intro z
      simpa [listSum,one,iter] using each f (by simp) z
  | succ j ih =>
    let a := l.take (2^j)
    let c := l.drop (2^j)
    have len' : l.length = 2^j + 2^j := by rw [len,pow_succ]; omega
    have la : a.length = 2^j := by simp [a,len']
    have lc : c.length = 2^j := by simp [c,len']
    have iter_s (f : Law G) (k : ℕ) : f.difference.iter k = f.iter (k+1) := by
      induction k with
      | zero => rfl
      | succ k ih => change (f.difference.iter k).difference = (f.iter (k+1)).difference; rw [ih]
    have part (s : List (Law G)) (ls : s.length = 2^j) (mem : ∀ f ∈ s, f ∈ l) :
        (listSum s).difference 0 ≤ b := by
      rw [diff_list]
      apply ih _ (by simpa using ls) _ 0
      intro f hf z
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      rw [iter_s]
      exact each g (mem g hg) z
    have ha := part a la (fun _ h => List.mem_of_mem_take h)
    have hc := part c lc (fun _ h => List.mem_of_mem_drop h)
    intro z
    have e : l = a++c := (List.take_append_drop ..).symm
    rw [e,list_append]
    have h := (plus_sq (listSum a) (listSum c) z).trans (mul_le_mul ha hc
      ((listSum c).difference.nonneg _) hb)
    nlinarith only [h,hb,((listSum a).plus (listSum c)).nonneg z]

end InducedDegreeRepetition.Duality.Law
