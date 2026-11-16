/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic

/-!
# A proved rational affine-jump compiler

Each jump contributes an affine function strictly to the right of its
rational knot. Sorting and combining equal knots preserve the exact real
function. A prefix scan then produces affine pieces with a universal
equality theorem on each open interval.
-/

namespace ErdosOverlap

public section

structure AffineJump where
  knot : ℚ
  constant : ℚ
  linear : ℚ
  deriving DecidableEq, Repr

structure AffinePiece where
  left : ℚ
  right : ℚ
  constant : ℚ
  linear : ℚ
  deriving DecidableEq, Repr

/-- A proof-transparent boolean equality checker for large generated
tables.  Its soundness uses only scalar rational equality. -/
@[expose] def affineJumpsEqual (as : List AffineJump) : List AffineJump → Bool :=
  List.rec (fun bs => bs.isEmpty)
    (fun a _ recurse bs => match bs with
      | [] => false
      | b :: bs => decide (a.knot = b.knot) && decide (a.constant = b.constant) &&
          decide (a.linear = b.linear) && recurse bs) as

theorem affineJumpsEqual_sound (as bs : List AffineJump)
    (h : affineJumpsEqual as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [affineJumpsEqual]
  | cons a as ih =>
    cases bs with
    | nil => simp [affineJumpsEqual] at h
    | cons b bs =>
      simp only [affineJumpsEqual, Bool.and_eq_true, decide_eq_true_eq] at h
      have hab : a = b := by cases a; cases b; simp_all
      exact congrArg₂ List.cons hab (ih bs h.2)

@[expose] def affinePiecesEqual (as : List AffinePiece) : List AffinePiece → Bool :=
  List.rec (fun bs => bs.isEmpty)
    (fun a _ recurse bs => match bs with
      | [] => false
      | b :: bs => decide (a.left = b.left) && decide (a.right = b.right) &&
          decide (a.constant = b.constant) && decide (a.linear = b.linear) && recurse bs) as

theorem affinePiecesEqual_sound (as bs : List AffinePiece)
    (h : affinePiecesEqual as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [affinePiecesEqual]
  | cons a as ih =>
    cases bs with
    | nil => simp [affinePiecesEqual] at h
    | cons b bs =>
      simp only [affinePiecesEqual, Bool.and_eq_true, decide_eq_true_eq] at h
      have hab : a = b := by cases a; cases b; simp_all
      exact congrArg₂ List.cons hab (ih bs h.2)

@[expose] noncomputable def AffineJump.value (j : AffineJump) (t : ℝ) : ℝ :=
  if (j.knot : ℝ) < t then (j.constant : ℝ) + (j.linear : ℝ) * t else 0

@[expose] noncomputable def AffinePiece.value (p : AffinePiece) (t : ℝ) : ℝ :=
  (p.constant : ℝ) + (p.linear : ℝ) * t

@[expose] noncomputable def affineJumpSum : List AffineJump → ℝ → ℝ
  | [], _ => 0
  | j :: rest, t => j.value t + affineJumpSum rest t

@[expose] def AffineJump.addAt (a b : AffineJump) : AffineJump :=
  ⟨a.knot, a.constant + b.constant, a.linear + b.linear⟩

@[expose] def AffineJump.scale (c : ℚ) (a : AffineJump) : AffineJump :=
  ⟨a.knot, c * a.constant, c * a.linear⟩

theorem AffineJump.value_scale (c : ℚ) (a : AffineJump) (t : ℝ) :
    (a.scale c).value t = (c : ℝ) * a.value t := by
  unfold AffineJump.value AffineJump.scale
  simp only [Rat.cast_mul]
  split_ifs <;> ring

theorem affineJumpSum_append (a b : List AffineJump) (t : ℝ) :
    affineJumpSum (a ++ b) t = affineJumpSum a t + affineJumpSum b t := by
  induction a with
  | nil => simp [affineJumpSum]
  | cons j rest ih => simp [affineJumpSum, ih, add_assoc]

theorem affineJumpSum_scale (c : ℚ) (jumps : List AffineJump) (t : ℝ) :
    affineJumpSum (jumps.map (AffineJump.scale c)) t = (c : ℝ) * affineJumpSum jumps t := by
  induction jumps with
  | nil => simp [affineJumpSum]
  | cons j rest ih => simp [affineJumpSum, AffineJump.value_scale, ih, mul_add]

theorem affineJumpSum_flatMap {α : Type*} (items : List α) (f : α → List AffineJump) (t : ℝ) :
    affineJumpSum (items.flatMap f) t = (items.map (fun a => affineJumpSum (f a) t)).sum := by
  induction items with
  | nil => simp [affineJumpSum]
  | cons j rest ih => simp [affineJumpSum_append, ih]

theorem sum_list_range_eq_finset (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

@[expose] def collapseJumpsAux (a : AffineJump) (rest : List AffineJump) : List AffineJump :=
  List.rec (fun a => [a])
    (fun b _ recurse a => if a.knot = b.knot then recurse (a.addAt b)
      else a :: recurse b) rest a

@[expose] def collapseJumps : List AffineJump → List AffineJump
  | [] => []
  | a :: rest => collapseJumpsAux a rest

/-- A structurally recursive merge.  The fallback preserves every input
term even if the fuel is insufficient; the concrete compiler uses the
sum of the two input lengths. -/
@[expose] def mergeJumpsFuel (fuel : ℕ) : List AffineJump → List AffineJump → List AffineJump :=
  Nat.rec (fun xs ys => xs ++ ys)
    (fun _ recurse xs ys =>
      match xs, ys with
      | [], ys => ys
      | xs, [] => xs
      | x :: xs, y :: ys =>
        if x.knot ≤ y.knot then x :: recurse xs (y :: ys)
        else y :: recurse (x :: xs) ys) fuel

@[expose] def mergeJumps (xs ys : List AffineJump) : List AffineJump :=
  mergeJumpsFuel (xs.length + ys.length) xs ys

/-- A merge sort with transparent structural recursion, so exact table
checks reduce in Lean's kernel without evaluating well-founded proof
terms.  Correctness of the real function does not depend on the fuel. -/
@[expose] def sortJumpsFuel (fuel : ℕ) : List AffineJump → List AffineJump :=
  Nat.rec (fun xs => xs)
    (fun _ recurse xs =>
      match xs with
      | [] => []
      | [x] => [x]
      | x :: y :: xs =>
        let items := x :: y :: xs
        let midpoint := items.length / 2
        mergeJumps (recurse (items.take midpoint)) (recurse (items.drop midpoint))) fuel

@[expose] def sortJumps (xs : List AffineJump) : List AffineJump :=
  sortJumpsFuel 32 xs

@[expose] def canonicalJumps (jumps : List AffineJump) : List AffineJump :=
  collapseJumps (sortJumps jumps)

theorem AffineJump.value_addAt {a b : AffineJump} (hab : a.knot = b.knot) (t : ℝ) :
    (a.addAt b).value t = a.value t + b.value t := by
  unfold AffineJump.value AffineJump.addAt
  simp only [hab, Rat.cast_add]
  split_ifs <;> ring

theorem affineJumpSum_collapseAux (a : AffineJump) (rest : List AffineJump) (t : ℝ) :
    affineJumpSum (collapseJumpsAux a rest) t = a.value t + affineJumpSum rest t := by
  induction rest generalizing a with
  | nil => simp [collapseJumpsAux, affineJumpSum]
  | cons b rest ih =>
    change affineJumpSum (if a.knot = b.knot then collapseJumpsAux (a.addAt b) rest
      else a :: collapseJumpsAux b rest) t = _
    by_cases hab : a.knot = b.knot
    · rw [ite_eq_left hab, ih, AffineJump.value_addAt hab]
      simp only [affineJumpSum]
      ring
    · rw [ite_eq_right hab]
      simp only [affineJumpSum, ih]

theorem affineJumpSum_collapse (jumps : List AffineJump) (t : ℝ) :
    affineJumpSum (collapseJumps jumps) t = affineJumpSum jumps t := by
  cases jumps with
  | nil => rfl
  | cons a rest => exact affineJumpSum_collapseAux a rest t

theorem affineJumpSum_eq_sum_map (jumps : List AffineJump) (t : ℝ) :
    affineJumpSum jumps t = (jumps.map (fun j => j.value t)).sum := by
  induction jumps with
  | nil => rfl
  | cons j rest ih => simp [affineJumpSum, ih]

theorem affineJumpSum_perm {a b : List AffineJump} (hab : a.Perm b) (t : ℝ) :
    affineJumpSum a t = affineJumpSum b t := by
  rw [affineJumpSum_eq_sum_map, affineJumpSum_eq_sum_map]
  exact (hab.map (fun j => j.value t)).sum_eq

theorem affineJumpSum_mergeFuel (fuel : ℕ) (xs ys : List AffineJump) (t : ℝ) :
    affineJumpSum (mergeJumpsFuel fuel xs ys) t =
      affineJumpSum xs t + affineJumpSum ys t := by
  induction fuel generalizing xs ys with
  | zero => exact affineJumpSum_append xs ys t
  | succ fuel ih =>
    cases xs with
    | nil => simp [mergeJumpsFuel, affineJumpSum]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeJumpsFuel, affineJumpSum]
      | cons y ys =>
        change affineJumpSum (if x.knot ≤ y.knot then
          x :: mergeJumpsFuel fuel xs (y :: ys) else
          y :: mergeJumpsFuel fuel (x :: xs) ys) t = _
        split_ifs <;> simp only [affineJumpSum, ih] <;> ring

theorem affineJumpSum_merge (xs ys : List AffineJump) (t : ℝ) :
    affineJumpSum (mergeJumps xs ys) t = affineJumpSum xs t + affineJumpSum ys t :=
  affineJumpSum_mergeFuel _ xs ys t

theorem affineJumpSum_sortFuel (fuel : ℕ) (xs : List AffineJump) (t : ℝ) :
    affineJumpSum (sortJumpsFuel fuel xs) t = affineJumpSum xs t := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y xs =>
        change affineJumpSum (mergeJumps
          (sortJumpsFuel fuel ((x :: y :: xs).take ((x :: y :: xs).length / 2)))
          (sortJumpsFuel fuel ((x :: y :: xs).drop ((x :: y :: xs).length / 2)))) t = _
        rw [affineJumpSum_merge, ih, ih, ← affineJumpSum_append, List.take_append_drop]

theorem affineJumpSum_sort (xs : List AffineJump) (t : ℝ) :
    affineJumpSum (sortJumps xs) t = affineJumpSum xs t :=
  affineJumpSum_sortFuel _ xs t

/-- The compiler's rational sorting and combination are exact identities,
independently of how any proposed output table was generated. -/
theorem affineJumpSum_canonical (jumps : List AffineJump) (t : ℝ) :
    affineJumpSum (canonicalJumps jumps) t = affineJumpSum jumps t := by
  rw [canonicalJumps, affineJumpSum_collapse]
  exact affineJumpSum_sort jumps t

@[expose] def pruneJumps (jumps : List AffineJump) : List AffineJump :=
  List.rec [] (fun j _ rest => if j.constant ≠ 0 ∨ j.linear ≠ 0 then j :: rest else rest) jumps

@[expose] def compressedJumps (jumps : List AffineJump) : List AffineJump :=
  pruneJumps (canonicalJumps jumps)

theorem affineJumpSum_prune (jumps : List AffineJump) (t : ℝ) :
    affineJumpSum (pruneJumps jumps) t = affineJumpSum jumps t := by
  induction jumps with
  | nil => rfl
  | cons j rest ih =>
    by_cases hz : j.constant = 0 ∧ j.linear = 0
    · have hv : j.value t = 0 := by simp [AffineJump.value, hz.1, hz.2]
      simpa [pruneJumps, hz.1, hz.2, affineJumpSum, hv] using ih
    · have hp : j.constant ≠ 0 ∨ j.linear ≠ 0 := by tauto
      simpa [pruneJumps, hp, affineJumpSum] using congrArg (fun x => j.value t + x) ih

theorem affineJumpSum_compressed (jumps : List AffineJump) (t : ℝ) :
    affineJumpSum (compressedJumps jumps) t = affineJumpSum jumps t := by
  rw [compressedJumps, affineJumpSum_prune, affineJumpSum_canonical]

/-- Merge already compressed blocks while preserving their real sum.
Intermediate cancellation keeps the exact kernel checker memory bounded. -/
@[expose] def mergeCompressedJumps (xs ys : List AffineJump) : List AffineJump :=
  pruneJumps (collapseJumps (mergeJumps xs ys))

theorem affineJumpSum_mergeCompressed (xs ys : List AffineJump) (t : ℝ) :
    affineJumpSum (mergeCompressedJumps xs ys) t =
      affineJumpSum xs t + affineJumpSum ys t := by
  rw [mergeCompressedJumps, affineJumpSum_prune, affineJumpSum_collapse, affineJumpSum_merge]

@[expose] def compiledJumpBlocksFuel (fuel : ℕ) : List (List AffineJump) → List AffineJump :=
  Nat.rec (fun blocks => compressedJumps blocks.flatten)
    (fun _ recurse blocks =>
      match blocks with
      | [] => []
      | [xs] => compressedJumps xs
      | xs :: ys :: rest =>
        let items := xs :: ys :: rest
        let midpoint := items.length / 2
        mergeCompressedJumps (recurse (items.take midpoint)) (recurse (items.drop midpoint))) fuel

@[expose] def compiledJumpBlocks (blocks : List (List AffineJump)) : List AffineJump :=
  compiledJumpBlocksFuel 32 blocks

theorem affineJumpSum_compiledBlocksFuel (fuel : ℕ) (blocks : List (List AffineJump)) (t : ℝ) :
    affineJumpSum (compiledJumpBlocksFuel fuel blocks) t = affineJumpSum blocks.flatten t := by
  induction fuel generalizing blocks with
  | zero => exact affineJumpSum_compressed _ t
  | succ fuel ih =>
    cases blocks with
    | nil => rfl
    | cons xs rest =>
      cases rest with
      | nil => simpa only [compiledJumpBlocksFuel, List.flatten_singleton] using
          affineJumpSum_compressed xs t
      | cons ys rest =>
        change affineJumpSum (mergeCompressedJumps
          (compiledJumpBlocksFuel fuel ((xs :: ys :: rest).take ((xs :: ys :: rest).length / 2)))
          (compiledJumpBlocksFuel fuel ((xs :: ys :: rest).drop ((xs :: ys :: rest).length / 2)))) t = _
        rw [affineJumpSum_mergeCompressed, ih, ih, ← affineJumpSum_append,
          ← List.flatten_append, List.take_append_drop]

theorem affineJumpSum_compiledBlocks (blocks : List (List AffineJump)) (t : ℝ) :
    affineJumpSum (compiledJumpBlocks blocks) t = affineJumpSum blocks.flatten t :=
  affineJumpSum_compiledBlocksFuel _ blocks t

@[expose] def compileAffinePieces (left right constant linear : ℚ) :
    List AffineJump → List AffinePiece
  | [] => [⟨left, right, constant, linear⟩]
  | j :: rest =>
    ⟨left, j.knot, constant, linear⟩ ::
      compileAffinePieces j.knot right (constant + j.constant) (linear + j.linear) rest

theorem compileAffinePieces_left_mem (left right constant linear : ℚ)
    (jumps : List AffineJump) {p : AffinePiece}
    (hp : p ∈ compileAffinePieces left right constant linear jumps) :
    p.left = left ∨ ∃ j ∈ jumps, p.left = j.knot := by
  induction jumps generalizing left constant linear with
  | nil =>
    simp only [compileAffinePieces, List.mem_singleton] at hp
    subst p
    exact Or.inl rfl
  | cons j rest ih =>
    simp only [compileAffinePieces, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · rcases ih _ _ _ hp with h | ⟨q, hq, heq⟩
      · exact Or.inr ⟨j, List.mem_cons_self, h⟩
      · exact Or.inr ⟨q, List.mem_cons_of_mem j hq, heq⟩

theorem affineJumpSum_zero_of_le (jumps : List AffineJump) (t : ℝ)
    (h : ∀ j ∈ jumps, t ≤ (j.knot : ℝ)) : affineJumpSum jumps t = 0 := by
  induction jumps with
  | nil => rfl
  | cons j rest ih =>
    rw [affineJumpSum, AffineJump.value, ite_eq_right (not_lt.mpr (h j List.mem_cons_self)), zero_add]
    exact ih (fun q hq => h q (List.mem_cons_of_mem j hq))

/-- Every prefix-scan piece is equal to the exact affine-jump function on
its open interval. Knots themselves are immaterial for integration. -/
theorem compileAffinePieces_value
    (left right constant linear : ℚ) (jumps : List AffineJump)
    (hsorted : jumps.Pairwise (fun a b => a.knot ≤ b.knot))
    {p : AffinePiece} (hp : p ∈ compileAffinePieces left right constant linear jumps)
    {t : ℝ} (ht : t ∈ Set.Ioo (p.left : ℝ) (p.right : ℝ)) :
    (constant : ℝ) + (linear : ℝ) * t + affineJumpSum jumps t = p.value t := by
  induction jumps generalizing left constant linear with
  | nil =>
    simp only [compileAffinePieces, List.mem_singleton] at hp
    subst p
    simp [affineJumpSum, AffinePiece.value]
  | cons j rest ih =>
    have hsorted' := List.pairwise_cons.mp hsorted
    simp only [compileAffinePieces, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hz : affineJumpSum (j :: rest) t = 0 := by
        apply affineJumpSum_zero_of_le
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ht.2.le
        · have hjq : (j.knot : ℝ) ≤ (q.knot : ℝ) := by exact_mod_cast hsorted'.1 q hq
          exact ht.2.le.trans hjq
      rw [hz, add_zero]
      rfl
    · have hjt : (j.knot : ℝ) < t := by
        rcases compileAffinePieces_left_mem j.knot right (constant + j.constant)
          (linear + j.linear) rest hp with heq | ⟨q, hq, heq⟩
        · rw [heq] at ht
          exact ht.1
        · have hjq : (j.knot : ℝ) ≤ (q.knot : ℝ) := by exact_mod_cast hsorted'.1 q hq
          rw [heq] at ht
          exact hjq.trans_lt ht.1
      have hi := ih j.knot (constant + j.constant) (linear + j.linear) hsorted'.2 hp
      rw [affineJumpSum, AffineJump.value, ite_eq_left hjt]
      push_cast at hi
      unfold AffinePiece.value at hi ⊢
      linarith

/-- The same exact prefix scan expressed with the primitive list
recursor to bound memory during large kernel reductions. -/
@[expose] def compileAffinePiecesFast (left right constant linear : ℚ)
    (jumps : List AffineJump) : List AffinePiece :=
  List.rec (fun left constant linear => [⟨left, right, constant, linear⟩])
    (fun j _ recurse left constant linear =>
      ⟨left, j.knot, constant, linear⟩ ::
        recurse j.knot (constant + j.constant) (linear + j.linear)) jumps left constant linear

theorem compileAffinePiecesFast_eq (left right constant linear : ℚ) (jumps : List AffineJump) :
    compileAffinePiecesFast left right constant linear jumps =
      compileAffinePieces left right constant linear jumps := by
  induction jumps generalizing left constant linear with
  | nil => rfl
  | cons j rest ih =>
    change (⟨left, j.knot, constant, linear⟩ ::
      compileAffinePiecesFast j.knot right (constant + j.constant) (linear + j.linear) rest) = _
    rw [ih]
    rfl

end
end ErdosOverlap
