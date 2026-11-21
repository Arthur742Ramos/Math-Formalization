module

public import EditAllowed
public import EditSampling
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Edit

open Finset
open scoped Classical
variable {X V : Type*}

@[expose] noncomputable def registered (F : Finset X) (d : X → V → ℕ) (ex : List V) (ref : X) :=
  F.filter fun x => ∀ y ∈ ex, d x y = d ref y

theorem registered_subset (F : Finset X) (d : X → V → ℕ) (ex : List V) (ref : X) :
    registered F d ex ref ⊆ F := by unfold registered; exact filter_subset ..

@[expose] def rowValues {J : Type*} (d : X → V → ℕ) (ys : J → V) (x : X) (j : J) : ℤ :=
  d x (ys j)

@[expose] def degreeCode (L k : ℕ) : Fin (L+1) := ⟨min k L,by omega⟩

theorem code_eq {L k l : ℕ} (hk : k ≤ L) (hl : l ≤ L) :
    degreeCode L k = degreeCode L l ↔ k=l := by simp [degreeCode,Fin.ext_iff,hk,hl]

/-- A reference with too small a full profile belongs to a small cell of the joint
partition by all exterior labels and all fresh rows. -/
theorem initial_profile_bound (F : Finset X) (d : X → V → ℕ) (L : ℕ) (ex : List V)
    {ℓ : ℕ} (ys : Fin ℓ → V) (bound : ∀ x ∈ F, ∀ y, d x y ≤ L) (v : ℝ) (hv : 0 ≤ v) :
    ((F.filter fun ref => ((profileFiber (registered F d ex ref) (rowValues d ys) (rowValues d ys ref)).card:ℝ) < v).card:ℝ)
      ≤ ((L:ℝ)+1)^(ex.length+ℓ)*v := by
  classical
  let code (x : X) := ((fun i : Fin ex.length => degreeCode L (d x (ex.get i))),
    fun i : Fin ℓ => degreeCode L (d x (ys i)))
  have eq (ref) (hr : ref ∈ F) : profileFiber (registered F d ex ref) (rowValues d ys) (rowValues d ys ref) =
      F.filter (fun x => code x = code ref) := by
    ext x
    simp only [profileFiber,registered,mem_filter,and_assoc]
    refine and_congr_right fun hx => ?_
    constructor
    · rintro ⟨external,rows⟩
      apply Prod.ext
      · exact funext fun i => congrArg (degreeCode L) (external (ex.get i) (List.get_mem ex i))
      · apply funext
        intro j
        apply congrArg (degreeCode L)
        exact Int.ofNat_inj.mp (congrFun rows j)
    · intro h
      refine ⟨?_,?_⟩
      · intro y hy
        obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hy
        exact (code_eq (bound x hx _) (bound ref hr _)).mp (congrFun (congrArg Prod.fst h) i)
      · apply funext
        intro j
        apply congrArg Int.ofNat
        exact (code_eq (bound x hx _) (bound ref hr _)).mp (congrFun (congrArg Prod.snd h) j)
  have event : F.filter (fun ref => ((profileFiber (registered F d ex ref) (rowValues d ys) (rowValues d ys ref)).card:ℝ) < v) =
      F.filter (fun ref => ((F.filter fun x => code x = code ref).card:ℝ) < v) := by
    ext ref
    simp only [mem_filter,and_congr_right_iff]
    intro hr
    rw [eq ref hr]
  rw [event]
  convert small_profile_cells F code v hv using 1
  · apply congrArg Nat.cast
    apply congrArg Finset.card
    ext ref
    simp only [mem_filter,and_congr_right_iff]
    intro _
    apply Iff.of_eq
    apply congrArg (fun U : Finset X => (U.card:ℝ) < v)
    ext x
    simp
  · simp [pow_add]

end InducedDegreeRepetition.Edit
