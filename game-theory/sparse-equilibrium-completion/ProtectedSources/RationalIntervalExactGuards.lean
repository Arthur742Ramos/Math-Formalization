/- AI-assisted formalization under the repository Apache-2.0 license.
Separate exact composition: all candidate linear/core/global guards are tested.
The sorted quadratic checker is exact; this is not the eta-grid relaxation. -/
module
public import ProtectedSources.RationalIntervalCutCheck
public import ProtectedSources.RationalGap
public import ProtectedSources.IntervalConvexity
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalExactGuards {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) ∧
  (∀ a, (∑ b, K a b*p b)-(∑ i, V i a) ≤ ε) ∧
  (∀ a b, K a b= -K b a) ∧
  (∀ a b, coreLo a b ≤ K a b ∧ K a b ≤ coreHi a b) ∧
  (∀ i, rationalScore lo p i ≤ ε+M*r)

instance rationalIntervalExactGuardsDecidable {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) :
    Decidable (RationalIntervalExactGuards lo hi V coreLo coreHi K p q M r ε) := by
  unfold RationalIntervalExactGuards
  infer_instance

def rationalIntervalExactCheck {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) : Bool :=
  decide (RationalIntervalExactGuards lo hi V coreLo coreHi K p q M r ε) &&
    (rationalIntervalCutCheck M r ε p q V).1

theorem rational_interval_exact_check_iff {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ) (hM : 0 ≤ M) :
    rationalIntervalExactCheck lo hi V coreLo coreHi K p q M r ε = true ↔
      intervalPerspectiveSystem
        (fun i a => (lo i a : ℝ)) (fun i a => (hi i a : ℝ))
        (fun a b => (coreLo a b : ℝ)) (fun a b => (coreHi a b : ℝ))
        (fun a => (p a : ℝ)) (M : ℝ) (r : ℝ) (ε : ℝ)
        ((fun i => (q i : ℝ)),(fun i a => (V i a : ℝ)),(fun a b => (K a b : ℝ))) := by
  rw [rationalIntervalExactCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hg,hcheck⟩
    rcases hg with ⟨hq,hr,hV,ha,hK,hC,hguard⟩
    have hc := (rational_interval_cut_check_iff M r ε lo hi V p q hM hq hV).mp hcheck
    dsimp only [intervalPerspectiveSystem, IsSkew]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,hc⟩
    · intro i; exact_mod_cast hq i
    · exact_mod_cast hr
    · intro i a
      constructor
      · exact_mod_cast (hV i a).1
      · exact_mod_cast (hV i a).2
    · intro a; exact_mod_cast ha a
    · intro a b; exact_mod_cast hK a b
    · intro a b
      constructor
      · exact_mod_cast (hC a b).1
      · exact_mod_cast (hC a b).2
    · intro i
      change (∑ a, (lo i a : ℝ)*(p a : ℝ)) ≤ (ε : ℝ)+(M : ℝ)*(r : ℝ)
      have hg' := hguard i
      unfold rationalScore at hg'
      exact_mod_cast hg'
  · rintro ⟨hq,hr,hV,ha,hK,hC,hguard,hcuts⟩
    dsimp only [IsSkew] at hq hr hV ha hK hC hguard hcuts
    have hqr : ∀ i, 0 ≤ q i := by intro i; exact_mod_cast hq i
    have hVr : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i := by
      intro i a
      constructor
      · exact_mod_cast (hV i a).1
      · exact_mod_cast (hV i a).2
    refine ⟨⟨hqr,?_,hVr,?_,?_,?_,?_⟩,
      (rational_interval_cut_check_iff M r ε lo hi V p q hM hqr hVr).mpr hcuts⟩
    · exact_mod_cast hr
    · intro a; exact_mod_cast ha a
    · intro a b; exact_mod_cast hK a b
    · intro a b
      constructor
      · exact_mod_cast (hC a b).1
      · exact_mod_cast (hC a b).2
    · intro i
      unfold rationalScore
      have hg' := hguard i
      change (∑ a, (lo i a : ℝ)*(p a : ℝ)) ≤ (ε : ℝ)+(M : ℝ)*(r : ℝ) at hg'
      exact_mod_cast hg'

theorem rational_interval_exact_check_full_game {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (coreLo coreHi K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 < M) (hp : ∀ a, 0 ≤ p a) (hpmass : (∑ a, p a)+r=1)
    (hclo : ∀ a b, -M ≤ coreLo a b) (hchi : ∀ a b, coreHi a b ≤ M)
    (hlo : ∀ i a, -M ≤ lo i a) (hhi : ∀ i a, hi i a ≤ M)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (hc : rationalIntervalExactCheck lo hi V coreLo coreHi K p q M r ε = true) :
    ∃ (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ),
      (∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ)) ∧
      (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a) ∧
      (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
      IsSkew (blockMatrix (fun a b => (K a b : ℝ)) D B) ∧
      (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) D B a b ∧
        blockMatrix (fun a b => (K a b : ℝ)) D B a b ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) D B)
        (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤ (ε : ℝ) := by
  have hs := (rational_interval_exact_check_iff lo hi V coreLo coreHi K p q M r ε (le_of_lt hM)).mp hc
  rcases hs with ⟨hq,hr,hV,ha,hK,hC,hg,hcuts⟩
  dsimp only [IsSkew] at hq hr hV ha hK hC hg hcuts
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpr : ∀ a, (0 : ℝ) ≤ (p a : ℝ) := by intro a; exact_mod_cast hp a
  have hpm : (∑ a, (p a : ℝ))+(r : ℝ)=1 := by exact_mod_cast hpmass
  have hKb : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    have hl : -(M : ℝ) ≤ (coreLo a b : ℝ) := by exact_mod_cast hclo a b
    have hu : (coreHi a b : ℝ) ≤ (M : ℝ) := by exact_mod_cast hchi a b
    exact ⟨hl.trans (hC a b).1,(hC a b).2.trans hu⟩
  exact (normalized_interval_perspective_iff _ _ _ _ _ _ _ _ hMr hpr hq hr hpm hK hKb
    (by intro i a; exact_mod_cast hlo i a)
    (by intro i a; exact_mod_cast hhi i a)
    (by intro i a; exact_mod_cast hlu i a)).mpr ⟨(fun i a => (V i a : ℝ)),hV,ha,hg,hcuts⟩

end SparseCompletion
