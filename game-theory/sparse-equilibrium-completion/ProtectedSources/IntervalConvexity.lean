/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.IntervalConic
public import ProtectedSources.ConicConvexity

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem perspective_quadratic_mix {ι : Type*} (S : Finset ι)
    (q q' H H' : ι → ℝ) (M r ε a b : ℝ)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    M*(mass S (a • q+b • q'))^2-M*r*mass S (a • q+b • q')+
      (∑ i ∈ S, ((a*H i+b*H' i)-ε*(a*q i+b*q' i))) ≤
      a*(M*(mass S q)^2-M*r*mass S q+(∑ i ∈ S, (H i-ε*q i)))+
      b*(M*(mass S q')^2-M*r*mass S q'+(∑ i ∈ S, (H' i-ε*q' i))) := by
  rw [finite_mass_mix]
  have he : (∑ i ∈ S, ((a*H i+b*H' i)-ε*(a*q i+b*q' i)))=
      a*(∑ i ∈ S, (H i-ε*q i))+b*(∑ i ∈ S, (H' i-ε*q' i)) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  have hid : M*(a*mass S q+b*mass S q')^2-M*r*(a*mass S q+b*mass S q')+
      (a*(∑ i ∈ S, (H i-ε*q i))+b*(∑ i ∈ S, (H' i-ε*q' i)))=
      a*(M*(mass S q)^2-M*r*mass S q+(∑ i ∈ S, (H i-ε*q i)))+
      b*(M*(mass S q')^2-M*r*mass S q'+(∑ i ∈ S, (H' i-ε*q' i)))-
      M*a*b*(mass S q-mass S q')^2 := by
    have hb' : b=1-a := by linarith
    rw [hb']
    ring
  rw [hid]
  exact sub_le_self _ (by positivity)

theorem perspective_cuts_mix {ι : Type*} [Fintype ι]
    (q q' H H' : ι → ℝ) (M r ε a b : ℝ)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (h : perspectiveCuts q H M r ε) (h' : perspectiveCuts q' H' M r ε) :
    perspectiveCuts (a • q+b • q') (a • H+b • H') M r ε := by
  intro S
  have hm := perspective_quadratic_mix S q q' H H' M r ε a b hM ha hb hab
  have h1 := mul_nonpos_of_nonneg_of_nonpos ha (h S)
  have h2 := mul_nonpos_of_nonneg_of_nonpos hb (h' S)
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using le_trans hm (by linarith)

theorem perspective_cut_system_convex {ι : Type*} [Fintype ι]
    (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {z : (ι → ℝ) × (ι → ℝ) | perspectiveCuts z.1 z.2 M r ε} := by
  intro z hz z' hz' a b ha hb hab
  exact perspective_cuts_mix z.1 z'.1 z.2 z'.2 M r ε a b hM ha hb hab hz hz'

theorem interval_moment_mix {ι α : Type*} [Fintype α]
    (p : α → ℝ) (V V' : ι → α → ℝ) (a b : ℝ) :
    intervalMomentScore p (a • V+b • V')=
      a • intervalMomentScore p V+b • intervalMomentScore p V' := by
  funext i
  unfold intervalMomentScore
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem interval_perspective_cut_system_convex {ι α : Type*} [Fintype ι] [Fintype α]
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {z : (ι → ℝ) × (ι → α → ℝ) |
      perspectiveCuts z.1 (intervalMomentScore p z.2) M r ε} := by
  intro z hz z' hz' a b ha hb hab
  change perspectiveCuts (a • z.1+b • z'.1)
    (intervalMomentScore p (a • z.2+b • z'.2)) M r ε
  rw [interval_moment_mix]
  exact perspective_cuts_mix z.1 z'.1 (intervalMomentScore p z.2)
    (intervalMomentScore p z'.2) M r ε a b hM ha hb hab hz hz'

def intervalPerspectiveSystem {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ)
    (z : (ι → ℝ) × (ι → α → ℝ) × (α → α → ℝ)) : Prop :=
  (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i)=r ∧
  (∀ i h, lo i h*z.1 i ≤ z.2.1 i h ∧ z.2.1 i h ≤ hi i h*z.1 i) ∧
  (∀ h, (∑ a, z.2.2 h a*p a)-(∑ i, z.2.1 i h) ≤ ε) ∧
  IsSkew z.2.2 ∧ (∀ h h', coreLo h h' ≤ z.2.2 h h' ∧ z.2.2 h h' ≤ coreHi h h') ∧
  (∀ i, score lo p i ≤ ε+M*r) ∧ perspectiveCuts z.1 (intervalMomentScore p z.2.1) M r ε

theorem interval_perspective_system_convex {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 ≤ M) :
    Convex ℝ {z | intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z} := by
  intro z hz z' hz' a b ha hb hab
  rcases hz with ⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩
  rcases hz' with ⟨hq',hr',hV',hA',hK',hC',_,hcuts'⟩
  change intervalPerspectiveSystem lo hi coreLo coreHi p M r ε
    (a • z.1+b • z'.1, a • z.2.1+b • z'.2.1, a • z.2.2+b • z'.2.2)
  refine ⟨?_,?_,?_,?_,?_,?_,hg,?_⟩
  · intro i
    change 0 ≤ a*z.1 i+b*z'.1 i
    exact add_nonneg (mul_nonneg ha (hq i)) (mul_nonneg hb (hq' i))
  · change (∑ i, (a*z.1 i+b*z'.1 i))=r
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hr,hr',←add_mul,hab,one_mul]
  · intro i h
    change lo i h*(a*z.1 i+b*z'.1 i) ≤ a*z.2.1 i h+b*z'.2.1 i h ∧
      a*z.2.1 i h+b*z'.2.1 i h ≤ hi i h*(a*z.1 i+b*z'.1 i)
    have h1 := mul_le_mul_of_nonneg_left (hV i h).1 ha
    have h2 := mul_le_mul_of_nonneg_left (hV' i h).1 hb
    have h3 := mul_le_mul_of_nonneg_left (hV i h).2 ha
    have h4 := mul_le_mul_of_nonneg_left (hV' i h).2 hb
    constructor <;> nlinarith
  · intro h
    change (∑ c, (a*z.2.2 h c+b*z'.2.2 h c)*p c)-(∑ i, (a*z.2.1 i h+b*z'.2.1 i h)) ≤ ε
    rw [finite_linear_mix]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hA h) ha
    have h2 := mul_le_mul_of_nonneg_left (hA' h) hb
    have he : a*ε+b*ε=ε := by rw [←add_mul,hab,one_mul]
    nlinarith
  · intro h h'
    change a*z.2.2 h h'+b*z'.2.2 h h'= -(a*z.2.2 h' h+b*z'.2.2 h' h)
    rw [hK h h',hK' h h']
    ring
  · intro h h'
    change coreLo h h' ≤ a*z.2.2 h h'+b*z'.2.2 h h' ∧
      a*z.2.2 h h'+b*z'.2.2 h h' ≤ coreHi h h'
    have h1 := mul_le_mul_of_nonneg_left (hC h h').1 ha
    have h2 := mul_le_mul_of_nonneg_left (hC' h h').1 hb
    have h3 := mul_le_mul_of_nonneg_left (hC h h').2 ha
    have h4 := mul_le_mul_of_nonneg_left (hC' h h').2 hb
    have hlo : a*coreLo h h'+b*coreLo h h'=coreLo h h' := by rw [←add_mul,hab,one_mul]
    have hhi : a*coreHi h h'+b*coreHi h h'=coreHi h h' := by rw [←add_mul,hab,one_mul]
    constructor <;> linarith
  · rw [interval_moment_mix]
    exact perspective_cuts_mix z.1 z'.1 (intervalMomentScore p z.2.1)
      (intervalMomentScore p z'.2.1) M r ε a b hM ha hb hab hcuts hcuts'

theorem variable_core_interval_completion_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h)
    (hpmass : (∑ h, p h)+r=1)
    (hclo : ∀ h h', -M ≤ coreLo h h') (hchi : ∀ h h', coreHi h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) :
    (∃ (q : ι → ℝ) (K : α → α → ℝ),
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧ IsSkew K ∧
      (∀ h h', coreLo h h' ≤ K h h' ∧ K h h' ≤ coreHi h h') ∧
      ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
        (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
        (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
        IsSkew (blockMatrix K D B) ∧
        (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
        ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ z, intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z := by
  constructor
  · rintro ⟨q,K,hq,hr,hK,hC,hgame⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    obtain ⟨V,hV,hA,hg,hcuts⟩ :=
      (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
        hK hKb hlo hhi hlu).mp hgame
    exact ⟨(q,V,K),hq,hr,hV,hA,hK,hC,hg,hcuts⟩
  · rintro ⟨⟨q,V,K⟩,hq,hr,hV,hA,hK,hC,hg,hcuts⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    refine ⟨q,K,hq,hr,hK,hC,?_⟩
    exact (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
      hK hKb hlo hhi hlu).mpr ⟨V,hV,hA,hg,hcuts⟩

theorem interval_system_repertoire_convex {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 ≤ M)
    (R : Set (ι → ℝ)) (hR : Convex ℝ R) :
    Convex ℝ {z | intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z ∧ z.1 ∈ R} := by
  intro z hz z' hz' a b ha hb hab
  exact ⟨interval_perspective_system_convex lo hi coreLo coreHi p M r ε hM
    hz.1 hz'.1 ha hb hab,hR hz.2 hz'.2 ha hb hab⟩

theorem residual_linear_repertoire_convex {ι κ : Type*} [Fintype ι]
    (F : κ → ι → ℝ) (b : κ → ℝ) :
    Convex ℝ {q : ι → ℝ | ∀ c, (∑ i, q i*F c i) ≤ b c} := by
  intro q hq q' hq' a d ha hd had c
  change (∑ i, (a*q i+d*q' i)*F c i) ≤ b c
  rw [finite_linear_mix]
  have h1 := mul_le_mul_of_nonneg_left (hq c) ha
  have h2 := mul_le_mul_of_nonneg_left (hq' c) hd
  have he : a*b c+d*b c=b c := by rw [←add_mul,had,one_mul]
  linarith

end
end SparseCompletion
