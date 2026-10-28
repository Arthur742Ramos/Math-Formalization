module
public import Conjugacy
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.Poisson
open ComputationalHodge.ResonanceObstruction

noncomputable def cosineN (n : ℕ) : Coefficient where
  toFun q := cosine (n • q)
  continuous_toFun := by fun_prop

noncomputable def sineN (n : ℕ) : Coefficient where
  toFun q := (AddCircle.toCircle (n • q) : ℂ).im
  continuous_toFun := by fun_prop

theorem cosineN_cover (n : ℕ) (x : ℝ) :
    cover (cosineN n) x = Real.cos (2 * Real.pi * ((n : ℝ) * x)) := by
  change cosine (n • (x : CircleHodge.Circle)) = _
  rw [← AddCircle.coe_nsmul]
  change cover cosine (n • x) = _
  rw [cosine_cover]
  simp only [nsmul_eq_mul]

theorem sineN_cover (n : ℕ) (x : ℝ) :
    cover (sineN n) x = Real.sin (2 * Real.pi * ((n : ℝ) * x)) := by
  change (AddCircle.toCircle (n • (x : CircleHodge.Circle)) : ℂ).im = _
  rw [← AddCircle.coe_nsmul]
  simp only [nsmul_eq_mul]
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  norm_num [Complex.exp_im]

noncomputable def cosineNC2 (n : ℕ) : C2Coefficient := ⟨cosineN n, by
  have h : cover (cosineN n) = fun x => Real.cos (2 * Real.pi * ((n : ℝ) * x)) := funext (cosineN_cover n)
  change ContDiff ℝ 2 (cover (cosineN n))
  rw [h]
  fun_prop⟩

noncomputable def sineNC2 (n : ℕ) : C2Coefficient := ⟨sineN n, by
  have h : cover (sineN n) = fun x => Real.sin (2 * Real.pi * ((n : ℝ) * x)) := funext (sineN_cover n)
  change ContDiff ℝ 2 (cover (sineN n))
  rw [h]
  fun_prop⟩

noncomputable def angular (n : ℕ) : ℝ := 2 * Real.pi * n
noncomputable def frequencyN (n : ℕ) : ℝ := angular n ^ 2

theorem cosineN_eigen (n : ℕ) : laplacian flatDensity (cosineNC2 n) = frequencyN n • cosineN n := by
  have he : cover (cosineN n) = fun x => Real.cos (angular n * x) := by
    funext x
    rw [cosineN_cover]
    congr 1
    unfold angular
    ring
  have h1 (x : ℝ) : HasDerivAt (cover (cosineN n)) (-(angular n) * Real.sin (angular n * x)) x := by
    rw [he]
    have h := (((hasDerivAt_id x).const_mul (angular n)).cos)
    simp only [id_eq, mul_one] at h
    convert h using 1; ring
  have h2 (x : ℝ) : HasDerivAt (fun t => -(angular n) * Real.sin (angular n * t))
      (-frequencyN n * Real.cos (angular n * x)) x := by
    have h := ((((hasDerivAt_id x).const_mul (angular n)).sin).const_mul (-(angular n)))
    simp only [id_eq, mul_one] at h
    convert h using 1; simp only [frequencyN]; ring
  have hd : deriv (cover (cosineN n)) = fun t => -(angular n) * Real.sin (angular n * t) :=
    funext fun x => (h1 x).deriv
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian flatDensity (cosineNC2 n)) x = frequencyN n * cover (cosineN n) x
  rw [laplacian_cover]
  change -(deriv (fun t => deriv (cover (cosineN n)) t / (1 : ℝ)) x) / 1 = _
  simp only [div_one]
  rw [hd, (h2 x).deriv, he]
  ring

theorem sineN_eigen (n : ℕ) : laplacian flatDensity (sineNC2 n) = frequencyN n • sineN n := by
  have he : cover (sineN n) = fun x => Real.sin (angular n * x) := by
    funext x
    rw [sineN_cover]
    congr 1
    unfold angular
    ring
  have h1 (x : ℝ) : HasDerivAt (cover (sineN n)) (angular n * Real.cos (angular n * x)) x := by
    rw [he]
    have h := (((hasDerivAt_id x).const_mul (angular n)).sin)
    simp only [id_eq, mul_one] at h
    convert h using 1; ring
  have h2 (x : ℝ) : HasDerivAt (fun t => angular n * Real.cos (angular n * t))
      (-frequencyN n * Real.sin (angular n * x)) x := by
    have h := ((((hasDerivAt_id x).const_mul (angular n)).cos).const_mul (angular n))
    simp only [id_eq, mul_one] at h
    convert h using 1; simp only [frequencyN]; ring
  have hd : deriv (cover (sineN n)) = fun t => angular n * Real.cos (angular n * t) :=
    funext fun x => (h1 x).deriv
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian flatDensity (sineNC2 n)) x = frequencyN n * cover (sineN n) x
  rw [laplacian_cover]
  change -(deriv (fun t => deriv (cover (sineN n)) t / (1 : ℝ)) x) / 1 = _
  simp only [div_one]
  rw [hd, (h2 x).deriv, he]
  ring
end ComputationalHodge.ArclengthSpectrum
