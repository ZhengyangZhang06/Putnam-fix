import Mathlib

open Filter Topology Metric MeasureTheory
open scoped Pointwise

noncomputable abbrev putnam_2021_a4_solution : ℝ := Real.pi * Real.log 2 / Real.sqrt 2

private noncomputable def putnam_2021_a4_F (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (1 / Real.sqrt 2 + ((p 0)^2 + (p 1)^2) / 2) /
    (1 + (p 0)^4 + (p 1)^4)

private noncomputable def putnam_2021_a4_Fc (z : ℂ) : ℝ :=
  (1 / Real.sqrt 2 + (z.re^2 + z.im^2) / 2) /
    (1 + z.re^4 + z.im^4)

private noncomputable def putnam_2021_a4_orig (z : ℂ) : ℝ :=
  (1 + 2 * z.re^2) / (1 + z.re^4 + 6 * z.re^2 * z.im^2 + z.im^4)
    - (1 + z.im^2) / (2 + z.re^4 + z.im^4)

private noncomputable def putnam_2021_a4_first (z : ℂ) : ℝ :=
  (1 + 2 * z.re^2) / (1 + z.re^4 + 6 * z.re^2 * z.im^2 + z.im^4)

private noncomputable def putnam_2021_a4_H (z : ℂ) : ℝ :=
  (1 + z.re^2 + z.im^2) / (1 + 2 * z.re^4 + 2 * z.im^4)

private noncomputable def putnam_2021_a4_X (z : ℂ) : ℝ :=
  (2 * z.re * z.im) / (1 + 2 * z.re^4 + 2 * z.im^4)

private noncomputable def putnam_2021_a4_K (z : ℂ) : ℝ :=
  (1 + (z.re^2 + z.im^2) / 2) / (2 + z.re^4 + z.im^4)

private noncomputable def putnam_2021_a4_second (z : ℂ) : ℝ :=
  (1 + z.im^2) / (2 + z.re^4 + z.im^4)

private noncomputable def putnam_2021_a4_second_swap (z : ℂ) : ℝ :=
  (1 + z.re^2) / (2 + z.re^4 + z.im^4)

private noncomputable def putnam_2021_a4_c : ℝ := Real.sqrt (Real.sqrt 2)

private noncomputable def putnam_2021_a4_scaledPolar (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  (R^2 * p.1 / Real.sqrt 2 + R^4 * p.1^3 / 2) /
    (1 + R^4 * p.1^4 * ((Real.cos p.2)^4 + (Real.sin p.2)^4))

private noncomputable def putnam_2021_a4_polar (p : ℝ × ℝ) : ℝ :=
  p.1 * (1 / Real.sqrt 2 + p.1^2 / 2) /
    (1 + p.1^4 * ((Real.cos p.2)^4 + (Real.sin p.2)^4))

private noncomputable def putnam_2021_a4_limitPolar (p : ℝ × ℝ) : ℝ :=
  1 / (2 * p.1 * ((Real.cos p.2)^4 + (Real.sin p.2)^4))

private noncomputable def putnam_2021_a4_boundPolar (p : ℝ × ℝ) : ℝ :=
  1 / (p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2)
    + 1 / (2 * p.1 * ((Real.cos p.2)^4 + (Real.sin p.2)^4))

private noncomputable def putnam_2021_a4_rot_circle : Circle :=
  ⟨(1 + Complex.I) / (Real.sqrt 2 : ℂ), by
    simp [Submonoid.unitSphere]
    have hnorm : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
      rw [← Complex.normSq_eq_norm_sq ((1 : ℂ) + Complex.I)]
      simp [Complex.normSq_apply]
      norm_num
    rw [hnorm]
    have hpos : 0 < Real.sqrt 2 := by positivity
    rw [abs_of_pos hpos]
    exact div_self hpos.ne'⟩

private noncomputable def putnam_2021_a4_rot_reflect : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (rotation putnam_2021_a4_rot_circle)

private noncomputable def putnam_2021_a4_I_circle : Circle :=
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

private noncomputable def putnam_2021_a4_swap : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (rotation putnam_2021_a4_I_circle)

private lemma putnam_2021_a4_rot_reflect_apply (z : ℂ) :
    putnam_2021_a4_rot_reflect z =
      ((z.re + z.im) / Real.sqrt 2) + ((z.re - z.im) / Real.sqrt 2) * Complex.I := by
  dsimp [putnam_2021_a4_rot_reflect, putnam_2021_a4_rot_circle]
  apply Complex.ext <;> simp [div_eq_mul_inv]
  · ring
  · ring

private lemma putnam_2021_a4_swap_apply (z : ℂ) :
    putnam_2021_a4_swap z = z.im + z.re * Complex.I := by
  dsimp [putnam_2021_a4_swap, putnam_2021_a4_I_circle]
  apply Complex.ext <;> simp

private lemma putnam_2021_a4_continuous_second :
    Continuous putnam_2021_a4_second := by
  change Continuous (fun z : ℂ => (1 + z.im^2) / (2 + z.re^4 + z.im^4))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]

private lemma putnam_2021_a4_continuous_first :
    Continuous putnam_2021_a4_first := by
  change Continuous
    (fun z : ℂ =>
      (1 + 2 * z.re^2) / (1 + z.re^4 + 6 * z.re^2 * z.im^2 + z.im^4))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    have h₁ : 0 ≤ z.re^4 := by positivity
    have h₂ : 0 ≤ 6 * z.re^2 * z.im^2 := by positivity
    have h₃ : 0 ≤ z.im^4 := by positivity
    nlinarith

private lemma putnam_2021_a4_continuous_second_swap :
    Continuous putnam_2021_a4_second_swap := by
  change Continuous (fun z : ℂ => (1 + z.re^2) / (2 + z.re^4 + z.im^4))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]

private lemma putnam_2021_a4_continuous_H :
    Continuous putnam_2021_a4_H := by
  change Continuous
    (fun z : ℂ => (1 + z.re^2 + z.im^2) / (1 + 2 * z.re^4 + 2 * z.im^4))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]

private lemma putnam_2021_a4_continuous_X :
    Continuous putnam_2021_a4_X := by
  change Continuous
    (fun z : ℂ => (2 * z.re * z.im) / (1 + 2 * z.re^4 + 2 * z.im^4))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]

private lemma putnam_2021_a4_integrableOn_ball_of_continuous
    {f : ℂ → ℝ} (hf : Continuous f) (R : ℝ) :
    IntegrableOn f (ball (0 : ℂ) R) := by
  exact (ContinuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) R) hf.continuousOn).mono_set ball_subset_closedBall

private lemma putnam_2021_a4_c_pos : 0 < putnam_2021_a4_c := by
  dsimp [putnam_2021_a4_c]
  positivity

private lemma putnam_2021_a4_c_sq :
    putnam_2021_a4_c^2 = Real.sqrt 2 := by
  dsimp [putnam_2021_a4_c]
  rw [Real.sq_sqrt]
  positivity

private lemma putnam_2021_a4_c_four :
    putnam_2021_a4_c^4 = (2 : ℝ) := by
  have h2 : (Real.sqrt 2)^2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  calc
    putnam_2021_a4_c^4 = (putnam_2021_a4_c^2)^2 := by ring
    _ = (Real.sqrt 2)^2 := by rw [putnam_2021_a4_c_sq]
    _ = 2 := h2

private lemma putnam_2021_a4_c_ne_zero : putnam_2021_a4_c ≠ 0 :=
  putnam_2021_a4_c_pos.ne'

private lemma putnam_2021_a4_one_lt_c : 1 < putnam_2021_a4_c := by
  by_contra h
  have hc_le : putnam_2021_a4_c ≤ 1 := le_of_not_gt h
  have hc4_le : putnam_2021_a4_c^4 ≤ (1 : ℝ)^4 := by
    exact pow_le_pow_left₀ putnam_2021_a4_c_pos.le hc_le 4
  rw [putnam_2021_a4_c_four] at hc4_le
  norm_num at hc4_le

private lemma putnam_2021_a4_inv_c_lt_c :
    putnam_2021_a4_c⁻¹ < putnam_2021_a4_c := by
  have hc1 := putnam_2021_a4_one_lt_c
  have hpos := putnam_2021_a4_c_pos
  nlinarith [inv_lt_one_of_one_lt₀ hc1, hpos]

private lemma putnam_2021_a4_inv_c_sq :
    (putnam_2021_a4_c⁻¹)^2 = 1 / Real.sqrt 2 := by
  rw [inv_pow, putnam_2021_a4_c_sq]
  ring

private lemma putnam_2021_a4_inv_c_four :
    (putnam_2021_a4_c⁻¹)^4 = (1 / 2 : ℝ) := by
  rw [inv_pow, putnam_2021_a4_c_four]
  norm_num

private lemma putnam_2021_a4_Fc_scale_big (z : ℂ) :
    putnam_2021_a4_c^2 * putnam_2021_a4_Fc (putnam_2021_a4_c • z)
      =
        (1 + z.re^2 + z.im^2) /
          (1 + 2 * z.re^4 + 2 * z.im^4) := by
  dsimp [putnam_2021_a4_Fc]
  simp
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hss : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    simpa [sq] using hs2
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  have hden : 1 + 2 * z.re^4 + 2 * z.im^4 ≠ 0 := by
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]
  have hden2 :
      1 + (putnam_2021_a4_c * z.re)^4 + (putnam_2021_a4_c * z.im)^4 ≠ 0 := by
    nlinarith [sq_nonneg ((putnam_2021_a4_c * z.re)^2),
      sq_nonneg ((putnam_2021_a4_c * z.im)^2)]
  field_simp [hsne, hden, hden2]
  rw [putnam_2021_a4_c_sq, putnam_2021_a4_c_four, hss]
  ring_nf

private lemma putnam_2021_a4_Fc_scale_small (z : ℂ) :
    (putnam_2021_a4_c⁻¹)^2 * putnam_2021_a4_Fc (putnam_2021_a4_c⁻¹ • z)
      =
        (1 + (z.re^2 + z.im^2) / 2) /
          (2 + z.re^4 + z.im^4) := by
  dsimp [putnam_2021_a4_Fc]
  simp
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  have hden : 2 + z.re^4 + z.im^4 ≠ 0 := by
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]
  have hden2 :
      1 + (putnam_2021_a4_c⁻¹ * z.re)^4 + (putnam_2021_a4_c⁻¹ * z.im)^4 ≠ 0 := by
    nlinarith [sq_nonneg ((putnam_2021_a4_c⁻¹ * z.re)^2),
      sq_nonneg ((putnam_2021_a4_c⁻¹ * z.im)^2)]
  field_simp [hsne, hden, hden2, putnam_2021_a4_c_ne_zero]
  rw [putnam_2021_a4_c_sq, putnam_2021_a4_c_four]
  field_simp [hden]

private lemma putnam_2021_a4_H_eq_scaled_Fc (z : ℂ) :
    putnam_2021_a4_H z =
      putnam_2021_a4_c^2 * putnam_2021_a4_Fc (putnam_2021_a4_c • z) := by
  rw [putnam_2021_a4_Fc_scale_big]
  rfl

private lemma putnam_2021_a4_K_eq_scaled_Fc (z : ℂ) :
    putnam_2021_a4_K z =
      (putnam_2021_a4_c⁻¹)^2 * putnam_2021_a4_Fc (putnam_2021_a4_c⁻¹ • z) := by
  rw [putnam_2021_a4_Fc_scale_small]
  rfl

private lemma putnam_2021_a4_X_conj (z : ℂ) :
    putnam_2021_a4_X (Complex.conjLIE z) = -putnam_2021_a4_X z := by
  dsimp [putnam_2021_a4_X]
  simp
  ring

private lemma putnam_2021_a4_integral_X_ball (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, putnam_2021_a4_X z) = 0 := by
  have hpre : (Complex.conjLIE ⁻¹' ball (0 : ℂ) R) = ball (0 : ℂ) R := by
    rw [Complex.conjLIE.preimage_ball]
    simp
  have hmp := LinearIsometryEquiv.measurePreserving Complex.conjLIE
  have h := hmp.setIntegral_preimage_emb
    Complex.conjLIE.toHomeomorph.measurableEmbedding putnam_2021_a4_X (ball (0 : ℂ) R)
  rw [hpre] at h
  have hcongr :
      (∫ z in ball (0 : ℂ) R, putnam_2021_a4_X (Complex.conjLIE z))
        = ∫ z in ball (0 : ℂ) R, -putnam_2021_a4_X z := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _hz
    exact putnam_2021_a4_X_conj z
  rw [hcongr, integral_neg] at h
  linarith

private lemma putnam_2021_a4_second_swap_apply (z : ℂ) :
    putnam_2021_a4_second (putnam_2021_a4_swap z)
      = putnam_2021_a4_second_swap z := by
  rw [putnam_2021_a4_swap_apply]
  dsimp [putnam_2021_a4_second, putnam_2021_a4_second_swap]
  simp [add_comm, add_left_comm]

private lemma putnam_2021_a4_K_avg (z : ℂ) :
    putnam_2021_a4_K z =
      (1 / 2) * (putnam_2021_a4_second z + putnam_2021_a4_second_swap z) := by
  dsimp [putnam_2021_a4_K, putnam_2021_a4_second, putnam_2021_a4_second_swap]
  have hden : 2 + z.re^4 + z.im^4 ≠ 0 := by
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]
  field_simp [hden]
  ring

private lemma putnam_2021_a4_integral_second_eq_K (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, putnam_2021_a4_second z)
      = ∫ z in ball (0 : ℂ) R, putnam_2021_a4_K z := by
  have hpre : (putnam_2021_a4_swap ⁻¹' ball (0 : ℂ) R) = ball (0 : ℂ) R := by
    rw [putnam_2021_a4_swap.preimage_ball]
    rw [map_zero]
  have hmp := LinearIsometryEquiv.measurePreserving putnam_2021_a4_swap
  have h := hmp.setIntegral_preimage_emb
    putnam_2021_a4_swap.toHomeomorph.measurableEmbedding
    putnam_2021_a4_second (ball (0 : ℂ) R)
  rw [hpre] at h
  have hcongr :
      (∫ z in ball (0 : ℂ) R, putnam_2021_a4_second (putnam_2021_a4_swap z))
        = ∫ z in ball (0 : ℂ) R, putnam_2021_a4_second_swap z := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _hz
    exact putnam_2021_a4_second_swap_apply z
  rw [hcongr] at h
  have hsym :
      (∫ z in ball (0 : ℂ) R, putnam_2021_a4_second_swap z)
        = ∫ z in ball (0 : ℂ) R, putnam_2021_a4_second z := h
  have hS : IntegrableOn putnam_2021_a4_second (ball (0 : ℂ) R) :=
    putnam_2021_a4_integrableOn_ball_of_continuous putnam_2021_a4_continuous_second R
  have hT : IntegrableOn putnam_2021_a4_second_swap (ball (0 : ℂ) R) :=
    putnam_2021_a4_integrableOn_ball_of_continuous putnam_2021_a4_continuous_second_swap R
  calc
    (∫ z in ball (0 : ℂ) R, putnam_2021_a4_second z)
        =
          (1 / 2) *
            ((∫ z in ball (0 : ℂ) R, putnam_2021_a4_second z)
              + (∫ z in ball (0 : ℂ) R, putnam_2021_a4_second_swap z)) := by
          rw [hsym]
          ring
    _ = (1 / 2) *
          (∫ z in ball (0 : ℂ) R,
            putnam_2021_a4_second z + putnam_2021_a4_second_swap z) := by
          rw [integral_add hS hT]
    _ = ∫ z in ball (0 : ℂ) R,
          (1 / 2) * (putnam_2021_a4_second z + putnam_2021_a4_second_swap z) := by
          rw [integral_const_mul]
    _ = ∫ z in ball (0 : ℂ) R, putnam_2021_a4_K z := by
          apply setIntegral_congr_fun measurableSet_ball
          intro z _hz
          rw [putnam_2021_a4_K_avg]

private lemma putnam_2021_a4_integral_H_scaled (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, putnam_2021_a4_H z)
      = ∫ z in ball (0 : ℂ) (putnam_2021_a4_c * R), putnam_2021_a4_Fc z := by
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure ℂ)) putnam_2021_a4_Fc
    (s := ball (0 : ℂ) R) putnam_2021_a4_c_pos
  rw [show (∫ z in ball (0 : ℂ) R, putnam_2021_a4_H z)
      = putnam_2021_a4_c^2 *
          ∫ z in ball (0 : ℂ) R, putnam_2021_a4_Fc (putnam_2021_a4_c • z) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro z _hz
    rw [putnam_2021_a4_H_eq_scaled_Fc]]
  rw [hscale]
  rw [Complex.finrank_real_complex]
  rw [show putnam_2021_a4_c • ball (0 : ℂ) R
      = ball (0 : ℂ) (putnam_2021_a4_c * R) by
    rw [_root_.smul_ball putnam_2021_a4_c_ne_zero (0 : ℂ) R]
    simp [Real.norm_of_nonneg putnam_2021_a4_c_pos.le]]
  rw [putnam_2021_a4_c_sq]
  simp [smul_eq_mul]

private lemma putnam_2021_a4_integral_K_scaled (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, putnam_2021_a4_K z)
      = ∫ z in ball (0 : ℂ) (putnam_2021_a4_c⁻¹ * R), putnam_2021_a4_Fc z := by
  have hinv_pos : 0 < putnam_2021_a4_c⁻¹ := inv_pos.mpr putnam_2021_a4_c_pos
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure ℂ)) putnam_2021_a4_Fc
    (s := ball (0 : ℂ) R) hinv_pos
  rw [show (∫ z in ball (0 : ℂ) R, putnam_2021_a4_K z)
      = (putnam_2021_a4_c⁻¹)^2 *
          ∫ z in ball (0 : ℂ) R, putnam_2021_a4_Fc (putnam_2021_a4_c⁻¹ • z) by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro z _hz
    rw [putnam_2021_a4_K_eq_scaled_Fc]]
  rw [hscale]
  rw [Complex.finrank_real_complex]
  rw [show putnam_2021_a4_c⁻¹ • ball (0 : ℂ) R
      = ball (0 : ℂ) (putnam_2021_a4_c⁻¹ * R) by
    rw [_root_.smul_ball (inv_ne_zero putnam_2021_a4_c_ne_zero) (0 : ℂ) R]
    simp [Real.norm_of_nonneg hinv_pos.le]]
  simp [smul_eq_mul, inv_pow]
  field_simp [putnam_2021_a4_c_ne_zero]

private lemma putnam_2021_a4_quartic_den_pos (x y : ℝ) :
    0 < 1 + x^4 + y^4 := by
  nlinarith [sq_nonneg (x^2), sq_nonneg (y^2)]

private lemma putnam_2021_a4_trig_quartic (θ : ℝ) :
    (Real.cos θ)^4 + (Real.sin θ)^4 = 1 - (Real.sin (2 * θ))^2 / 2 := by
  rw [Real.sin_two_mul]
  have h : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := by
    rw [Real.sin_sq_add_cos_sq]
  nlinarith [sq_nonneg ((Real.sin θ)^2 - (Real.cos θ)^2)]

private lemma putnam_2021_a4_trig_quartic_pos (θ : ℝ) :
    0 < (Real.cos θ)^4 + (Real.sin θ)^4 := by
  have hsum : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := by
    rw [Real.sin_sq_add_cos_sq]
  have hnonneg₁ : 0 ≤ (Real.cos θ)^4 := by positivity
  have hnonneg₂ : 0 ≤ (Real.sin θ)^4 := by positivity
  by_contra h
  have hle : (Real.cos θ)^4 + (Real.sin θ)^4 ≤ 0 := le_of_not_gt h
  have hcos4 : (Real.cos θ)^4 = 0 := le_antisymm (by nlinarith) hnonneg₁
  have hsin4 : (Real.sin θ)^4 = 0 := le_antisymm (by nlinarith) hnonneg₂
  have hcos2 : (Real.cos θ)^2 = 0 := by
    nlinarith [sq_nonneg ((Real.cos θ)^2), hcos4]
  have hsin2 : (Real.sin θ)^2 = 0 := by
    nlinarith [sq_nonneg ((Real.sin θ)^2), hsin4]
  nlinarith

private lemma putnam_2021_a4_trig_quartic_ge_half (θ : ℝ) :
    (1 / 2 : ℝ) ≤ (Real.cos θ)^4 + (Real.sin θ)^4 := by
  have hsum : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := by
    rw [Real.sin_sq_add_cos_sq]
  have hsq : 0 ≤ ((Real.cos θ)^2 - (Real.sin θ)^2)^2 := sq_nonneg _
  nlinarith

private lemma putnam_2021_a4_measurableSet_rect :
    MeasurableSet
      (Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
        Set.Ioo (-Real.pi) Real.pi) :=
  measurableSet_Ioo.prod measurableSet_Ioo

private lemma putnam_2021_a4_continuous_scaledPolar (R : ℝ) :
    Continuous (putnam_2021_a4_scaledPolar R) := by
  unfold putnam_2021_a4_scaledPolar
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    have hq : 0 < (Real.cos p.2)^4 + (Real.sin p.2)^4 :=
      putnam_2021_a4_trig_quartic_pos p.2
    have hnonneg : 0 ≤ R^4 * p.1^4 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) := by
      positivity
    nlinarith

private lemma putnam_2021_a4_continuous_limitPolar :
    ContinuousOn putnam_2021_a4_limitPolar
      (Set.Icc (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
        Set.Icc (-Real.pi) Real.pi) := by
  unfold putnam_2021_a4_limitPolar
  apply ContinuousOn.div
  · exact continuous_const.continuousOn
  · fun_prop
  · intro p hp
    have ht : 0 < p.1 := by
      exact lt_of_lt_of_le (inv_pos.mpr putnam_2021_a4_c_pos) hp.1.1
    have hq : 0 < (Real.cos p.2)^4 + (Real.sin p.2)^4 :=
      putnam_2021_a4_trig_quartic_pos p.2
    positivity

private lemma putnam_2021_a4_rational_decomp (x : ℝ) :
    (1 + x^2) / (1 + x^4)
      =
        (1 / 2) *
          (((x - 1 / Real.sqrt 2)^2 + (1 / Real.sqrt 2)^2)⁻¹
            + ((x + 1 / Real.sqrt 2)^2 + (1 / Real.sqrt 2)^2)⁻¹) := by
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hs4 : (Real.sqrt 2)^4 = (4 : ℝ) := by
    nlinarith [hs2]
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  have h₁ : (x - 1 / Real.sqrt 2)^2 + (1 / Real.sqrt 2)^2 ≠ 0 := by
    nlinarith [sq_nonneg (x - 1 / Real.sqrt 2), sq_pos_of_ne_zero (one_div_ne_zero hsne)]
  have h₂ : (x + 1 / Real.sqrt 2)^2 + (1 / Real.sqrt 2)^2 ≠ 0 := by
    nlinarith [sq_nonneg (x + 1 / Real.sqrt 2), sq_pos_of_ne_zero (one_div_ne_zero hsne)]
  have hden : 1 + x^4 ≠ 0 := by
    nlinarith [sq_nonneg (x^2)]
  field_simp [h₁, h₂, hden, hsne]
  all_goals
    have hs2' := hs2
    have hs4' := hs4
    ring_nf at *
    rw [hs2', hs4'] at *
    ring_nf at *
    try contradiction

private lemma putnam_2021_a4_cauchy_scaled_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, (x^2 + a^2)⁻¹) = Real.pi / a := by
  have hcomp := MeasureTheory.Measure.integral_comp_div
    (fun y : ℝ => (1 + y^2)⁻¹) a
  have hcomp' :
      (∫ x : ℝ, (1 + (x / a)^2)⁻¹) = a * Real.pi := by
    simpa [abs_of_pos ha, smul_eq_mul, integral_univ_inv_one_add_sq] using hcomp
  have hpoint : ∀ x : ℝ, (x^2 + a^2)⁻¹ = a⁻¹^2 * (1 + (x / a)^2)⁻¹ := by
    intro x
    field_simp [ha.ne']
    ring
  calc
    (∫ x : ℝ, (x^2 + a^2)⁻¹)
        = ∫ x : ℝ, a⁻¹^2 * (1 + (x / a)^2)⁻¹ := by
          apply MeasureTheory.integral_congr_ae
          exact Eventually.of_forall hpoint
    _ = a⁻¹^2 * (∫ x : ℝ, (1 + (x / a)^2)⁻¹) := by
          rw [MeasureTheory.integral_const_mul]
    _ = Real.pi / a := by
          rw [hcomp']
          field_simp [ha.ne']

private lemma putnam_2021_a4_cauchy_shifted_integral {a c : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, (((x - c)^2 + a^2)⁻¹)) = Real.pi / a := by
  have htrans := MeasureTheory.integral_add_right_eq_self
    (μ := volume) (fun y : ℝ => (y^2 + a^2)⁻¹) (-c)
  calc
    (∫ x : ℝ, (((x - c)^2 + a^2)⁻¹))
        = ∫ x : ℝ, ((x + -c)^2 + a^2)⁻¹ := by
          simp [sub_eq_add_neg]
    _ = ∫ x : ℝ, (x^2 + a^2)⁻¹ := by
          simpa using htrans
    _ = Real.pi / a := putnam_2021_a4_cauchy_scaled_integral ha

private lemma putnam_2021_a4_cauchy_shifted_integrable {a c : ℝ} (ha : a ≠ 0) :
    Integrable (fun x : ℝ => (((x - c)^2 + a^2)⁻¹)) := by
  let f : ℝ → ℝ := fun y => (1 + y^2)⁻¹
  have hf₁ : Integrable (fun x : ℝ => f (x * a⁻¹)) :=
    integrable_inv_one_add_sq.comp_mul_right' (inv_ne_zero ha)
  have hf₂ : Integrable (fun x : ℝ => f ((x + -c) * a⁻¹)) :=
    hf₁.comp_add_right (-c)
  have hf₃ : Integrable (fun x : ℝ => a⁻¹^2 * f ((x + -c) * a⁻¹)) :=
    hf₂.const_mul (a⁻¹^2)
  refine hf₃.congr (Eventually.of_forall ?_)
  intro x
  dsimp [f]
  field_simp [ha]
  ring

private lemma putnam_2021_a4_rational_integral :
    (∫ x : ℝ, (1 + x^2) / (1 + x^4)) = Real.pi * Real.sqrt 2 := by
  let a : ℝ := 1 / Real.sqrt 2
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hAint : Integrable (fun x : ℝ => (((x - a)^2 + a^2)⁻¹)) :=
    putnam_2021_a4_cauchy_shifted_integrable ha_pos.ne'
  have hBint : Integrable (fun x : ℝ => (((x - (-a))^2 + a^2)⁻¹)) :=
    putnam_2021_a4_cauchy_shifted_integrable ha_pos.ne'
  have hAval :
      (∫ x : ℝ, (((x - a)^2 + a^2)⁻¹)) = Real.pi / a :=
    putnam_2021_a4_cauchy_shifted_integral ha_pos
  have hBval :
      (∫ x : ℝ, (((x - (-a))^2 + a^2)⁻¹)) = Real.pi / a :=
    putnam_2021_a4_cauchy_shifted_integral ha_pos
  calc
    (∫ x : ℝ, (1 + x^2) / (1 + x^4))
        =
          ∫ x : ℝ, (1 / 2) *
            ((((x - a)^2 + a^2)⁻¹) + (((x - (-a))^2 + a^2)⁻¹)) := by
          apply integral_congr_ae
          refine Eventually.of_forall ?_
          intro x
          dsimp [a]
          simpa [sub_neg_eq_add] using putnam_2021_a4_rational_decomp x
    _ =
          (1 / 2) *
            (∫ x : ℝ, (((x - a)^2 + a^2)⁻¹) + (((x - (-a))^2 + a^2)⁻¹)) := by
          rw [integral_const_mul]
    _ =
          (1 / 2) *
            ((∫ x : ℝ, (((x - a)^2 + a^2)⁻¹))
              + (∫ x : ℝ, (((x - (-a))^2 + a^2)⁻¹))) := by
          rw [integral_add hAint hBint]
    _ = Real.pi * Real.sqrt 2 := by
          rw [hAval, hBval]
          dsimp [a]
          have hsne : Real.sqrt 2 ≠ 0 := by positivity
          field_simp [hsne]
          ring

private lemma putnam_2021_a4_tan_integrand (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    |1 / (Real.cos θ)^2| *
        ((1 + (Real.tan θ)^2) / (1 + (Real.tan θ)^4))
      =
        1 / ((Real.cos θ)^4 + (Real.sin θ)^4) := by
  have hcpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  have hc : Real.cos θ ≠ 0 := hcpos.ne'
  have hden : (Real.cos θ)^4 + (Real.sin θ)^4 ≠ 0 :=
    (putnam_2021_a4_trig_quartic_pos θ).ne'
  rw [abs_of_pos (div_pos zero_lt_one (sq_pos_of_ne_zero hc))]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc, hden]
  ring_nf
  rw [Real.cos_sq_add_sin_sq]

private lemma putnam_2021_a4_half_angular_integral :
    (∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
        1 / ((Real.cos θ)^4 + (Real.sin θ)^4))
      = Real.pi * Real.sqrt 2 := by
  let s : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hcv := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := s) (f := Real.tan) (f' := fun θ : ℝ => 1 / (Real.cos θ)^2)
    (F := ℝ) isOpen_Ioo.measurableSet
    (fun θ hθ => (Real.hasDerivAt_tan_of_mem_Ioo hθ).hasDerivWithinAt)
    Real.injOn_tan
    (fun t : ℝ => (1 + t^2) / (1 + t^4))
  have hright :
      (∫ θ in s,
          |1 / (Real.cos θ)^2| •
            ((1 + (Real.tan θ)^2) / (1 + (Real.tan θ)^4)))
        =
      (∫ θ in s, 1 / ((Real.cos θ)^4 + (Real.sin θ)^4)) := by
    apply MeasureTheory.setIntegral_congr_fun isOpen_Ioo.measurableSet
    intro θ hθ
    simpa [smul_eq_mul] using putnam_2021_a4_tan_integrand θ hθ
  have hleft :
      (∫ t in Real.tan '' s, (1 + t^2) / (1 + t^4))
        = (∫ t : ℝ, (1 + t^2) / (1 + t^4)) := by
    rw [show Real.tan '' s = Set.univ by
      dsimp [s]
      exact Real.image_tan_Ioo]
    simp
  rw [hleft, hright] at hcv
  exact hcv.symm.trans putnam_2021_a4_rational_integral

private lemma putnam_2021_a4_angular_integral :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        1 / ((Real.cos θ)^4 + (Real.sin θ)^4))
      = 2 * Real.pi * Real.sqrt 2 := by
  let g : ℝ → ℝ := fun θ => 1 / ((Real.cos θ)^4 + (Real.sin θ)^4)
  have hg_cont : Continuous g := by
    dsimp [g]
    apply continuous_const.div
    · fun_prop
    · intro θ
      exact (putnam_2021_a4_trig_quartic_pos θ).ne'
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hg_cont.intervalIntegrable a b
  have hhalf_interval :
      (∫ θ in -(Real.pi / 2)..(Real.pi / 2), g θ)
        = Real.pi * Real.sqrt 2 := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    dsimp [g]
    exact putnam_2021_a4_half_angular_integral
  have hper : Function.Periodic g Real.pi := by
    intro θ
    dsimp [g]
    rw [Real.cos_add_pi, Real.sin_add_pi]
    ring_nf
  have hleft :
      (∫ θ in -Real.pi..0, g θ)
        = ∫ θ in -(Real.pi / 2)..(Real.pi / 2), g θ := by
    have h := hper.intervalIntegral_add_eq (-Real.pi) (-(Real.pi / 2))
    have hπ : Real.pi + -(Real.pi / 2) = Real.pi / 2 := by ring
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul, hπ] using h
  have hright :
      (∫ θ in 0..Real.pi, g θ)
        = ∫ θ in -(Real.pi / 2)..(Real.pi / 2), g θ := by
    have h := hper.intervalIntegral_add_eq 0 (-(Real.pi / 2))
    have hπ : Real.pi + -(Real.pi / 2) = Real.pi / 2 := by ring
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul, hπ] using h
  have hfull_interval :
      (∫ θ in -Real.pi..Real.pi, g θ) = 2 * Real.pi * Real.sqrt 2 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hg_int (-Real.pi) 0) (hg_int 0 Real.pi)
    rw [← hadd, hleft, hright, hhalf_interval]
    ring
  rw [← hfull_interval]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

private lemma putnam_2021_a4_scaled_radial_pointwise {t q : ℝ} (ht : 0 < t) (hq : 0 < q) :
    Tendsto
      (fun R : ℝ =>
        (R^2 * t / Real.sqrt 2 + R^4 * t^3 / 2) /
          (1 + R^4 * t^4 * q))
      atTop (𝓝 (1 / (2 * t * q))) := by
  let transformed : ℝ → ℝ := fun R =>
    (((R⁻¹)^2 * t / Real.sqrt 2 + t^3 / 2) /
      ((R⁻¹)^4 + t^4 * q))
  have hRinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hR2 : Tendsto (fun R : ℝ => (R⁻¹)^2) atTop (𝓝 0) := by
    simpa using hRinv.pow 2
  have hR4 : Tendsto (fun R : ℝ => (R⁻¹)^4) atTop (𝓝 0) := by
    simpa using hRinv.pow 4
  have hnum :
      Tendsto (fun R : ℝ => (R⁻¹)^2 * t / Real.sqrt 2 + t^3 / 2)
        atTop (𝓝 (t^3 / 2)) := by
    simpa using (((hR2.mul_const t).div_const (Real.sqrt 2)).add tendsto_const_nhds)
  have hden :
      Tendsto (fun R : ℝ => (R⁻¹)^4 + t^4 * q)
        atTop (𝓝 (t^4 * q)) := by
    simpa using hR4.add_const (t^4 * q)
  have hden_ne : t^4 * q ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 4 ht.ne') hq.ne'
  have hlim :
      Tendsto transformed atTop (𝓝 ((t^3 / 2) / (t^4 * q))) := by
    simpa [transformed] using hnum.div hden hden_ne
  have hconst : (t^3 / 2) / (t^4 * q) = 1 / (2 * t * q) := by
    field_simp [ht.ne', hq.ne']
  have heq : (fun R : ℝ =>
        (R^2 * t / Real.sqrt 2 + R^4 * t^3 / 2) /
          (1 + R^4 * t^4 * q)) =ᶠ[atTop] transformed := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
    dsimp [transformed]
    have hden₁ : 1 + R^4 * t^4 * q ≠ 0 := by
      have hnonneg : 0 ≤ R^4 * t^4 * q := by positivity
      nlinarith
    have hden₂ : (R⁻¹)^4 + t^4 * q ≠ 0 := by
      have hpos : 0 < t^4 * q := mul_pos (pow_pos ht 4) hq
      have hnonneg : 0 ≤ (R⁻¹)^4 := by positivity
      nlinarith
    field_simp [hR, hden₁, hden₂]
  have hlim' : Tendsto transformed atTop (𝓝 (1 / (2 * t * q))) := by
    simpa [hconst] using hlim
  exact hlim'.congr' heq.symm

private lemma putnam_2021_a4_scaledPolar_pointwise
    {p : ℝ × ℝ}
    (hp : p ∈ Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
      Set.Ioo (-Real.pi) Real.pi) :
    Tendsto (fun R : ℝ => putnam_2021_a4_scaledPolar R p) atTop
      (𝓝 (putnam_2021_a4_limitPolar p)) := by
  have ht : 0 < p.1 := by
    exact lt_trans (inv_pos.mpr putnam_2021_a4_c_pos) hp.1.1
  have hq : 0 < (Real.cos p.2)^4 + (Real.sin p.2)^4 :=
    putnam_2021_a4_trig_quartic_pos p.2
  simpa [putnam_2021_a4_scaledPolar, putnam_2021_a4_limitPolar] using
    putnam_2021_a4_scaled_radial_pointwise (t := p.1)
      (q := (Real.cos p.2)^4 + (Real.sin p.2)^4) ht hq

private lemma putnam_2021_a4_scaled_bound_aux {R t q : ℝ}
    (hR : 1 ≤ R) (ht : 0 < t) (hq : 0 < q) :
    |(R^2 * t / Real.sqrt 2 + R^4 * t^3 / 2) /
        (1 + R^4 * t^4 * q)|
      ≤ 1 / (R^2 * t^3 * q * Real.sqrt 2) + 1 / (2 * t * q) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsqrt_pos : 0 < Real.sqrt 2 := by positivity
  have hden_base_pos : 0 < R^4 * t^4 * q := by positivity
  have hden_pos : 0 < 1 + R^4 * t^4 * q := by positivity
  have hnum₁_nonneg : 0 ≤ R^2 * t / Real.sqrt 2 := by positivity
  have hnum₂_nonneg : 0 ≤ R^4 * t^3 / 2 := by positivity
  have hnonneg :
      0 ≤ (R^2 * t / Real.sqrt 2 + R^4 * t^3 / 2) /
        (1 + R^4 * t^4 * q) := by
    exact div_nonneg (add_nonneg hnum₁_nonneg hnum₂_nonneg) hden_pos.le
  rw [abs_of_nonneg hnonneg]
  calc
    (R^2 * t / Real.sqrt 2 + R^4 * t^3 / 2) /
        (1 + R^4 * t^4 * q)
        = (R^2 * t / Real.sqrt 2) / (1 + R^4 * t^4 * q)
            + (R^4 * t^3 / 2) / (1 + R^4 * t^4 * q) := by
          rw [add_div]
    _ ≤ (R^2 * t / Real.sqrt 2) / (R^4 * t^4 * q)
            + (R^4 * t^3 / 2) / (R^4 * t^4 * q) := by
          apply add_le_add
          · exact div_le_div₀ hnum₁_nonneg
              (le_refl _)
              hden_base_pos
              (by nlinarith)
          · exact div_le_div₀ hnum₂_nonneg
              (le_refl _)
              hden_base_pos
              (by nlinarith)
    _ = 1 / (R^2 * t^3 * q * Real.sqrt 2) + 1 / (2 * t * q) := by
          field_simp [hRpos.ne', ht.ne', hq.ne']

private lemma putnam_2021_a4_scaledPolar_bound
    {R : ℝ} (hR : 1 ≤ R) {p : ℝ × ℝ}
    (hp : p ∈ Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
      Set.Ioo (-Real.pi) Real.pi) :
    ‖putnam_2021_a4_scaledPolar R p‖ ≤ putnam_2021_a4_boundPolar p := by
  have ht : 0 < p.1 := by
    exact lt_trans (inv_pos.mpr putnam_2021_a4_c_pos) hp.1.1
  have hq : 0 < (Real.cos p.2)^4 + (Real.sin p.2)^4 :=
    putnam_2021_a4_trig_quartic_pos p.2
  have haux := putnam_2021_a4_scaled_bound_aux (R := R) (t := p.1)
    (q := (Real.cos p.2)^4 + (Real.sin p.2)^4) hR ht hq
  rw [Real.norm_eq_abs]
  refine haux.trans ?_
  dsimp [putnam_2021_a4_boundPolar]
  apply add_le_add
  · have hden_pos :
        0 < p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2 := by
      positivity
    have hden_le :
        p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2
          ≤ R^2 * p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2 := by
      have hR2 : 1 ≤ R^2 := by nlinarith [sq_nonneg (R - 1)]
      nlinarith [hden_pos.le, hR2]
    exact one_div_le_one_div_of_le hden_pos hden_le
  · rfl

private lemma putnam_2021_a4_scaledPolar_const_bound
    {R : ℝ} (hR : 1 ≤ R) {p : ℝ × ℝ}
    (hp : p ∈ Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
      Set.Ioo (-Real.pi) Real.pi) :
    ‖putnam_2021_a4_scaledPolar R p‖
      ≤ 4 * putnam_2021_a4_c^3 + 2 * putnam_2021_a4_c := by
  have hbound := putnam_2021_a4_scaledPolar_bound hR hp
  refine hbound.trans ?_
  dsimp [putnam_2021_a4_boundPolar]
  have ht : 0 < p.1 := by
    exact lt_trans (inv_pos.mpr putnam_2021_a4_c_pos) hp.1.1
  have hqhalf : (1 / 2 : ℝ) ≤ (Real.cos p.2)^4 + (Real.sin p.2)^4 :=
    putnam_2021_a4_trig_quartic_ge_half p.2
  have hqpos : 0 < (Real.cos p.2)^4 + (Real.sin p.2)^4 :=
    putnam_2021_a4_trig_quartic_pos p.2
  have hsqrt_pos : 0 < Real.sqrt 2 := by positivity
  have ht_lower : putnam_2021_a4_c⁻¹ ≤ p.1 := hp.1.1.le
  have ht3_lower : putnam_2021_a4_c⁻¹^3 ≤ p.1^3 := by
    exact pow_le_pow_left₀ (inv_pos.mpr putnam_2021_a4_c_pos).le ht_lower 3
  have hden1_pos : 0 < p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2 := by
    positivity
  have hden1_lower :
      putnam_2021_a4_c⁻¹^3 * (1 / 2) * 1
        ≤ p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2 := by
    have hsqrt_one : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        sq_nonneg (Real.sqrt 2 - 1), Real.sqrt_nonneg (2 : ℝ)]
    have hcinv3_nonneg : 0 ≤ putnam_2021_a4_c⁻¹^3 :=
      (pow_nonneg (inv_pos.mpr putnam_2021_a4_c_pos).le 3)
    have hp13_nonneg : 0 ≤ p.1^3 := by positivity
    have hmul :
        putnam_2021_a4_c⁻¹^3 * (1 / 2)
          ≤ p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) := by
      exact mul_le_mul ht3_lower hqhalf (by norm_num) hp13_nonneg
    have hmul' :
        putnam_2021_a4_c⁻¹^3 * (1 / 2) * 1
          ≤ p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * 1 := by
      simpa using mul_le_mul_of_nonneg_left (a := (1 : ℝ)) hmul zero_le_one
    exact hmul'.trans (by
      exact mul_le_mul_of_nonneg_left hsqrt_one (by positivity))
  have hterm1 :
      1 / (p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2)
        ≤ 2 * putnam_2021_a4_c^3 := by
    have hbase_pos : 0 < putnam_2021_a4_c⁻¹^3 * (1 / 2) * 1 := by
      have hcinv3_pos : 0 < putnam_2021_a4_c⁻¹^3 :=
        pow_pos (inv_pos.mpr putnam_2021_a4_c_pos) 3
      positivity
    have hle := one_div_le_one_div_of_le hbase_pos hden1_lower
    refine hle.trans_eq ?_
    rw [show 1 / (putnam_2021_a4_c⁻¹^3 * (1 / 2) * 1)
        = 2 * putnam_2021_a4_c^3 by
      field_simp [putnam_2021_a4_c_ne_zero]
      ]
  have hden2_pos : 0 < 2 * p.1 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) := by
    positivity
  have hden2_lower :
      putnam_2021_a4_c⁻¹
        ≤ 2 * p.1 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) := by
    nlinarith [ht_lower, hqhalf, ht.le]
  have hterm2 :
      1 / (2 * p.1 * ((Real.cos p.2)^4 + (Real.sin p.2)^4))
        ≤ putnam_2021_a4_c := by
    have hbase_pos : 0 < putnam_2021_a4_c⁻¹ := inv_pos.mpr putnam_2021_a4_c_pos
    have hle := one_div_le_one_div_of_le hbase_pos hden2_lower
    refine hle.trans_eq ?_
    field_simp [putnam_2021_a4_c_ne_zero]
  calc
    1 / (p.1^3 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) * Real.sqrt 2)
          + 1 / (2 * p.1 * ((Real.cos p.2)^4 + (Real.sin p.2)^4))
        ≤ 2 * putnam_2021_a4_c^3 + putnam_2021_a4_c := by
          exact add_le_add hterm1 hterm2
    _ ≤ 4 * putnam_2021_a4_c^3 + 2 * putnam_2021_a4_c := by
          nlinarith [putnam_2021_a4_c_pos, sq_nonneg putnam_2021_a4_c,
            sq_nonneg (putnam_2021_a4_c^2)]

private lemma putnam_2021_a4_rect_measure_ne_top :
    volume
        (Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
          Set.Ioo (-Real.pi) Real.pi) ≠ ⊤ := by
  let closedRect : Set (ℝ × ℝ) :=
    Set.Icc (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
      Set.Icc (-Real.pi) Real.pi
  have hcompact : IsCompact closedRect := isCompact_Icc.prod isCompact_Icc
  have hsubset :
      Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
          Set.Ioo (-Real.pi) Real.pi ⊆ closedRect := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  exact measure_ne_top_of_subset hsubset hcompact.measure_ne_top

private lemma putnam_2021_a4_scaled_integral_limit :
    Tendsto
      (fun R : ℝ =>
        ∫ p in Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
            Set.Ioo (-Real.pi) Real.pi,
          putnam_2021_a4_scaledPolar R p)
      atTop
      (𝓝 (∫ p in Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
            Set.Ioo (-Real.pi) Real.pi,
          putnam_2021_a4_limitPolar p)) := by
  let rect : Set (ℝ × ℝ) :=
    Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
      Set.Ioo (-Real.pi) Real.pi
  let M : ℝ := 4 * putnam_2021_a4_c^3 + 2 * putnam_2021_a4_c
  have hrect_meas : MeasurableSet rect := putnam_2021_a4_measurableSet_rect
  have hM_int : Integrable (fun _ : ℝ × ℝ => M) (volume.restrict rect) := by
    exact integrableOn_const (μ := volume) (s := rect) (C := M)
      putnam_2021_a4_rect_measure_ne_top
  have hmeas :
      ∀ᶠ R : ℝ in atTop,
        AEStronglyMeasurable (putnam_2021_a4_scaledPolar R) (volume.restrict rect) := by
    filter_upwards with R
    exact (putnam_2021_a4_continuous_scaledPolar R).aestronglyMeasurable
  have hbound :
      ∀ᶠ R : ℝ in atTop,
        ∀ᵐ p ∂volume.restrict rect,
          ‖putnam_2021_a4_scaledPolar R p‖ ≤ (fun _ : ℝ × ℝ => M) p := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards [ae_restrict_mem hrect_meas] with p hp
    exact putnam_2021_a4_scaledPolar_const_bound hR hp
  have hlim :
      ∀ᵐ p ∂volume.restrict rect,
        Tendsto (fun R : ℝ => putnam_2021_a4_scaledPolar R p) atTop
          (𝓝 (putnam_2021_a4_limitPolar p)) := by
    filter_upwards [ae_restrict_mem hrect_meas] with p hp
    exact putnam_2021_a4_scaledPolar_pointwise hp
  simpa [rect] using
    (tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict rect)
      (F := fun R : ℝ => putnam_2021_a4_scaledPolar R)
      (f := putnam_2021_a4_limitPolar)
      (bound := fun _ : ℝ × ℝ => M)
      hmeas hbound hM_int hlim)

private lemma putnam_2021_a4_radial_limit_integral :
    (∫ t in Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c,
        1 / (2 * t)) = Real.log 2 / 4 := by
  let a : ℝ := putnam_2021_a4_c⁻¹
  let b : ℝ := putnam_2021_a4_c
  have ha_pos : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr putnam_2021_a4_c_pos
  have hab : a ≤ b := by
    dsimp [a, b]
    exact putnam_2021_a4_inv_c_lt_c.le
  have hderiv :
      ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ => Real.log y / 2) (1 / (2 * x)) x := by
    intro x hx
    have hxpos : 0 < x := by
      have hxIcc : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hx
      have hax : a ≤ x := hxIcc.1
      exact lt_of_lt_of_le ha_pos hax
    have h := (Real.hasDerivAt_log hxpos.ne').const_mul (1 / 2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (2 * x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuous_const.continuousOn
    · fun_prop
    · intro x hx
      have hxpos : 0 < x := by
        have hxIcc : x ∈ Set.Icc a b := by
          simpa [Set.uIcc_of_le hab] using hx
        have hax : a ≤ x := hxIcc.1
        exact lt_of_lt_of_le ha_pos hax
      positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hlogc : Real.log putnam_2021_a4_c = Real.log 2 / 4 := by
    have hpow := congrArg Real.log putnam_2021_a4_c_four
    rw [Real.log_pow] at hpow
    norm_num at hpow
    linarith
  have hinterval :
      (∫ t in a..b, 1 / (2 * t)) = Real.log 2 / 4 := by
    rw [hFTC]
    dsimp [a, b]
    rw [Real.log_inv, hlogc]
    ring
  rw [← hinterval]
  rw [intervalIntegral.integral_of_le hab]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

private lemma putnam_2021_a4_limitPolar_integral :
    (∫ p in Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
        Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_limitPolar p)
      = Real.pi * Real.log 2 / Real.sqrt 2 := by
  let s : Set ℝ := Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c
  let t : Set ℝ := Set.Ioo (-Real.pi) Real.pi
  have hsep :
      (∫ p in s ×ˢ t, putnam_2021_a4_limitPolar p)
        =
      ∫ p in s ×ˢ t,
        (1 / (2 * p.1)) *
          (1 / ((Real.cos p.2)^4 + (Real.sin p.2)^4)) := by
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    dsimp [putnam_2021_a4_limitPolar]
    field_simp [putnam_2021_a4_trig_quartic_pos p.2 |>.ne']
  rw [show Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
        Set.Ioo (-Real.pi) Real.pi = s ×ˢ t by rfl]
  rw [hsep]
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod_mul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun x : ℝ => 1 / (2 * x))
    (g := fun y : ℝ => 1 / ((Real.cos y)^4 + (Real.sin y)^4))
    (s := s) (t := t)]
  rw [show (∫ x in s, 1 / (2 * x)) = Real.log 2 / 4 by
    dsimp [s]
    exact putnam_2021_a4_radial_limit_integral]
  rw [show (∫ y in t, 1 / ((Real.cos y)^4 + (Real.sin y)^4))
      = 2 * Real.pi * Real.sqrt 2 by
    dsimp [t]
    exact putnam_2021_a4_angular_integral]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private lemma putnam_2021_a4_scaled_integral_limit_value :
    Tendsto
      (fun R : ℝ =>
        ∫ p in Set.Ioo (putnam_2021_a4_c⁻¹) putnam_2021_a4_c ×ˢ
            Set.Ioo (-Real.pi) Real.pi,
          putnam_2021_a4_scaledPolar R p)
      atTop
      (𝓝 (Real.pi * Real.log 2 / Real.sqrt 2)) := by
  simpa [putnam_2021_a4_limitPolar_integral] using
    putnam_2021_a4_scaled_integral_limit

private lemma putnam_2021_a4_rotate_quartic (u v : ℝ) :
    ((u + v) / Real.sqrt 2)^4
      + 6 * ((u + v) / Real.sqrt 2)^2 * ((u - v) / Real.sqrt 2)^2
      + ((u - v) / Real.sqrt 2)^4 = 2 * (u^4 + v^4) := by
  have hsq : (Real.sqrt 2)^2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hs4 : (Real.sqrt 2)^4 = (4 : ℝ) := by
    nlinarith [hsq]
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsne]
  rw [hs4]
  ring

private lemma putnam_2021_a4_rotate_num (u v : ℝ) :
    1 + 2 * ((u + v) / Real.sqrt 2)^2 = 1 + u^2 + v^2 + 2 * u * v := by
  have hsq : (Real.sqrt 2)^2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsne]
  rw [hsq]
  ring

private lemma putnam_2021_a4_first_rot_reflect (z : ℂ) :
    (1 + 2 * (putnam_2021_a4_rot_reflect z).re^2) /
        (1 + (putnam_2021_a4_rot_reflect z).re^4
          + 6 * (putnam_2021_a4_rot_reflect z).re^2
              * (putnam_2021_a4_rot_reflect z).im^2
          + (putnam_2021_a4_rot_reflect z).im^4)
      =
        (1 + z.re^2 + z.im^2 + 2 * z.re * z.im) /
          (1 + 2 * z.re^4 + 2 * z.im^4) := by
  rw [putnam_2021_a4_rot_reflect_apply]
  simp
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hs4 : (Real.sqrt 2)^4 = (4 : ℝ) := by
    nlinarith [hs2]
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  have hden1 :
      1 + ((z.re + z.im) / Real.sqrt 2)^4
          + 6 * ((z.re + z.im) / Real.sqrt 2)^2
              * ((z.re - z.im) / Real.sqrt 2)^2
          + ((z.re - z.im) / Real.sqrt 2)^4 ≠ 0 := by
    have hpos :
        0 < 1 + ((z.re + z.im) / Real.sqrt 2)^4
            + 6 * ((z.re + z.im) / Real.sqrt 2)^2
                * ((z.re - z.im) / Real.sqrt 2)^2
            + ((z.re - z.im) / Real.sqrt 2)^4 := by
      nlinarith [sq_nonneg (((z.re + z.im) / Real.sqrt 2)^2),
        sq_nonneg (((z.re - z.im) / Real.sqrt 2)^2),
        sq_nonneg (((z.re + z.im) / Real.sqrt 2)
          * ((z.re - z.im) / Real.sqrt 2))]
    exact hpos.ne'
  have hden2 : 1 + 2 * z.re^4 + 2 * z.im^4 ≠ 0 := by
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]
  field_simp [hsne, hden1, hden2]
  rw [hs2, hs4]
  ring

private lemma putnam_2021_a4_first_rot_reflect_decomp (z : ℂ) :
    (1 + 2 * (putnam_2021_a4_rot_reflect z).re^2) /
        (1 + (putnam_2021_a4_rot_reflect z).re^4
          + 6 * (putnam_2021_a4_rot_reflect z).re^2
              * (putnam_2021_a4_rot_reflect z).im^2
          + (putnam_2021_a4_rot_reflect z).im^4)
      =
        putnam_2021_a4_H z + putnam_2021_a4_X z := by
  rw [putnam_2021_a4_first_rot_reflect]
  dsimp [putnam_2021_a4_H, putnam_2021_a4_X]
  have hden : 1 + 2 * z.re^4 + 2 * z.im^4 ≠ 0 := by
    nlinarith [sq_nonneg (z.re^2), sq_nonneg (z.im^2)]
  field_simp [hden]

private lemma putnam_2021_a4_first_rot_reflect_decomp' (z : ℂ) :
    putnam_2021_a4_first (putnam_2021_a4_rot_reflect z)
      = putnam_2021_a4_H z + putnam_2021_a4_X z := by
  exact putnam_2021_a4_first_rot_reflect_decomp z

private lemma putnam_2021_a4_integral_first_eq_H (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, putnam_2021_a4_first z)
      = ∫ z in ball (0 : ℂ) R, putnam_2021_a4_H z := by
  have hpre : (putnam_2021_a4_rot_reflect ⁻¹' ball (0 : ℂ) R) = ball (0 : ℂ) R := by
    rw [putnam_2021_a4_rot_reflect.preimage_ball]
    rw [map_zero]
  have hmp := LinearIsometryEquiv.measurePreserving putnam_2021_a4_rot_reflect
  have h := hmp.setIntegral_preimage_emb
    putnam_2021_a4_rot_reflect.toHomeomorph.measurableEmbedding
    putnam_2021_a4_first (ball (0 : ℂ) R)
  rw [hpre] at h
  have hcongr :
      (∫ z in ball (0 : ℂ) R,
          putnam_2021_a4_first (putnam_2021_a4_rot_reflect z))
        =
      ∫ z in ball (0 : ℂ) R, putnam_2021_a4_H z + putnam_2021_a4_X z := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _hz
    exact putnam_2021_a4_first_rot_reflect_decomp' z
  rw [hcongr] at h
  have hH : IntegrableOn putnam_2021_a4_H (ball (0 : ℂ) R) :=
    putnam_2021_a4_integrableOn_ball_of_continuous putnam_2021_a4_continuous_H R
  have hX : IntegrableOn putnam_2021_a4_X (ball (0 : ℂ) R) :=
    putnam_2021_a4_integrableOn_ball_of_continuous putnam_2021_a4_continuous_X R
  rw [integral_add hH hX, putnam_2021_a4_integral_X_ball R, add_zero] at h
  exact h.symm

private lemma putnam_2021_a4_complex_finite_identity (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, putnam_2021_a4_orig z)
      =
        (∫ z in ball (0 : ℂ) (putnam_2021_a4_c * R), putnam_2021_a4_Fc z)
          - ∫ z in ball (0 : ℂ) (putnam_2021_a4_c⁻¹ * R), putnam_2021_a4_Fc z := by
  have hfirst : IntegrableOn putnam_2021_a4_first (ball (0 : ℂ) R) :=
    putnam_2021_a4_integrableOn_ball_of_continuous putnam_2021_a4_continuous_first R
  have hsecond : IntegrableOn putnam_2021_a4_second (ball (0 : ℂ) R) :=
    putnam_2021_a4_integrableOn_ball_of_continuous putnam_2021_a4_continuous_second R
  rw [show (∫ z in ball (0 : ℂ) R, putnam_2021_a4_orig z)
      = ∫ z in ball (0 : ℂ) R,
          putnam_2021_a4_first z - putnam_2021_a4_second z by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _hz
    rfl]
  rw [integral_sub hfirst hsecond]
  rw [putnam_2021_a4_integral_first_eq_H R]
  rw [putnam_2021_a4_integral_second_eq_K R]
  rw [putnam_2021_a4_integral_H_scaled R]
  rw [putnam_2021_a4_integral_K_scaled R]

private lemma putnam_2021_a4_continuous_Fc :
    Continuous putnam_2021_a4_Fc := by
  change Continuous
    (fun z : ℂ =>
      (1 / Real.sqrt 2 + (z.re^2 + z.im^2) / 2) /
        (1 + z.re^4 + z.im^4))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact (putnam_2021_a4_quartic_den_pos z.re z.im).ne'

private lemma putnam_2021_a4_euclidean_integral_eq_complex (R : ℝ) :
    (∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) R,
      (1 + 2*(p 0)^2)/(1 + (p 0)^4 + 6*(p 0)^2*(p 1)^2 + (p 1)^4)
        - (1 + (p 1)^2)/(2 + (p 0)^4 + (p 1)^4))
    = ∫ z in ball (0 : ℂ) R, putnam_2021_a4_orig z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
    Complex.orthonormalBasisOneI.repr.symm
  have hpre : (e ⁻¹' ball (0 : ℂ) R) = ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    rw [e.preimage_ball]
    simp [e]
  have hmp : MeasurePreserving e :=
    Complex.orthonormalBasisOneI.measurePreserving_repr_symm
  have h := hmp.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    putnam_2021_a4_orig (ball (0 : ℂ) R)
  rw [hpre] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_ball
  intro p _
  dsimp [putnam_2021_a4_orig, e]
  simp

private lemma putnam_2021_a4_Fc_polar (r θ : ℝ) :
    putnam_2021_a4_Fc (Complex.polarCoord.symm (r, θ))
      =
        (1 / Real.sqrt 2 + r^2 / 2) /
          (1 + r^4 * ((Real.cos θ)^4 + (Real.sin θ)^4)) := by
  rw [Complex.polarCoord_symm_apply]
  dsimp [putnam_2021_a4_Fc]
  simp [mul_add]
  have hnum :
      (r * Real.cos θ)^2 + (r * Real.sin θ)^2 = r^2 := by
    have htrig : (Real.cos θ)^2 + (Real.sin θ)^2 = 1 := by
      rw [Real.cos_sq_add_sin_sq]
    nlinarith
  rw [hnum]
  ring_nf

private lemma putnam_2021_a4_scaledPolar_eq (R t θ : ℝ) :
    R * putnam_2021_a4_polar (R * t, θ)
      = putnam_2021_a4_scaledPolar R (t, θ) := by
  dsimp [putnam_2021_a4_polar, putnam_2021_a4_scaledPolar]
  ring_nf

private lemma putnam_2021_a4_continuous_polar :
    Continuous putnam_2021_a4_polar := by
  unfold putnam_2021_a4_polar
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    have hq : 0 < (Real.cos p.2)^4 + (Real.sin p.2)^4 :=
      putnam_2021_a4_trig_quartic_pos p.2
    have hnonneg : 0 ≤ p.1^4 * ((Real.cos p.2)^4 + (Real.sin p.2)^4) := by
      positivity
    nlinarith

private lemma putnam_2021_a4_integrableOn_Ioo_prod_of_continuous
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) {a b u v : ℝ} :
    IntegrableOn f (Set.Ioo a b ×ˢ Set.Ioo u v)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let closedRect : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc u v
  have hcompact : IsCompact closedRect := isCompact_Icc.prod isCompact_Icc
  have hsubset : Set.Ioo a b ×ˢ Set.Ioo u v ⊆ closedRect := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  exact (ContinuousOn.integrableOn_compact (μ := (volume : Measure ℝ).prod volume)
    hcompact hf.continuousOn).mono_set hsubset

private lemma putnam_2021_a4_polar_annulus
    {a b : ℝ} (ha : 0 < a) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Set.Ioo a b}, putnam_2021_a4_Fc z)
      =
    ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_polar p := by
  let ann : Set ℂ := {z : ℂ | ‖z‖ ∈ Set.Ioo a b}
  let rect : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi
  let g : ℝ × ℝ → ℝ :=
    fun p => p.1 * putnam_2021_a4_Fc (Complex.polarCoord.symm p)
  have hann : MeasurableSet ann :=
    measurableSet_Ioo.preimage continuous_norm.measurable
  have hrect : MeasurableSet rect := measurableSet_Ioo.prod measurableSet_Ioo
  have htarget : MeasurableSet Complex.polarCoord.target :=
    Complex.polarCoord.open_target.measurableSet
  have hrect_subset_target : rect ⊆ Complex.polarCoord.target := by
    intro p hp
    rw [Complex.polarCoord_target]
    exact ⟨lt_of_lt_of_le ha hp.1.1.le, hp.2⟩
  have hpolar :=
    Complex.integral_comp_polarCoord_symm
      (fun z : ℂ => ann.indicator putnam_2021_a4_Fc z)
  rw [MeasureTheory.integral_indicator hann] at hpolar
  have htarget_eq :
      (∫ p in Complex.polarCoord.target,
          p.1 • ann.indicator putnam_2021_a4_Fc (Complex.polarCoord.symm p))
        =
      ∫ p in Complex.polarCoord.target, rect.indicator g p := by
    apply setIntegral_congr_fun htarget
    intro p hp
    have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
      simpa [Complex.polarCoord_target] using hp
    have hp_pos : 0 < p.1 := hp'.1
    have hann_iff : Complex.polarCoord.symm p ∈ ann ↔ p ∈ rect := by
      dsimp [ann, rect]
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp_pos]
      exact ⟨fun h => ⟨h, hp'.2⟩, fun h => h.1⟩
    change p.1 • ann.indicator putnam_2021_a4_Fc (Complex.polarCoord.symm p)
      = rect.indicator g p
    by_cases hp_rect : p ∈ rect
    · have hp_ann : Complex.polarCoord.symm p ∈ ann := hann_iff.mpr hp_rect
      rw [Set.indicator_of_mem hp_ann, Set.indicator_of_mem hp_rect]
      simp [g, smul_eq_mul]
    · have hp_ann : Complex.polarCoord.symm p ∉ ann := by
        intro hp_ann
        exact hp_rect (hann_iff.mp hp_ann)
      rw [Set.indicator_of_notMem hp_ann, Set.indicator_of_notMem hp_rect]
      simp [smul_eq_mul]
  have htarget_indicator :
      (∫ p in Complex.polarCoord.target, rect.indicator g p)
        = ∫ p in rect, g p := by
    calc
      (∫ p in Complex.polarCoord.target, rect.indicator g p)
          = ∫ p, Complex.polarCoord.target.indicator (rect.indicator g) p := by
              rw [MeasureTheory.integral_indicator htarget]
      _ = ∫ p, rect.indicator g p := by
              apply integral_congr_ae
              filter_upwards with p
              by_cases hp_rect : p ∈ rect
              · have hp_target : p ∈ Complex.polarCoord.target :=
                  hrect_subset_target hp_rect
                simp [hp_rect, hp_target]
              · simp [hp_rect]
      _ = ∫ p in rect, g p := by
              rw [MeasureTheory.integral_indicator hrect]
  calc
    (∫ z in {z : ℂ | ‖z‖ ∈ Set.Ioo a b}, putnam_2021_a4_Fc z)
        = ∫ z in ann, putnam_2021_a4_Fc z := rfl
    _ = ∫ p in Complex.polarCoord.target,
          p.1 • ann.indicator putnam_2021_a4_Fc (Complex.polarCoord.symm p) := by
          exact hpolar.symm
    _ = ∫ p in Complex.polarCoord.target, rect.indicator g p := htarget_eq
    _ = ∫ p in rect, g p := htarget_indicator
    _ = ∫ p in rect, putnam_2021_a4_polar p := by
          apply setIntegral_congr_fun hrect
          intro p _hp
          dsimp [g, putnam_2021_a4_polar]
          rw [putnam_2021_a4_Fc_polar]
          ring_nf
    _ = ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
          putnam_2021_a4_polar p := rfl

private lemma putnam_2021_a4_scaledPolar_integral_eq_polar_scaled
    {R : ℝ} (hR : 0 < R) :
    (∫ p in Set.Ioo putnam_2021_a4_c⁻¹ putnam_2021_a4_c ×ˢ
        Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_scaledPolar R p)
      =
    ∫ p in Set.Ioo (R * putnam_2021_a4_c⁻¹) (R * putnam_2021_a4_c) ×ˢ
        Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_polar p := by
  let s : Set ℝ := Set.Ioo putnam_2021_a4_c⁻¹ putnam_2021_a4_c
  let t : Set ℝ := Set.Ioo (-Real.pi) Real.pi
  let sR : Set ℝ := Set.Ioo (R * putnam_2021_a4_c⁻¹) (R * putnam_2021_a4_c)
  let G : ℝ → ℝ := fun r => ∫ θ in t, putnam_2021_a4_polar (r, θ)
  have hs_meas : MeasurableSet s := measurableSet_Ioo
  have ht_meas : MeasurableSet t := measurableSet_Ioo
  have hscaled_int :
      IntegrableOn (putnam_2021_a4_scaledPolar R) (s ×ˢ t)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    putnam_2021_a4_integrableOn_Ioo_prod_of_continuous
      (putnam_2021_a4_continuous_scaledPolar R)
  have hpolar_int :
      IntegrableOn putnam_2021_a4_polar (sR ×ˢ t)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    putnam_2021_a4_integrableOn_Ioo_prod_of_continuous
      putnam_2021_a4_continuous_polar
  have hs_smul : R • s = sR := by
    dsimp [s, sR]
    simpa [smul_eq_mul] using
      (LinearOrderedField.smul_Ioo
        (a := putnam_2021_a4_c⁻¹) (b := putnam_2021_a4_c) hR)
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure ℝ)) G (s := s) hR
  have hscale' :
      R * (∫ r in s, G (R * r)) = ∫ r in sR, G r := by
    rw [Module.finrank_self, pow_one, hs_smul] at hscale
    simp only [smul_eq_mul] at hscale
    rw [hscale]
    field_simp [hR.ne']
  have hinner : ∀ r : ℝ,
      (∫ θ in t, putnam_2021_a4_scaledPolar R (r, θ))
        = R * G (R * r) := by
    intro r
    dsimp [G]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun ht_meas
    intro θ _hθ
    exact (putnam_2021_a4_scaledPolar_eq R r θ).symm
  calc
    (∫ p in Set.Ioo putnam_2021_a4_c⁻¹ putnam_2021_a4_c ×ˢ
        Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_scaledPolar R p)
        = ∫ p in s ×ˢ t, putnam_2021_a4_scaledPolar R p := rfl
    _ = ∫ r in s, ∫ θ in t, putnam_2021_a4_scaledPolar R (r, θ) := by
          rw [Measure.volume_eq_prod]
          exact setIntegral_prod (putnam_2021_a4_scaledPolar R) hscaled_int
    _ = ∫ r in s, R * G (R * r) := by
          apply setIntegral_congr_fun hs_meas
          intro r _hr
          exact hinner r
    _ = R * ∫ r in s, G (R * r) := by
          rw [integral_const_mul]
    _ = ∫ r in sR, G r := hscale'
    _ = ∫ p in sR ×ˢ t, putnam_2021_a4_polar p := by
          rw [Measure.volume_eq_prod]
          exact (setIntegral_prod putnam_2021_a4_polar hpolar_int).symm
    _ = ∫ p in Set.Ioo (R * putnam_2021_a4_c⁻¹) (R * putnam_2021_a4_c) ×ˢ
        Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_polar p := rfl

private lemma putnam_2021_a4_complex_disk_diff_eq_scaledPolar
    {R : ℝ} (hR : 0 < R) :
    (∫ z in ball (0 : ℂ) (putnam_2021_a4_c * R), putnam_2021_a4_Fc z)
      - ∫ z in ball (0 : ℂ) (putnam_2021_a4_c⁻¹ * R), putnam_2021_a4_Fc z
      =
    ∫ p in Set.Ioo putnam_2021_a4_c⁻¹ putnam_2021_a4_c ×ˢ
        Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_scaledPolar R p := by
  let a : ℝ := putnam_2021_a4_c⁻¹ * R
  let b : ℝ := putnam_2021_a4_c * R
  let annClosed : Set ℂ := ball (0 : ℂ) b \ ball (0 : ℂ) a
  let annOpen : Set ℂ := {z : ℂ | ‖z‖ ∈ Set.Ioo a b}
  have ha_pos : 0 < a := by
    dsimp [a]
    exact mul_pos (inv_pos.mpr putnam_2021_a4_c_pos) hR
  have hab_lt : a < b := by
    dsimp [a, b]
    exact mul_lt_mul_of_pos_right putnam_2021_a4_inv_c_lt_c hR
  have hsubset : ball (0 : ℂ) a ⊆ ball (0 : ℂ) b := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    exact lt_of_lt_of_le hz hab_lt.le
  have houter_int : IntegrableOn putnam_2021_a4_Fc (ball (0 : ℂ) b) :=
    putnam_2021_a4_integrableOn_ball_of_continuous putnam_2021_a4_continuous_Fc b
  have hae_ann : annClosed =ᵐ[volume] annOpen := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · apply measure_mono_null (t := sphere (0 : ℂ) a)
      · intro z hz
        have hz_ball : z ∈ ball (0 : ℂ) b := hz.1.1
        have hz_not_inner : z ∉ ball (0 : ℂ) a := hz.1.2
        have hz_not_open : z ∉ annOpen := hz.2
        rw [mem_ball_zero_iff] at hz_ball hz_not_inner
        have hle_a : ‖z‖ ≤ a := by
          by_contra hlt
          exact hz_not_open ⟨lt_of_not_ge hlt, hz_ball⟩
        have ha_le : a ≤ ‖z‖ := le_of_not_gt hz_not_inner
        rw [Metric.mem_sphere, dist_zero_right]
        exact le_antisymm hle_a ha_le
      · exact Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) a
    · rw [show annOpen \ annClosed = (∅ : Set ℂ) by
        ext z
        constructor
        · intro hz
          have hz_open : z ∈ annOpen := hz.1
          have hz_not_closed : z ∉ annClosed := hz.2
          have hz_norm : a < ‖z‖ ∧ ‖z‖ < b := hz_open
          have hz_outer : z ∈ ball (0 : ℂ) b := by
            rw [mem_ball_zero_iff]
            exact hz_norm.2
          have hz_inner : z ∉ ball (0 : ℂ) a := by
            rw [mem_ball_zero_iff]
            exact not_lt.mpr hz_norm.1.le
          exact False.elim (hz_not_closed ⟨hz_outer, hz_inner⟩)
        · intro hz
          exact False.elim hz]
      simp
  calc
    (∫ z in ball (0 : ℂ) (putnam_2021_a4_c * R), putnam_2021_a4_Fc z)
        - ∫ z in ball (0 : ℂ) (putnam_2021_a4_c⁻¹ * R), putnam_2021_a4_Fc z
        = ∫ z in annClosed, putnam_2021_a4_Fc z := by
          dsimp [annClosed, a, b]
          rw [MeasureTheory.integral_diff measurableSet_ball houter_int hsubset]
    _ = ∫ z in annOpen, putnam_2021_a4_Fc z := by
          exact setIntegral_congr_set hae_ann
    _ = ∫ p in Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi,
          putnam_2021_a4_polar p := by
          dsimp [annOpen]
          exact putnam_2021_a4_polar_annulus ha_pos
    _ = ∫ p in Set.Ioo (R * putnam_2021_a4_c⁻¹) (R * putnam_2021_a4_c) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
          putnam_2021_a4_polar p := by
          dsimp [a, b]
          rw [mul_comm putnam_2021_a4_c⁻¹ R, mul_comm putnam_2021_a4_c R]
    _ = ∫ p in Set.Ioo putnam_2021_a4_c⁻¹ putnam_2021_a4_c ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
          putnam_2021_a4_scaledPolar R p := by
          exact (putnam_2021_a4_scaledPolar_integral_eq_polar_scaled hR).symm

/--
Let
\[
I(R) = \iint_{x^2+y^2 \leq R^2} \left( \frac{1+2x^2}{1+x^4+6x^2y^2+y^4} - \frac{1+y^2}{2+x^4+y^4} \right)\,dx\,dy.
\]
Find
\[
\lim_{R \to \infty} I(R),
\]
or show that this limit does not exist.
-/
theorem putnam_2021_a4
  (S : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
  (hS : S = fun R => ball (0 : EuclideanSpace ℝ (Fin 2)) R)
  (I : ℝ → ℝ)
  (hI : I = fun R => ∫ p in S R,
    (1 + 2*(p 0)^2)/(1 + (p 0)^4 + 6*(p 0)^2*(p 1)^2 + (p 1)^4) - (1 + (p 1)^2)/(2 + (p 0)^4 + (p 1)^4)) :
  Tendsto I atTop (𝓝 putnam_2021_a4_solution) :=
by
  subst S
  subst I
  dsimp [putnam_2021_a4_solution]
  refine putnam_2021_a4_scaled_integral_limit_value.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [putnam_2021_a4_euclidean_integral_eq_complex R]
  rw [putnam_2021_a4_complex_finite_identity R]
  exact (putnam_2021_a4_complex_disk_diff_eq_scaledPolar hR).symm
