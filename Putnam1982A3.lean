import Mathlib

open Set Function Filter Topology Polynomial Real

noncomputable abbrev putnam_1982_a3_solution : ℝ := (Real.pi / 2) * Real.log Real.pi

open MeasureTheory

private lemma putnam_1982_a3_arctan_sub_div_eq_param {x : ℝ} (hx : x ≠ 0) :
    (∫ u in (1 : ℝ)..Real.pi, (1 + (u * x) ^ 2)⁻¹) =
      (arctan (Real.pi * x) - arctan x) / x := by
  rw [intervalIntegral.integral_comp_mul_right (fun y : ℝ => (1 + y ^ 2)⁻¹) hx]
  simp [one_mul]
  field_simp [hx]

private lemma putnam_1982_a3_inner_integral_eq {u t : ℝ} (hu : u ≠ 0) :
    (∫ x in (0 : ℝ)..t, (1 + (u * x) ^ 2)⁻¹) = arctan (u * t) / u := by
  rw [intervalIntegral.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) hu]
  simp
  field_simp [hu]

private lemma putnam_1982_a3_kernel_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable
      (Function.uncurry (fun x u : ℝ => (1 + (u * x) ^ 2)⁻¹ : ℝ → ℝ → ℝ))
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod
        (volume.restrict (Set.uIoc (1 : ℝ) Real.pi))) := by
  have h1pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  simp only [Set.uIoc_of_le ht, Set.uIoc_of_le h1pi]
  have hcont :
      Continuous
        (Function.uncurry (fun x u : ℝ => (1 + (u * x) ^ 2)⁻¹ : ℝ → ℝ → ℝ)) := by
    dsimp [Function.uncurry]
    refine Continuous.inv₀ ?_ ?_
    · fun_prop
    · intro z
      nlinarith [sq_nonneg (z.2 * z.1)]
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (fun x u : ℝ => (1 + (u * x) ^ 2)⁻¹ : ℝ → ℝ → ℝ))
        ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod
          (volume.restrict (Set.Ioc (1 : ℝ) Real.pi))) :=
    hcont.aestronglyMeasurable
  refine Integrable.of_bound hmeas 1 ?_
  filter_upwards with z
  dsimp [Function.uncurry]
  have hpos : 0 ≤ 1 + (z.2 * z.1) ^ 2 := by positivity
  rw [abs_of_nonneg (inv_nonneg.mpr hpos)]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (z.2 * z.1)])

private lemma putnam_1982_a3_finite_identity {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in (0)..t, (arctan (Real.pi * x) - arctan x) / x) =
      ∫ u in (1)..Real.pi, arctan (u * t) / u := by
  let h : ℝ → ℝ → ℝ := fun x u => (1 + (u * x) ^ 2)⁻¹
  have h1pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc
    (∫ x in (0)..t, (arctan (Real.pi * x) - arctan x) / x)
        = ∫ x in (0)..t, ∫ u in (1)..Real.pi, h x u := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [Measure.ae_ne (volume : Measure ℝ) (0 : ℝ)] with x hx _hxmem
          exact (putnam_1982_a3_arctan_sub_div_eq_param hx).symm
    _ = ∫ u in (1)..Real.pi, ∫ x in (0)..t, h x u := by
          have hs := MeasureTheory.intervalIntegral_integral_swap (a := (0 : ℝ)) (b := t)
            (μ := volume.restrict (Set.uIoc (1 : ℝ) Real.pi)) (f := h)
            (putnam_1982_a3_kernel_integrable t ht)
          simp only [Set.uIoc_of_le h1pi] at hs
          simpa [h, intervalIntegral.integral_of_le h1pi] using hs
    _ = ∫ u in (1)..Real.pi, arctan (u * t) / u := by
          refine intervalIntegral.integral_congr ?_
          intro u hu
          have huIcc : u ∈ Set.Icc (1 : ℝ) Real.pi := by
            simpa [Set.uIcc_of_le h1pi] using hu
          have hune : u ≠ 0 := by linarith [huIcc.1]
          simpa [h] using putnam_1982_a3_inner_integral_eq (t := t) hune

private lemma putnam_1982_a3_param_limit :
    Tendsto (fun t : ℝ => ∫ u in (1 : ℝ)..Real.pi, arctan (u * t) / u) atTop
      (𝓝 putnam_1982_a3_solution) := by
  have h1pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hlim_int :
      Tendsto (fun t : ℝ => ∫ u in (1 : ℝ)..Real.pi, arctan (u * t) / u) atTop
        (𝓝 (∫ u in (1 : ℝ)..Real.pi, (Real.pi / 2) / u)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := (1 : ℝ)) (b := Real.pi)
      (F := fun t u : ℝ => arctan (u * t) / u)
      (f := fun u : ℝ => (Real.pi / 2) / u)
      (bound := fun _ : ℝ => Real.pi / 2) ?hmeas ?hbound ?hbound_int ?hlim
    · refine Eventually.of_forall fun t => ?_
      have hcont : ContinuousOn (fun u : ℝ => arctan (u * t) / u)
          (Set.uIoc (1 : ℝ) Real.pi) := by
        rw [Set.uIoc_of_le h1pi]
        refine ContinuousOn.div ?_ continuousOn_id ?_
        · exact continuous_arctan.comp_continuousOn
            ((continuous_id.mul continuous_const).continuousOn)
        · intro u hu
          linarith [hu.1]
      exact hcont.aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun t => ?_
      filter_upwards with u hu_mem
      have huIoc : u ∈ Set.Ioc (1 : ℝ) Real.pi := by
        simpa [Set.uIoc_of_le h1pi] using hu_mem
      have hu_pos : 0 < u := by linarith [huIoc.1]
      have hu_abs : 1 ≤ |u| := by
        rw [abs_of_pos hu_pos]
        exact huIoc.1.le
      have harctan_abs : |arctan (u * t)| ≤ Real.pi / 2 :=
        abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le,
          (Real.arctan_lt_pi_div_two _).le⟩
      rw [Real.norm_eq_abs, abs_div]
      calc
        |arctan (u * t)| / |u| = |arctan (u * t)| * |u|⁻¹ := by
          rw [div_eq_mul_inv]
        _ ≤ (Real.pi / 2) * 1 := by
          gcongr
          exact inv_le_one_of_one_le₀ hu_abs
        _ = Real.pi / 2 := by ring
    · exact intervalIntegrable_const
    · filter_upwards with u hu_mem
      have huIoc : u ∈ Set.Ioc (1 : ℝ) Real.pi := by
        simpa [Set.uIoc_of_le h1pi] using hu_mem
      have hu_pos : 0 < u := by linarith [huIoc.1]
      have hmul : Tendsto (fun t : ℝ => u * t) atTop atTop :=
        tendsto_id.const_mul_atTop hu_pos
      exact ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hmul).div_const u
  have heval : (∫ u in (1 : ℝ)..Real.pi, (Real.pi / 2) / u) =
      (Real.pi / 2) * Real.log Real.pi := by
    calc
      (∫ u in (1 : ℝ)..Real.pi, (Real.pi / 2) / u)
          = ∫ u in (1 : ℝ)..Real.pi, (Real.pi / 2) * (1 / u) := by
            refine intervalIntegral.integral_congr ?_
            intro u _hu
            ring
      _ = (Real.pi / 2) * ∫ u in (1 : ℝ)..Real.pi, 1 / u := by
            rw [intervalIntegral.integral_const_mul]
      _ = (Real.pi / 2) * Real.log (Real.pi / 1) := by
            rw [integral_one_div_of_pos (by norm_num) Real.pi_pos]
      _ = (Real.pi / 2) * Real.log Real.pi := by simp
  simpa [putnam_1982_a3_solution, heval] using hlim_int

/--
Evaluate $\int_0^{\infty} \frac{\tan^{-1}(\pi x) - \tan^{-1} x}{x} \, dx$.
-/
theorem putnam_1982_a3 :
  Tendsto (fun t ↦ ∫ x in (0)..t, (arctan (Real.pi * x) - arctan x) / x) atTop (𝓝 putnam_1982_a3_solution) :=
by
  refine putnam_1982_a3_param_limit.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (putnam_1982_a3_finite_identity ht).symm
