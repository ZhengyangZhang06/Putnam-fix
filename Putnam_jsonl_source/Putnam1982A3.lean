import Mathlib

open Set Function Filter Topology Polynomial Real MeasureTheory

-- (Real.pi / 2) * log Real.pi
/--
Evaluate $\int_0^{\infty} \frac{\tan^{-1}(\pi x) - \tan^{-1} x}{x} \, dx$.
-/
theorem putnam_1982_a3 :
  Tendsto (fun t ↦ ∫ x in (0)..t, (arctan (Real.pi * x) - arctan x) / x) atTop (𝓝 (((Real.pi / 2) * log Real.pi) : ℝ )) := by
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have param_id (x : ℝ) (hx : x ≠ 0) :
      (∫ s in (1 : ℝ)..Real.pi, (1 + (s * x) ^ 2)⁻¹) =
        (arctan (Real.pi * x) - arctan x) / x := by
    have hmul := intervalIntegral.smul_integral_comp_mul_right
        (a := (1 : ℝ)) (b := Real.pi) (f := fun y : ℝ => (1 + y ^ 2)⁻¹) x
    have hmul_eq0 : x * (∫ s in (1 : ℝ)..Real.pi, (1 + (s * x) ^ 2)⁻¹) =
        ∫ y in (1 : ℝ) * x..Real.pi * x, (1 + y ^ 2)⁻¹ := by
      simpa using hmul
    have hright : (∫ y in (1 : ℝ) * x..Real.pi * x, (1 + y ^ 2)⁻¹) =
        arctan (Real.pi * x) - arctan x := by
      simp [one_mul]
    have hmul_eq : x * (∫ s in (1 : ℝ)..Real.pi, (1 + (s * x) ^ 2)⁻¹) =
        arctan (Real.pi * x) - arctan x := hmul_eq0.trans hright
    calc
      (∫ s in (1 : ℝ)..Real.pi, (1 + (s * x) ^ 2)⁻¹)
          = (x * (∫ s in (1 : ℝ)..Real.pi, (1 + (s * x) ^ 2)⁻¹)) / x := by
              exact (mul_div_cancel_left₀ _ hx).symm
      _ = (arctan (Real.pi * x) - arctan x) / x := by rw [hmul_eq]
  have inner_id (s t : ℝ) (hs : s ≠ 0) :
      (∫ x in (0 : ℝ)..t, (1 + (s * x) ^ 2)⁻¹) = arctan (s * t) / s := by
    have hmul := intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := t) (f := fun y : ℝ => (1 + y ^ 2)⁻¹) s
    have hmul_eq0 : s * (∫ x in (0 : ℝ)..t, (1 + (s * x) ^ 2)⁻¹) =
        ∫ y in s * (0 : ℝ)..s * t, (1 + y ^ 2)⁻¹ := by
      simpa using hmul
    have hright : (∫ y in s * (0 : ℝ)..s * t, (1 + y ^ 2)⁻¹) = arctan (s * t) := by
      simp [Real.arctan_zero]
    have hmul_eq : s * (∫ x in (0 : ℝ)..t, (1 + (s * x) ^ 2)⁻¹) =
        arctan (s * t) := hmul_eq0.trans hright
    calc
      (∫ x in (0 : ℝ)..t, (1 + (s * x) ^ 2)⁻¹)
          = (s * (∫ x in (0 : ℝ)..t, (1 + (s * x) ^ 2)⁻¹)) / s := by
              exact (mul_div_cancel_left₀ _ hs).symm
      _ = arctan (s * t) / s := by rw [hmul_eq]
  have transformed (t : ℝ) (ht : 0 ≤ t) :
      (∫ x in (0 : ℝ)..t, (arctan (Real.pi * x) - arctan x) / x) =
        ∫ s in (1 : ℝ)..Real.pi, arctan (s * t) / s := by
    let k : ℝ → ℝ → ℝ := fun x s => (1 + (s * x) ^ 2)⁻¹
    let μs : MeasureTheory.Measure ℝ := volume.restrict (Set.uIoc (1 : ℝ) Real.pi)
    have h_left :
        (∫ x in (0 : ℝ)..t, (arctan (Real.pi * x) - arctan x) / x) =
          ∫ x in (0 : ℝ)..t, ∫ s in (1 : ℝ)..Real.pi, k x s := by
      refine intervalIntegral.integral_congr_ae ?_
      exact ae_of_all _ fun x hxmem => by
        have hxI : x ∈ Set.Ioc (0 : ℝ) t := by simpa [Set.uIoc_of_le ht] using hxmem
        have hxne : x ≠ 0 := ne_of_gt hxI.1
        exact (param_id x hxne).symm
    have h_interval_to_restrict (x : ℝ) :
        (∫ s in (1 : ℝ)..Real.pi, k x s) = ∫ s, k x s ∂μs := by
      simp [μs, intervalIntegral.integral_of_le hπ, Set.uIoc_of_le hπ]
    have h_restrict_to_interval :
        (∫ s, arctan (s * t) / s ∂μs) =
          ∫ s in (1 : ℝ)..Real.pi, arctan (s * t) / s := by
      simp [μs, intervalIntegral.integral_of_le hπ, Set.uIoc_of_le hπ]
    have h_int : Integrable (Function.uncurry k)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod μs) := by
      have hbase : Continuous (fun p : ℝ × ℝ => 1 + (p.2 * p.1) ^ 2) := by fun_prop
      have hcont : Continuous (fun p : ℝ × ℝ => (1 + (p.2 * p.1) ^ 2)⁻¹) := by
        refine hbase.inv₀ ?_
        intro p
        nlinarith [sq_nonneg (p.2 * p.1)]
      have hcompact : IsCompact (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (1 : ℝ) Real.pi) :=
        isCompact_Icc.prod isCompact_Icc
      have hint_comp : IntegrableOn (fun p : ℝ × ℝ => (1 + (p.2 * p.1) ^ 2)⁻¹)
          (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (1 : ℝ) Real.pi) (volume.prod volume) :=
        hcont.continuousOn.integrableOn_compact hcompact
      change Integrable (fun p : ℝ × ℝ => (1 + (p.2 * p.1) ^ 2)⁻¹)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod
          (volume.restrict (Set.uIoc (1 : ℝ) Real.pi)))
      rw [MeasureTheory.Measure.prod_restrict, ← IntegrableOn]
      refine hint_comp.mono_set ?_
      intro p hp
      rcases hp with ⟨hpx, hps⟩
      have hpxI : p.1 ∈ Set.Ioc (0 : ℝ) t := by simpa [Set.uIoc_of_le ht] using hpx
      have hpsI : p.2 ∈ Set.Ioc (1 : ℝ) Real.pi := by simpa [Set.uIoc_of_le hπ] using hps
      exact ⟨⟨hpxI.1.le, hpxI.2⟩, ⟨hpsI.1.le, hpsI.2⟩⟩
    have hswap :
        (∫ x in (0 : ℝ)..t, ∫ s, k x s ∂μs) =
          ∫ s, (∫ x in (0 : ℝ)..t, k x s) ∂μs :=
      MeasureTheory.intervalIntegral_integral_swap
        (μ := μs) (a := (0 : ℝ)) (b := t) (f := k) h_int
    have h_inner :
        (∫ s, (∫ x in (0 : ℝ)..t, k x s) ∂μs) =
          ∫ s, arctan (s * t) / s ∂μs := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (μ := volume) (s := Set.uIoc (1 : ℝ) Real.pi) measurableSet_uIoc] with s hsmem
      have hsI : s ∈ Set.Ioc (1 : ℝ) Real.pi := by simpa [Set.uIoc_of_le hπ] using hsmem
      have hsne : s ≠ 0 := ne_of_gt (lt_trans zero_lt_one hsI.1)
      exact inner_id s t hsne
    calc
      (∫ x in (0 : ℝ)..t, (arctan (Real.pi * x) - arctan x) / x)
          = ∫ x in (0 : ℝ)..t, ∫ s in (1 : ℝ)..Real.pi, k x s := h_left
      _ = ∫ x in (0 : ℝ)..t, ∫ s, k x s ∂μs := by
            refine intervalIntegral.integral_congr (fun x hx => ?_)
            exact h_interval_to_restrict x
      _ = ∫ s, (∫ x in (0 : ℝ)..t, k x s) ∂μs := hswap
      _ = ∫ s, arctan (s * t) / s ∂μs := h_inner
      _ = ∫ s in (1 : ℝ)..Real.pi, arctan (s * t) / s := h_restrict_to_interval
  have hG_limit :
      Tendsto (fun t : ℝ => ∫ s in (1 : ℝ)..Real.pi, arctan (s * t) / s) atTop
        (𝓝 (∫ s in (1 : ℝ)..Real.pi, (Real.pi / 2) / s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := (1 : ℝ)) (b := Real.pi)
      (F := fun t s => arctan (s * t) / s) (f := fun s => (Real.pi / 2) / s)
      (bound := fun _ : ℝ => Real.pi / 2) ?hmeas ?hbound ?hbound_int ?hlim
    · exact Eventually.of_forall fun t => by
        have hm : Measurable (fun s : ℝ => arctan (s * t) * s⁻¹) := by
          exact (Real.continuous_arctan.comp
            (continuous_id.mul continuous_const)).measurable.mul measurable_id.inv
        simpa [div_eq_mul_inv] using
          hm.aestronglyMeasurable
            (μ := volume.restrict (Set.uIoc (1 : ℝ) Real.pi))
    · refine Eventually.of_forall fun t => ?_
      exact ae_of_all _ fun s hs => by
        have hsI : s ∈ Set.Ioc (1 : ℝ) Real.pi := by simpa [Set.uIoc_of_le hπ] using hs
        have hspos : 0 < s := lt_trans zero_lt_one hsI.1
        have hsges : 1 ≤ |s| := by simpa [abs_of_pos hspos] using hsI.1.le
        have hatan : |arctan (s * t)| ≤ Real.pi / 2 := by
          rw [abs_le]
          constructor
          · exact le_of_lt (Real.neg_pi_div_two_lt_arctan _)
          · exact le_of_lt (Real.arctan_lt_pi_div_two _)
        calc
          ‖arctan (s * t) / s‖ = |arctan (s * t)| / |s| := by
            rw [Real.norm_eq_abs, abs_div]
          _ ≤ |arctan (s * t)| := div_le_self (abs_nonneg _) hsges
          _ ≤ Real.pi / 2 := hatan
    · exact (continuous_const.intervalIntegrable (1 : ℝ) Real.pi)
    · exact ae_of_all _ fun s hs => by
        have hsI : s ∈ Set.Ioc (1 : ℝ) Real.pi := by simpa [Set.uIoc_of_le hπ] using hs
        have hspos : 0 < s := lt_trans zero_lt_one hsI.1
        have hmul : Tendsto (fun t : ℝ => s * t) atTop atTop := by
          simpa using (tendsto_id.const_mul_atTop hspos)
        have hatan : Tendsto (fun t : ℝ => arctan (s * t)) atTop (𝓝 (Real.pi / 2)) :=
          (tendsto_nhdsWithin_iff.mp (Real.tendsto_arctan_atTop.comp hmul)).1
        simpa using hatan.div_const s
  have hG_value :
      (∫ s in (1 : ℝ)..Real.pi, (Real.pi / 2) / s) = (Real.pi / 2) * log Real.pi := by
    have hπpos : 0 < Real.pi := Real.pi_pos
    have h1 : (0 : ℝ) < 1 := by norm_num
    calc
      ∫ s in (1 : ℝ)..Real.pi, (Real.pi / 2) / s =
          (Real.pi / 2) * ∫ s in (1 : ℝ)..Real.pi, 1 / s := by
        simp [div_eq_mul_inv, intervalIntegral.integral_const_mul]
      _ = (Real.pi / 2) * log (Real.pi / 1) := by rw [integral_one_div_of_pos h1 hπpos]
      _ = (Real.pi / 2) * log Real.pi := by simp
  have hG :
      Tendsto (fun t : ℝ => ∫ s in (1 : ℝ)..Real.pi, arctan (s * t) / s) atTop
        (𝓝 ((Real.pi / 2) * log Real.pi)) := by
    simpa [hG_value] using hG_limit
  have heq :
      (fun t : ℝ => ∫ x in (0 : ℝ)..t, (arctan (Real.pi * x) - arctan x) / x)
        =ᶠ[atTop] (fun t : ℝ => ∫ s in (1 : ℝ)..Real.pi, arctan (s * t) / s) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact transformed t ht
  exact hG.congr' heq.symm
