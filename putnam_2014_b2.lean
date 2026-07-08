import Mathlib

open Topology Filter Nat MeasureTheory

noncomputable abbrev putnam_2014_b2_solution : ℝ := Real.log (2 / 1 : ℝ) - Real.log (3 / 2 : ℝ)

/--
Suppose that \( f \) is a function on the interval \([1,3]\) such that \(-1 \leq f(x) \leq 1\) for all \( x \) and \( \int_{1}^{3} f(x) \, dx = 0 \). How large can \(\int_{1}^{3} \frac{f(x)}{x} \, dx \) be?
-/
theorem putnam_2014_b2 :
  IsGreatest {t | ∃ f : ℝ → ℝ,
    (∀ x : Set.Icc (1 : ℝ) 3, -1 ≤ f x ∧ f x ≤ 1) ∧
    (∫ x in Set.Ioo 1 3, f x = 0) ∧
    (∫ x in Set.Ioo 1 3, (f x) / x) = t}
  putnam_2014_b2_solution :=
by
  have hInvInt : ∀ {a b : ℝ}, a ≤ b → 0 < a →
      IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b := by
    intro a b hab ha
    refine intervalIntegral.intervalIntegrable_inv (f := fun x : ℝ => x) ?_ continuousOn_id
    intro x hx
    have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx'.1
    exact ne_of_gt hxpos
  have hInvIntegral : ∀ {a b : ℝ}, a ≤ b → 0 < a →
      ∫ x in a..b, x⁻¹ = Real.log b - Real.log a := by
    intro a b hab ha
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ (hInvInt hab ha)
    · refine Real.continuousOn_log.mono ?_
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
      simpa using (ne_of_gt hxpos)
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ha hx.1.le
      exact Real.hasDerivAt_log (ne_of_gt hxpos)
  have hAbsIntegral :
      ∫ x in Set.Ioo (1 : ℝ) 3, |x⁻¹ - (2 : ℝ)⁻¹| =
        Real.log (2 / 1 : ℝ) - Real.log (3 / 2 : ℝ) := by
    have hcont12 :
        ContinuousOn (fun x : ℝ => |x⁻¹ - (2 : ℝ)⁻¹|) (Set.uIcc (1 : ℝ) 2) := by
      refine ((continuousOn_id.inv₀ ?_).sub continuousOn_const).abs
      intro x hx
      have hx' : x ∈ Set.Icc (1 : ℝ) 2 := by
        simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
      have hxpos : 0 < x := by linarith [hx'.1]
      exact ne_of_gt hxpos
    have hcont23 :
        ContinuousOn (fun x : ℝ => |x⁻¹ - (2 : ℝ)⁻¹|) (Set.uIcc (2 : ℝ) 3) := by
      refine ((continuousOn_id.inv₀ ?_).sub continuousOn_const).abs
      intro x hx
      have hx' : x ∈ Set.Icc (2 : ℝ) 3 := by
        simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
      have hxpos : 0 < x := by linarith [hx'.1]
      exact ne_of_gt hxpos
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (a := (1 : ℝ)) (b := (2 : ℝ)) (c := (3 : ℝ)) (μ := volume)
      (f := fun x : ℝ => |x⁻¹ - (2 : ℝ)⁻¹|)
      hcont12.intervalIntegrable hcont23.intervalIntegrable
    have hcongr12 :
        ∫ x in (1 : ℝ)..2, |x⁻¹ - (2 : ℝ)⁻¹| =
          ∫ x in (1 : ℝ)..2, x⁻¹ - (2 : ℝ)⁻¹ := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (1 : ℝ) 2 := by
        simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
      have hxpos : 0 < x := by linarith [hx'.1]
      have hle : (2 : ℝ)⁻¹ ≤ x⁻¹ := by
        simpa [one_div] using (one_div_le_one_div_of_le hxpos hx'.2)
      change |x⁻¹ - (2 : ℝ)⁻¹| = x⁻¹ - (2 : ℝ)⁻¹
      exact abs_of_nonneg (sub_nonneg.mpr hle)
    have hcongr23 :
        ∫ x in (2 : ℝ)..3, |x⁻¹ - (2 : ℝ)⁻¹| =
          ∫ x in (2 : ℝ)..3, (2 : ℝ)⁻¹ - x⁻¹ := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : x ∈ Set.Icc (2 : ℝ) 3 := by
        simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
      have hxpos2 : 0 < (2 : ℝ) := by norm_num
      have hle : x⁻¹ ≤ (2 : ℝ)⁻¹ := by
        simpa [one_div] using (one_div_le_one_div_of_le hxpos2 hx'.1)
      change |x⁻¹ - (2 : ℝ)⁻¹| = (2 : ℝ)⁻¹ - x⁻¹
      rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    have hcalc12 :
        ∫ x in (1 : ℝ)..2, x⁻¹ - (2 : ℝ)⁻¹ =
          Real.log 2 - Real.log 1 - (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_sub
        (hInvInt (by norm_num) (by norm_num))
        (intervalIntegral.intervalIntegrable_const (μ := volume))]
      rw [hInvIntegral (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1)]
      rw [intervalIntegral.integral_const]
      norm_num
    have hcalc23 :
        ∫ x in (2 : ℝ)..3, (2 : ℝ)⁻¹ - x⁻¹ =
          (1 / 2 : ℝ) - (Real.log 3 - Real.log 2) := by
      rw [intervalIntegral.integral_sub
        (intervalIntegral.intervalIntegrable_const (μ := volume))
        (hInvInt (by norm_num) (by norm_num))]
      rw [intervalIntegral.integral_const]
      rw [hInvIntegral (by norm_num : (2 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    rw [← hsplit]
    rw [hcongr12, hcongr23, hcalc12, hcalc23]
    have hlog21 : Real.log 2 - Real.log 1 = Real.log (2 / 1 : ℝ) := by
      rw [← Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (1 : ℝ) ≠ 0)]
    have hlog32 : Real.log 3 - Real.log 2 = Real.log (3 / 2 : ℝ) := by
      rw [← Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← hlog21, ← hlog32]
    ring
  constructor
  · let f0 : ℝ → ℝ := fun x => if x ≤ (2 : ℝ) then 1 else -1
    refine ⟨f0, ?_, ?_, ?_⟩
    · intro x
      change -1 ≤ (if (x : ℝ) ≤ (2 : ℝ) then 1 else -1) ∧
        (if (x : ℝ) ≤ (2 : ℝ) then 1 else -1) ≤ 1
      by_cases hx : (x : ℝ) ≤ (2 : ℝ) <;> simp [hx]
    · have hfint12 : IntervalIntegrable f0 volume (1 : ℝ) 2 := by
        refine (intervalIntegral.intervalIntegrable_const (μ := volume) (c := (1 : ℝ))).congr ?_
        intro x hx
        have hx' : x ∈ Set.Ioc (1 : ℝ) 2 := by
          simpa [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
        simp [f0, hx'.2]
      have hfint23 : IntervalIntegrable f0 volume (2 : ℝ) 3 := by
        refine (intervalIntegral.intervalIntegrable_const (μ := volume) (c := (-1 : ℝ))).congr ?_
        intro x hx
        have hx' : x ∈ Set.Ioc (2 : ℝ) 3 := by
          simpa [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
        have hxnot : ¬ x ≤ (2 : ℝ) := not_le.mpr hx'.1
        simp [f0, hxnot]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (a := (1 : ℝ)) (b := (2 : ℝ)) (c := (3 : ℝ)) (μ := volume)
        (f := f0) hfint12 hfint23
      have h12 : ∫ x in (1 : ℝ)..2, f0 x = 1 := by
        calc
          ∫ x in (1 : ℝ)..2, f0 x = ∫ x in (1 : ℝ)..2, (1 : ℝ) := by
            refine intervalIntegral.integral_congr_ae (μ := volume) ?_
            exact Filter.Eventually.of_forall fun x hx => by
              have hx' : x ∈ Set.Ioc (1 : ℝ) 2 := by
                simpa [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
              simp [f0, hx'.2]
          _ = 1 := by
            rw [intervalIntegral.integral_const]
            norm_num
      have h23 : ∫ x in (2 : ℝ)..3, f0 x = -1 := by
        calc
          ∫ x in (2 : ℝ)..3, f0 x = ∫ x in (2 : ℝ)..3, (-1 : ℝ) := by
            refine intervalIntegral.integral_congr_ae (μ := volume) ?_
            exact Filter.Eventually.of_forall fun x hx => by
              have hx' : x ∈ Set.Ioc (2 : ℝ) 3 := by
                simpa [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
              have hxnot : ¬ x ≤ (2 : ℝ) := not_le.mpr hx'.1
              simp [f0, hxnot]
          _ = -1 := by
            rw [intervalIntegral.integral_const]
            norm_num
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      rw [← hsplit, h12, h23]
      norm_num
    · change ∫ x in Set.Ioo (1 : ℝ) 3, f0 x / x =
        Real.log (2 / 1 : ℝ) - Real.log (3 / 2 : ℝ)
      have hfwint12 : IntervalIntegrable (fun x : ℝ => f0 x / x) volume (1 : ℝ) 2 := by
        refine (hInvInt (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1)).congr ?_
        intro x hx
        have hx' : x ∈ Set.Ioc (1 : ℝ) 2 := by
          simpa [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
        simp [f0, hx'.2, div_eq_mul_inv]
      have hfwint23 : IntervalIntegrable (fun x : ℝ => f0 x / x) volume (2 : ℝ) 3 := by
        refine ((hInvInt (by norm_num : (2 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) < 2)).const_mul
          (-1 : ℝ)).congr ?_
        intro x hx
        have hx' : x ∈ Set.Ioc (2 : ℝ) 3 := by
          simpa [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
        have hxnot : ¬ x ≤ (2 : ℝ) := not_le.mpr hx'.1
        simp [f0, hxnot, div_eq_mul_inv]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (a := (1 : ℝ)) (b := (2 : ℝ)) (c := (3 : ℝ)) (μ := volume)
        (f := fun x : ℝ => f0 x / x) hfwint12 hfwint23
      have h12 : ∫ x in (1 : ℝ)..2, f0 x / x = Real.log 2 - Real.log 1 := by
        calc
          ∫ x in (1 : ℝ)..2, f0 x / x = ∫ x in (1 : ℝ)..2, x⁻¹ := by
            refine intervalIntegral.integral_congr_ae (μ := volume) ?_
            exact Filter.Eventually.of_forall fun x hx => by
              have hx' : x ∈ Set.Ioc (1 : ℝ) 2 := by
                simpa [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
              simp [f0, hx'.2, div_eq_mul_inv]
          _ = Real.log 2 - Real.log 1 :=
            hInvIntegral (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1)
      have h23 : ∫ x in (2 : ℝ)..3, f0 x / x = Real.log 2 - Real.log 3 := by
        calc
          ∫ x in (2 : ℝ)..3, f0 x / x = ∫ x in (2 : ℝ)..3, -x⁻¹ := by
            refine intervalIntegral.integral_congr_ae (μ := volume) ?_
            exact Filter.Eventually.of_forall fun x hx => by
              have hx' : x ∈ Set.Ioc (2 : ℝ) 3 := by
                simpa [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
              have hxnot : ¬ x ≤ (2 : ℝ) := not_le.mpr hx'.1
              simp [f0, hxnot, div_eq_mul_inv]
          _ = Real.log 2 - Real.log 3 := by
            rw [show (fun x : ℝ => -x⁻¹) = fun x : ℝ => (-1 : ℝ) * x⁻¹ by
              funext x
              ring]
            rw [intervalIntegral.integral_const_mul]
            rw [hInvIntegral (by norm_num : (2 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) < 2)]
            ring
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      rw [← hsplit, h12, h23]
      have hlog21 : Real.log 2 - Real.log 1 = Real.log (2 / 1 : ℝ) := by
        rw [← Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (1 : ℝ) ≠ 0)]
      have hlog32 : Real.log 3 - Real.log 2 = Real.log (3 / 2 : ℝ) := by
        rw [← Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      rw [← hlog21, ← hlog32]
      ring
  · intro t ht
    rcases ht with ⟨f, hbd, hzero, ht⟩
    rw [← ht]
    change ∫ x in Set.Ioo (1 : ℝ) 3, f x / x ≤
      Real.log (2 / 1 : ℝ) - Real.log (3 / 2 : ℝ)
    let S : Set ℝ := Set.Ioo (1 : ℝ) 3
    have hSmeas : MeasurableSet S := measurableSet_Ioo
    have hcontInv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) 3) := by
      refine continuousOn_id.inv₀ ?_
      intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      exact ne_of_gt hxpos
    have hcontShift : ContinuousOn (fun x : ℝ => x⁻¹ - (2 : ℝ)⁻¹) (Set.Icc (1 : ℝ) 3) :=
      hcontInv.sub continuousOn_const
    have hcontAbs :
        ContinuousOn (fun x : ℝ => |x⁻¹ - (2 : ℝ)⁻¹|) (Set.uIcc (1 : ℝ) 3) := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using hcontShift.abs
    have hAbsInt : IntegrableOn (fun x : ℝ => |x⁻¹ - (2 : ℝ)⁻¹|) S := by
      rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      exact hcontAbs.intervalIntegrable
    by_cases hfint : IntegrableOn f S
    · have hfIcc : IntegrableOn f (Set.Icc (1 : ℝ) 3) :=
        (integrableOn_Icc_iff_integrableOn_Ioo
          (f := f) (μ := volume) (a := (1 : ℝ)) (b := 3)).2 hfint
      have hprodIcc :
          IntegrableOn (fun x : ℝ => f x * (x⁻¹ - (2 : ℝ)⁻¹)) (Set.Icc (1 : ℝ) 3) :=
        hfIcc.mul_continuousOn hcontShift isCompact_Icc
      have hprodInt : IntegrableOn (fun x : ℝ => f x * (x⁻¹ - (2 : ℝ)⁻¹)) S :=
        hprodIcc.mono_set Set.Ioo_subset_Icc_self
      have hfxIcc : IntegrableOn (fun x : ℝ => f x * x⁻¹) (Set.Icc (1 : ℝ) 3) :=
        hfIcc.mul_continuousOn hcontInv isCompact_Icc
      have hfxInt : IntegrableOn (fun x : ℝ => f x * x⁻¹) S :=
        hfxIcc.mono_set Set.Ioo_subset_Icc_self
      have hshift :
          ∫ x in S, f x / x = ∫ x in S, f x * (x⁻¹ - (2 : ℝ)⁻¹) := by
        calc
          ∫ x in S, f x / x = ∫ x in S, f x * x⁻¹ := by
            simp [S, div_eq_mul_inv]
          _ = ∫ x in S, f x * x⁻¹ - f x * (2 : ℝ)⁻¹ := by
            rw [MeasureTheory.integral_sub hfxInt.integrable
              (hfint.integrable.mul_const ((2 : ℝ)⁻¹))]
            rw [MeasureTheory.integral_mul_const]
            rw [show (∫ x in S, f x) = 0 by simpa [S] using hzero]
            ring
          _ = ∫ x in S, f x * (x⁻¹ - (2 : ℝ)⁻¹) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => by ring
      have hpoint :
          ∀ x ∈ S, f x * (x⁻¹ - (2 : ℝ)⁻¹) ≤ |x⁻¹ - (2 : ℝ)⁻¹| := by
        intro x hx
        have hxIcc : x ∈ Set.Icc (1 : ℝ) 3 := ⟨hx.1.le, hx.2.le⟩
        have hfabs : |f x| ≤ (1 : ℝ) := by
          have hb := hbd ⟨x, hxIcc⟩
          exact abs_le.mpr ⟨hb.1, hb.2⟩
        calc
          f x * (x⁻¹ - (2 : ℝ)⁻¹) ≤ |f x * (x⁻¹ - (2 : ℝ)⁻¹)| := le_abs_self _
          _ = |f x| * |x⁻¹ - (2 : ℝ)⁻¹| := abs_mul _ _
          _ ≤ 1 * |x⁻¹ - (2 : ℝ)⁻¹| := mul_le_mul_of_nonneg_right hfabs (abs_nonneg _)
          _ = |x⁻¹ - (2 : ℝ)⁻¹| := one_mul _
      calc
        ∫ x in Set.Ioo (1 : ℝ) 3, f x / x = ∫ x in S, f x / x := by simp [S]
        _ = ∫ x in S, f x * (x⁻¹ - (2 : ℝ)⁻¹) := hshift
        _ ≤ ∫ x in S, |x⁻¹ - (2 : ℝ)⁻¹| :=
          setIntegral_mono_on hprodInt hAbsInt hSmeas hpoint
        _ = Real.log (2 / 1 : ℝ) - Real.log (3 / 2 : ℝ) := by simpa [S] using hAbsIntegral
    · have hweighted_zero : ∫ x in S, f x / x = 0 := by
        by_contra hne
        have hwin : Integrable (fun x : ℝ => f x / x) (volume.restrict S) :=
          Integrable.of_integral_ne_zero hne
        have hxBound : ∀ᵐ x ∂volume.restrict S, ‖x‖ ≤ (3 : ℝ) := by
          rw [ae_restrict_iff' hSmeas]
          exact Filter.Eventually.of_forall fun x hx => by
            have hxnonneg : 0 ≤ x := by linarith [hx.1]
            rw [Real.norm_eq_abs, abs_of_nonneg hxnonneg]
            exact hx.2.le
        have hprod : Integrable (fun x : ℝ => (f x / x) * x) (volume.restrict S) :=
          hwin.mul_bdd measurable_id.aestronglyMeasurable hxBound
        have hEq : (fun x : ℝ => (f x / x) * x) =ᵐ[volume.restrict S] f := by
          rw [Filter.EventuallyEq, ae_restrict_iff' hSmeas]
          exact Filter.Eventually.of_forall fun x hx => by
            have hxne : x ≠ 0 := by linarith [hx.1]
            field_simp [hxne]
        have hfint' : Integrable f (volume.restrict S) := hprod.congr hEq
        exact hfint hfint'
      rw [show ∫ x in Set.Ioo (1 : ℝ) 3, f x / x = 0 by simpa [S] using hweighted_zero]
      rw [show Real.log (2 / 1 : ℝ) - Real.log (3 / 2 : ℝ) =
          Real.log (4 / 3 : ℝ) by
        rw [← Real.log_div (by norm_num : (2 / 1 : ℝ) ≠ 0)
          (by norm_num : (3 / 2 : ℝ) ≠ 0)]
        norm_num]
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4 / 3)
