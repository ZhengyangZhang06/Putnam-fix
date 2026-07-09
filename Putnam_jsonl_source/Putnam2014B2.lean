import Mathlib

open Topology Filter Nat

-- Note: uses (ℝ → ℝ) instead of (Set.Icc (1 : ℝ) 3 → ℝ)
-- Real.log (4 / 3)
/--
Suppose that \( f \) is a function on the interval \([1,3]\) such that \(-1 \leq f(x) \leq 1\) for all \( x \) and \( \int_{1}^{3} f(x) \, dx = 0 \). How large can \(\int_{1}^{3} \frac{f(x)}{x} \, dx \) be?
-/
theorem putnam_2014_b2 :
  IsGreatest {t | ∃ f : ℝ → ℝ,
    (∀ x : Set.Icc (1 : ℝ) 3, -1 ≤ f x ∧ f x ≤ 1) ∧
    (∫ x in Set.Ioo 1 3, f x = 0) ∧
    (∫ x in Set.Ioo 1 3, (f x) / x) = t}
  ((Real.log (4 / 3)) : ℝ ) := by
  classical
  open MeasureTheory in
  have integral_inv_Ioo : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      (∫ x in Set.Ioo a b, x⁻¹) = Real.log b - Real.log a := by
    intro a b ha hab
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hab]
    have hderiv : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ Real.log x := by
      intro x hx
      have hxI : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hx
      exact Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le ha hxI.1))
    have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a b) := by
      refine continuousOn_id.inv₀ ?_
      intro x hx
      have hxI : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hx
      exact ne_of_gt (lt_of_lt_of_le ha hxI.1)
    have hint : IntervalIntegrable (deriv Real.log) volume a b := by
      simpa [Real.deriv_log] using hcont.intervalIntegrable (μ := volume)
    have hftc := intervalIntegral.integral_deriv_eq_sub (f := Real.log) hderiv hint
    simpa [Real.deriv_log] using hftc
  have intervalIntegrable_inv : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b := by
    intro a b ha hab
    have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a b) := by
      refine continuousOn_id.inv₀ ?_
      intro x hx
      have hxI : x ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hx
      exact ne_of_gt (lt_of_lt_of_le ha hxI.1)
    exact hcont.intervalIntegrable (μ := volume)
  have hlog : (2 : ℝ) * Real.log 2 - Real.log 3 = Real.log (4 / 3 : ℝ) := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = 2 * 2 by norm_num]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hAbsIntegral :
      (∫ x in Set.Ioo (1 : ℝ) 3, |x⁻¹ - (1 / 2 : ℝ)|) =
        Real.log (4 / 3 : ℝ) := by
    have hAbs12 :
        IntervalIntegrable (fun x : ℝ => |x⁻¹ - (1 / 2 : ℝ)|) volume (1 : ℝ) 2 := by
      have hcont : ContinuousOn (fun x : ℝ => |x⁻¹ - (1 / 2 : ℝ)|)
          (Set.uIcc (1 : ℝ) 2) := by
        have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc (1 : ℝ) 2) := by
          refine continuousOn_id.inv₀ ?_
          intro x hx
          have hxI : x ∈ Set.Icc (1 : ℝ) 2 := by
            simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one hxI.1)
        exact (hinv.sub continuousOn_const).abs
      exact hcont.intervalIntegrable (μ := volume)
    have hAbs23 :
        IntervalIntegrable (fun x : ℝ => |x⁻¹ - (1 / 2 : ℝ)|) volume (2 : ℝ) 3 := by
      have hcont : ContinuousOn (fun x : ℝ => |x⁻¹ - (1 / 2 : ℝ)|)
          (Set.uIcc (2 : ℝ) 3) := by
        have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc (2 : ℝ) 3) := by
          refine continuousOn_id.inv₀ ?_
          intro x hx
          have hxI : x ∈ Set.Icc (2 : ℝ) 3 := by
            simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
          exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hxI.1)
        exact (hinv.sub continuousOn_const).abs
      exact hcont.intervalIntegrable (μ := volume)
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    rw [← intervalIntegral.integral_add_adjacent_intervals hAbs12 hAbs23]
    have hcongr12 :
        (∫ x in (1 : ℝ)..2, |x⁻¹ - (1 / 2 : ℝ)|) =
          ∫ x in (1 : ℝ)..2, x⁻¹ - (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Set.Icc (1 : ℝ) 2 := by
        simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxI.1
      have hinv : (1 / (2 : ℝ)) ≤ 1 / x := one_div_le_one_div_of_le hxpos hxI.2
      have hnonneg : 0 ≤ x⁻¹ - (1 / 2 : ℝ) := by
        rw [show x⁻¹ = 1 / x by rw [one_div]]
        norm_num at hinv ⊢
        linarith
      exact abs_of_nonneg hnonneg
    have hcongr23 :
        (∫ x in (2 : ℝ)..3, |x⁻¹ - (1 / 2 : ℝ)|) =
          ∫ x in (2 : ℝ)..3, (1 / 2 : ℝ) - x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Set.Icc (2 : ℝ) 3 := by
        simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
      have hinv : 1 / x ≤ 1 / (2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hxI.1
      have hnonpos : x⁻¹ - (1 / 2 : ℝ) ≤ 0 := by
        rw [show x⁻¹ = 1 / x by rw [one_div]]
        norm_num at hinv ⊢
        linarith
      change |x⁻¹ - (1 / 2 : ℝ)| = (1 / 2 : ℝ) - x⁻¹
      rw [abs_of_nonpos hnonpos]
      ring
    rw [hcongr12, hcongr23]
    have hinv12 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (1 : ℝ) 2 :=
      intervalIntegrable_inv (by norm_num) (by norm_num)
    have hinv23 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (2 : ℝ) 3 :=
      intervalIntegrable_inv (by norm_num) (by norm_num)
    rw [intervalIntegral.integral_sub hinv12 intervalIntegral.intervalIntegrable_const]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const hinv23]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const]
    have hI12 : (∫ x in (1 : ℝ)..2, x⁻¹) = Real.log 2 - Real.log 1 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact integral_inv_Ioo (by norm_num) (by norm_num)
    have hI23 : (∫ x in (2 : ℝ)..3, x⁻¹) = Real.log 3 - Real.log 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 3)]
      rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact integral_inv_Ioo (by norm_num) (by norm_num)
    rw [hI12, hI23]
    simp [Real.log_one]
    linarith
  let s : Set ℝ := Set.Ioo (1 : ℝ) 3
  let u : Set ℝ := Set.Ioo (1 : ℝ) 2
  let f₀ : ℝ → ℝ := fun x => u.indicator (fun _ : ℝ => (2 : ℝ)) x - 1
  have hf₀_bound : ∀ x : Set.Icc (1 : ℝ) 3, -1 ≤ f₀ x ∧ f₀ x ≤ 1 := by
    intro x
    change -1 ≤ u.indicator (fun _ : ℝ => (2 : ℝ)) (x : ℝ) - 1 ∧
      u.indicator (fun _ : ℝ => (2 : ℝ)) (x : ℝ) - 1 ≤ 1
    by_cases hx : (x : ℝ) ∈ u
    · rw [Set.indicator_of_mem hx]
      norm_num
    · rw [Set.indicator_apply, if_neg hx]
      norm_num
  have hf₀_zero : (∫ x in Set.Ioo (1 : ℝ) 3, f₀ x) = 0 := by
    have hconst1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s volume := by
      apply integrableOn_const
      · dsimp [s]
        rw [Real.volume_Ioo]
        norm_num
      · simp
    have hconst2 : IntegrableOn (fun _ : ℝ => (2 : ℝ)) s volume := by
      apply integrableOn_const
      · dsimp [s]
        rw [Real.volume_Ioo]
        norm_num
      · simp
    have hind : IntegrableOn (u.indicator (fun _ : ℝ => (2 : ℝ))) s volume := by
      exact hconst2.indicator measurableSet_Ioo
    change (∫ x in s, u.indicator (fun _ : ℝ => (2 : ℝ)) x - 1) = 0
    rw [MeasureTheory.integral_sub hind hconst1]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo]
    rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const]
    dsimp [s, u]
    rw [Set.Ioo_inter_Ioo]
    rw [Real.volume_real_Ioo, Real.volume_real_Ioo]
    norm_num
  have hf₀_weight : (∫ x in Set.Ioo (1 : ℝ) 3, f₀ x / x) = Real.log (4 / 3) := by
    have hinv_s : IntegrableOn (fun x : ℝ => x⁻¹) s volume := by
      have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) 3) := by
        refine continuousOn_id.inv₀ ?_
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
      exact hcont.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
    have htwoInv_s : IntegrableOn (fun x : ℝ => (2 : ℝ) / x) s volume := by
      simpa [div_eq_mul_inv] using hinv_s.const_mul 2
    have hindInv : IntegrableOn (u.indicator (fun x : ℝ => (2 : ℝ) / x)) s volume := by
      exact htwoInv_s.indicator measurableSet_Ioo
    have hrewrite :
        (∫ x in s, ((u.indicator (fun _ : ℝ => (2 : ℝ)) x - 1) / x)) =
          ∫ x in s, u.indicator (fun x : ℝ => (2 : ℝ) / x) x - x⁻¹ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      by_cases hxu : x ∈ u
      · simp [Set.indicator, hxu, div_eq_mul_inv]
        ring
      · simp [Set.indicator, hxu, div_eq_mul_inv]
    change (∫ x in s, (u.indicator (fun _ : ℝ => (2 : ℝ)) x - 1) / x) =
      Real.log (4 / 3)
    rw [hrewrite]
    rw [MeasureTheory.integral_sub hindInv hinv_s]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo]
    dsimp [s, u]
    rw [Set.Ioo_inter_Ioo]
    have h12 :
        (∫ x in Set.Ioo (max (1 : ℝ) 1) (min (3 : ℝ) 2), (2 : ℝ) / x) =
          2 * Real.log 2 := by
      calc
        (∫ x in Set.Ioo (max (1 : ℝ) 1) (min (3 : ℝ) 2), (2 : ℝ) / x)
            = ∫ x in Set.Ioo (1 : ℝ) 2, (2 : ℝ) * x⁻¹ := by
              norm_num [div_eq_mul_inv]
        _ = 2 * ∫ x in Set.Ioo (1 : ℝ) 2, x⁻¹ := by
              rw [MeasureTheory.integral_const_mul]
        _ = 2 * Real.log 2 := by
              rw [integral_inv_Ioo (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)]
              simp [Real.log_one]
    have h13 : (∫ x in Set.Ioo (1 : ℝ) 3, x⁻¹) = Real.log 3 := by
      rw [integral_inv_Ioo (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 3)]
      simp [Real.log_one]
    rw [h12, h13]
    exact hlog
  constructor
  · exact ⟨f₀, hf₀_bound, hf₀_zero, hf₀_weight⟩
  · change ∀ t : ℝ, t ∈ {t | ∃ f : ℝ → ℝ,
        (∀ x : Set.Icc (1 : ℝ) 3, -1 ≤ f x ∧ f x ≤ 1) ∧
        (∫ x in Set.Ioo 1 3, f x = 0) ∧
        (∫ x in Set.Ioo 1 3, (f x) / x) = t} →
        t ≤ Real.log (4 / 3)
    intro t ht
    obtain ⟨f, hfprops⟩ := ht
    have hbound : ∀ x : Set.Icc (1 : ℝ) 3, -1 ≤ f x ∧ f x ≤ 1 := hfprops.1
    have hzero : (∫ x in Set.Ioo 1 3, f x) = 0 := hfprops.2.1
    have hweight : (∫ x in Set.Ioo 1 3, f x / x) = t := hfprops.2.2
    have hzero_sf : (∫ x in Set.Ioo (1 : ℝ) 3, f x) = 0 := hzero
    have hle : (∫ x in Set.Ioo (1 : ℝ) 3, f x / x) ≤ Real.log (4 / 3 : ℝ) := by
      by_cases hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioo (1 : ℝ) 3))
      · have hsfinite : volume (Set.Ioo (1 : ℝ) 3) < ⊤ := by
          rw [Real.volume_Ioo]
          norm_num
        have hnorm_bound : ∀ᵐ x ∂volume.restrict (Set.Ioo (1 : ℝ) 3), ‖f x‖ ≤ (1 : ℝ) := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          have hb := hbound ⟨x, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
          rw [Real.norm_eq_abs]
          exact abs_le.mpr hb
        have hfint : IntegrableOn f (Set.Ioo (1 : ℝ) 3) volume :=
          IntegrableOn.of_bound hsfinite hmeas 1 hnorm_bound
        have hinv_asm : AEStronglyMeasurable (fun x : ℝ => x⁻¹) (volume.restrict (Set.Ioo (1 : ℝ) 3)) := by
          have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioo (1 : ℝ) 3) := by
            refine continuousOn_id.inv₀ ?_
            intro x hx
            exact ne_of_gt (lt_trans zero_lt_one hx.1)
          exact hcont.aestronglyMeasurable measurableSet_Ioo
        have hcoeff_asm :
            AEStronglyMeasurable (fun x : ℝ => x⁻¹ - (1 / 2 : ℝ))
              (volume.restrict (Set.Ioo (1 : ℝ) 3)) := by
          exact hinv_asm.sub aestronglyMeasurable_const
        have hprod_asm :
            AEStronglyMeasurable (fun x : ℝ => f x * (x⁻¹ - (1 / 2 : ℝ)))
              (volume.restrict (Set.Ioo (1 : ℝ) 3)) := by
          simpa [Pi.mul_apply] using hmeas.mul hcoeff_asm
        have hprod_bound :
            ∀ᵐ x ∂volume.restrict (Set.Ioo (1 : ℝ) 3), ‖f x * (x⁻¹ - (1 / 2 : ℝ))‖ ≤ (1 : ℝ) := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          have hb := hbound ⟨x, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
          have hfx_abs : |f x| ≤ (1 : ℝ) := abs_le.mpr hb
          have hxpos : 0 < x := lt_trans zero_lt_one hx.1
          have hcoeff_abs : |x⁻¹ - (1 / 2 : ℝ)| ≤ (1 : ℝ) := by
            have hxinv_nonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
            have hxinv_le_one : x⁻¹ ≤ (1 : ℝ) := by
              have hxone : (1 : ℝ) ≤ x := le_of_lt hx.1
              have htmp : 1 / x ≤ 1 / (1 : ℝ) :=
                one_div_le_one_div_of_le zero_lt_one hxone
              simpa [one_div] using htmp
            rw [abs_le]
            constructor <;> linarith
          calc
            ‖f x * (x⁻¹ - (1 / 2 : ℝ))‖ =
                |f x| * |x⁻¹ - (1 / 2 : ℝ)| := by
              simp [Real.norm_eq_abs]
            _ ≤ 1 * 1 := mul_le_mul hfx_abs hcoeff_abs (abs_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        have hprod_int :
            IntegrableOn (fun x : ℝ => f x * (x⁻¹ - (1 / 2 : ℝ))) (Set.Ioo (1 : ℝ) 3) volume :=
          IntegrableOn.of_bound hsfinite hprod_asm 1 hprod_bound
        have habs_int :
            IntegrableOn (fun x : ℝ => |x⁻¹ - (1 / 2 : ℝ)|) (Set.Ioo (1 : ℝ) 3) volume := by
          have hcont : ContinuousOn (fun x : ℝ => |x⁻¹ - (1 / 2 : ℝ)|)
              (Set.Icc (1 : ℝ) 3) := by
            have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) 3) := by
              refine continuousOn_id.inv₀ ?_
              intro x hx
              exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
            exact (hinv.sub continuousOn_const).abs
          exact hcont.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
        have hhalf_int : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * f x) (Set.Ioo (1 : ℝ) 3) volume := by
          exact hfint.const_mul (1 / 2 : ℝ)
        have hrewrite :
            (∫ x in Set.Ioo (1 : ℝ) 3, f x / x) =
              ∫ x in Set.Ioo (1 : ℝ) 3, f x * (x⁻¹ - (1 / 2 : ℝ)) := by
          have hpoint : Set.EqOn (fun x : ℝ => f x / x)
              (fun x : ℝ => f x * (x⁻¹ - (1 / 2 : ℝ)) + (1 / 2 : ℝ) * f x) (Set.Ioo (1 : ℝ) 3) := by
            intro x hx
            have hxne : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx.1)
            field_simp [hxne]
            ring
          calc
            (∫ x in Set.Ioo (1 : ℝ) 3, f x / x) =
                ∫ x in Set.Ioo (1 : ℝ) 3, f x * (x⁻¹ - (1 / 2 : ℝ)) + (1 / 2 : ℝ) * f x := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpoint
            _ = (∫ x in Set.Ioo (1 : ℝ) 3, f x * (x⁻¹ - (1 / 2 : ℝ))) +
                  ∫ x in Set.Ioo (1 : ℝ) 3, (1 / 2 : ℝ) * f x := by
              rw [MeasureTheory.integral_add hprod_int hhalf_int]
            _ = (∫ x in Set.Ioo (1 : ℝ) 3, f x * (x⁻¹ - (1 / 2 : ℝ))) +
                  (1 / 2 : ℝ) * ∫ x in Set.Ioo (1 : ℝ) 3, f x := by
              rw [MeasureTheory.integral_const_mul]
            _ = ∫ x in Set.Ioo (1 : ℝ) 3, f x * (x⁻¹ - (1 / 2 : ℝ)) := by
              rw [hzero_sf]
              ring
        have hmono :
            (∫ x in Set.Ioo (1 : ℝ) 3, f x * (x⁻¹ - (1 / 2 : ℝ))) ≤
              ∫ x in Set.Ioo (1 : ℝ) 3, |x⁻¹ - (1 / 2 : ℝ)| := by
          apply MeasureTheory.setIntegral_mono_on hprod_int habs_int measurableSet_Ioo
          intro x hx
          have hb := hbound ⟨x, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
          have hfx_abs : |f x| ≤ (1 : ℝ) := abs_le.mpr hb
          calc
            f x * (x⁻¹ - (1 / 2 : ℝ)) ≤ |f x * (x⁻¹ - (1 / 2 : ℝ))| :=
              le_abs_self _
            _ = |f x| * |x⁻¹ - (1 / 2 : ℝ)| := abs_mul _ _
            _ ≤ 1 * |x⁻¹ - (1 / 2 : ℝ)| :=
              mul_le_mul_of_nonneg_right hfx_abs (abs_nonneg _)
            _ = |x⁻¹ - (1 / 2 : ℝ)| := by ring
        calc
          (∫ x in Set.Ioo (1 : ℝ) 3, f x / x) = ∫ x in Set.Ioo (1 : ℝ) 3, f x / x := rfl
          _ = ∫ x in Set.Ioo (1 : ℝ) 3, f x * (x⁻¹ - (1 / 2 : ℝ)) := hrewrite
          _ ≤ ∫ x in Set.Ioo (1 : ℝ) 3, |x⁻¹ - (1 / 2 : ℝ)| := hmono
          _ = Real.log (4 / 3 : ℝ) := by simpa using hAbsIntegral
      · have hquot_not :
            ¬ AEStronglyMeasurable (fun x : ℝ => f x / x) (volume.restrict (Set.Ioo (1 : ℝ) 3)) := by
          intro hq
          apply hmeas
          have hxasm : AEStronglyMeasurable (fun x : ℝ => x) (volume.restrict (Set.Ioo (1 : ℝ) 3)) := by
            simpa using
              (continuous_id : Continuous (fun x : ℝ => x)).aestronglyMeasurable
                (μ := volume.restrict (Set.Ioo (1 : ℝ) 3))
          have hprod : AEStronglyMeasurable (fun x : ℝ => (f x / x) * x)
              (volume.restrict (Set.Ioo (1 : ℝ) 3)) := by
            simpa [Pi.mul_apply] using hq.mul hxasm
          refine hprod.congr ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          have hxne : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx.1)
          field_simp [hxne]
        have hzeroquot : (∫ x in Set.Ioo (1 : ℝ) 3, f x / x) = 0 :=
          MeasureTheory.integral_non_aestronglyMeasurable hquot_not
        calc
          (∫ x in Set.Ioo (1 : ℝ) 3, f x / x) = ∫ x in Set.Ioo (1 : ℝ) 3, f x / x := rfl
          _ = 0 := hzeroquot
          _ ≤ Real.log (4 / 3 : ℝ) :=
            Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4 / 3)
    linarith
