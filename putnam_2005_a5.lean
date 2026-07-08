import Mathlib

open Nat Set

noncomputable abbrev putnam_2005_a5_solution : ℝ := Real.pi * (Real.log (Real.sqrt 2) / 4)

/--
Evaluate $\int_0^1 \frac{\ln(x+1)}{x^2+1}\,dx$.
-/
theorem putnam_2005_a5 :
  ∫ x in (0:ℝ)..1, (Real.log (x+1))/(x^2 + 1) = putnam_2005_a5_solution :=
by
  have htangent :
      (∫ x in (0 : ℝ)..1, Real.log (x + 1) / (x ^ 2 + 1)) =
        ∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.tan t + 1) := by
    let g : ℝ → ℝ := fun x => Real.log (x + 1) / (x ^ 2 + 1)
    have hsubst :
        (∫ t in (0 : ℝ)..(Real.pi / 4), (g ∘ Real.tan) t * (1 / Real.cos t ^ 2)) =
          ∫ x in Real.tan (0 : ℝ)..Real.tan (Real.pi / 4), g x := by
      refine intervalIntegral.integral_comp_mul_deriv' (a := (0 : ℝ)) (b := Real.pi / 4)
        (f := Real.tan) (f' := fun t => 1 / Real.cos t ^ 2) (g := g) ?hder ?hcont ?hg
      · intro t ht
        have hle : (0 : ℝ) ≤ Real.pi / 4 := by positivity
        have ht' : t ∈ Icc (0 : ℝ) (Real.pi / 4) := by
          simpa [uIcc_of_le hle] using ht
        have hcost : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo
            ⟨by linarith [ht'.1, Real.pi_pos], by linarith [ht'.2, Real.pi_pos]⟩
        exact Real.hasDerivAt_tan (ne_of_gt hcost)
      · refine continuousOn_const.div ((Real.continuous_cos.continuousOn).pow 2) ?_
        intro t ht
        have hle : (0 : ℝ) ≤ Real.pi / 4 := by positivity
        have ht' : t ∈ Icc (0 : ℝ) (Real.pi / 4) := by
          simpa [uIcc_of_le hle] using ht
        have hcost : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo
            ⟨by linarith [ht'.1, Real.pi_pos], by linarith [ht'.2, Real.pi_pos]⟩
        exact pow_ne_zero 2 (ne_of_gt hcost)
      · dsimp [g]
        apply ContinuousOn.div
        · apply ContinuousOn.log
          · exact continuousOn_id.add continuousOn_const
          · intro x hx
            rcases hx with ⟨t, ht, rfl⟩
            have hle : (0 : ℝ) ≤ Real.pi / 4 := by positivity
            have ht' : t ∈ Icc (0 : ℝ) (Real.pi / 4) := by
              simpa [uIcc_of_le hle] using ht
            have htan_nonneg : 0 ≤ Real.tan t :=
              Real.tan_nonneg_of_nonneg_of_le_pi_div_two ht'.1
                (by linarith [ht'.2, Real.pi_pos])
            linarith
        · exact (continuousOn_id.pow 2).add continuousOn_const
        · intro x hx
          nlinarith [sq_nonneg x]
    calc
      (∫ x in (0 : ℝ)..1, Real.log (x + 1) / (x ^ 2 + 1))
          = ∫ x in Real.tan (0 : ℝ)..Real.tan (Real.pi / 4), g x := by
            simp [g, Real.tan_zero, Real.tan_pi_div_four]
      _ = ∫ t in (0 : ℝ)..(Real.pi / 4), (g ∘ Real.tan) t * (1 / Real.cos t ^ 2) :=
        hsubst.symm
      _ = ∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.tan t + 1) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [g]
        have hle : (0 : ℝ) ≤ Real.pi / 4 := by positivity
        have ht' : t ∈ Icc (0 : ℝ) (Real.pi / 4) := by
          simpa [uIcc_of_le hle] using ht
        have hcost : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo
            ⟨by linarith [ht'.1, Real.pi_pos], by linarith [ht'.2, Real.pi_pos]⟩
        have h1 : (Real.tan t ^ 2 + 1)⁻¹ = Real.cos t ^ 2 := by
          simpa [add_comm] using Real.inv_one_add_tan_sq (ne_of_gt hcost)
        rw [div_eq_mul_inv, h1]
        field_simp [pow_ne_zero 2 (ne_of_gt hcost)]
  have heval :
      (∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.tan t + 1)) =
        Real.pi * (Real.log (Real.sqrt 2) / 4) := by
    have hlogid :
        (∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.tan t + 1)) =
          ∫ t in (0 : ℝ)..(Real.pi / 4),
            Real.log (√2) + Real.log (Real.cos (Real.pi / 4 - t)) - Real.log (Real.cos t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hle : (0 : ℝ) ≤ Real.pi / 4 := by positivity
      have ht' : t ∈ Icc (0 : ℝ) (Real.pi / 4) := by
        simpa [uIcc_of_le hle] using ht
      have hcost : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo
          ⟨by linarith [ht'.1, Real.pi_pos], by linarith [ht'.2, Real.pi_pos]⟩
      have hcosu : 0 < Real.cos (Real.pi / 4 - t) :=
        Real.cos_pos_of_mem_Ioo
          ⟨by linarith [ht'.2, Real.pi_pos], by linarith [ht'.1, Real.pi_pos]⟩
      have hcost_ne : Real.cos t ≠ 0 := ne_of_gt hcost
      have hcosu_ne : Real.cos (Real.pi / 4 - t) ≠ 0 := ne_of_gt hcosu
      have hsqrt_ne : (√2 : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))
      have htan : Real.tan t + 1 = √2 * Real.cos (Real.pi / 4 - t) / Real.cos t := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp [hcost_ne]
        rw [show (Real.pi - 4 * t) / 4 = Real.pi / 4 - t by ring]
        rw [show Real.sin t + Real.cos t = √2 * Real.cos (Real.pi / 4 - t) by
          rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
          ring_nf
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring]
      calc
        Real.log (Real.tan t + 1)
            = Real.log (√2 * Real.cos (Real.pi / 4 - t) / Real.cos t) := by
              rw [htan]
        _ = Real.log (√2 * Real.cos (Real.pi / 4 - t)) - Real.log (Real.cos t) := by
          rw [Real.log_div (mul_ne_zero hsqrt_ne hcosu_ne) hcost_ne]
        _ = Real.log (√2) + Real.log (Real.cos (Real.pi / 4 - t)) - Real.log (Real.cos t) := by
          rw [Real.log_mul hsqrt_ne hcosu_ne]
    have hcos : IntervalIntegrable (fun t : ℝ => Real.log (Real.cos t)) MeasureTheory.volume
        (0 : ℝ) (Real.pi / 4) := by
      simpa [Function.comp_def] using
        (intervalIntegrable_log_cos (a := (0 : ℝ)) (b := Real.pi / 4))
    have hcosSub : IntervalIntegrable (fun t : ℝ => Real.log (Real.cos (Real.pi / 4 - t)))
        MeasureTheory.volume (0 : ℝ) (Real.pi / 4) := by
      have h : IntervalIntegrable (fun t : ℝ => Real.log (Real.cos (Real.pi / 4 - t)))
          MeasureTheory.volume (Real.pi / 4) (0 : ℝ) := by
        simpa [Function.comp_def] using
          (intervalIntegrable_log_cos (a := (0 : ℝ)) (b := Real.pi / 4)).comp_sub_left
            (Real.pi / 4)
      exact h.symm
    have hconst : IntervalIntegrable (fun _ : ℝ => Real.log (√2)) MeasureTheory.volume
        (0 : ℝ) (Real.pi / 4) := by
      exact intervalIntegrable_const
    have hcos_eq :
        (∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.cos (Real.pi / 4 - t))) =
          ∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.cos t) := by
      simp [intervalIntegral.integral_comp_sub_left (fun t => Real.log (Real.cos t))
        (Real.pi / 4)]
    rw [hlogid]
    calc
      (∫ t in (0 : ℝ)..(Real.pi / 4),
          Real.log (√2) + Real.log (Real.cos (Real.pi / 4 - t)) - Real.log (Real.cos t))
          = (∫ t in (0 : ℝ)..(Real.pi / 4),
                Real.log (√2) + Real.log (Real.cos (Real.pi / 4 - t)))
              - ∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.cos t) := by
            rw [intervalIntegral.integral_sub]
            · exact hconst.add hcosSub
            · exact hcos
      _ = (∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (√2))
            + (∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.cos (Real.pi / 4 - t)))
            - ∫ t in (0 : ℝ)..(Real.pi / 4), Real.log (Real.cos t) := by
            rw [intervalIntegral.integral_add]
            · exact hconst
            · exact hcosSub
      _ = Real.pi * (Real.log (Real.sqrt 2) / 4) := by
            rw [hcos_eq]
            simp [intervalIntegral.integral_const]
            ring
  rw [putnam_2005_a5_solution]
  exact htangent.trans heval
