import Mathlib

open Nat Set

-- Real.pi * (Real.log 2) / 8
/--
Evaluate $\int_0^1 \frac{\ln(x+1)}{x^2+1}\,dx$.
-/
theorem putnam_2005_a5 :
  ∫ x in (0:ℝ)..1, (Real.log (x+1))/(x^2 + 1) = ((Real.pi * (Real.log 2) / 8) : ℝ ) := by
  have hsubst :
      (∫ x in (0:ℝ)..1, (Real.log (x + 1)) / (x ^ 2 + 1)) =
        ∫ t in (0:ℝ)..Real.pi / 4, Real.log (1 + Real.tan t) := by
    have hderiv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := by
      intro x _hx
      exact Real.hasDerivAt_arctan x
    have hderivCont : ContinuousOn (fun x : ℝ => 1 / (1 + x ^ 2)) (uIcc (0:ℝ) 1) := by
      apply Continuous.continuousOn
      exact continuous_const.div₀ (continuous_const.add (continuous_id.pow 2))
        (fun x : ℝ => by nlinarith [sq_nonneg x])
    have hg : ContinuousOn (fun t : ℝ => Real.log (1 + Real.tan t))
        (Real.arctan '' uIcc (0:ℝ) 1) := by
      have htan : ContinuousOn Real.tan (Real.arctan '' uIcc (0:ℝ) 1) := by
        apply Real.continuousOn_tan.mono
        intro y hy
        rcases hy with ⟨x, _hx, rfl⟩
        exact (Real.cos_arctan_pos x).ne'
      have hsum : ContinuousOn (fun t : ℝ => 1 + Real.tan t)
          (Real.arctan '' uIcc (0:ℝ) 1) := by
        exact continuousOn_const.add htan
      exact hsum.log (by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        rw [Real.tan_arctan]
        have hx0 : 0 ≤ x := by
          have h01 : (0 : ℝ) ≤ 1 := by norm_num
          rw [uIcc_of_le h01] at hx
          exact hx.1
        exact ne_of_gt (by linarith : 0 < 1 + x))
    have hsub := intervalIntegral.integral_comp_mul_deriv' (a := (0:ℝ)) (b := 1)
      (f := Real.arctan) (f' := fun x : ℝ => 1 / (1 + x ^ 2))
      (g := fun t : ℝ => Real.log (1 + Real.tan t)) hderiv hderivCont hg
    simpa [Real.arctan_zero, Real.arctan_one, Real.tan_arctan, div_eq_mul_inv,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hsub
  have htrig :
      (∫ x in (0:ℝ)..Real.pi / 4, Real.log (1 + Real.tan x)) =
        Real.pi * Real.log 2 / 8 := by
    have hdecomp :
        (∫ x in (0:ℝ)..Real.pi / 4, Real.log (1 + Real.tan x)) =
        ∫ x in (0:ℝ)..Real.pi / 4,
          Real.log (√2) + Real.log (Real.cos (x - Real.pi / 4)) - Real.log (Real.cos x) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hpi4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
      rw [uIcc_of_le hpi4] at ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ Real.pi / 4 := ht.2
      have hcos : Real.cos t ≠ 0 := by
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos], by linarith [ht1, Real.pi_pos]⟩)
      have hcosShift : Real.cos (t - Real.pi / 4) ≠ 0 := by
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [ht0, Real.pi_pos], by linarith [ht1, Real.pi_pos]⟩)
      have hsqrt : (√2 : ℝ) ≠ 0 := by positivity
      have harg : 1 + Real.tan t = (√2 * Real.cos (t - Real.pi / 4)) / Real.cos t := by
        rw [Real.tan_eq_sin_div_cos, Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
        field_simp [hcos]
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      change Real.log (1 + Real.tan t) =
        Real.log (√2) + Real.log (Real.cos (t - Real.pi / 4)) - Real.log (Real.cos t)
      rw [harg, Real.log_div (mul_ne_zero hsqrt hcosShift) hcos,
        Real.log_mul hsqrt hcosShift]
    have hconst : IntervalIntegrable (fun _ : ℝ => Real.log (√2)) MeasureTheory.volume
        0 (Real.pi / 4) := by
      exact intervalIntegrable_const
    have hshiftInt : IntervalIntegrable
        (fun x : ℝ => Real.log (Real.cos (x - Real.pi / 4))) MeasureTheory.volume
        0 (Real.pi / 4) := by
      have h := (intervalIntegrable_log_cos (a := -(Real.pi / 4)) (b := 0)).comp_sub_right
        (Real.pi / 4)
      simpa using h
    have hcosInt : IntervalIntegrable (fun x : ℝ => Real.log (Real.cos x)) MeasureTheory.volume
        0 (Real.pi / 4) := by
      exact intervalIntegrable_log_cos
    have hcancel :
        (∫ x in (0:ℝ)..Real.pi / 4, Real.log (Real.cos (x - Real.pi / 4))) =
          ∫ x in (0:ℝ)..Real.pi / 4, Real.log (Real.cos x) := by
      calc
        (∫ x in (0:ℝ)..Real.pi / 4, Real.log (Real.cos (x - Real.pi / 4)))
            = ∫ x in -(Real.pi / 4)..0, Real.log (Real.cos x) := by
              rw [intervalIntegral.integral_comp_sub_right
                (fun x : ℝ => Real.log (Real.cos x)) (Real.pi / 4)]
              ring_nf
        _ = ∫ x in (0:ℝ)..Real.pi / 4, Real.log (Real.cos x) := by
              have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := Real.pi / 4)
                (fun x : ℝ => Real.log (Real.cos x))
              simpa [Real.cos_neg] using h.symm
    calc
      (∫ x in (0:ℝ)..Real.pi / 4, Real.log (1 + Real.tan x))
          = ∫ x in (0:ℝ)..Real.pi / 4,
            Real.log (√2) + Real.log (Real.cos (x - Real.pi / 4)) -
              Real.log (Real.cos x) := hdecomp
      _ = (∫ x in (0:ℝ)..Real.pi / 4, Real.log (√2))
            + (∫ x in (0:ℝ)..Real.pi / 4, Real.log (Real.cos (x - Real.pi / 4)))
            - (∫ x in (0:ℝ)..Real.pi / 4, Real.log (Real.cos x)) := by
          rw [intervalIntegral.integral_sub (hconst.add hshiftInt) hcosInt,
            intervalIntegral.integral_add hconst hshiftInt]
      _ = (Real.pi / 4) * Real.log (√2) := by
          rw [intervalIntegral.integral_const, hcancel]
          simp [smul_eq_mul]
      _ = Real.pi * Real.log 2 / 8 := by
          rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
  exact hsubst.trans htrig
