import Mathlib

open Topology Filter

-- Note: There may be multiple possible correct answers.
-- (-1, 2 / Real.pi)
/--
Find a real number $c$ and a positive number $L$ for which $\lim_{r \to \infty} \frac{r^c \int_0^{\pi/2} x^r\sin x\,dx}{\int_0^{\pi/2} x^r\cos x\,dx}=L$.
-/
theorem putnam_2011_a3
: ((-1, 2 / Real.pi) : ℝ × ℝ ).2 > 0 ∧ Tendsto (fun r : ℝ => (r ^ ((-1, 2 / Real.pi) : ℝ × ℝ ).1 * ∫ x in Set.Ioo 0 (Real.pi / 2), x ^ r * Real.sin x) / (∫ x in Set.Ioo 0 (Real.pi / 2), x ^ r * Real.cos x)) atTop (𝓝 ((-1, 2 / Real.pi) : ℝ × ℝ ).2) := by
  constructor
  · positivity
  · change
      Tendsto
        (fun r : ℝ =>
          (r ^ (-1 : ℝ) * ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), x ^ r * Real.sin x) /
            (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), x ^ r * Real.cos x))
        atTop (𝓝 (2 / Real.pi))
    let a : ℝ := Real.pi / 2
    let J : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..a, x ^ s * Real.sin x
    let C : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..a, x ^ s * Real.cos x
    let A : ℝ → ℝ := fun s => J s / (a ^ (s + 1) / (s + 1))
    have ha_pos : 0 < a := by
      dsimp [a]
      positivity
    have ha_nonneg : (0 : ℝ) ≤ a := ha_pos.le
    have ha_le_pi : a ≤ Real.pi := by
      dsimp [a]
      linarith [Real.pi_pos]
    have hsin_a : Real.sin a = 1 := by
      dsimp [a]
      exact Real.sin_pi_div_two
    have hcos_a : Real.cos a = 0 := by
      dsimp [a]
      exact Real.cos_pi_div_two
    have hset_sin :
        ∀ s : ℝ, (∫ x in Set.Ioo (0 : ℝ) a, x ^ s * Real.sin x) = J s := by
      intro s
      dsimp [J]
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [← intervalIntegral.integral_of_le ha_nonneg]
    have hset_cos :
        ∀ s : ℝ, (∫ x in Set.Ioo (0 : ℝ) a, x ^ s * Real.cos x) = C s := by
      intro s
      dsimp [C]
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [← intervalIntegral.integral_of_le ha_nonneg]
    have hcos_id :
        ∀ s : ℝ, 0 ≤ s → C s = (1 / (s + 1)) * J (s + 1) := by
      intro s hs
      have hne : s + 1 ≠ 0 := by linarith
      have hder_cos :
          ∀ x ∈ Set.Ioo (min (0 : ℝ) a) (max (0 : ℝ) a),
            HasDerivAt Real.cos (-Real.sin x) x := by
        intro x hx
        simpa using Real.hasDerivAt_cos x
      have hder_pow :
          ∀ x ∈ Set.Ioo (min (0 : ℝ) a) (max (0 : ℝ) a),
            HasDerivAt (fun y : ℝ => y ^ (s + 1) / (s + 1)) (x ^ s) x := by
        intro x hx
        have hx0 : x ≠ 0 := by
          have hmin : min (0 : ℝ) a = 0 := min_eq_left ha_nonneg
          rw [hmin] at hx
          exact ne_of_gt hx.1
        have h :=
          (Real.hasDerivAt_rpow_const (x := x) (p := s + 1) (Or.inl hx0)).div_const
            (s + 1)
        convert h using 1
        field_simp [hne]
        rw [show s + 1 - 1 = s by ring]
      have hcos_int :
          IntervalIntegrable (fun x : ℝ => -Real.sin x) MeasureTheory.volume (0 : ℝ) a := by
        exact (Real.continuous_sin.neg).intervalIntegrable _ _
      have hpow_int :
          IntervalIntegrable (fun x : ℝ => x ^ s) MeasureTheory.volume (0 : ℝ) a := by
        exact (Real.continuous_rpow_const hs).intervalIntegrable _ _
      have H :=
        intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
          (u := Real.cos) (v := fun y : ℝ => y ^ (s + 1) / (s + 1))
          (u' := fun y : ℝ => -Real.sin y) (v' := fun y : ℝ => y ^ s)
          (a := (0 : ℝ)) (b := a) Real.continuous_cos.continuousOn
          ((Real.continuous_rpow_const (by linarith : 0 ≤ s + 1)).div_const _).continuousOn
          hder_cos hder_pow hcos_int hpow_int
      rw [hcos_a, Real.cos_zero] at H
      simp [hne] at H
      calc
        C s = ∫ x in (0 : ℝ)..a, Real.cos x * x ^ s := by
          dsimp [C]
          apply intervalIntegral.integral_congr
          intro x hx
          ring
        _ = (1 / (s + 1)) * J (s + 1) := by
          rw [H]
          dsimp [J]
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x hx
          ring
    have hsin_id :
        ∀ s : ℝ, 0 ≤ s →
          J s = a ^ (s + 1) / (s + 1) - (1 / (s + 1)) * C (s + 1) := by
      intro s hs
      have hne : s + 1 ≠ 0 := by linarith
      have hder_sin :
          ∀ x ∈ Set.Ioo (min (0 : ℝ) a) (max (0 : ℝ) a),
            HasDerivAt Real.sin (Real.cos x) x := by
        intro x hx
        simpa using Real.hasDerivAt_sin x
      have hder_pow :
          ∀ x ∈ Set.Ioo (min (0 : ℝ) a) (max (0 : ℝ) a),
            HasDerivAt (fun y : ℝ => y ^ (s + 1) / (s + 1)) (x ^ s) x := by
        intro x hx
        have hx0 : x ≠ 0 := by
          have hmin : min (0 : ℝ) a = 0 := min_eq_left ha_nonneg
          rw [hmin] at hx
          exact ne_of_gt hx.1
        have h :=
          (Real.hasDerivAt_rpow_const (x := x) (p := s + 1) (Or.inl hx0)).div_const
            (s + 1)
        convert h using 1
        field_simp [hne]
        rw [show s + 1 - 1 = s by ring]
      have hsin_int :
          IntervalIntegrable (fun x : ℝ => Real.cos x) MeasureTheory.volume (0 : ℝ) a := by
        exact Real.continuous_cos.intervalIntegrable _ _
      have hpow_int :
          IntervalIntegrable (fun x : ℝ => x ^ s) MeasureTheory.volume (0 : ℝ) a := by
        exact (Real.continuous_rpow_const hs).intervalIntegrable _ _
      have H :=
        intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
          (u := Real.sin) (v := fun y : ℝ => y ^ (s + 1) / (s + 1))
          (u' := fun y : ℝ => Real.cos y) (v' := fun y : ℝ => y ^ s)
          (a := (0 : ℝ)) (b := a) Real.continuous_sin.continuousOn
          ((Real.continuous_rpow_const (by linarith : 0 ≤ s + 1)).div_const _).continuousOn
          hder_sin hder_pow hsin_int hpow_int
      rw [hsin_a, Real.sin_zero] at H
      simp [hne] at H
      calc
        J s = ∫ x in (0 : ℝ)..a, Real.sin x * x ^ s := by
          dsimp [J]
          apply intervalIntegral.integral_congr
          intro x hx
          ring
        _ = a ^ (s + 1) / (s + 1) - (1 / (s + 1)) * C (s + 1) := by
          rw [H]
          congr 1
          dsimp [C]
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x hx
          ring
    have hJ_nonneg : ∀ s : ℝ, 0 ≤ J s := by
      intro s
      dsimp [J]
      apply intervalIntegral.integral_nonneg ha_nonneg
      intro x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1 s)
        (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (hx.2.trans ha_le_pi))
    have hJ_le : ∀ s : ℝ, 0 ≤ s → J s ≤ a ^ (s + 1) / (s + 1) := by
      intro s hs
      dsimp [J]
      have hleft_int :
          IntervalIntegrable (fun x : ℝ => x ^ s * Real.sin x) MeasureTheory.volume (0 : ℝ) a := by
        exact ((Real.continuous_rpow_const hs).mul Real.continuous_sin).intervalIntegrable _ _
      have hright_int :
          IntervalIntegrable (fun x : ℝ => x ^ s) MeasureTheory.volume (0 : ℝ) a := by
        exact (Real.continuous_rpow_const hs).intervalIntegrable _ _
      calc
        (∫ x in (0 : ℝ)..a, x ^ s * Real.sin x) ≤ ∫ x in (0 : ℝ)..a, x ^ s := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo ha_nonneg hleft_int hright_int
          intro x hx
          exact mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt hx.1) s) (Real.sin_le_one x)
        _ = a ^ (s + 1) / (s + 1) := by
          rw [integral_rpow (a := (0 : ℝ)) (b := a) (r := s) (Or.inl (by linarith))]
          rw [Real.zero_rpow (by linarith : s + 1 ≠ 0)]
          ring
    have hrec :
        ∀ s : ℝ, 0 ≤ s →
          J s = a ^ (s + 1) / (s + 1) - J (s + 2) / ((s + 1) * (s + 2)) := by
      intro s hs
      rw [hsin_id s hs, hcos_id (s + 1) (by linarith)]
      have harg : s + 1 + 1 = s + 2 := by ring
      rw [harg]
      field_simp [(by linarith : s + 1 ≠ 0), (by linarith : s + 2 ≠ 0)]
    have hE :
        Tendsto (fun s : ℝ => J (s + 2) / ((s + 2) * a ^ (s + 1))) atTop (𝓝 0) := by
      let B : ℝ → ℝ := fun s => a ^ (2 : ℝ) * (s + 2)⁻¹ * (s + 3)⁻¹
      have hB : Tendsto B atTop (𝓝 0) := by
        have h2 : Tendsto (fun s : ℝ => (s + 2)⁻¹) atTop (𝓝 0) := by
          exact tendsto_inv_atTop_zero.comp
            (Filter.tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id)
        have h3 : Tendsto (fun s : ℝ => (s + 3)⁻¹) atTop (𝓝 0) := by
          exact tendsto_inv_atTop_zero.comp
            (Filter.tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_id)
        simpa [B] using (tendsto_const_nhds.mul h2).mul h3
      apply squeeze_zero' (t₀ := atTop) ?_ ?_ hB
      · exact (eventually_ge_atTop (0 : ℝ)).mono fun s hs => by
          have hnum : 0 ≤ J (s + 2) := hJ_nonneg (s + 2)
          have hden : 0 ≤ (s + 2) * a ^ (s + 1) := by positivity
          exact div_nonneg hnum hden
      · exact (eventually_ge_atTop (0 : ℝ)).mono fun s hs => by
          have hnum_le : J (s + 2) ≤ a ^ (s + 3) / (s + 3) := by
            convert hJ_le (s + 2) (by linarith) using 2
            · ring_nf
            · ring_nf
          have hden_nonneg : 0 ≤ (s + 2) * a ^ (s + 1) := by positivity
          calc
            J (s + 2) / ((s + 2) * a ^ (s + 1))
                ≤ (a ^ (s + 3) / (s + 3)) / ((s + 2) * a ^ (s + 1)) :=
                  div_le_div_of_nonneg_right hnum_le hden_nonneg
            _ = B s := by
              have hs2 : s + 2 ≠ 0 := by linarith
              have hs3 : s + 3 ≠ 0 := by linarith
              have hpow : a ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos ha_pos (s + 1)).ne'
              have hpow_add : a ^ (s + 3) = a ^ (s + 1) * a ^ (2 : ℝ) := by
                convert Real.rpow_add ha_pos (s + 1) (2 : ℝ) using 2
                · ring
              rw [hpow_add]
              change
                (a ^ (s + 1) * a ^ (2 : ℝ) / (s + 3)) / ((s + 2) * a ^ (s + 1)) =
                  a ^ (2 : ℝ) * (s + 2)⁻¹ * (s + 3)⁻¹
              field_simp [hs2, hs3, hpow]
    have hA : Tendsto A atTop (𝓝 1) := by
      dsimp [A]
      have hEq :
          (fun s : ℝ => J s / (a ^ (s + 1) / (s + 1))) =ᶠ[atTop]
            (fun s : ℝ => (1 : ℝ) - J (s + 2) / ((s + 2) * a ^ (s + 1))) := by
        exact (eventually_ge_atTop (0 : ℝ)).mono fun s hs => by
          change
            J s / (a ^ (s + 1) / (s + 1)) =
              1 - J (s + 2) / ((s + 2) * a ^ (s + 1))
          have hs1 : s + 1 ≠ 0 := by linarith
          have hs2 : s + 2 ≠ 0 := by linarith
          have hpow : a ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos ha_pos (s + 1)).ne'
          rw [hrec s hs]
          field_simp [hs1, hs2, hpow]
      have ht :
          Tendsto (fun s : ℝ => (1 : ℝ) - J (s + 2) / ((s + 2) * a ^ (s + 1))) atTop
            (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub hE
      simpa using Tendsto.congr' hEq.symm ht
    have hA_shift : Tendsto (fun s : ℝ => A (s + 1)) atTop (𝓝 1) := by
      exact hA.comp (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    have hfactor : Tendsto (fun s : ℝ => (s + 2) / s) atTop (𝓝 1) := by
      have hEq : (fun s : ℝ => (s + 2) / s) =ᶠ[atTop] fun s : ℝ => (1 : ℝ) + 2 / s := by
        exact (eventually_gt_atTop (0 : ℝ)).mono fun s hs => by
          field_simp [ne_of_gt hs]
      have hlim : Tendsto (fun s : ℝ => (1 : ℝ) + 2 / s) atTop (𝓝 (1 + 0)) := by
        exact tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
      simpa using Tendsto.congr' hEq.symm hlim
    have hmain :
        Tendsto (fun s : ℝ => ((s + 2) / s) * (1 / a) * (A s / A (s + 1))) atTop
          (𝓝 (2 / Real.pi)) := by
      have hAdiv : Tendsto (fun s : ℝ => A s / A (s + 1)) atTop (𝓝 (1 / 1 : ℝ)) := by
        exact hA.div hA_shift one_ne_zero
      have hprod := (hfactor.mul (tendsto_const_nhds (x := 1 / a))).mul hAdiv
      dsimp [a] at hprod ⊢
      simpa [one_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hprod
    have hfinal_eq :
        (fun s : ℝ =>
            (s ^ (-1 : ℝ) * ∫ x in Set.Ioo (0 : ℝ) a, x ^ s * Real.sin x) /
              (∫ x in Set.Ioo (0 : ℝ) a, x ^ s * Real.cos x)) =ᶠ[atTop]
          (fun s : ℝ => ((s + 2) / s) * (1 / a) * (A s / A (s + 1))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ),
        hA_shift.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with s hs hA_ne
      rw [hset_sin s, hset_cos s, hcos_id s hs.le]
      dsimp [A] at hA_ne ⊢
      change
        (s ^ (-1 : ℝ) * J s) / ((1 / (s + 1)) * J (s + 1)) =
          ((s + 2) / s) * (1 / a) *
            ((J s / (a ^ (s + 1) / (s + 1))) /
              (J (s + 1) / (a ^ ((s + 1) + 1) / ((s + 1) + 1))))
      have hs_ne : s ≠ 0 := ne_of_gt hs
      have hs1 : s + 1 ≠ 0 := by linarith
      have hs2 : s + 2 ≠ 0 := by linarith
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hpow0 : a ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos ha_pos (s + 1)).ne'
      have hpow_add : a ^ (s + 2) = a ^ (s + 1) * a := by
        convert Real.rpow_add ha_pos (s + 1) (1 : ℝ) using 2
        · ring
        · simp [Real.rpow_one]
      have hJ1_ne : J (s + 1) ≠ 0 := by
        intro hJ
        apply hA_ne
        simp [hJ]
      rw [Real.rpow_neg_one]
      rw [show (s + 1) + 1 = s + 2 by ring]
      rw [hpow_add]
      field_simp [hs_ne, hs1, hs2, ha_ne, hpow0, hJ1_ne]
    exact Tendsto.congr' hfinal_eq.symm hmain
