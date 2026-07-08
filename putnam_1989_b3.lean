import Mathlib

open Nat Filter Topology MeasureTheory
open scoped BigOperators Topology

noncomputable abbrev putnam_1989_b3_solution : ℕ → ℝ → ℝ :=
  fun n μ0 =>
    μ0 * ∏ k ∈ Finset.Icc 1 n,
      ((k : ℝ) / (3 - 6 / (2 : ℝ) ^ (k + 1)))

private lemma putnam_1989_b3_integrable_bound (n : ℕ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-√x)) (Set.Ioi 0) := by
  have hs0 : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le (2 * n + 1)
  have hs : (-1 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by linarith
  have hbase :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ ((2 * n + 1 : ℕ) : ℝ) * Real.exp (-x ^ (1 : ℝ)))
        (Set.Ioi 0) := by
    exact integrableOn_rpow_mul_exp_neg_rpow (p := (1 : ℝ))
      (s := ((2 * n + 1 : ℕ) : ℝ)) hs (by norm_num)
  have hleft :
      MeasureTheory.IntegrableOn
        (fun x : ℝ =>
          x ^ ((2 : ℝ) - 1) •
            ((x ^ (2 : ℝ)) ^ n * Real.exp (-√(x ^ (2 : ℝ)))))
        (Set.Ioi 0) := by
    refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [Real.rpow_two, Real.sqrt_sq_eq_abs, abs_of_pos hx]
    rw [show x ^ ((2 * n + 1 : ℕ) : ℝ) = x ^ (2 * n + 1 : ℕ) by
      rw [Real.rpow_natCast]]
    ring
  exact (MeasureTheory.integrableOn_Ioi_comp_rpow_iff'
    (fun x : ℝ => x ^ n * Real.exp (-√x)) (by norm_num : (2 : ℝ) ≠ 0)).mp hleft

private lemma putnam_1989_b3_tendsto_bound (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-√x)) atTop (𝓝 0) := by
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2 * n : ℕ) : ℝ) (1 : ℝ)
      (by norm_num)).comp Real.tendsto_sqrt_atTop
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [show (√x) ^ ((2 * n : ℕ) : ℝ) = (√x) ^ (2 * n : ℕ) by
    rw [Real.rpow_natCast]]
  rw [pow_mul]
  rw [show √x ^ 2 = x by rw [Real.sq_sqrt hx]]
  simp

private lemma putnam_1989_b3_integrable_moment
    (f : ℝ → ℝ) (hfdiff : Differentiable ℝ f)
    (hdecay : ∀ x ≥ 0, |f x| ≤ Real.exp (-√x)) (n : ℕ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ n * f x) (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (putnam_1989_b3_integrable_bound n) ?_ ?_
  · exact (((continuous_id.pow n).mul hfdiff.continuous).aestronglyMeasurable)
  · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    calc
      ‖x ^ n * f x‖ = |x ^ n * f x| := Real.norm_eq_abs _
      _ = x ^ n * |f x| := by rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 n)]
      _ ≤ x ^ n * Real.exp (-√x) := by
        gcongr
        exact hdecay x hx0

private lemma putnam_1989_b3_tendsto_moment_atTop
    (f : ℝ → ℝ) (hdecay : ∀ x ≥ 0, |f x| ≤ Real.exp (-√x)) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * f x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (putnam_1989_b3_tendsto_bound n)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  calc
    ‖x ^ n * f x‖ = |x ^ n * f x| := Real.norm_eq_abs _
    _ = x ^ n * |f x| := by rw [abs_mul, abs_of_nonneg (pow_nonneg hx n)]
    _ ≤ x ^ n * Real.exp (-√x) := by
      gcongr
      exact hdecay x hx

private lemma putnam_1989_b3_tendsto_moment_right_zero
    (f : ℝ → ℝ) (hfdiff : Differentiable ℝ f) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ => x ^ n * f x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ => x ^ n) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ n : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.pow n)
  have hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds hfdiff.continuous.continuousAt
  convert hx.mul hf using 1
  rw [zero_pow hn.ne', zero_mul]

private lemma putnam_1989_b3_integrable_scaled_moment
    (f : ℝ → ℝ) (hfdiff : Differentiable ℝ f)
    (hdecay : ∀ x ≥ 0, |f x| ≤ Real.exp (-√x)) (n : ℕ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ n * f (2 * x)) (Set.Ioi 0) := by
  have hmom := putnam_1989_b3_integrable_moment f hfdiff hdecay n
  have hg : MeasureTheory.IntegrableOn (fun u : ℝ => (u / 2) ^ n * f u) (Set.Ioi 0) := by
    have hconst :
        MeasureTheory.IntegrableOn
          (fun u : ℝ => ((2 : ℝ)⁻¹) ^ n * (u ^ n * f u)) (Set.Ioi 0) :=
      hmom.const_mul (((2 : ℝ)⁻¹) ^ n)
    refine hconst.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [div_eq_mul_inv, mul_pow]
    ring
  have hcomp :=
    (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => (u / 2) ^ n * f u) 0 (a := (2 : ℝ)) (by norm_num)).mpr
      (by simpa using hg)
  refine hcomp.congr_fun (fun x _ => ?_) measurableSet_Ioi
  norm_num

private lemma putnam_1989_b3_scaled_integral
    (f : ℝ → ℝ) (μ : ℕ → ℝ)
    (μ_def : ∀ n, μ n = ∫ x in Set.Ioi 0, x ^ n * f x) (n : ℕ) :
    (∫ x in Set.Ioi 0, x ^ n * f (2 * x)) =
      (((2 : ℝ) ^ (n + 1))⁻¹) * μ n := by
  let g : ℝ → ℝ := fun u => (u / 2) ^ n * f u
  have hcv := MeasureTheory.integral_comp_mul_left_Ioi g 0 (by norm_num : (0 : ℝ) < 2)
  have hgint :
      (∫ u in Set.Ioi 0, g u) =
        ((2 : ℝ)⁻¹) ^ n * ∫ u in Set.Ioi 0, u ^ n * f u := by
    calc
      (∫ u in Set.Ioi 0, g u)
          = ∫ u in Set.Ioi 0, ((2 : ℝ)⁻¹) ^ n * (u ^ n * f u) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro u _
            change (u / 2) ^ n * f u = ((2 : ℝ)⁻¹) ^ n * (u ^ n * f u)
            rw [div_eq_mul_inv, mul_pow]
            ring
      _ = ((2 : ℝ)⁻¹) ^ n * ∫ u in Set.Ioi 0, u ^ n * f u := by
            rw [MeasureTheory.integral_const_mul]
  calc
    (∫ x in Set.Ioi 0, x ^ n * f (2 * x))
        = ∫ x in Set.Ioi 0, g (2 * x) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change x ^ n * f (2 * x) = ((2 * x) / 2) ^ n * f (2 * x)
          norm_num
    _ = (2 : ℝ)⁻¹ * ∫ u in Set.Ioi 0, g u := by
          simpa using hcv
    _ = (2 : ℝ)⁻¹ * (((2 : ℝ)⁻¹) ^ n * ∫ u in Set.Ioi 0, u ^ n * f u) := by
          rw [hgint]
    _ = (((2 : ℝ) ^ (n + 1))⁻¹) * μ n := by
          rw [← μ_def n]
          rw [← mul_assoc, ← pow_succ' ((2 : ℝ)⁻¹) n, ← inv_pow]

private lemma putnam_1989_b3_recurrence
    (f : ℝ → ℝ)
    (hfdiff : Differentiable ℝ f)
    (hfderiv : ∀ x > 0, deriv f x = -3 * f x + 6 * f (2 * x))
    (hdecay : ∀ x ≥ 0, |f x| ≤ Real.exp (-√x))
    (μ : ℕ → ℝ)
    (μ_def : ∀ n, μ n = ∫ x in Set.Ioi 0, x ^ n * f x) :
    ∀ n, μ (n + 1) =
      ((((n + 1 : ℕ) : ℝ) / (3 - 6 / (2 : ℝ) ^ ((n + 1) + 1))) * μ n) := by
  intro n
  let m := n + 1
  have hmpos : 0 < m := Nat.succ_pos n
  have hm_sub : m - 1 = n := Nat.succ_sub_one n
  have hderiv_int :
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ m * deriv f x) (Set.Ioi 0) := by
    have h1 :
        MeasureTheory.IntegrableOn (fun x : ℝ => -3 * (x ^ m * f x)) (Set.Ioi 0) :=
      (putnam_1989_b3_integrable_moment f hfdiff hdecay m).const_mul (-3)
    have h2 :
        MeasureTheory.IntegrableOn (fun x : ℝ => 6 * (x ^ m * f (2 * x))) (Set.Ioi 0) :=
      (putnam_1989_b3_integrable_scaled_moment f hfdiff hdecay m).const_mul 6
    have hsum := h1.add h2
    refine (MeasureTheory.integrableOn_congr_fun (s := Set.Ioi 0) ?_ measurableSet_Ioi).mpr hsum
    intro x hx
    change x ^ m * deriv f x = -3 * (x ^ m * f x) + 6 * (x ^ m * f (2 * x))
    rw [hfderiv x hx]
    ring
  have hu'v_int :
      MeasureTheory.IntegrableOn (fun x : ℝ => ((m : ℝ) * x ^ (m - 1)) * f x)
        (Set.Ioi 0) := by
    have hconst :
        MeasureTheory.IntegrableOn (fun x : ℝ => (m : ℝ) * (x ^ (m - 1) * f x))
          (Set.Ioi 0) :=
      (putnam_1989_b3_integrable_moment f hfdiff hdecay (m - 1)).const_mul (m : ℝ)
    refine hconst.congr_fun (fun x _ => ?_) measurableSet_Ioi
    ring
  have hparts :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (u := fun x : ℝ => x ^ m) (v := f)
      (u' := fun x : ℝ => (m : ℝ) * x ^ (m - 1)) (v' := deriv f)
      (fun x _ => hasDerivAt_pow m x)
      (fun x _ => (hfdiff x).hasDerivAt)
      (by simpa [Pi.mul_def] using hderiv_int)
      (by simpa [Pi.mul_def] using hu'v_int)
      (putnam_1989_b3_tendsto_moment_right_zero f hfdiff m hmpos)
      (putnam_1989_b3_tendsto_moment_atTop f hdecay m)
  have hleft :
      (∫ x in Set.Ioi 0, x ^ m * deriv f x) = -((m : ℝ) * μ (m - 1)) := by
    have hu'v :
        (∫ x in Set.Ioi 0, ((m : ℝ) * x ^ (m - 1)) * f x) =
          (m : ℝ) * μ (m - 1) := by
      calc
        (∫ x in Set.Ioi 0, ((m : ℝ) * x ^ (m - 1)) * f x)
            = ∫ x in Set.Ioi 0, (m : ℝ) * (x ^ (m - 1) * f x) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
              intro x _
              ring
        _ = (m : ℝ) * ∫ x in Set.Ioi 0, x ^ (m - 1) * f x := by
              rw [MeasureTheory.integral_const_mul]
        _ = (m : ℝ) * μ (m - 1) := by rw [← μ_def (m - 1)]
    simpa [sub_eq_add_neg, hu'v] using hparts
  have hright :
      (∫ x in Set.Ioi 0, x ^ m * deriv f x) =
        -3 * μ m + 6 * ((((2 : ℝ) ^ (m + 1))⁻¹) * μ m) := by
    have h1 :
        MeasureTheory.IntegrableOn (fun x : ℝ => -3 * (x ^ m * f x)) (Set.Ioi 0) :=
      (putnam_1989_b3_integrable_moment f hfdiff hdecay m).const_mul (-3)
    have h2 :
        MeasureTheory.IntegrableOn (fun x : ℝ => 6 * (x ^ m * f (2 * x))) (Set.Ioi 0) :=
      (putnam_1989_b3_integrable_scaled_moment f hfdiff hdecay m).const_mul 6
    calc
      (∫ x in Set.Ioi 0, x ^ m * deriv f x)
          = ∫ x in Set.Ioi 0, -3 * (x ^ m * f x) + 6 * (x ^ m * f (2 * x)) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            change x ^ m * deriv f x = -3 * (x ^ m * f x) + 6 * (x ^ m * f (2 * x))
            rw [hfderiv x hx]
            ring
      _ = (∫ x in Set.Ioi 0, -3 * (x ^ m * f x)) +
            ∫ x in Set.Ioi 0, 6 * (x ^ m * f (2 * x)) := by
            rw [MeasureTheory.integral_add h1 h2]
      _ = -3 * (∫ x in Set.Ioi 0, x ^ m * f x) +
            6 * ∫ x in Set.Ioi 0, x ^ m * f (2 * x) := by
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = -3 * μ m + 6 * ((((2 : ℝ) ^ (m + 1))⁻¹) * μ m) := by
            rw [← μ_def m, putnam_1989_b3_scaled_integral f μ μ_def m]
  have hrec :
      - (m : ℝ) * μ (m - 1) =
        -3 * μ m + 6 * ((((2 : ℝ) ^ (m + 1))⁻¹) * μ m) := by
    simpa [neg_mul] using hleft.symm.trans hright
  have hsolve :
      μ m = ((m : ℝ) / (3 - 6 / (2 : ℝ) ^ (m + 1))) * μ (m - 1) := by
    have hcoef_ne : 3 - 6 / (2 : ℝ) ^ (m + 1) ≠ 0 := by
      rw [show 3 - 6 / (2 : ℝ) ^ (m + 1) =
          3 * (1 - (1 : ℝ) / (2 : ℝ) ^ m) by
        have hpow_ne : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [pow_succ]
        field_simp [hpow_ne]
        ring]
      have hunit : 1 - (1 : ℝ) / (2 : ℝ) ^ m ≠ 0 := by
        rw [← show ((1 : ℝ) / 2) ^ m = 1 / (2 : ℝ) ^ m by
          rw [div_pow]
          simp]
        have hhalf_lt : ((1 : ℝ) / 2) ^ m < 1 :=
          pow_lt_one₀ (by norm_num : 0 ≤ (1 : ℝ) / 2)
            (by norm_num : (1 : ℝ) / 2 < 1) hmpos.ne'
        exact sub_ne_zero.mpr hhalf_lt.ne'
      exact mul_ne_zero (by norm_num) hunit
    have hcoef :
        ((-3 : ℝ) + 6 / (2 : ℝ) ^ (m + 1)) =
          -(3 - 6 / (2 : ℝ) ^ (m + 1)) := by
      ring
    have hrec' :
        - (m : ℝ) * μ (m - 1) =
          ((-3 : ℝ) + 6 / (2 : ℝ) ^ (m + 1)) * μ m := by
      rw [hrec]
      ring
    rw [hcoef] at hrec'
    have hμm :
        μ m =
          (- (m : ℝ) * μ (m - 1)) /
            (-(3 - 6 / (2 : ℝ) ^ (m + 1))) := by
      rw [eq_div_iff (neg_ne_zero.mpr hcoef_ne)]
      simpa [mul_comm] using hrec'.symm
    rw [hμm]
    field_simp [hcoef_ne]
  simpa [m, hm_sub] using hsolve

private lemma putnam_1989_b3_solution_zero (a : ℝ) :
    putnam_1989_b3_solution 0 a = a := by
  simp [putnam_1989_b3_solution]

private lemma putnam_1989_b3_unit_denom_ne_zero {k : ℕ} (hk : 0 < k) :
    1 - (1 : ℝ) / (2 : ℝ) ^ k ≠ 0 := by
  rw [← show ((1 : ℝ) / 2) ^ k = 1 / (2 : ℝ) ^ k by
    rw [div_pow]
    simp]
  have hhalf_lt : ((1 : ℝ) / 2) ^ k < 1 :=
    pow_lt_one₀ (by norm_num : 0 ≤ (1 : ℝ) / 2)
      (by norm_num : (1 : ℝ) / 2 < 1) hk.ne'
  exact sub_ne_zero.mpr hhalf_lt.ne'

private lemma putnam_1989_b3_denom_ne_zero {k : ℕ} (hk : 0 < k) :
    3 - 6 / (2 : ℝ) ^ (k + 1) ≠ 0 := by
  rw [show 3 - 6 / (2 : ℝ) ^ (k + 1) =
      3 * (1 - (1 : ℝ) / (2 : ℝ) ^ k) by
    have hpow_ne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [pow_succ]
    field_simp [hpow_ne]
    ring]
  exact mul_ne_zero (by norm_num) (putnam_1989_b3_unit_denom_ne_zero hk)

private lemma putnam_1989_b3_scaled_denom_ne_zero {k : ℕ} (hk : 0 < k) :
    3 * (1 - (1 : ℝ) / (2 : ℝ) ^ k) ≠ 0 := by
  exact mul_ne_zero (by norm_num) (putnam_1989_b3_unit_denom_ne_zero hk)

private lemma putnam_1989_b3_solution_succ (n : ℕ) (a : ℝ) :
    putnam_1989_b3_solution (n + 1) a =
      ((((n + 1 : ℕ) : ℝ) / (3 - 6 / (2 : ℝ) ^ ((n + 1) + 1))) *
        putnam_1989_b3_solution n a) := by
  unfold putnam_1989_b3_solution
  rw [Finset.prod_Icc_succ_top (Nat.succ_pos n)]
  ring

private lemma putnam_1989_b3_solution_scaled (n : ℕ) (a : ℝ) :
    putnam_1989_b3_solution n a * (3 : ℝ) ^ n / (n ! : ℝ) =
      a * (∏ k ∈ Finset.range n, (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1))⁻¹) := by
  induction n with
  | zero =>
      simp [putnam_1989_b3_solution]
  | succ n ih =>
      have hden : 3 - 6 / (2 : ℝ) ^ ((n + 1) + 1) ≠ 0 :=
        putnam_1989_b3_denom_ne_zero (Nat.succ_pos n)
      have hn : (((n + 1 : ℕ) : ℝ) ≠ 0) := by
        exact_mod_cast Nat.succ_ne_zero n
      have hf : (n ! : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have h3 : (3 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have hfactor :
          (3 : ℝ) / (3 - 6 / (2 : ℝ) ^ ((n + 1) + 1)) =
            (1 - (1 : ℝ) / (2 : ℝ) ^ (n + 1))⁻¹ := by
        have hden_eq :
            (3 : ℝ) - 6 / (2 : ℝ) ^ ((n + 1) + 1) =
              3 * (1 - (1 : ℝ) / (2 : ℝ) ^ (n + 1)) := by
          have hpow_ne : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
          rw [pow_succ]
          field_simp [hpow_ne]
          ring
        rw [hden_eq]
        field_simp
      calc
        putnam_1989_b3_solution (n + 1) a * (3 : ℝ) ^ (n + 1) /
            ((n + 1)! : ℝ)
            = (putnam_1989_b3_solution n a * (3 : ℝ) ^ n / (n ! : ℝ)) *
                ((3 : ℝ) / (3 - 6 / (2 : ℝ) ^ ((n + 1) + 1))) := by
              rw [putnam_1989_b3_solution_succ n a, pow_succ]
              rw [show (((n + 1)! : ℕ) : ℝ) =
                  (((n + 1 : ℕ) : ℝ) * (n ! : ℝ)) by
                rw [Nat.factorial_succ]
                norm_num [Nat.cast_mul]]
              field_simp [hden, hn, hf, h3]
              ring
        _ = (putnam_1989_b3_solution n a * (3 : ℝ) ^ n / (n ! : ℝ)) *
              (1 - (1 : ℝ) / (2 : ℝ) ^ (n + 1))⁻¹ := by
              rw [hfactor]
        _ = (a * ∏ k ∈ Finset.range n, (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1))⁻¹) *
              (1 - (1 : ℝ) / (2 : ℝ) ^ (n + 1))⁻¹ := by
              rw [ih]
        _ = a * (∏ k ∈ Finset.range (n + 1), (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1))⁻¹) := by
              rw [Finset.prod_range_succ]
              ring

private lemma putnam_1989_b3_inv_factor_eq_one_add_inv (k : ℕ) :
    (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1))⁻¹ =
      1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹) := by
  have hden : (2 : ℝ) ^ (k + 1) - 1 ≠ 0 := by
    have hpow : 1 < (2 : ℝ) ^ (k + 1) :=
      one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero k)
    nlinarith
  have hpow_ne : (2 : ℝ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hden, hpow_ne]
  ring

private lemma putnam_1989_b3_product_inv_eq_one_add (n : ℕ) :
    (∏ k ∈ Finset.range n, (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1))⁻¹) =
      ∏ k ∈ Finset.range n, (1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹)) := by
  apply Finset.prod_congr rfl
  intro k _
  exact putnam_1989_b3_inv_factor_eq_one_add_inv k

private lemma putnam_1989_b3_summable_perturb :
    Summable (fun k : ℕ => ‖(((2 : ℝ) ^ (k + 1) - 1)⁻¹)‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1))
  have hpow_ge_one : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hden_pos : 0 < (2 : ℝ) ^ (k + 1) - 1 := by
    have hpow : 1 < (2 : ℝ) ^ (k + 1) :=
      one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero k)
    nlinarith
  have hden_ge : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) - 1 := by
    rw [pow_succ]
    nlinarith
  have hinv_le : (((2 : ℝ) ^ (k + 1) - 1)⁻¹) ≤ ((2 : ℝ) ^ k)⁻¹ := by
    exact (inv_le_inv₀ hden_pos (pow_pos (by norm_num) k)).mpr hden_ge
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hden_pos.le)]
  calc
    (((2 : ℝ) ^ (k + 1) - 1)⁻¹) ≤ ((2 : ℝ) ^ k)⁻¹ := hinv_le
    _ = ((1 / 2 : ℝ) ^ k) := by rw [← inv_pow]; norm_num

private lemma putnam_1989_b3_product_tendsto (a : ℝ) :
    Tendsto
      (fun n : ℕ =>
        a * (∏ k ∈ Finset.range n, (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1))⁻¹))
      atTop
      (𝓝 (a * ∏' k : ℕ, (1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹)))) := by
  have hmult : Multipliable fun k : ℕ => 1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹) :=
    multipliable_one_add_of_summable putnam_1989_b3_summable_perturb
  have ht := hmult.tendsto_prod_tprod_nat.const_mul a
  refine ht.congr' ?_
  filter_upwards with n
  rw [putnam_1989_b3_product_inv_eq_one_add n]

private lemma putnam_1989_b3_solution_scaled_tendsto (a : ℝ) :
    Tendsto
      (fun n : ℕ => putnam_1989_b3_solution n a * (3 : ℝ) ^ n / (n ! : ℝ))
      atTop
      (𝓝 (a * ∏' k : ℕ, (1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹)))) := by
  refine (putnam_1989_b3_product_tendsto a).congr' ?_
  filter_upwards with n
  rw [putnam_1989_b3_solution_scaled n a]

private lemma putnam_1989_b3_tprod_ne_zero :
    (∏' k : ℕ, (1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹))) ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable ?_ putnam_1989_b3_summable_perturb
  intro k
  have hden_pos : 0 < (2 : ℝ) ^ (k + 1) - 1 := by
    have hpow : 1 < (2 : ℝ) ^ (k + 1) :=
      one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero k)
    nlinarith
  positivity

private lemma putnam_1989_b3_solution_scaled_zero
    (a : ℝ)
    (hzero : Tendsto
      (fun n : ℕ => putnam_1989_b3_solution n a * (3 : ℝ) ^ n / (n ! : ℝ))
      atTop (𝓝 0)) :
    a = 0 := by
  have hlim := putnam_1989_b3_solution_scaled_tendsto a
  have hprod_zero :
      a * (∏' k : ℕ, (1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹))) = 0 :=
    tendsto_nhds_unique hlim hzero
  exact (mul_eq_zero.mp hprod_zero).resolve_right putnam_1989_b3_tprod_ne_zero

/--
Let $f$ be a function on $[0,\infty)$, differentiable and satisfying
\[
f'(x)=-3f(x)+6f(2x)
\]
for $x>0$. Assume that $|f(x)|\le e^{-\sqrt{x}}$ for $x\ge 0$ (so that $f(x)$ tends rapidly to $0$ as $x$ increases). For $n$ a non-negative integer, define
\[
\mu_n=\int_0^\infty x^n f(x)\,dx
\]
(sometimes called the $n$th moment of $f$).
\begin{enumerate}
\item[a)] Express $\mu_n$ in terms of $\mu_0$.
\item[b)] Prove that the sequence $\{\mu_n \frac{3^n}{n!}\}$ always converges, and that the limit is $0$ only if $\mu_0=0$.
\end{enumerate}
-/
theorem putnam_1989_b3
    (f : ℝ → ℝ)
    (hfdiff : Differentiable ℝ f)
    (hfderiv : ∀ x > 0, deriv f x = -3 * f x + 6 * f (2 * x))
    (hdecay : ∀ x ≥ 0, |f x| ≤ Real.exp (- √x))
    (μ : ℕ → ℝ)
    (μ_def : ∀ n, μ n = ∫ x in Set.Ioi 0, x ^ n * f x) :
    (∀ n, μ n = putnam_1989_b3_solution n (μ 0)) ∧
    (∃ L, Tendsto (fun n ↦ (μ n) * 3 ^ n / n !) atTop (𝓝 L)) ∧
    (Tendsto (fun n ↦ (μ n) * 3 ^ n / n !) atTop (𝓝 0) → μ 0 = 0) :=
by
  have hrec := putnam_1989_b3_recurrence f hfdiff hfderiv hdecay μ μ_def
  have hformula : ∀ n, μ n = putnam_1989_b3_solution n (μ 0) := by
    intro n
    induction n with
    | zero =>
        exact (putnam_1989_b3_solution_zero (μ 0)).symm
    | succ n ih =>
        rw [hrec n, ih, putnam_1989_b3_solution_succ n (μ 0)]
  refine ⟨hformula, ?_, ?_⟩
  · refine ⟨μ 0 * ∏' k : ℕ, (1 + (((2 : ℝ) ^ (k + 1) - 1)⁻¹)), ?_⟩
    refine (putnam_1989_b3_solution_scaled_tendsto (μ 0)).congr' ?_
    filter_upwards with n
    rw [hformula n]
  · intro hzero
    apply putnam_1989_b3_solution_scaled_zero (μ 0)
    refine hzero.congr' ?_
    filter_upwards with n
    rw [hformula n]
