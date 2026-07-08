import Mathlib

open Filter Topology
open MeasureTheory Set
open scoped ENNReal

noncomputable abbrev putnam_1997_a3_solution : ℝ := Real.exp (1 / 2)

lemma putnam_1997_a3_prod_range_two_mul_add_one_mem (n : ℕ) :
    (∏ i ∈ Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)) = 2 ^ n * (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      ring

lemma putnam_1997_a3_prod_range_two_mul_add_one (n : ℕ) :
    (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)) = 2 ^ n * (n.factorial : ℝ) := by
  rw [← putnam_1997_a3_prod_range_two_mul_add_one_mem n]
  simpa using
    (Finset.prod_attach (Finset.range n) (fun i : ℕ => (2 : ℝ) * ((i : ℝ) + 1)))

lemma putnam_1997_a3_prod_range_sq_two_mul_add_one (n : ℕ) :
    (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2) =
      4 ^ n * ((n.factorial : ℝ) ^ 2) := by
  calc
    (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2)
        = (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)) ^ 2 := by
          rw [← Finset.prod_pow]
    _ = 4 ^ n * ((n.factorial : ℝ) ^ 2) := by
          rw [putnam_1997_a3_prod_range_two_mul_add_one]
          rw [sq]
          rw [show (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n by norm_num]
          rw [← pow_mul]
          ring_nf

lemma putnam_1997_a3_series1_term (x : ℝ) (n : ℕ) :
    (-1 : ℝ)^n * x^(2*n + 1)/(∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)) =
      x * (((-(x^2) / 2) ^ n) / (n.factorial : ℝ)) := by
  rw [putnam_1997_a3_prod_range_two_mul_add_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
    pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
  rw [show (-(x ^ 2 / 2) : ℝ) = (-1 : ℝ) * x^2 / 2 by ring]
  rw [div_pow, mul_pow]
  rw [← pow_mul]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
  ring_nf

lemma putnam_1997_a3_series1_tsum_eq (x : ℝ) :
    (∑' n : ℕ, (-1 : ℝ)^n * x^(2*n + 1)/
      (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1))) =
      x * Real.exp (-(x^2) / 2) := by
  calc
    (∑' n : ℕ, (-1 : ℝ)^n * x^(2*n + 1)/
      (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)))
        = ∑' n : ℕ, x * (((-(x^2) / 2) ^ n) / (n.factorial : ℝ)) := by
          exact tsum_congr (putnam_1997_a3_series1_term x)
    _ = x * Real.exp (-(x^2) / 2) := by
          rw [tsum_mul_left]
          rw [Real.exp_eq_exp_ℝ]
          exact congrArg (fun y => x * y)
            (NormedSpace.expSeries_div_hasSum_exp (-(x^2) / 2 : ℝ)).tsum_eq

lemma putnam_1997_a3_rpow_half_neg_nat_add_one (n : ℕ) :
    (1 / 2 : ℝ) ^ (-((n : ℝ) + 1)) = (2 : ℝ) ^ (n + 1) := by
  rw [show (-((n : ℝ) + 1)) = -(((n + 1 : ℕ) : ℝ)) by norm_num]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast, ← inv_pow]
  norm_num

lemma putnam_1997_a3_gaussian_moment (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), x^(2*n+1) * Real.exp (-(1/2 : ℝ) * x^2)) =
      2^n * (n.factorial : ℝ) := by
  let q : ℝ := ((2*n+1 : ℕ) : ℝ)
  have hq : -1 < q := by
    have hnonneg : (0 : ℝ) ≤ q := by
      dsimp [q]
      positivity
    linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := q) (b := (1/2 : ℝ)) (by norm_num) hq (by norm_num)
  have hleft :
      (∫ x in Ioi (0 : ℝ), x^(2*n+1) * Real.exp (-(1/2 : ℝ) * x^2)) =
      (∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-(1/2 : ℝ) * x ^ (2 : ℝ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    dsimp [q]
    rw [Real.rpow_natCast (x := x) (n := 2 * n + 1)]
    simp
  have harg : (q + 1) / 2 = (n : ℝ) + 1 := by
    dsimp [q]
    norm_num
    ring
  have hexp : -(q + 1) / 2 = -((n : ℝ) + 1) := by
    dsimp [q]
    norm_num
    ring
  calc
    (∫ x in Ioi (0 : ℝ), x^(2*n+1) * Real.exp (-(1/2 : ℝ) * x^2))
        = (∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-(1/2 : ℝ) * x ^ (2 : ℝ))) := hleft
    _ = (1 / 2 : ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) := h
    _ = (1 / 2 : ℝ) ^ (-((n : ℝ) + 1)) * (1 / 2) * Real.Gamma ((n : ℝ) + 1) := by
          rw [hexp, harg]
    _ = (2 : ℝ)^n * (n.factorial : ℝ) := by
          rw [putnam_1997_a3_rpow_half_neg_nat_add_one n]
          rw [show (Real.Gamma ((n : ℝ) + 1)) = (n.factorial : ℝ) by
            simpa using Real.Gamma_nat_eq_factorial n]
          rw [pow_succ]
          ring

lemma putnam_1997_a3_second_term_integral (n : ℕ) :
    (∫ x in Ioi (0 : ℝ),
      (x * Real.exp (-(x^2) / 2)) *
        (x^(2*n) / (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2))) =
      (1 / 2 : ℝ)^n / (n.factorial : ℝ) := by
  let d : ℝ := (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2)
  have hd : d = 4 ^ n * ((n.factorial : ℝ) ^ 2) := by
    dsimp [d]
    exact putnam_1997_a3_prod_range_sq_two_mul_add_one n
  have hcongr :
      (∫ x in Ioi (0 : ℝ), (x * Real.exp (-(x^2) / 2)) * (x^(2*n) / d)) =
      (∫ x in Ioi (0 : ℝ), (1 / d) *
        (x^(2*n+1) * Real.exp (-(1/2 : ℝ) * x^2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [show (-(x ^ 2) / 2 : ℝ) = -(1 / 2 : ℝ) * x^2 by ring]
    ring
  calc
    (∫ x in Ioi (0 : ℝ),
      (x * Real.exp (-(x^2) / 2)) *
        (x^(2*n) / (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2)))
        = (∫ x in Ioi (0 : ℝ), (x * Real.exp (-(x^2) / 2)) *
            (x^(2*n) / d)) := by rfl
    _ = (∫ x in Ioi (0 : ℝ), (1 / d) *
        (x^(2*n+1) * Real.exp (-(1/2 : ℝ) * x^2))) := hcongr
    _ = (1 / d) * (2^n * (n.factorial : ℝ)) := by
          rw [integral_const_mul, putnam_1997_a3_gaussian_moment]
    _ = (1 / 2 : ℝ)^n / (n.factorial : ℝ) := by
          rw [hd]
          field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
            pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0),
            pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
          rw [show (4 : ℝ) = 2^2 by norm_num, ← mul_pow]
          norm_num

noncomputable def putnam_1997_a3_Fterm (n : ℕ) (x : ℝ) : ℝ :=
  (x * Real.exp (-(x^2) / 2)) *
    (x^(2*n) / (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2))

lemma putnam_1997_a3_second_term_integrable (n : ℕ) :
    IntegrableOn (putnam_1997_a3_Fterm n) (Ioi (0 : ℝ)) := by
  let d : ℝ := (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2)
  have hbase :
      IntegrableOn
        (fun x : ℝ => x ^ (((2*n+1 : ℕ) : ℝ)) * Real.exp (-(1/2 : ℝ) * x^2))
        (Ioi 0) := by
    exact integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2) (by
      have hnonneg : (0 : ℝ) ≤ (((2*n+1 : ℕ) : ℝ)) := by positivity
      linarith)
  have hbase' :
      IntegrableOn
        (fun x : ℝ => (1 / d) *
          (x ^ (((2*n+1 : ℕ) : ℝ)) * Real.exp (-(1/2 : ℝ) * x^2)))
        (Ioi 0) :=
    hbase.const_mul (1 / d)
  refine hbase'.congr_fun ?_ measurableSet_Ioi
  intro x hx
  dsimp [putnam_1997_a3_Fterm, d]
  rw [show (-(x ^ 2) / 2 : ℝ) = -(1 / 2 : ℝ) * x^2 by ring]
  rw [Real.rpow_natCast (x := x) (n := 2 * n + 1)]
  ring

lemma putnam_1997_a3_hF_int :
    ∀ n : ℕ, Integrable (putnam_1997_a3_Fterm n) (volume.restrict (Ioi (0 : ℝ))) := by
  intro n
  exact putnam_1997_a3_second_term_integrable n

lemma putnam_1997_a3_hnorm (n : ℕ) :
    (∫ x, ‖putnam_1997_a3_Fterm n x‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
      (1 / 2 : ℝ)^n / (n.factorial : ℝ) := by
  calc
    (∫ x, ‖putnam_1997_a3_Fterm n x‖ ∂(volume.restrict (Ioi (0 : ℝ))))
        = ∫ x, putnam_1997_a3_Fterm n x ∂(volume.restrict (Ioi (0 : ℝ))) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          rw [Real.norm_of_nonneg]
          have hx0 : 0 ≤ x := le_of_lt hx
          dsimp [putnam_1997_a3_Fterm]
          positivity
    _ = (∫ x in Ioi (0 : ℝ), putnam_1997_a3_Fterm n x) := rfl
    _ = (1 / 2 : ℝ)^n / (n.factorial : ℝ) := by
          simpa [putnam_1997_a3_Fterm] using putnam_1997_a3_second_term_integral n

lemma putnam_1997_a3_hF_sum :
    Summable fun n : ℕ =>
      ∫ x, ‖putnam_1997_a3_Fterm n x‖ ∂(volume.restrict (Ioi (0 : ℝ))) := by
  exact (NormedSpace.expSeries_div_summable (1 / 2 : ℝ)).congr
    (fun n => (putnam_1997_a3_hnorm n).symm)

lemma putnam_1997_a3_weighted_series_integrable :
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, putnam_1997_a3_Fterm n x) (Ioi (0 : ℝ)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hf'' (i : ℕ) :
      AEMeasurable (fun x : ℝ => ‖putnam_1997_a3_Fterm i x‖ₑ) μ :=
    (putnam_1997_a3_hF_int i).1.enorm
  have hf_ne_top :
      (∑' i : ℕ, ∫⁻ x : ℝ, ‖putnam_1997_a3_Fterm i x‖ₑ ∂ μ) ≠ ∞ := by
    have (i : ℕ) :
        (∫⁻ x : ℝ, ‖putnam_1997_a3_Fterm i x‖ₑ ∂ μ) =
          ‖(∫ x : ℝ, ‖putnam_1997_a3_Fterm i x‖ ∂ μ)‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (putnam_1997_a3_hF_int i).norm,
        ENNReal.coe_nnreal_eq]
      simp [coe_nnnorm]
      have hnonnegint :
          0 ≤ ∫ a : ℝ, |putnam_1997_a3_Fterm i a| ∂ μ :=
        integral_nonneg (μ := μ) (fun a => abs_nonneg (putnam_1997_a3_Fterm i a))
      rw [abs_of_nonneg hnonnegint]
    rw [funext this]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 putnam_1997_a3_hF_sum.abs
  have h_norm_summable_ae :
      ∀ᵐ x : ℝ ∂ μ, Summable fun n : ℕ => (‖putnam_1997_a3_Fterm n x‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf_ne_top
    refine (ae_lt_top' (AEMeasurable.ennreal_tsum hf'') hf_ne_top).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  let Bnn : ℝ → NNReal := fun x => ∑' n : ℕ, ‖putnam_1997_a3_Fterm n x‖₊
  have hB_int : Integrable (fun x : ℝ => (Bnn x : ℝ)) μ := by
    refine ⟨?_, ?_⟩
    · rw [aestronglyMeasurable_iff_aemeasurable]
      dsimp [Bnn]
      exact AEMeasurable.coe_nnreal_real (AEMeasurable.nnreal_tsum fun i =>
        (putnam_1997_a3_hF_int i).1.nnnorm.aemeasurable)
    · rw [hasFiniteIntegral_iff_ofNNReal]
      dsimp [Bnn]
      have hfinite :
          ∫⁻ x : ℝ, ∑' n : ℕ, ‖putnam_1997_a3_Fterm n x‖ₑ ∂ μ < ⊤ := by
        rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
      convert hfinite using 1
      apply lintegral_congr_ae
      filter_upwards [h_norm_summable_ae] with x hx
      rw [ENNReal.coe_tsum (NNReal.summable_coe.mp hx)]
      simp_rw [enorm_eq_nnnorm]
  have hsum_meas :
      AEStronglyMeasurable (fun x : ℝ => ∑' n : ℕ, putnam_1997_a3_Fterm n x) μ := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter ℕ))
      (f := fun k x => ∑ n ∈ Finset.range k, putnam_1997_a3_Fterm n x) ?_ ?_
    · intro k
      change AEStronglyMeasurable
        (fun x : ℝ => ∑ n ∈ Finset.range k, putnam_1997_a3_Fterm n x) μ
      dsimp [μ]
      exact Finset.aestronglyMeasurable_fun_sum (Finset.range k) fun i hi =>
        (putnam_1997_a3_hF_int i).1
    · filter_upwards [h_norm_summable_ae] with x hx
      have hxnorm : Summable fun n : ℕ => ‖putnam_1997_a3_Fterm n x‖ := by
        simpa [coe_nnnorm] using hx
      exact hxnorm.of_norm.hasSum.tendsto_sum_nat
  refine Integrable.mono' hB_int hsum_meas ?_
  filter_upwards [h_norm_summable_ae] with x hx
  have hxnorm : Summable fun n : ℕ => ‖putnam_1997_a3_Fterm n x‖ := by
    simpa [coe_nnnorm] using hx
  calc
    ‖∑' n : ℕ, putnam_1997_a3_Fterm n x‖
        ≤ ∑' n : ℕ, ‖putnam_1997_a3_Fterm n x‖ := norm_tsum_le_tsum_norm hxnorm
    _ = (Bnn x : ℝ) := by
          dsimp [Bnn]
          simpa only [coe_nnnorm] using
            (NNReal.coe_tsum (f := fun n : ℕ => ‖putnam_1997_a3_Fterm n x‖₊)).symm

lemma putnam_1997_a3_weighted_series_integral :
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, putnam_1997_a3_Fterm n x) = Real.exp (1 / 2) := by
  calc
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, putnam_1997_a3_Fterm n x)
        = ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), putnam_1997_a3_Fterm n x := by
          symm
          exact MeasureTheory.integral_tsum_of_summable_integral_norm
            putnam_1997_a3_hF_int putnam_1997_a3_hF_sum
    _ = ∑' n : ℕ, (1 / 2 : ℝ)^n / (n.factorial : ℝ) := by
          exact tsum_congr (fun n => by
            simpa [putnam_1997_a3_Fterm] using putnam_1997_a3_second_term_integral n)
    _ = Real.exp (1 / 2) := by
          rw [Real.exp_eq_exp_ℝ]
          exact (NormedSpace.expSeries_div_hasSum_exp (1 / 2 : ℝ)).tsum_eq

/--
Evaluate \begin{gather*} \int_0^\infty \left(x-\frac{x^3}{2}+\frac{x^5}{2\cdot 4}-\frac{x^7}{2\cdot 4\cdot 6}+\cdots\right) \\ \left(1+\frac{x^2}{2^2}+\frac{x^4}{2^2\cdot 4^2}+\frac{x^6}{2^2\cdot 4^2 \cdot 6^2}+\cdots\right)\,dx. \end{gather*}
-/
theorem putnam_1997_a3
(series1 series2 : ℝ → ℝ)
(hseries1 : series1 = fun x => ∑' n : ℕ, (-1)^n * x^(2*n + 1)/(∏ i : Finset.range n, 2 * ((i : ℝ) + 1)))
(hseries2 : series2 = fun x => ∑' n : ℕ, x^(2*n)/(∏ i : Finset.range n, (2 * ((i : ℝ) + 1))^2))
: Tendsto (fun t => ∫ x in Set.Icc 0 t, series1 x * series2 x) atTop (𝓝 (putnam_1997_a3_solution)) := by
  have hprod (x : ℝ) : series1 x * series2 x = ∑' n : ℕ, putnam_1997_a3_Fterm n x := by
    rw [hseries1, hseries2]
    change
      (∑' n : ℕ, (-1 : ℝ)^n * x^(2*n + 1) /
        (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1))) *
        (∑' n : ℕ, x^(2*n) /
          (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1))^2)) =
        ∑' n : ℕ, putnam_1997_a3_Fterm n x
    rw [putnam_1997_a3_series1_tsum_eq x]
    rw [← tsum_mul_left]
    rfl
  have htend :
      Tendsto
        (fun t : ℝ => ∫ x in (0 : ℝ)..t, ∑' n : ℕ, putnam_1997_a3_Fterm n x)
        atTop (𝓝 (Real.exp (1 / 2))) := by
    have h := intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      putnam_1997_a3_weighted_series_integrable Filter.tendsto_id
    rwa [putnam_1997_a3_weighted_series_integral] at h
  have h_event :
      (fun t : ℝ => ∫ x in Set.Icc 0 t, series1 x * series2 x)
        =ᶠ[atTop]
      (fun t : ℝ => ∫ x in (0 : ℝ)..t, ∑' n : ℕ, putnam_1997_a3_Fterm n x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    calc
      (∫ x in Set.Icc 0 t, series1 x * series2 x)
          = ∫ x in Set.Icc 0 t, ∑' n : ℕ, putnam_1997_a3_Fterm n x := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro x hx
            exact hprod x
      _ = ∫ x in Set.Ioc 0 t, ∑' n : ℕ, putnam_1997_a3_Fterm n x := by
            exact MeasureTheory.integral_Icc_eq_integral_Ioc
      _ = ∫ x in (0 : ℝ)..t, ∑' n : ℕ, putnam_1997_a3_Fterm n x := by
            exact (intervalIntegral.integral_of_le ht).symm
  simpa [putnam_1997_a3_solution] using Filter.Tendsto.congr' h_event.symm htend
