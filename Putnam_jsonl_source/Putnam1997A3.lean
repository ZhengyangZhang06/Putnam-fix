import Mathlib

open Filter Topology

open scoped BigOperators

private noncomputable def putnam1997A3Term (n : ℕ) (x : ℝ) : ℝ :=
  (x * Real.exp (-(x ^ 2 / 2))) *
    (x ^ (2 * n) / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2)

private lemma putnam1997A3_prod_cast (n : ℕ) :
    (∏ i ∈ Finset.range n, ((i : ℝ) + 1)) = (n.factorial : ℝ) := by
  exact_mod_cast Finset.prod_range_add_one_eq_factorial n

private lemma putnam1997A3_prod1_range (n : ℕ) :
    (∏ i ∈ Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)) =
      2 ^ n * (n.factorial : ℝ) := by
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_const]
  simp [putnam1997A3_prod_cast]

private lemma putnam1997A3_prod1 (n : ℕ) :
    (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)) =
      2 ^ n * (n.factorial : ℝ) := by
  rw [← (Finset.prod_subtype (Finset.range n) (by intro x; simp)
    (fun i : ℕ => (2 : ℝ) * ((i : ℝ) + 1)))]
  exact putnam1997A3_prod1_range n

private lemma putnam1997A3_prod2 (n : ℕ) :
    (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2) =
      (2 ^ n * (n.factorial : ℝ)) ^ 2 := by
  rw [← (Finset.prod_subtype (Finset.range n) (by intro x; simp)
    (fun i : ℕ => ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2))]
  rw [Finset.prod_pow]
  rw [putnam1997A3_prod1_range n]

private lemma putnam1997A3_term_s1 (x : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 ^ n * (n.factorial : ℝ)) =
      x * ((-(x ^ 2 / 2)) ^ n / (n.factorial : ℝ)) := by
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
    pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
  rw [show (-(x ^ 2 / 2) : ℝ) ^ n = x ^ (2 * n) * ((-1 / 2 : ℝ) ^ n) by
    ring_nf]
  calc
    (-1 : ℝ) ^ n * x ^ (2 * n + 1) = x * x ^ (2 * n) * (-1 : ℝ) ^ n := by
      ring_nf
    _ = x * x ^ (2 * n) * (((-1 / 2 : ℝ) ^ n) * (2 : ℝ) ^ n) := by
      rw [show ((-1 / 2 : ℝ) ^ n) * (2 : ℝ) ^ n = (-1 : ℝ) ^ n by
        rw [← mul_pow]
        norm_num]
    _ = (2 : ℝ) ^ n * x * (x ^ (2 * n) * (-1 / 2 : ℝ) ^ n) := by
      ring

private lemma putnam1997A3_series1_point (x : ℝ) :
    (∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
      (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1))) =
      x * Real.exp (-(x ^ 2 / 2)) := by
  have hexp :
      (∑' n : ℕ, (-(x ^ 2 / 2) : ℝ) ^ n / (n.factorial : ℝ)) =
        Real.exp (-(x ^ 2 / 2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (-(x ^ 2 / 2) : ℝ)).tsum_eq
  calc
    (∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
      (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1)))
        = ∑' n : ℕ, x * ((-(x ^ 2 / 2)) ^ n / (n.factorial : ℝ)) := by
          apply tsum_congr
          intro n
          rw [putnam1997A3_prod1 n]
          exact putnam1997A3_term_s1 x n
    _ = x * (∑' n : ℕ, (-(x ^ 2 / 2)) ^ n / (n.factorial : ℝ)) := by
      rw [tsum_mul_left]
    _ = x * Real.exp (-(x ^ 2 / 2)) := by
      rw [hexp]

private lemma putnam1997A3_half_power (n : ℕ) :
    (1 / 2 : ℝ) ^ (-(↑n + 1 : ℝ)) * (1 / 2 : ℝ) = (2 : ℝ) ^ n := by
  rw [show (1 / 2 : ℝ) ^ (-(↑n + 1 : ℝ)) =
      ((1 / 2 : ℝ) ^ ((n + 1 : ℕ)))⁻¹ by
    rw [show (↑n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by norm_num]
    rw [← Real.rpow_natCast]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]]
  rw [pow_succ]
  rw [show (((1 / 2 : ℝ) ^ n * (1 / 2))⁻¹ * (1 / 2)) =
      ((1 / 2 : ℝ) ^ n)⁻¹ by
    field_simp [pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0)]]
  rw [show ((1 / 2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ n by
    rw [← inv_pow]
    norm_num]

private lemma putnam1997A3_base_integral (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ),
      x ^ (2 * n + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      (2 : ℝ) ^ n * (n.factorial : ℝ) := by
  have hq : (-1 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := ((2 * n + 1 : ℕ) : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num : (0 : ℝ) < 2) hq (by norm_num : (0 : ℝ) < 1 / 2)
  calc
    (∫ x in Set.Ioi (0 : ℝ),
      x ^ (2 * n + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        = ∫ x in Set.Ioi (0 : ℝ),
            x ^ (((2 * n + 1 : ℕ) : ℝ)) *
              Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          change x ^ (2 * n + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
            x ^ (((2 * n + 1 : ℕ) : ℝ)) *
              Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))
          rw [Real.rpow_natCast, Real.rpow_ofNat]
    _ = (1 / 2 : ℝ) ^ (-(((2 * n + 1 : ℕ) : ℝ) + 1) / 2) *
          (1 / 2 : ℝ) * Real.Gamma ((((2 * n + 1 : ℕ) : ℝ) + 1) / 2) := h
    _ = (2 : ℝ) ^ n * (n.factorial : ℝ) := by
          rw [show ((((2 * n + 1 : ℕ) : ℝ) + 1) / 2) = (n : ℝ) + 1 by
            norm_num
            ring]
          rw [show (-(((2 * n + 1 : ℕ) : ℝ) + 1) / 2) = -(↑n + 1 : ℝ) by
            norm_num
            ring]
          rw [Real.Gamma_nat_eq_factorial]
          rw [putnam1997A3_half_power n]

private lemma putnam1997A3_coeff_integral (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), putnam1997A3Term n x) =
      1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) := by
  let d : ℝ := (2 : ℝ) ^ n * (n.factorial : ℝ)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact mul_ne_zero (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  calc
    (∫ x in Set.Ioi (0 : ℝ), putnam1997A3Term n x)
        = ∫ x in Set.Ioi (0 : ℝ),
            (1 / d ^ 2) *
              (x ^ (2 * n + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          dsimp [putnam1997A3Term, d]
          field_simp [hd]
          ring_nf
    _ = (1 / d ^ 2) *
          (∫ x in Set.Ioi (0 : ℝ),
            x ^ (2 * n + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
    _ = 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) := by
          rw [putnam1997A3_base_integral n]
          dsimp [d]
          field_simp [hd]

private lemma putnam1997A3_coeff_integrable (n : ℕ) :
    MeasureTheory.IntegrableOn (putnam1997A3Term n) (Set.Ioi (0 : ℝ)) := by
  let d : ℝ := (2 : ℝ) ^ n * (n.factorial : ℝ)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact mul_ne_zero (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hq : (-1 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hbase : MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        x ^ (((2 * n + 1 : ℕ) : ℝ)) *
          Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (s := ((2 * n + 1 : ℕ) : ℝ)) (b := (1 / 2 : ℝ))
      hq (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1 / 2)
  refine MeasureTheory.IntegrableOn.congr_fun (hbase.const_mul (1 / d ^ 2)) ?_
    measurableSet_Ioi
  intro x hx
  change (1 / d ^ 2) *
      (x ^ (((2 * n + 1 : ℕ) : ℝ)) *
        Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))) =
    putnam1997A3Term n x
  dsimp [putnam1997A3Term, d]
  rw [Real.rpow_natCast, Real.rpow_ofNat]
  field_simp [hd]
  ring_nf

private lemma putnam1997A3_coeff_nonneg (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    0 ≤ putnam1997A3Term n x := by
  dsimp [putnam1997A3Term]
  have hx0 : 0 ≤ x := le_of_lt hx
  positivity

private lemma putnam1997A3_summable_coeff :
    Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ))) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, inv_pow]
    using Real.summable_pow_div_factorial (1 / 2 : ℝ)

private lemma putnam1997A3_tsum_coeff :
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ))) =
      Real.exp (1 / 2) := by
  have hterm : ∀ n : ℕ,
      (1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ)) =
        (1 / 2 : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
      pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 by
      rw [← mul_pow]
      norm_num]
  calc
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ)))
        = ∑' n : ℕ, (1 / 2 : ℝ) ^ n / (n.factorial : ℝ) := by
          exact tsum_congr hterm
    _ = Real.exp (1 / 2) := by
          rw [Real.exp_eq_exp_ℝ]
          exact (NormedSpace.expSeries_div_hasSum_exp (1 / 2 : ℝ)).tsum_eq

private lemma putnam1997A3_norm_integral (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), ‖putnam1997A3Term n x‖) =
      (1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ)) := by
  calc
    (∫ x in Set.Ioi (0 : ℝ), ‖putnam1997A3Term n x‖)
        = ∫ x in Set.Ioi (0 : ℝ), putnam1997A3Term n x := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          exact Real.norm_of_nonneg (putnam1997A3_coeff_nonneg n hx)
    _ = (1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ)) :=
          putnam1997A3_coeff_integral n

private lemma putnam1997A3_integral_series :
    (∫ x in Set.Ioi (0 : ℝ), ∑' n : ℕ, putnam1997A3Term n x) =
      Real.exp (1 / 2) := by
  have hsum_norm :
      Summable (fun n : ℕ =>
        ∫ x in Set.Ioi (0 : ℝ), ‖putnam1997A3Term n x‖) :=
    putnam1997A3_summable_coeff.congr
      (fun n => (putnam1997A3_norm_integral n).symm)
  have hswap :
      (∫ x in Set.Ioi (0 : ℝ), ∑' n : ℕ, putnam1997A3Term n x) =
        ∑' n : ℕ, ∫ x in Set.Ioi (0 : ℝ), putnam1997A3Term n x := by
    symm
    exact MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (F := fun n x => putnam1997A3Term n x)
      (fun n => putnam1997A3_coeff_integrable n) hsum_norm
  rw [hswap]
  calc
    (∑' n : ℕ, ∫ x in Set.Ioi (0 : ℝ), putnam1997A3Term n x)
        = ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ)) := by
          exact tsum_congr putnam1997A3_coeff_integral
    _ = Real.exp (1 / 2) := putnam1997A3_tsum_coeff

private lemma putnam1997A3_integrable_series :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => ∑' n : ℕ, putnam1997A3Term n x) (Set.Ioi (0 : ℝ)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hF_int : ∀ n : ℕ, MeasureTheory.Integrable (putnam1997A3Term n) μ := by
    intro n
    exact putnam1997A3_coeff_integrable n
  have hsum_norm :
      Summable (fun n : ℕ => ∫ x, ‖putnam1997A3Term n x‖ ∂μ) := by
    change Summable (fun n : ℕ =>
      ∫ x in Set.Ioi (0 : ℝ), ‖putnam1997A3Term n x‖)
    exact putnam1997A3_summable_coeff.congr
      (fun n => (putnam1997A3_norm_integral n).symm)
  have hlin_ne :
      (∑' n : ℕ, (∫⁻ x, ‖putnam1997A3Term n x‖ₑ ∂μ)) ≠ (⊤ : ENNReal) := by
    have hlin_eq :
        (fun n : ℕ => (∫⁻ x, ‖putnam1997A3Term n x‖ₑ ∂μ)) =
          fun n : ℕ => ‖∫ x, ‖putnam1997A3Term n x‖ ∂μ‖ₑ := by
      funext n
      dsimp [enorm]
      rw [MeasureTheory.lintegral_coe_eq_integral _ (hF_int n).norm]
      rw [ENNReal.coe_nnreal_eq]
      congr 1
      simp only [coe_nnnorm]
      change (∫ a : ℝ, ‖putnam1997A3Term n a‖ ∂μ) =
        ‖∫ x : ℝ, ‖putnam1997A3Term n x‖ ∂μ‖
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg
        (fun x => norm_nonneg (putnam1997A3Term n x)))]
    rw [hlin_eq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hsum_norm.abs
  have hF_enorm_meas :
      ∀ n : ℕ, AEMeasurable (fun x => ‖putnam1997A3Term n x‖ₑ) μ := by
    intro n
    exact (hF_int n).aemeasurable.enorm
  have hbound_lintegral :
      (∫⁻ x, ∑' n : ℕ, ‖putnam1997A3Term n x‖ₑ ∂μ) < (⊤ : ENNReal) := by
    rw [MeasureTheory.lintegral_tsum hF_enorm_meas]
    exact lt_top_iff_ne_top.mpr hlin_ne
  have hnorm_summable_ae :
      ∀ᵐ x ∂μ, Summable fun n : ℕ => (‖putnam1997A3Term n x‖₊ : ℝ) := by
    rw [← MeasureTheory.lintegral_tsum hF_enorm_meas] at hlin_ne
    refine (MeasureTheory.ae_lt_top' (AEMeasurable.ennreal_tsum hF_enorm_meas) hlin_ne).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    simpa [enorm_eq_nnnorm] using hx.ne
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ => ∑' n : ℕ, putnam1997A3Term n x) μ := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter ℕ))
      (f := fun N => ∑ n ∈ Finset.range N, putnam1997A3Term n)
      (g := fun x : ℝ => ∑' n : ℕ, putnam1997A3Term n x) ?_ ?_
    · intro N
      simpa using Finset.aestronglyMeasurable_sum (Finset.range N)
        (fun n hn => (hF_int n).aestronglyMeasurable)
    · refine hnorm_summable_ae.mono ?_
      intro x hx
      simpa using hx.of_norm.hasSum.tendsto_sum_nat
  refine ⟨hmeas, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt
    (MeasureTheory.lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
    hbound_lintegral

private lemma putnam1997A3_product_series_point (x : ℝ) :
    ((∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
        (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1))) *
      (∑' n : ℕ, x ^ (2 * n) /
        (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2))) =
      ∑' n : ℕ, putnam1997A3Term n x := by
  calc
    ((∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
        (∏ i : Finset.range n, (2 : ℝ) * ((i : ℝ) + 1))) *
      (∑' n : ℕ, x ^ (2 * n) /
        (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2)))
        = (x * Real.exp (-(x ^ 2 / 2))) *
            (∑' n : ℕ, x ^ (2 * n) /
              (∏ i : Finset.range n, ((2 : ℝ) * ((i : ℝ) + 1)) ^ 2)) := by
          rw [putnam1997A3_series1_point x]
    _ = (x * Real.exp (-(x ^ 2 / 2))) *
          (∑' n : ℕ, x ^ (2 * n) /
            (((2 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2)) := by
          congr 1
          apply tsum_congr
          intro n
          rw [putnam1997A3_prod2 n]
    _ = ∑' n : ℕ, (x * Real.exp (-(x ^ 2 / 2))) *
        (x ^ (2 * n) / (((2 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2)) := by
          rw [← tsum_mul_left]
    _ = ∑' n : ℕ, putnam1997A3Term n x := by
          rfl

-- Real.sqrt (Real.exp 1)
/--
Evaluate \begin{gather*} \int_0^\infty \left(x-\frac{x^3}{2}+\frac{x^5}{2\cdot 4}-\frac{x^7}{2\cdot 4\cdot 6}+\cdots\right) \\ \left(1+\frac{x^2}{2^2}+\frac{x^4}{2^2\cdot 4^2}+\frac{x^6}{2^2\cdot 4^2 \cdot 6^2}+\cdots\right)\,dx. \end{gather*}
-/
theorem putnam_1997_a3
(series1 series2 : ℝ → ℝ)
(hseries1 : series1 = fun x => ∑' n : ℕ, (-1)^n * x^(2*n + 1)/(∏ i : Finset.range n, 2 * ((i : ℝ) + 1)))
(hseries2 : series2 = fun x => ∑' n : ℕ, x^(2*n)/(∏ i : Finset.range n, (2 * ((i : ℝ) + 1))^2))
: Tendsto (fun t => ∫ x in Set.Icc 0 t, series1 x * series2 x) atTop (𝓝 (((Real.sqrt (Real.exp 1)) : ℝ ))) := by
  have hprod : ∀ x : ℝ,
      series1 x * series2 x = ∑' n : ℕ, putnam1997A3Term n x := by
    intro x
    rw [hseries1, hseries2]
    exact putnam1997A3_product_series_point x
  have hlim_interval :
      Tendsto
        (fun t : ℝ => ∫ x in (0 : ℝ)..t, ∑' n : ℕ, putnam1997A3Term n x)
        atTop
        (𝓝 (Real.exp (1 / 2))) := by
    simpa [putnam1997A3_integral_series] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        (μ := MeasureTheory.volume)
        (f := fun x : ℝ => ∑' n : ℕ, putnam1997A3Term n x)
        (a := (0 : ℝ))
        putnam1997A3_integrable_series
        (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
  have hlim_Icc :
      Tendsto
        (fun t : ℝ => ∫ x in Set.Icc (0 : ℝ) t, ∑' n : ℕ, putnam1997A3Term n x)
        atTop
        (𝓝 (Real.exp (1 / 2))) := by
    refine Filter.Tendsto.congr' ?_ hlim_interval
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [intervalIntegral.integral_of_le ht, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hlim_original :
      Tendsto (fun t => ∫ x in Set.Icc 0 t, series1 x * series2 x)
        atTop (𝓝 (Real.exp (1 / 2))) := by
    refine Filter.Tendsto.congr' ?_ hlim_Icc
    filter_upwards with t
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x hx => (hprod x).symm)
  have hsqrt : Real.exp (1 / 2 : ℝ) = Real.sqrt (Real.exp 1) := by
    simpa using Real.exp_half (1 : ℝ)
  rw [hsqrt] at hlim_original
  simpa using hlim_original
