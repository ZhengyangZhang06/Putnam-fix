import Mathlib

open Nat Topology Filter
open MeasureTheory

private noncomputable def putnam_2004_b5_logsum (x : ℝ) : ℝ :=
  ∑' n : ℕ, (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))

private lemma putnam_2004_b5_summable_log_shift {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (k : ℕ) :
    Summable (fun n : ℕ => (1 - x) * x ^ n * Real.log (1 + x ^ (n + k))) := by
  have hgeom : Summable (fun n : ℕ => Real.log 2 * x ^ n) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left _
  refine hgeom.of_norm_bounded (fun n => ?_)
  have hpow0 : 0 ≤ x ^ n := pow_nonneg hx0 n
  have hpowk0 : 0 ≤ x ^ (n + k) := pow_nonneg hx0 (n + k)
  have hpowk1 : x ^ (n + k) ≤ 1 := pow_le_one₀ hx0 hx1.le
  have hlog_nonneg : 0 ≤ Real.log (1 + x ^ (n + k)) := Real.log_nonneg (by linarith)
  have hone_sub : 0 ≤ 1 - x := sub_nonneg.mpr hx1.le
  have hterm_nonneg : 0 ≤ (1 - x) * x ^ n * Real.log (1 + x ^ (n + k)) :=
    mul_nonneg (mul_nonneg hone_sub hpow0) hlog_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
  have hlog_le : Real.log (1 + x ^ (n + k)) ≤ Real.log 2 := by
    exact Real.log_le_log (by linarith) (by linarith)
  calc
    (1 - x) * x ^ n * Real.log (1 + x ^ (n + k))
        ≤ 1 * x ^ n * Real.log 2 := by
          gcongr
          exact sub_le_self 1 hx0
    _ = Real.log 2 * x ^ n := by ring

private lemma putnam_2004_b5_intervalIntegrable_log_one_add_of_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.log (1 + t)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have htpos : 0 < 1 + t := by linarith [ha, ht.1]
  exact ((Real.continuousAt_log htpos.ne').comp
    (continuousAt_const.add continuousAt_id)).continuousWithinAt

private lemma putnam_2004_b5_integral_log_one_add_of_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (1 + t))
      = ((1 + b) * Real.log (1 + b) - (1 + b))
        - ((1 + a) * Real.log (1 + a) - (1 + a)) := by
  let F : ℝ → ℝ := fun t => (1 + t) * Real.log (1 + t) - (1 + t)
  have hcont : ContinuousOn F (Set.Icc a b) := by
    intro t ht
    have htpos : 0 < 1 + t := by linarith [ha, ht.1]
    exact (((continuousAt_const.add continuousAt_id).mul
      ((Real.continuousAt_log htpos.ne').comp (continuousAt_const.add continuousAt_id))).sub
      (continuousAt_const.add continuousAt_id)).continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt F (Real.log (1 + t)) t := by
    intro t ht
    have htne : 1 + t ≠ 0 := by linarith [ha, ht.1.le]
    have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 t := (hasDerivAt_id t).const_add 1
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
      simpa using h1.log htne
    unfold F
    convert (h1.mul hlog).sub h1 using 1
    field_simp [htne]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.log (1 + t)) volume a b :=
    putnam_2004_b5_intervalIntegrable_log_one_add_of_nonneg ha hab
  simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

private lemma putnam_2004_b5_integral_zero_one :
    (∫ t in (0 : ℝ)..1, Real.log (1 + t)) = 2 * Real.log 2 - 1 := by
  rw [putnam_2004_b5_integral_log_one_add_of_nonneg (by norm_num) (by norm_num)]
  norm_num [Real.log_one]
  ring

private lemma putnam_2004_b5_tendsto_geom_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => ∫ t in x ^ N..1, Real.log (1 + t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, Real.log (1 + t))) := by
  have hpow : Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1
  have hbase : Tendsto (fun N : ℕ => 1 + x ^ N) atTop (𝓝 (1 + (0 : ℝ))) :=
    tendsto_const_nhds.add hpow
  have hlog :
      Tendsto (fun N : ℕ => Real.log (1 + x ^ N)) atTop
        (𝓝 (Real.log (1 + (0 : ℝ)))) := by
    simpa [Function.comp_def] using
      Filter.Tendsto.comp (Real.continuousAt_log (by norm_num : (1 + (0 : ℝ)) ≠ 0)) hbase
  have hF :
      Tendsto (fun N : ℕ => (1 + x ^ N) * Real.log (1 + x ^ N) - (1 + x ^ N))
        atTop (𝓝 ((1 + (0 : ℝ)) * Real.log (1 + (0 : ℝ)) - (1 + (0 : ℝ)))) :=
    (hbase.mul hlog).sub hbase
  have hmain : Tendsto (fun N : ℕ =>
      ((1 + (1 : ℝ)) * Real.log (1 + (1 : ℝ)) - (1 + (1 : ℝ)))
        - ((1 + x ^ N) * Real.log (1 + x ^ N) - (1 + x ^ N))) atTop
      (𝓝 (((1 + (1 : ℝ)) * Real.log (1 + (1 : ℝ)) - (1 + (1 : ℝ)))
        - ((1 + (0 : ℝ)) * Real.log (1 + (0 : ℝ)) - (1 + (0 : ℝ))))) :=
    tendsto_const_nhds.sub hF
  have hEqN : (fun N : ℕ => ∫ t in x ^ N..1, Real.log (1 + t)) =ᶠ[atTop]
      (fun N : ℕ => ((1 + (1 : ℝ)) * Real.log (1 + (1 : ℝ)) - (1 + (1 : ℝ)))
        - ((1 + x ^ N) * Real.log (1 + x ^ N) - (1 + x ^ N))) :=
    Eventually.of_forall fun N =>
      putnam_2004_b5_integral_log_one_add_of_nonneg (pow_nonneg hx0 N) (pow_le_one₀ hx0 hx1.le)
  have hEq0 : (∫ t in (0 : ℝ)..1, Real.log (1 + t)) =
      ((1 + (1 : ℝ)) * Real.log (1 + (1 : ℝ)) - (1 + (1 : ℝ)))
        - ((1 + (0 : ℝ)) * Real.log (1 + (0 : ℝ)) - (1 + (0 : ℝ))) :=
    putnam_2004_b5_integral_log_one_add_of_nonneg (by norm_num) (by norm_num)
  rw [hEq0]
  exact Filter.Tendsto.congr' hEqN.symm hmain

private lemma putnam_2004_b5_lower_rect_le_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (n : ℕ) :
    (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))
      ≤ ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t) := by
  have hab : x ^ (n + 1) ≤ x ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hx0 n) hx1.le
  have hint_log : IntervalIntegrable (fun t : ℝ => Real.log (1 + t)) volume
      (x ^ (n + 1)) (x ^ n) :=
    putnam_2004_b5_intervalIntegrable_log_one_add_of_nonneg (pow_nonneg hx0 (n + 1)) hab
  have hmono :
      (∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + x ^ (n + 1)))
        ≤ ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t) := by
    refine intervalIntegral.integral_mono_on hab intervalIntegrable_const hint_log ?_
    intro t ht
    exact Real.log_le_log (by linarith [pow_nonneg hx0 (n + 1)]) (by linarith [ht.1])
  have hdiff : x ^ n - x ^ (n + 1) = (1 - x) * x ^ n := by
    rw [pow_succ]
    ring
  calc
    (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))
        = ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + x ^ (n + 1)) := by
          rw [intervalIntegral.integral_const, hdiff]
          simp [smul_eq_mul]
    _ ≤ ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t) := hmono

private lemma putnam_2004_b5_upper_rect_ge_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (n : ℕ) :
    (∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t))
      ≤ (1 - x) * x ^ n * Real.log (1 + x ^ n) := by
  have hab : x ^ (n + 1) ≤ x ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hx0 n) hx1.le
  have hint_log : IntervalIntegrable (fun t : ℝ => Real.log (1 + t)) volume
      (x ^ (n + 1)) (x ^ n) :=
    putnam_2004_b5_intervalIntegrable_log_one_add_of_nonneg (pow_nonneg hx0 (n + 1)) hab
  have hmono :
      (∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t))
        ≤ ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + x ^ n) := by
    refine intervalIntegral.integral_mono_on hab hint_log intervalIntegrable_const ?_
    intro t ht
    exact Real.log_le_log (by linarith [ht.1, pow_nonneg hx0 (n + 1)]) (by linarith [ht.2])
  have hdiff : x ^ n - x ^ (n + 1) = (1 - x) * x ^ n := by
    rw [pow_succ]
    ring
  calc
    (∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t))
        ≤ ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + x ^ n) := hmono
    _ = (1 - x) * x ^ n * Real.log (1 + x ^ n) := by
          rw [intervalIntegral.integral_const, hdiff]
          simp [smul_eq_mul]

private lemma putnam_2004_b5_geom_integral_sum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t))
      = ∫ t in x ^ N..1, Real.log (1 + t) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ => Real.log (1 + t)) (μ := volume) (a := fun n : ℕ => x ^ n) (n := N)
    (by
      intro k hk
      have hle : x ^ (k + 1) ≤ x ^ k := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hx0 k) hx1.le
      exact (putnam_2004_b5_intervalIntegrable_log_one_add_of_nonneg
        (pow_nonneg hx0 (k + 1)) hle).symm)
  have hflip : ∀ n : ℕ, (∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t))
      = - ∫ t in x ^ n..x ^ (n + 1), Real.log (1 + t) := by
    intro n
    rw [intervalIntegral.integral_symm (a := x ^ n) (b := x ^ (n + 1))]
  calc
    (∑ n ∈ Finset.range N, ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t))
        = - (∑ n ∈ Finset.range N, ∫ t in x ^ n..x ^ (n + 1), Real.log (1 + t)) := by
          simp_rw [hflip]
          rw [Finset.sum_neg_distrib]
    _ = - ∫ t in x ^ 0..x ^ N, Real.log (1 + t) := by rw [hsum]
    _ = ∫ t in x ^ N..1, Real.log (1 + t) := by
          rw [intervalIntegral.integral_symm (a := 1) (b := x ^ N)]
          simp

private lemma putnam_2004_b5_logsum_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ putnam_2004_b5_logsum x := by
  apply tsum_nonneg
  intro n
  have hpow0 : 0 ≤ x ^ n := pow_nonneg hx0 n
  have hpow1 : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 (n + 1)
  have hlog : 0 ≤ Real.log (1 + x ^ (n + 1)) := Real.log_nonneg (by linarith)
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hx1.le) hpow0) hlog

private lemma putnam_2004_b5_logsum_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    putnam_2004_b5_logsum x ≤ (∫ t in (0 : ℝ)..1, Real.log (1 + t)) ∧
      (∫ t in (0 : ℝ)..1, Real.log (1 + t))
        ≤ (1 - x) * Real.log 2 + x * putnam_2004_b5_logsum x := by
  have hLowerSumm :
      Summable (fun n : ℕ => (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))) :=
    putnam_2004_b5_summable_log_shift hx0 hx1 1
  have hUpperSumm : Summable (fun n : ℕ => (1 - x) * x ^ n * Real.log (1 + x ^ n)) :=
    putnam_2004_b5_summable_log_shift hx0 hx1 0
  have hLowerTend :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))) atTop
        (𝓝 (putnam_2004_b5_logsum x)) := by
    simpa [putnam_2004_b5_logsum] using hLowerSumm.hasSum.tendsto_sum_nat
  have hUpperTend :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (1 - x) * x ^ n * Real.log (1 + x ^ n)) atTop
        (𝓝 (∑' n : ℕ, (1 - x) * x ^ n * Real.log (1 + x ^ n))) :=
    hUpperSumm.hasSum.tendsto_sum_nat
  have hIntTend := putnam_2004_b5_tendsto_geom_integral hx0 hx1
  have hlower_event :
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))) ≤ᶠ[atTop]
      (fun N : ℕ => ∫ t in x ^ N..1, Real.log (1 + t)) := by
    exact Eventually.of_forall fun N => by
      calc
        (∑ n ∈ Finset.range N, (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1)))
            ≤ ∑ n ∈ Finset.range N, ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t) := by
              exact Finset.sum_le_sum fun n hn =>
                putnam_2004_b5_lower_rect_le_integral hx0 hx1 n
        _ = ∫ t in x ^ N..1, Real.log (1 + t) :=
              putnam_2004_b5_geom_integral_sum hx0 hx1 N
  have hupper_event :
      (fun N : ℕ => ∫ t in x ^ N..1, Real.log (1 + t)) ≤ᶠ[atTop]
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (1 - x) * x ^ n * Real.log (1 + x ^ n)) := by
    exact Eventually.of_forall fun N => by
      calc
        (∫ t in x ^ N..1, Real.log (1 + t))
            = ∑ n ∈ Finset.range N, ∫ t in x ^ (n + 1)..x ^ n, Real.log (1 + t) :=
              (putnam_2004_b5_geom_integral_sum hx0 hx1 N).symm
        _ ≤ ∑ n ∈ Finset.range N, (1 - x) * x ^ n * Real.log (1 + x ^ n) := by
              exact Finset.sum_le_sum fun n hn =>
                putnam_2004_b5_upper_rect_ge_integral hx0 hx1 n
  have hleLower :
      putnam_2004_b5_logsum x ≤ (∫ t in (0 : ℝ)..1, Real.log (1 + t)) :=
    le_of_tendsto_of_tendsto hLowerTend hIntTend hlower_event
  have hleUpperRaw : (∫ t in (0 : ℝ)..1, Real.log (1 + t))
      ≤ (∑' n : ℕ, (1 - x) * x ^ n * Real.log (1 + x ^ n)) :=
    le_of_tendsto_of_tendsto hIntTend hUpperTend hupper_event
  have hUpperEq : (∑' n : ℕ, (1 - x) * x ^ n * Real.log (1 + x ^ n))
      = (1 - x) * Real.log 2 + x * putnam_2004_b5_logsum x := by
    have hzero :
        (1 - x) * x ^ 0 * Real.log (1 + x ^ 0) = (1 - x) * Real.log 2 := by
      norm_num
    calc
      (∑' n : ℕ, (1 - x) * x ^ n * Real.log (1 + x ^ n))
          = (1 - x) * x ^ 0 * Real.log (1 + x ^ 0)
              + ∑' n : ℕ, (1 - x) * x ^ (n + 1) * Real.log (1 + x ^ (n + 1)) :=
            hUpperSumm.tsum_eq_zero_add
      _ = (1 - x) * Real.log 2
              + ∑' n : ℕ, x * ((1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))) := by
            rw [hzero]
            congr 1
            apply tsum_congr
            intro n
            rw [pow_succ]
            ring
      _ = (1 - x) * Real.log 2 + x * putnam_2004_b5_logsum x := by
            rw [tsum_mul_left]
            rfl
  exact ⟨hleLower, hleUpperRaw.trans_eq hUpperEq⟩

private lemma putnam_2004_b5_logsum_error_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ‖putnam_2004_b5_logsum x - (∫ t in (0 : ℝ)..1, Real.log (1 + t))‖
      ≤ (1 - x) * Real.log 2 := by
  have hb := putnam_2004_b5_logsum_bounds hx0 hx1
  have hSnonneg := putnam_2004_b5_logsum_nonneg hx0 hx1
  have hxmul : (x - 1) * putnam_2004_b5_logsum x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx1.le) hSnonneg
  have hdiff_le :
      (∫ t in (0 : ℝ)..1, Real.log (1 + t)) - putnam_2004_b5_logsum x
        ≤ (1 - x) * Real.log 2 := by
    nlinarith [hb.2, hxmul]
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hb.1)]
  simpa [neg_sub] using hdiff_le

private lemma putnam_2004_b5_tendsto_logsum :
    Tendsto putnam_2004_b5_logsum (𝓝[<] (1 : ℝ)) (𝓝 (2 * Real.log 2 - 1)) := by
  have htoIntegral :
      Tendsto putnam_2004_b5_logsum (𝓝[<] (1 : ℝ))
        (𝓝 (∫ t in (0 : ℝ)..1, Real.log (1 + t))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound_tend :
        Tendsto (fun x : ℝ => (1 - x) * Real.log 2) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hx_tend : Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        continuousAt_id.mono_left nhdsWithin_le_nhds
      have hsub : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝[<] (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
        tendsto_const_nhds.sub hx_tend
      have hmul : Tendsto (fun x : ℝ => ((1 : ℝ) - x) * Real.log 2) (𝓝[<] (1 : ℝ))
          (𝓝 (((1 : ℝ) - 1) * Real.log 2)) :=
        hsub.mul tendsto_const_nhds
      simpa using hmul
    have h_event : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Set.Iio (1 : ℝ)),
        nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds zero_lt_one)] with x hxlt hxpos
      exact ⟨hxpos, hxlt⟩
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hbound_tend
    filter_upwards [h_event] with x hx
    exact putnam_2004_b5_logsum_error_le hx.1.le hx.2
  rw [putnam_2004_b5_integral_zero_one] at htoIntegral
  exact htoIntegral

private lemma putnam_2004_b5_log_sum_identity (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) =
      -Real.log 2 + (∑ n ∈ Finset.range N,
        (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1)))
        + x ^ N * Real.log (1 + x ^ N) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [pow_succ]
      ring

private lemma putnam_2004_b5_tail_tendsto_zero {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => x ^ N * Real.log (1 + x ^ N)) atTop (𝓝 (0 : ℝ)) := by
  have hpow : Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1
  have hbase : Tendsto (fun N : ℕ => 1 + x ^ N) atTop (𝓝 (1 + (0 : ℝ))) :=
    tendsto_const_nhds.add hpow
  have hlog : Tendsto (fun N : ℕ => Real.log (1 + x ^ N)) atTop (𝓝 (0 : ℝ)) := by
    have hlog1 :
        Tendsto (fun N : ℕ => Real.log (1 + x ^ N)) atTop
          (𝓝 (Real.log (1 + (0 : ℝ)))) := by
      simpa [Function.comp_def] using
        Filter.Tendsto.comp (Real.continuousAt_log (by norm_num : (1 + (0 : ℝ)) ≠ 0)) hbase
    simpa [Real.log_one] using hlog1
  simpa using hpow.mul hlog

private lemma putnam_2004_b5_factor_exp {x : ℝ} (hx0 : 0 ≤ x) (n : ℕ) :
    ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n) =
      Real.exp (x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) := by
  have hnum : 0 < 1 + x ^ (n + 1) := by linarith [pow_nonneg hx0 (n + 1)]
  have hden : 0 < 1 + x ^ n := by linarith [pow_nonneg hx0 n]
  have hbase : 0 < (1 + x ^ (n + 1)) / (1 + x ^ n) := div_pos hnum hden
  rw [Real.rpow_def_of_pos hbase]
  rw [Real.log_div hnum.ne' hden.ne']
  ring_nf

private lemma putnam_2004_b5_product_eq_exp_sum {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) :
    (∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)) =
      Real.exp (∑ n ∈ Finset.range N,
        x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) := by
  calc
    (∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
        = ∏ n ∈ Finset.range N,
            Real.exp (x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) := by
          refine Finset.prod_congr rfl ?_
          intro n hn
          exact putnam_2004_b5_factor_exp hx0 n
    _ = Real.exp (∑ n ∈ Finset.range N,
        x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) := by
          rw [Real.exp_sum]

private lemma putnam_2004_b5_products_tendsto {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N,
      ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)) atTop
      (𝓝 (Real.exp (-Real.log 2 + putnam_2004_b5_logsum x))) := by
  have hLowerSumm :
      Summable (fun n : ℕ => (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))) :=
    putnam_2004_b5_summable_log_shift hx0 hx1 1
  have hPartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1))) atTop
      (𝓝 (putnam_2004_b5_logsum x)) := by
    simpa [putnam_2004_b5_logsum] using hLowerSumm.hasSum.tendsto_sum_nat
  have hTail := putnam_2004_b5_tail_tendsto_zero hx0 hx1
  have hTel : Tendsto (fun N : ℕ =>
      -Real.log 2 + (∑ n ∈ Finset.range N,
        (1 - x) * x ^ n * Real.log (1 + x ^ (n + 1)))
        + x ^ N * Real.log (1 + x ^ N)) atTop
      (𝓝 (-Real.log 2 + putnam_2004_b5_logsum x)) := by
    simpa using (tendsto_const_nhds.add hPartial).add hTail
  have hSum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) atTop
      (𝓝 (-Real.log 2 + putnam_2004_b5_logsum x)) :=
    Filter.Tendsto.congr'
      (Eventually.of_forall fun N => (putnam_2004_b5_log_sum_identity x N).symm) hTel
  have hExp : Tendsto (fun N : ℕ => Real.exp (∑ n ∈ Finset.range N,
      x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)))) atTop
      (𝓝 (Real.exp (-Real.log 2 + putnam_2004_b5_logsum x))) := by
    simpa [Function.comp_def] using Filter.Tendsto.comp Real.continuous_exp.continuousAt hSum
  exact Filter.Tendsto.congr'
    (Eventually.of_forall fun N => (putnam_2004_b5_product_eq_exp_sum hx0 N).symm) hExp

-- 2 / Real.exp 1
/--
Evaluate $\lim_{x \to 1^-} \prod_{n=0}^\infty \left(\frac{1+x^{n+1}}{1+x^n}\right)^{x^n}$.
-/
theorem putnam_2004_b5
    (xprod : ℝ → ℝ)
    (hxprod : ∀ x ∈ Set.Ioo 0 1,
      Tendsto (fun N ↦ ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
      atTop (𝓝 (xprod x))) :
    Tendsto xprod (𝓝[<] 1) (𝓝 ((2 / Real.exp 1) : ℝ )) := by
  have h_event : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Set.Iio (1 : ℝ)),
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds zero_lt_one)] with x hxlt hxpos
    exact ⟨hxpos, hxlt⟩
  have hxprod_eq : xprod =ᶠ[𝓝[<] (1 : ℝ)]
      (fun x : ℝ => Real.exp (-Real.log 2 + putnam_2004_b5_logsum x)) := by
    filter_upwards [h_event] with x hx
    exact tendsto_nhds_unique (hxprod x hx)
      (putnam_2004_b5_products_tendsto hx.1.le hx.2)
  have hinner : Tendsto (fun x : ℝ => -Real.log 2 + putnam_2004_b5_logsum x)
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2 - 1)) := by
    have hraw : Tendsto (fun x : ℝ => -Real.log 2 + putnam_2004_b5_logsum x)
        (𝓝[<] (1 : ℝ)) (𝓝 (-Real.log 2 + (2 * Real.log 2 - 1))) :=
      tendsto_const_nhds.add putnam_2004_b5_tendsto_logsum
    convert hraw using 1
    ring_nf
  have hlimit : Tendsto (fun x : ℝ => Real.exp (-Real.log 2 + putnam_2004_b5_logsum x))
      (𝓝[<] (1 : ℝ)) (𝓝 ((2 / Real.exp 1) : ℝ)) := by
    have hExp : Tendsto (fun x : ℝ => Real.exp (-Real.log 2 + putnam_2004_b5_logsum x))
        (𝓝[<] (1 : ℝ)) (𝓝 (Real.exp (Real.log 2 - 1))) := by
      simpa [Function.comp_def] using Filter.Tendsto.comp Real.continuous_exp.continuousAt hinner
    have htarget : Real.exp (Real.log 2 - 1) = (2 / Real.exp 1 : ℝ) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simpa [htarget] using hExp
  exact Filter.Tendsto.congr' hxprod_eq.symm hlimit
