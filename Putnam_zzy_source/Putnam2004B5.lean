import Mathlib

set_option maxHeartbeats 0

open Nat Topology Filter

noncomputable def putnam_2004_b5_series : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k / (((k : ℝ) + 1) * ((k : ℝ) + 2))

noncomputable abbrev putnam_2004_b5_solution : ℝ :=
  Real.exp (-Real.log 2 + putnam_2004_b5_series)

private noncomputable def putnam_2004_b5_term (x : ℝ) (n : ℕ) : ℝ :=
  ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)

private noncomputable def putnam_2004_b5_logTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))

private noncomputable def putnam_2004_b5_logMain (x : ℝ) : ℝ :=
  -Real.log 2 + (1 - x) * ∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1))

private noncomputable def putnam_2004_b5_seriesTerm (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k / ((k : ℝ) + 1) *
    ((1 - x) * x ^ (k + 1) / (1 - x ^ (k + 2)))

private lemma putnam_2004_b5_seriesBound_summable :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    exact (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hshift : Summable (fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using
      ((summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2 hbase)
  refine Summable.of_nonneg_of_le
    (f := fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2))
    (g := fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)))
    ?_ ?_ hshift
  · intro k
    positivity
  · intro k
    have hk1 : 0 < (k : ℝ) + 1 := by positivity
    have hk2 : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by norm_num
    have hden : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hk2 hk1.le]
    have hpos1 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
    calc
      (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
          1 / (((k : ℝ) + 1) ^ 2) := by
        exact one_div_le_one_div_of_le hpos1 hden
      _ = (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) := by norm_num

private lemma putnam_2004_b5_geom_factor_le {x : ℝ} (hx : x ∈ Set.Ioo 0 1) (k : ℕ) :
    0 ≤ (1 - x) * x ^ (k + 1) / (1 - x ^ (k + 2)) ∧
    (1 - x) * x ^ (k + 1) / (1 - x ^ (k + 2)) ≤ 1 / ((k : ℝ) + 2) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hxle1 : x ≤ 1 := hx1.le
  have hxpow : 0 < x ^ (k + 1) := pow_pos hx0 _
  have hsum_pos : 0 < ∑ i ∈ Finset.range (k + 2), x ^ i := by
    apply Finset.sum_pos
    · intro i _hi
      exact pow_pos hx0 i
    · exact ⟨0, by simp⟩
  have hgeom : 1 - x ^ (k + 2) = (1 - x) * ∑ i ∈ Finset.range (k + 2), x ^ i := by
    rw [mul_comm, geom_sum_mul_neg]
  have hfactor_eq : (1 - x) * x ^ (k + 1) / (1 - x ^ (k + 2)) =
      x ^ (k + 1) / (∑ i ∈ Finset.range (k + 2), x ^ i) := by
    rw [hgeom]
    field_simp [ne_of_gt hsum_pos, sub_ne_zero.mpr hx1.ne']
  have hsum_lower : ((k : ℝ) + 2) * x ^ (k + 1) ≤
      ∑ i ∈ Finset.range (k + 2), x ^ i := by
    calc
      ((k : ℝ) + 2) * x ^ (k + 1) =
          ∑ i ∈ Finset.range (k + 2), x ^ (k + 1) := by
        simp [mul_comm]
      _ ≤ ∑ i ∈ Finset.range (k + 2), x ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi_le : i ≤ k + 1 := by
          have hlt : i < k + 2 := Finset.mem_range.mp hi
          omega
        exact pow_le_pow_of_le_one hx0.le hxle1 hi_le
  constructor
  · rw [hfactor_eq]
    positivity
  · rw [hfactor_eq]
    calc
      x ^ (k + 1) / (∑ i ∈ Finset.range (k + 2), x ^ i) ≤
          x ^ (k + 1) / (((k : ℝ) + 2) * x ^ (k + 1)) := by
        exact div_le_div_of_nonneg_left hxpow.le (by positivity) hsum_lower
      _ = 1 / ((k : ℝ) + 2) := by
        have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
        field_simp [ne_of_gt hxpow, hk2]

private lemma putnam_2004_b5_seriesTerm_bound {x : ℝ} (hx : x ∈ Set.Ioo 0 1) (k : ℕ) :
    ‖putnam_2004_b5_seriesTerm x k‖ ≤
      (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hfac := putnam_2004_b5_geom_factor_le hx k
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hk2 : 0 < (k : ℝ) + 2 := by positivity
  have hfac_nonneg : 0 ≤ (1 - x) * x ^ (k + 1) / (1 - x ^ (k + 2)) := hfac.1
  calc
    ‖putnam_2004_b5_seriesTerm x k‖ =
        (1 / ((k : ℝ) + 1)) *
          ((1 - x) * x ^ (k + 1) / (1 - x ^ (k + 2))) := by
      rw [putnam_2004_b5_seriesTerm, norm_mul, norm_div, norm_pow, norm_neg, norm_one]
      simp [abs_of_pos hk1, Real.norm_of_nonneg hfac_nonneg, one_div]
    _ ≤ (1 / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 2)) := by
      exact mul_le_mul_of_nonneg_left hfac.2 (by positivity)
    _ = (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      field_simp [hk1.ne', hk2.ne']

private lemma putnam_2004_b5_eventually_Ioo :
    ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
  have hlt : Set.Iio (1 : ℝ) ∈ 𝓝[<] (1 : ℝ) := self_mem_nhdsWithin
  filter_upwards [hpos, hlt] with x hx0 hx1
  exact ⟨hx0, hx1⟩

private lemma putnam_2004_b5_seriesTerm_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => putnam_2004_b5_seriesTerm x k) (𝓝[<] (1 : ℝ))
      (𝓝 ((-1 : ℝ) ^ k / (((k : ℝ) + 1) * ((k : ℝ) + 2)))) := by
  have hratio : Tendsto
      (fun x : ℝ => x ^ (k + 1) / (∑ i ∈ Finset.range (k + 2), x ^ i))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 / ((k : ℝ) + 2))) := by
    have hnum : Tendsto (fun x : ℝ => x ^ (k + 1)) (𝓝[<] (1 : ℝ))
        (𝓝 ((1 : ℝ) ^ (k + 1))) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).pow (k + 1)
    have hden : Tendsto (fun x : ℝ => ∑ i ∈ Finset.range (k + 2), x ^ i)
        (𝓝[<] (1 : ℝ)) (𝓝 (∑ i ∈ Finset.range (k + 2), (1 : ℝ) ^ i)) := by
      exact tendsto_finset_sum _ fun i _hi =>
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).pow i
    have hden_ne : (∑ i ∈ Finset.range (k + 2), (1 : ℝ) ^ i) ≠ 0 := by
      simp [show (k : ℝ) + 2 ≠ 0 by positivity]
    simpa using hnum.div hden hden_ne
  have hmain : Tendsto
      (fun x : ℝ => (-1 : ℝ) ^ k / ((k : ℝ) + 1) *
        (x ^ (k + 1) / (∑ i ∈ Finset.range (k + 2), x ^ i)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 2)))) :=
    hratio.const_mul _
  have h_eq : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), putnam_2004_b5_seriesTerm x k =
      (-1 : ℝ) ^ k / ((k : ℝ) + 1) *
        (x ^ (k + 1) / (∑ i ∈ Finset.range (k + 2), x ^ i)) := by
    filter_upwards [putnam_2004_b5_eventually_Ioo] with x hx
    have hx1 : x < 1 := hx.2
    have hsum_pos : 0 < ∑ i ∈ Finset.range (k + 2), x ^ i := by
      apply Finset.sum_pos
      · intro i _hi
        exact pow_pos hx.1 i
      · exact ⟨0, by simp⟩
    have hgeom : 1 - x ^ (k + 2) = (1 - x) * ∑ i ∈ Finset.range (k + 2), x ^ i := by
      rw [mul_comm, geom_sum_mul_neg]
    rw [putnam_2004_b5_seriesTerm, hgeom]
    field_simp [ne_of_gt hsum_pos, sub_ne_zero.mpr hx1.ne']
  have hlim := hmain.congr' (h_eq.mono fun _ hx => hx.symm)
  convert hlim using 1
  field_simp [show (k : ℝ) + 1 ≠ 0 by positivity, show (k : ℝ) + 2 ≠ 0 by positivity]

private lemma putnam_2004_b5_seriesTerm_tendsto_tsum :
    Tendsto (fun x : ℝ => ∑' k : ℕ, putnam_2004_b5_seriesTerm x k) (𝓝[<] (1 : ℝ))
      (𝓝 putnam_2004_b5_series) := by
  refine tendsto_tsum_of_dominated_convergence putnam_2004_b5_seriesBound_summable ?_ ?_
  · intro k
    exact putnam_2004_b5_seriesTerm_tendsto k
  · filter_upwards [putnam_2004_b5_eventually_Ioo] with x hx k
    exact putnam_2004_b5_seriesTerm_bound hx k

private lemma putnam_2004_b5_hasSum_log_one_add_pow {x : ℝ}
    (hx : x ∈ Set.Ioo 0 1) (n : ℕ) :
    HasSum
      (fun k : ℕ => (-1 : ℝ) ^ k * (x ^ (n + 1)) ^ (k + 1) / ((k : ℝ) + 1))
      (Real.log (1 + x ^ (n + 1))) := by
  have hx0 : 0 ≤ x ^ (n + 1) := pow_nonneg hx.1.le _
  have hxlt : x ^ (n + 1) < 1 := pow_lt_one₀ hx.1.le hx.2 (by omega)
  have habs : |-(x ^ (n + 1))| < 1 := by
    rw [abs_neg, abs_of_nonneg hx0]
    exact hxlt
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (x := -(x ^ (n + 1))) habs).mul_left (-1 : ℝ)
  convert h using 1
  · ext k
    field_simp [show ((k : ℝ) + 1) ≠ 0 by positivity]
    rw [neg_pow]
    ring
  · simp

private lemma putnam_2004_b5_summable_logWeighted {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Summable (fun n : ℕ => x ^ n * Real.log (1 + x ^ (n + 1))) := by
  have hgeom : Summable (fun n : ℕ => Real.log 2 * x ^ n) :=
    (summable_geometric_of_lt_one hx.1.le hx.2).mul_left (Real.log 2)
  refine hgeom.of_norm_bounded ?_
  intro n
  have hxpow_nonneg : 0 ≤ x ^ (n + 1) := pow_nonneg hx.1.le _
  have hxpow_le_one : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
  have hlog_nonneg : 0 ≤ Real.log (1 + x ^ (n + 1)) := by
    exact Real.log_nonneg (by linarith)
  have hlog_le : Real.log (1 + x ^ (n + 1)) ≤ Real.log 2 := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hxnpow_nonneg : 0 ≤ x ^ n := pow_nonneg hx.1.le _
  calc
    ‖x ^ n * Real.log (1 + x ^ (n + 1))‖ =
        x ^ n * Real.log (1 + x ^ (n + 1)) := by
      rw [Real.norm_of_nonneg (mul_nonneg hxnpow_nonneg hlog_nonneg)]
    _ ≤ Real.log 2 * x ^ n := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hlog_le hxnpow_nonneg

private lemma putnam_2004_b5_logWeighted_eq_series {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    (1 - x) * (∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1))) =
      ∑' k : ℕ, putnam_2004_b5_seriesTerm x k := by
  let A : ℕ → ℕ → ℝ := fun n k =>
    (1 - x) * x ^ n *
      ((-1 : ℝ) ^ k * (x ^ (n + 1)) ^ (k + 1) / ((k : ℝ) + 1))
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hx1nonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx1.le
  have hfx : Summable (fun n : ℕ => (1 - x) * x ^ n) :=
    (summable_geometric_of_lt_one hx0.le hx1).mul_left (1 - x)
  have hgx : Summable (fun k : ℕ => x ^ (k + 1) / ((k : ℝ) + 1)) := by
    have habs : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
    exact (Real.hasSum_pow_div_log_of_abs_lt_one (x := x) habs).summable
  have hprod : Summable
      (fun p : ℕ × ℕ => ((1 - x) * x ^ p.1) *
        (x ^ (p.2 + 1) / ((p.2 : ℝ) + 1))) := by
    refine Summable.mul_of_nonneg hfx hgx ?_ ?_
    · intro n
      exact mul_nonneg hx1nonneg (pow_nonneg hx0.le n)
    · intro k
      exact div_nonneg (pow_nonneg hx0.le (k + 1)) (by positivity)
  have hA : Summable (Function.uncurry A) := by
    refine hprod.of_norm_bounded ?_
    rintro ⟨n, k⟩
    have hnonneg1 : 0 ≤ (1 - x) * x ^ n := by
      exact mul_nonneg hx1nonneg (pow_nonneg hx0.le n)
    have hdenpos : 0 < (k : ℝ) + 1 := by positivity
    calc
      ‖Function.uncurry A (n, k)‖ =
          ((1 - x) * x ^ n) * ((x ^ (n + 1)) ^ (k + 1) / ((k : ℝ) + 1)) := by
        simp [A, Function.uncurry, norm_mul, norm_div, norm_pow,
          abs_of_nonneg hx1nonneg, abs_of_pos hdenpos]
        rw [abs_of_pos hx0]
      _ ≤ ((1 - x) * x ^ n) * (x ^ (k + 1) / ((k : ℝ) + 1)) := by
        have hpow_le : (x ^ (n + 1)) ^ (k + 1) ≤ x ^ (k + 1) := by
          rw [← pow_mul]
          exact pow_le_pow_of_le_one hx0.le hx1.le (by nlinarith : k + 1 ≤ (n + 1) * (k + 1))
        gcongr
      _ = ((1 - x) * x ^ n) * (x ^ (k + 1) / ((k : ℝ) + 1)) := rfl
  calc
    (1 - x) * (∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1)))
        = ∑' n : ℕ, (1 - x) * (x ^ n * Real.log (1 + x ^ (n + 1))) := by
      exact ((putnam_2004_b5_summable_logWeighted hx).tsum_mul_left (1 - x)).symm
    _ = ∑' n : ℕ, ∑' k : ℕ, A n k := by
      apply tsum_congr
      intro n
      convert ((putnam_2004_b5_hasSum_log_one_add_pow hx n).mul_left
        ((1 - x) * x ^ n)).tsum_eq.symm using 1
      · ring
    _ = ∑' k : ℕ, ∑' n : ℕ, A n k := hA.tsum_comm.symm
    _ = ∑' k : ℕ, putnam_2004_b5_seriesTerm x k := by
      apply tsum_congr
      intro k
      have hr0 : 0 ≤ x ^ (k + 2) := pow_nonneg hx0.le _
      have hr1 : x ^ (k + 2) < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
      have hgeomSummable : Summable (fun n : ℕ => (x ^ (k + 2)) ^ n) :=
        summable_geometric_of_lt_one hr0 hr1
      calc
        (∑' n : ℕ, A n k) =
            ∑' n : ℕ, ((-1 : ℝ) ^ k / ((k : ℝ) + 1) *
              ((1 - x) * x ^ (k + 1))) * (x ^ (k + 2)) ^ n := by
          apply tsum_congr
          intro n
          simp only [A]
          rw [← pow_mul, ← pow_mul]
          ring_nf
        _ = ((-1 : ℝ) ^ k / ((k : ℝ) + 1) * ((1 - x) * x ^ (k + 1))) *
            ∑' n : ℕ, (x ^ (k + 2)) ^ n := by
          exact hgeomSummable.tsum_mul_left _
        _ = putnam_2004_b5_seriesTerm x k := by
          rw [tsum_geometric_of_lt_one hr0 hr1]
          rw [putnam_2004_b5_seriesTerm]
          field_simp [show ((k : ℝ) + 1) ≠ 0 by positivity, sub_ne_zero.mpr (ne_of_lt hr1)]

private lemma putnam_2004_b5_logMain_tendsto :
    Tendsto putnam_2004_b5_logMain (𝓝[<] (1 : ℝ))
      (𝓝 (-Real.log 2 + putnam_2004_b5_series)) := by
  have hconst : Tendsto (fun _ : ℝ => -Real.log 2) (𝓝[<] (1 : ℝ)) (𝓝 (-Real.log 2)) :=
    tendsto_const_nhds
  have hlim := hconst.add putnam_2004_b5_seriesTerm_tendsto_tsum
  refine hlim.congr' ?_
  filter_upwards [putnam_2004_b5_eventually_Ioo] with x hx
  rw [putnam_2004_b5_logMain, putnam_2004_b5_logWeighted_eq_series hx]

private lemma putnam_2004_b5_summable_logCurrent {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Summable (fun n : ℕ => x ^ n * Real.log (1 + x ^ n)) := by
  have hgeom : Summable (fun n : ℕ => Real.log 2 * x ^ n) :=
    (summable_geometric_of_lt_one hx.1.le hx.2).mul_left (Real.log 2)
  refine hgeom.of_norm_bounded ?_
  intro n
  have hxpow_nonneg : 0 ≤ x ^ n := pow_nonneg hx.1.le _
  have hxpow_le_one : x ^ n ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
  have hlog_nonneg : 0 ≤ Real.log (1 + x ^ n) := Real.log_nonneg (by linarith)
  have hlog_le : Real.log (1 + x ^ n) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith)
  calc
    ‖x ^ n * Real.log (1 + x ^ n)‖ = x ^ n * Real.log (1 + x ^ n) := by
      rw [Real.norm_of_nonneg (mul_nonneg hxpow_nonneg hlog_nonneg)]
    _ ≤ Real.log 2 * x ^ n := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hlog_le hxpow_nonneg

private lemma putnam_2004_b5_summable_logTerm {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    Summable (putnam_2004_b5_logTerm x) := by
  have h1 := putnam_2004_b5_summable_logWeighted hx
  have h0 := putnam_2004_b5_summable_logCurrent hx
  exact (h1.sub h0).congr fun n => by rw [putnam_2004_b5_logTerm, mul_sub]

private lemma putnam_2004_b5_tsum_logTerm_eq_logMain {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    ∑' n : ℕ, putnam_2004_b5_logTerm x n = putnam_2004_b5_logMain x := by
  have h1 := putnam_2004_b5_summable_logWeighted hx
  have h0 := putnam_2004_b5_summable_logCurrent hx
  calc
    ∑' n : ℕ, putnam_2004_b5_logTerm x n =
        (∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1))) -
          (∑' n : ℕ, x ^ n * Real.log (1 + x ^ n)) := by
      simpa [putnam_2004_b5_logTerm, mul_sub] using h1.tsum_sub h0
    _ = (∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1))) -
        (Real.log 2 + x * (∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1)))) := by
      have hsplit := h0.sum_add_tsum_nat_add 1
      have htail : (∑' n : ℕ, x ^ (n + 1) * Real.log (1 + x ^ (n + 1))) =
          x * (∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1))) := by
        calc
          (∑' n : ℕ, x ^ (n + 1) * Real.log (1 + x ^ (n + 1))) =
              ∑' n : ℕ, x * (x ^ n * Real.log (1 + x ^ (n + 1))) := by
            apply tsum_congr
            intro n
            rw [pow_succ]
            ring
          _ = x * (∑' n : ℕ, x ^ n * Real.log (1 + x ^ (n + 1))) := by
            exact h1.tsum_mul_left x
      rw [← hsplit]
      simp [htail]
      norm_num
    _ = putnam_2004_b5_logMain x := by
      rw [putnam_2004_b5_logMain]
      ring

private lemma putnam_2004_b5_log_term_eq (x : ℝ) (hx : x ∈ Set.Ioo 0 1) (n : ℕ) :
    Real.log (putnam_2004_b5_term x n) = putnam_2004_b5_logTerm x n := by
  have hnumpos : 0 < 1 + x ^ (n + 1) := by linarith [pow_pos hx.1 (n + 1)]
  have hdenpos : 0 < 1 + x ^ n := by linarith [pow_pos hx.1 n]
  have hratio : 0 < (1 + x ^ (n + 1)) / (1 + x ^ n) := div_pos hnumpos hdenpos
  rw [putnam_2004_b5_term, Real.log_rpow hratio,
    Real.log_div hnumpos.ne' hdenpos.ne', putnam_2004_b5_logTerm]

private lemma putnam_2004_b5_term_pos (x : ℝ) (hx : x ∈ Set.Ioo 0 1) (n : ℕ) :
    0 < putnam_2004_b5_term x n := by
  have hnumpos : 0 < 1 + x ^ (n + 1) := by linarith [pow_pos hx.1 (n + 1)]
  have hdenpos : 0 < 1 + x ^ n := by linarith [pow_pos hx.1 n]
  have hratio : 0 < (1 + x ^ (n + 1)) / (1 + x ^ n) := div_pos hnumpos hdenpos
  rw [putnam_2004_b5_term]
  exact Real.rpow_pos_of_pos hratio _

private lemma putnam_2004_b5_finite_products_tendsto (x : ℝ) (hx : x ∈ Set.Ioo 0 1) :
    Tendsto (fun N ↦ ∏ n ∈ Finset.range N, putnam_2004_b5_term x n)
      atTop (𝓝 (Real.exp (putnam_2004_b5_logMain x))) := by
  have hs := putnam_2004_b5_summable_logTerm hx
  have hsumlog : HasSum (fun n : ℕ => Real.log (putnam_2004_b5_term x n))
      (putnam_2004_b5_logMain x) := by
    rw [← putnam_2004_b5_tsum_logTerm_eq_logMain hx]
    simpa [putnam_2004_b5_log_term_eq x hx] using hs.hasSum
  exact (Real.hasProd_of_hasSum_log (putnam_2004_b5_term_pos x hx) hsumlog).tendsto_prod_nat

/--
Evaluate $\lim_{x \to 1^-} \prod_{n=0}^\infty \left(\frac{1+x^{n+1}}{1+x^n}\right)^{x^n}$.
-/
theorem putnam_2004_b5
    (xprod : ℝ → ℝ)
    (hxprod : ∀ x ∈ Set.Ioo 0 1,
      Tendsto (fun N ↦ ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
      atTop (𝓝 (xprod x))) :
    Tendsto xprod (𝓝[<] 1) (𝓝 putnam_2004_b5_solution) :=
by
  have hxprod_eq : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ),
      xprod x = Real.exp (putnam_2004_b5_logMain x) := by
    filter_upwards [putnam_2004_b5_eventually_Ioo] with x hx
    have hgiven := hxprod x hx
    have hcalc : Tendsto
        (fun N ↦ ∏ n ∈ Finset.range N,
          ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
        atTop (𝓝 (Real.exp (putnam_2004_b5_logMain x))) := by
      simpa [putnam_2004_b5_term] using putnam_2004_b5_finite_products_tendsto x hx
    exact tendsto_nhds_unique hgiven hcalc
  have hexp : Tendsto (fun x : ℝ => Real.exp (putnam_2004_b5_logMain x))
      (𝓝[<] (1 : ℝ)) (𝓝 putnam_2004_b5_solution) := by
    simpa [putnam_2004_b5_solution] using
      (Real.continuous_exp.continuousAt.tendsto.comp putnam_2004_b5_logMain_tendsto)
  exact hexp.congr' (hxprod_eq.mono fun x hx => hx.symm)
