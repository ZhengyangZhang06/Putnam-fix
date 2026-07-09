import Mathlib

open Metric Set EuclideanGeometry Filter Topology

-- Real.exp (2 * Real.log 5 - 4 + 2 * Real.arctan 2)

noncomputable section

private abbrev putnam_1970_b1_f (x : ℝ) : ℝ :=
  Real.log (1 + x ^ 2)

private abbrev putnam_1970_b1_A : ℝ :=
  ∫ x in (0 : ℝ)..2, putnam_1970_b1_f x

private abbrev putnam_1970_b1_term (n : ℤ) : ℝ :=
  1 / ((n : ℝ) ^ 4) *
    ∏ i ∈ Finset.Icc (1 : ℤ) (2 * n),
      ((n : ℝ) ^ 2 + (i : ℝ) ^ 2) ^ ((1 : ℝ) / (n : ℝ))

private lemma putnam_1970_b1_f_mono :
    MonotoneOn putnam_1970_b1_f (Set.Icc (0 : ℝ) 2) := by
  intro x hx y hy hxy
  apply Real.log_le_log
  · nlinarith [sq_nonneg x]
  · have hsq : x ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_self_le_mul_self hx.1 hxy]
    nlinarith

private lemma putnam_1970_b1_scaled_integral (n : ℕ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..(2 * n : ℕ), putnam_1970_b1_f (x / (n : ℝ))) =
      (n : ℝ) * putnam_1970_b1_A := by
  rw [intervalIntegral.integral_comp_div putnam_1970_b1_f
    (show (n : ℝ) ≠ 0 by exact_mod_cast hn)]
  congr 1
  congr
  · norm_num
  · norm_num [Nat.cast_mul]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn]

private lemma putnam_1970_b1_riemann_bounds (n : ℕ) (hn : n ≠ 0) :
    putnam_1970_b1_A ≤
        (1 / (n : ℝ)) *
          (∑ k ∈ Finset.range (2 * n),
            putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ))) ∧
      (1 / (n : ℝ)) *
          (∑ k ∈ Finset.range (2 * n),
            putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ))) ≤
        putnam_1970_b1_A + Real.log 5 / (n : ℝ) := by
  let right : ℝ :=
    ∑ k ∈ Finset.range (2 * n), putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ))
  let left : ℝ :=
    ∑ k ∈ Finset.range (2 * n), putnam_1970_b1_f ((k : ℝ) / (n : ℝ))
  let R : ℝ := (1 / (n : ℝ)) * right
  have hnpos : 0 < (n : ℝ) := by positivity
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hmono_n :
      MonotoneOn (fun x : ℝ => putnam_1970_b1_f (x / (n : ℝ)))
        (Set.Icc (((0 : ℕ) : ℝ)) (((2 * n : ℕ) : ℝ))) := by
    intro x hx y hy hxy
    apply putnam_1970_b1_f_mono
    · constructor
      · exact div_nonneg (by simpa using hx.1) hnpos.le
      · rw [div_le_iff₀ hnpos]
        exact_mod_cast hx.2
    · constructor
      · exact div_nonneg (by simpa using hy.1) hnpos.le
      · rw [div_le_iff₀ hnpos]
        exact_mod_cast hy.2
    · exact div_le_div_of_nonneg_right hxy hnpos.le
  have hscale' :
      (∫ x in (((0 : ℕ) : ℝ))..(((2 * n : ℕ) : ℝ)),
          (fun x : ℝ => putnam_1970_b1_f (x / (n : ℝ))) x) =
        (n : ℝ) * putnam_1970_b1_A := by
    simpa using putnam_1970_b1_scaled_integral n hn
  have hlower0 :=
    MonotoneOn.integral_le_sum_Ico (a := 0) (b := 2 * n)
      (f := fun x : ℝ => putnam_1970_b1_f (x / (n : ℝ))) (Nat.zero_le _) hmono_n
  rw [hscale'] at hlower0
  have hlower0' : (n : ℝ) * putnam_1970_b1_A ≤ right := by
    simpa [right, Nat.Ico_zero_eq_range] using hlower0
  have hRmul : (n : ℝ) * R = right := by
    dsimp [R]
    field_simp [hnR]
  have hleft0 :=
    MonotoneOn.sum_le_integral_Ico (a := 0) (b := 2 * n)
      (f := fun x : ℝ => putnam_1970_b1_f (x / (n : ℝ))) (Nat.zero_le _) hmono_n
  rw [hscale'] at hleft0
  have hleft_le : left ≤ (n : ℝ) * putnam_1970_b1_A := by
    simpa [left, Nat.Ico_zero_eq_range] using hleft0
  have hdiff : right - left = Real.log 5 := by
    have htel :=
      Finset.sum_range_sub (fun k : ℕ => putnam_1970_b1_f ((k : ℝ) / (n : ℝ))) (2 * n)
    have hend : putnam_1970_b1_f (((2 * n : ℕ) : ℝ) / (n : ℝ)) = Real.log 5 := by
      unfold putnam_1970_b1_f
      have : (((2 * n : ℕ) : ℝ) / (n : ℝ)) = 2 := by
        norm_num [Nat.cast_mul]
        field_simp [hnR]
      rw [this]
      norm_num
    have hzero : putnam_1970_b1_f (((0 : ℕ) : ℝ) / (n : ℝ)) = 0 := by
      unfold putnam_1970_b1_f
      norm_num
    have hsum :
        right - left =
          ∑ i ∈ Finset.range (2 * n),
            (putnam_1970_b1_f (((i + 1 : ℕ) : ℝ) / (n : ℝ)) -
              putnam_1970_b1_f ((i : ℝ) / (n : ℝ))) := by
      simp [right, left, Finset.sum_sub_distrib]
    rw [hsum, htel, hend, hzero]
    ring
  have hupper0 : right ≤ (n : ℝ) * putnam_1970_b1_A + Real.log 5 := by
    linarith
  have hUpperMul :
      (n : ℝ) * (putnam_1970_b1_A + Real.log 5 / (n : ℝ)) =
        (n : ℝ) * putnam_1970_b1_A + Real.log 5 := by
    field_simp [hnR]
  constructor
  · change putnam_1970_b1_A ≤ R
    nlinarith [hlower0', hRmul, hnpos]
  · change R ≤ putnam_1970_b1_A + Real.log 5 / (n : ℝ)
    nlinarith [hupper0, hRmul, hUpperMul, hnpos]

private lemma putnam_1970_b1_riemann_range :
    Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) *
          (∑ k ∈ Finset.range (2 * n),
            putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ))))
      atTop (𝓝 putnam_1970_b1_A) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℕ => putnam_1970_b1_A)
    (h := fun n : ℕ => putnam_1970_b1_A + Real.log 5 / (n : ℝ))
    tendsto_const_nhds ?_ ?_ ?_
  · have hzero : Tendsto (fun n : ℕ => Real.log 5 / (n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        tendsto_const_nhds.mul
          (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa using tendsto_const_nhds.add hzero
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (putnam_1970_b1_riemann_bounds n (Nat.pos_iff_ne_zero.mp hn)).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (putnam_1970_b1_riemann_bounds n (Nat.pos_iff_ne_zero.mp hn)).2

private lemma putnam_1970_b1_int_sum_eq_range (n : ℕ) :
    (∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
        putnam_1970_b1_f ((i : ℝ) / (n : ℝ))) =
      ∑ k ∈ Finset.range (2 * n),
        putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  rw [Int.Icc_eq_finset_map]
  simp only [Finset.sum_map]
  have htoNat : (2 * (n : ℤ) + 1 - 1).toNat = 2 * n := by
    omega
  rw [htoNat]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [div_eq_mul_inv, add_comm]

private lemma putnam_1970_b1_riemann_int :
    Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) *
          ∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
            putnam_1970_b1_f ((i : ℝ) / (n : ℝ)))
      atTop (𝓝 putnam_1970_b1_A) := by
  refine Filter.Tendsto.congr' ?_ putnam_1970_b1_riemann_range
  exact Eventually.of_forall fun n => by
    change
      (1 / (n : ℝ)) *
          (∑ k ∈ Finset.range (2 * n),
            putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ))) =
        (1 / (n : ℝ)) *
          ∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
            putnam_1970_b1_f ((i : ℝ) / (n : ℝ))
    rw [putnam_1970_b1_int_sum_eq_range n]

private lemma putnam_1970_b1_integral :
    putnam_1970_b1_A = 2 * Real.log 5 - 4 + 2 * Real.arctan 2 := by
  let F : ℝ → ℝ := fun y => y * Real.log (1 + y ^ 2) - 2 * y + 2 * Real.arctan y
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 2) := by
    unfold F
    refine ((continuousOn_id.mul ?_).sub (continuousOn_const.mul continuousOn_id)).add
      (continuousOn_const.mul Real.continuous_arctan.continuousOn)
    exact ((continuousOn_const.add (continuousOn_id.pow 2)).log fun x hx => by
      have : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
      exact ne_of_gt this)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 2, HasDerivAt F (putnam_1970_b1_f x) x := by
    intro x hx
    have hpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    unfold F putnam_1970_b1_f
    convert (((hasDerivAt_id x).mul ((Real.hasDerivAt_log (ne_of_gt hpos)).comp x
      (((hasDerivAt_const x (1 : ℝ)).add (((hasDerivAt_id x).pow 2)))))).sub
      ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x))).add
      ((hasDerivAt_const x (2 : ℝ)).mul (Real.hasDerivAt_arctan x)) using 1
    simp only [Pi.add_apply, Pi.pow_apply, Function.comp_apply, id_eq]
    field_simp [hpos.ne']
    ring
  have hint : IntervalIntegrable putnam_1970_b1_f MeasureTheory.volume (0 : ℝ) 2 := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num) ?_
    exact ((continuousOn_const.add (continuousOn_id.pow 2)).log fun x hx => by
      have : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
      exact ne_of_gt this)
  rw [show putnam_1970_b1_A = ∫ x in (0 : ℝ)..2, putnam_1970_b1_f x from rfl]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hFcont hderiv hint]
  unfold F
  norm_num [Real.log_one]

private lemma putnam_1970_b1_log_base (n i : ℤ) (hnpos : 0 < (n : ℝ)) :
    Real.log ((n : ℝ) ^ 2 + (i : ℝ) ^ 2) =
      2 * Real.log (n : ℝ) + putnam_1970_b1_f ((i : ℝ) / (n : ℝ)) := by
  have hn : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hbase :
      (n : ℝ) ^ 2 + (i : ℝ) ^ 2 =
        (n : ℝ) ^ 2 * (1 + ((i : ℝ) / (n : ℝ)) ^ 2) := by
    field_simp [hn]
  rw [hbase]
  rw [Real.log_mul]
  · rw [Real.log_pow]
    norm_num [putnam_1970_b1_f]
  · positivity
  · positivity

private lemma putnam_1970_b1_product_eq_exp (n : ℤ) (hn : 0 < n) :
    putnam_1970_b1_term n =
      Real.exp
        ((1 / (n : ℝ)) *
          ∑ i ∈ Finset.Icc (1 : ℤ) (2 * n),
            putnam_1970_b1_f ((i : ℝ) / (n : ℝ))) := by
  let s : Finset ℤ := Finset.Icc (1 : ℤ) (2 * n)
  let P : ℝ := putnam_1970_b1_term n
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnposR
  have hPpos : 0 < P := by
    dsimp [P, putnam_1970_b1_term]
    positivity
  have hcard : (s.card : ℝ) = 2 * (n : ℝ) := by
    have hcard_int : (s.card : ℤ) = 2 * n := by
      dsimp [s]
      rw [Int.card_Icc_of_le]
      · ring
      · omega
    exact_mod_cast hcard_int
  have hlog_pref : Real.log (1 / ((n : ℝ) ^ 4)) = -4 * Real.log (n : ℝ) := by
    rw [Real.log_div]
    · simp [Real.log_pow]
    · norm_num
    · positivity
  have hlog :
      Real.log P =
        (1 / (n : ℝ)) * ∑ i ∈ s, putnam_1970_b1_f ((i : ℝ) / (n : ℝ)) := by
    dsimp [P, putnam_1970_b1_term]
    rw [Real.log_mul]
    · rw [hlog_pref]
      rw [Real.log_prod]
      · trans
          -4 * Real.log (n : ℝ) +
            ∑ i ∈ s,
              (1 / (n : ℝ)) *
                (2 * Real.log (n : ℝ) + putnam_1970_b1_f ((i : ℝ) / (n : ℝ)))
        · congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Real.log_rpow]
          · rw [putnam_1970_b1_log_base n i hnposR]
          · positivity
        · simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          rw [hcard]
          field_simp [hnR]
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          field_simp [hnR]
          ring
      · intro i hi
        exact (Real.rpow_pos_of_pos
          (by positivity : 0 < ((n : ℝ) ^ 2 + (i : ℝ) ^ 2)) _).ne'
    · positivity
    · exact Finset.prod_ne_zero_iff.mpr fun i hi =>
        (Real.rpow_pos_of_pos
          (by positivity : 0 < ((n : ℝ) ^ 2 + (i : ℝ) ^ 2)) _).ne'
  calc
    putnam_1970_b1_term n = P := by rfl
    _ = Real.exp (Real.log P) := by rw [Real.exp_log hPpos]
    _ =
        Real.exp
          ((1 / (n : ℝ)) * ∑ i ∈ Finset.Icc (1 : ℤ) (2 * n),
            putnam_1970_b1_f ((i : ℝ) / (n : ℝ))) := by
      rw [hlog]

private lemma putnam_1970_b1_int_toNat_tendsto :
    Tendsto Int.toNat (atTop : Filter ℤ) (atTop : Filter ℕ) := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨(b : ℤ), ?_⟩
  intro a ha
  have ha0 : 0 ≤ a := by
    exact (show (0 : ℤ) ≤ b by exact_mod_cast Nat.zero_le b).trans ha
  have hba : (b : ℤ) ≤ (a.toNat : ℤ) := by
    simpa [Int.toNat_of_nonneg ha0] using ha
  exact_mod_cast hba

/--
Evaluate the infinite product $\lim_{n \to \infty} \frac{1}{n^4} \prod_{i = 1}^{2n} (n^2 + i^2)^{1/n}$.
-/
theorem putnam_1970_b1
: Tendsto (fun n => 1/(n^4) * ∏ i ∈ Finset.Icc (1 : ℤ) (2*n), ((n^2 + i^2) : ℝ)^((1 : ℝ)/n)) atTop (𝓝 ((Real.exp (2 * Real.log 5 - 4 + 2 * Real.arctan 2)) : ℝ )) := by
  have hExpNat :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            ((1 / (n : ℝ)) *
              ∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
                putnam_1970_b1_f ((i : ℝ) / (n : ℝ))))
        atTop (𝓝 (Real.exp putnam_1970_b1_A)) :=
    (Real.continuous_exp.tendsto putnam_1970_b1_A).comp putnam_1970_b1_riemann_int
  have hNat :
      Tendsto (fun n : ℕ => putnam_1970_b1_term (n : ℤ))
        atTop (𝓝 (Real.exp putnam_1970_b1_A)) := by
    refine Filter.Tendsto.congr' ?_ hExpNat
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (putnam_1970_b1_product_eq_exp (n : ℤ) (by exact_mod_cast hn)).symm
  have hIntComp :
      Tendsto (fun n : ℤ => putnam_1970_b1_term ((n.toNat : ℕ) : ℤ))
        atTop (𝓝 (Real.exp putnam_1970_b1_A)) :=
    hNat.comp putnam_1970_b1_int_toNat_tendsto
  have hInt :
      Tendsto putnam_1970_b1_term atTop (𝓝 (Real.exp putnam_1970_b1_A)) := by
    refine Filter.Tendsto.congr' ?_ hIntComp
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
    rw [Int.toNat_of_nonneg hn]
  have hTarget :
      Tendsto putnam_1970_b1_term atTop
        (𝓝 (Real.exp (2 * Real.log 5 - 4 + 2 * Real.arctan 2))) := by
    simpa [putnam_1970_b1_integral] using hInt
  refine Filter.Tendsto.congr' ?_ hTarget
  exact Eventually.of_forall fun n => by
    simp [putnam_1970_b1_term, one_div]
