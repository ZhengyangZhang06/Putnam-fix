import Mathlib

open Nat Filter Topology Real

noncomputable section

open scoped BigOperators

private lemma putnam_1983_a6_tendsto_inv_sq :
    Tendsto (fun a : ℝ => (a ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
  have hpow : Tendsto (fun a : ℝ => a ^ (-(2 : ℤ))) atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_zpow_atTop_zero (𝕜 := ℝ) (n := (-(2 : ℤ))) (by norm_num))
  refine hpow.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
  change (a ^ 2)⁻¹ = a ^ (-(2 : ℤ))
  exact rfl

private lemma putnam_1983_a6_integral_id_mul_exp_neg_mul
    (k r : ℝ) (hk : k ≠ 0) :
    (∫ u in (0)..r, u * exp (-k * u)) =
      (1 - (k * r + 1) * exp (-k * r)) / k ^ 2 := by
  let A : ℝ → ℝ := fun u => (-(k * u + 1) / k ^ 2) * exp (-k * u)
  have hderiv : ∀ x ∈ Set.uIcc 0 r, HasDerivAt A (x * exp (-k * x)) x := by
    intro x hx
    have hlin : HasDerivAt (fun u : ℝ => -(k * u + 1)) (-k) x := by
      convert
        (((hasDerivAt_const x k).mul (hasDerivAt_id x)).add
          (hasDerivAt_const x 1)).neg using 1
      · ring
    have h1 : HasDerivAt (fun u : ℝ => (-(k * u + 1) / k ^ 2))
        (-k / k ^ 2) x := by
      convert hlin.const_mul (1 / k ^ 2) using 1
      field_simp [hk]
      ring
    have h2 : HasDerivAt (fun u : ℝ => exp (-k * u))
        (exp (-k * x) * (-k)) x := by
      simpa [Pi.mul_apply, id_eq, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_const x (-k)).mul (hasDerivAt_id x)).exp
    convert h1.mul h2 using 1
    field_simp [hk]
    ring
  have hcont : Continuous fun u : ℝ => u * exp (-k * u) := by fun_prop
  have hint : IntervalIntegrable (fun u : ℝ => u * exp (-k * u))
      MeasureTheory.volume 0 r :=
    hcont.intervalIntegrable 0 r
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := r) (f := A) (f' := fun u : ℝ => u * exp (-k * u))
    hderiv hint
  dsimp [A] at hFTC
  rw [hFTC]
  simp [exp_zero]
  field_simp [hk]
  ring

private lemma putnam_1983_a6_rat_limit_plus :
    Tendsto (fun a : ℝ => a ^ 4 / (3 * a ^ 2 + 1) ^ 2) atTop
      (𝓝 ((1 / 9 : ℝ))) := by
  have hs := putnam_1983_a6_tendsto_inv_sq
  have hden : Tendsto (fun a : ℝ => 3 + (a ^ 2)⁻¹) atTop (𝓝 (3 + 0)) :=
    tendsto_const_nhds.add hs
  have hinv : Tendsto (fun a : ℝ => (3 + (a ^ 2)⁻¹)⁻¹) atTop
      (𝓝 ((3 + 0 : ℝ)⁻¹)) :=
    hden.inv₀ (by norm_num)
  have htarget :
      Tendsto (fun a : ℝ => ((3 + (a ^ 2)⁻¹)⁻¹) *
        ((3 + (a ^ 2)⁻¹)⁻¹)) atTop (𝓝 ((1 / 9 : ℝ))) := by
    convert hinv.mul hinv using 1
    norm_num
  refine htarget.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [ha0]

private lemma putnam_1983_a6_rat_limit_minus :
    Tendsto (fun a : ℝ => a ^ 4 / (3 * a ^ 2 - 3) ^ 2) atTop
      (𝓝 ((1 / 9 : ℝ))) := by
  have hs := putnam_1983_a6_tendsto_inv_sq
  have hden : Tendsto (fun a : ℝ => 3 - 3 * (a ^ 2)⁻¹) atTop
      (𝓝 (3 - 3 * 0)) := by
    exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hs)
  have hinv : Tendsto (fun a : ℝ => (3 - 3 * (a ^ 2)⁻¹)⁻¹) atTop
      (𝓝 ((3 - 3 * 0 : ℝ)⁻¹)) :=
    hden.inv₀ (by norm_num)
  have htarget :
      Tendsto (fun a : ℝ => ((3 - 3 * (a ^ 2)⁻¹)⁻¹) *
        ((3 - 3 * (a ^ 2)⁻¹)⁻¹)) atTop (𝓝 ((1 / 9 : ℝ))) := by
    convert hinv.mul hinv using 1
    norm_num
  refine htarget.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with a ha
  have ha0 : a ≠ 0 := by positivity
  have hden0 : 3 * a ^ 2 - 3 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero ha0]
  field_simp [ha0, hden0]

private lemma putnam_1983_a6_tail_limit :
    Tendsto
      (fun a : ℝ =>
        (((3 * a ^ 2 + 1) / a) + 1) * exp (-((3 * a ^ 2 + 1) / a)))
      atTop (𝓝 (0 : ℝ)) := by
  have h3 : Tendsto (fun a : ℝ => 3 * a) atTop atTop := by
    simpa using
      (Filter.tendsto_id.const_mul_atTop (α := ℝ) (β := ℝ) (l := atTop)
        (f := id) (r := (3 : ℝ)) (by norm_num))
  have hExp3 : Tendsto (fun a : ℝ => exp (-(3 * a))) atTop (𝓝 (0 : ℝ)) := by
    have hneg : Tendsto (fun a : ℝ => -(3 * a)) atTop atBot := by
      exact Filter.tendsto_neg_atTop_atBot.comp h3
    exact Real.tendsto_exp_atBot.comp hneg
  have hAexp : Tendsto (fun a : ℝ => a * exp (-(3 * a))) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h3
    have h' : Tendsto (fun a : ℝ => (3 * a) ^ 1 * exp (-(3 * a)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using h
    have hscaled := h'.const_mul (1 / 3 : ℝ)
    convert hscaled using 1
    · ext a
      ring
    · norm_num
  have hInv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hInvExp : Tendsto (fun a : ℝ => a⁻¹ * exp (-(3 * a))) atTop
      (𝓝 (0 : ℝ)) := by
    simpa using hInv.mul hExp3
  have hOneExp : Tendsto (fun a : ℝ => (1 : ℝ) * exp (-(3 * a))) atTop
      (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).mul hExp3
  have hpolyExp : Tendsto (fun a : ℝ => (3 * a + a⁻¹ + 1) * exp (-(3 * a)))
      atTop (𝓝 (0 : ℝ)) := by
    have hsum := (hAexp.const_mul (3 : ℝ)).add (hInvExp.add hOneExp)
    convert hsum using 1
    · ext a
      ring_nf
    · norm_num
  have hExpInv : Tendsto (fun a : ℝ => exp (-(a⁻¹))) atTop (𝓝 (1 : ℝ)) := by
    have hneg : Tendsto (fun a : ℝ => -(a⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      simpa using hInv.neg
    simpa [exp_zero] using (Real.continuous_exp.tendsto 0).comp hneg
  have hprod0 :
      Tendsto
        (fun a : ℝ => ((3 * a + a⁻¹ + 1) * exp (-(3 * a))) * exp (-(a⁻¹)))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hpolyExp.mul hExpInv
  refine hprod0.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [ha0]
  rw [← exp_add]
  congr 1
  field_simp [ha0]
  ring

private lemma putnam_1983_a6_lower_strip_limit :
    Tendsto
      (fun a : ℝ =>
        a ^ 4 * ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u))
      atTop (𝓝 ((1 / 9 : ℝ))) := by
  have htail := putnam_1983_a6_tail_limit
  have hone :
      Tendsto
        (fun a : ℝ =>
          1 - (((3 * a ^ 2 + 1) / a) + 1) * exp (-((3 * a ^ 2 + 1) / a)))
        atTop (𝓝 (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub htail
  have hprod := putnam_1983_a6_rat_limit_plus.mul hone
  have hprod' :
      Tendsto
        (fun a : ℝ =>
          (a ^ 4 / (3 * a ^ 2 + 1) ^ 2) *
            (1 - (((3 * a ^ 2 + 1) / a) + 1) *
              exp (-((3 * a ^ 2 + 1) / a))))
        atTop (𝓝 ((1 / 9 : ℝ))) := by
    convert hprod using 1
    norm_num
  refine hprod'.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hk : 3 * a ^ 2 + 1 ≠ 0 := by positivity
  rw [putnam_1983_a6_integral_id_mul_exp_neg_mul (k := 3 * a ^ 2 + 1)
    (r := a⁻¹) hk]
  field_simp [ha0, hk]

private lemma putnam_1983_a6_tail_limit_minus :
    Tendsto
      (fun a : ℝ =>
        (((3 * a ^ 2 - 3) / a) + 1) * exp (-((3 * a ^ 2 - 3) / a)))
      atTop (𝓝 (0 : ℝ)) := by
  have h3 : Tendsto (fun a : ℝ => 3 * a) atTop atTop := by
    simpa using
      (Filter.tendsto_id.const_mul_atTop (α := ℝ) (β := ℝ) (l := atTop)
        (f := id) (r := (3 : ℝ)) (by norm_num))
  have hExp3 : Tendsto (fun a : ℝ => exp (-(3 * a))) atTop (𝓝 (0 : ℝ)) := by
    have hneg : Tendsto (fun a : ℝ => -(3 * a)) atTop atBot := by
      exact Filter.tendsto_neg_atTop_atBot.comp h3
    exact Real.tendsto_exp_atBot.comp hneg
  have hAexp : Tendsto (fun a : ℝ => a * exp (-(3 * a))) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h3
    have h' : Tendsto (fun a : ℝ => (3 * a) ^ 1 * exp (-(3 * a)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using h
    have hscaled := h'.const_mul (1 / 3 : ℝ)
    convert hscaled using 1
    · ext a
      ring
    · norm_num
  have hInv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hInvExp : Tendsto (fun a : ℝ => a⁻¹ * exp (-(3 * a))) atTop
      (𝓝 (0 : ℝ)) := by
    simpa using hInv.mul hExp3
  have hOneExp : Tendsto (fun a : ℝ => (1 : ℝ) * exp (-(3 * a))) atTop
      (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).mul hExp3
  have hpolyExp : Tendsto (fun a : ℝ => (3 * a - 3 * a⁻¹ + 1) * exp (-(3 * a)))
      atTop (𝓝 (0 : ℝ)) := by
    have hsum := (hAexp.const_mul (3 : ℝ)).sub ((hInvExp.const_mul (3 : ℝ)).sub hOneExp)
    convert hsum using 1
    · ext a
      ring
    · norm_num
  have hExpInv : Tendsto (fun a : ℝ => exp (3 * a⁻¹)) atTop (𝓝 (1 : ℝ)) := by
    have hmul : Tendsto (fun a : ℝ => 3 * a⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (3 : ℝ))).mul hInv
    simpa [exp_zero] using (Real.continuous_exp.tendsto 0).comp hmul
  have hprod0 :
      Tendsto
        (fun a : ℝ => ((3 * a - 3 * a⁻¹ + 1) * exp (-(3 * a))) * exp (3 * a⁻¹))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hpolyExp.mul hExpInv
  refine hprod0.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [ha0]
  rw [mul_assoc, ← exp_add]
  congr 1
  field_simp [ha0]
  ring_nf

private lemma putnam_1983_a6_upper_strip_limit :
    Tendsto
      (fun a : ℝ =>
        a ^ 4 * ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u))
      atTop (𝓝 ((1 / 9 : ℝ))) := by
  have htail := putnam_1983_a6_tail_limit_minus
  have hone :
      Tendsto
        (fun a : ℝ =>
          1 - (((3 * a ^ 2 - 3) / a) + 1) * exp (-((3 * a ^ 2 - 3) / a)))
        atTop (𝓝 (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub htail
  have hprod := putnam_1983_a6_rat_limit_minus.mul hone
  have hprod' :
      Tendsto
        (fun a : ℝ =>
          (a ^ 4 / (3 * a ^ 2 - 3) ^ 2) *
            (1 - (((3 * a ^ 2 - 3) / a) + 1) *
              exp (-((3 * a ^ 2 - 3) / a))))
        atTop (𝓝 ((1 / 9 : ℝ))) := by
    convert hprod using 1
    norm_num
  refine hprod'.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with a ha
  have ha0 : a ≠ 0 := by positivity
  have hk : 3 * a ^ 2 - 3 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero ha0]
  rw [putnam_1983_a6_integral_id_mul_exp_neg_mul (k := 3 * a ^ 2 - 3)
    (r := a⁻¹) hk]
  field_simp [ha0, hk]

private lemma putnam_1983_a6_exp_const_sub_mul_integral
    (C k p q : ℝ) (hk : k ≠ 0) :
    (∫ u in p..q, exp (C - k * u)) =
      (exp (C - k * p) - exp (C - k * q)) / k := by
  have hmk : -k ≠ 0 := neg_ne_zero.mpr hk
  have h := intervalIntegral.integral_comp_add_mul (f := fun t : ℝ => exp t)
      (a := p) (b := q) hmk C
  rw [integral_exp] at h
  calc
    (∫ u in p..q, exp (C - k * u)) =
        (∫ u in p..q, exp (C + (-k) * u)) := by
      congr with u
      ring_nf
    _ = (-k)⁻¹ * (exp (C + (-k) * q) - exp (C + (-k) * p)) := by
      simpa [smul_eq_mul] using h
    _ = (exp (C - k * p) - exp (C - k * q)) / k := by
      field_simp [hk]
      ring_nf

private lemma putnam_1983_a6_integral_id_mul_exp_const_sub_mul
    (C k r : ℝ) (hk : k ≠ 0) :
    (∫ u in (0)..r, u * exp (C - k * u)) =
      exp C * (1 - (k * r + 1) * exp (-k * r)) / k ^ 2 := by
  have hbase := putnam_1983_a6_integral_id_mul_exp_neg_mul k r hk
  calc
    (∫ u in (0)..r, u * exp (C - k * u)) =
        ∫ u in (0)..r, exp C * (u * exp (-k * u)) := by
      congr with u
      rw [show C - k * u = C + (-k * u) by ring, exp_add]
      ring
    _ = exp C * ∫ u in (0)..r, u * exp (-k * u) := by
      simp
    _ = exp C * (1 - (k * r + 1) * exp (-k * r)) / k ^ 2 := by
      rw [hbase]
      ring

private lemma putnam_1983_a6_x_model_integral
    (C k r a : ℝ) (hk : k ≠ 0) :
    (∫ x in (a - r)..a, (a - x) * exp (C - k * (a - x))) =
      exp C * (1 - (k * r + 1) * exp (-k * r)) / k ^ 2 := by
  calc
    (∫ x in (a - r)..a, (a - x) * exp (C - k * (a - x))) =
        ∫ u in (0)..r, u * exp (C - k * u) := by
      have h := intervalIntegral.integral_comp_sub_mul
          (f := fun u : ℝ => u * exp (C - k * u))
          (a := a - r) (b := a) (c := (1 : ℝ)) (d := a) one_ne_zero
      simpa using h
    _ = exp C * (1 - (k * r + 1) * exp (-k * r)) / k ^ 2 :=
      putnam_1983_a6_integral_id_mul_exp_const_sub_mul C k r hk

private lemma putnam_1983_a6_y_model_integral
    (C k r a : ℝ) (hk : k ≠ 0) :
    (∫ x in (0)..r, ∫ y in (a - r)..(a - x), exp (C - k * (a - y))) =
      exp C * (1 - (k * r + 1) * exp (-k * r)) / k ^ 2 := by
  have hinner : ∀ x : ℝ,
      (∫ y in (a - r)..(a - x), exp (C - k * (a - y))) =
        (exp (C - k * x) - exp (C - k * r)) / k := by
    intro x
    calc
      (∫ y in (a - r)..(a - x), exp (C - k * (a - y))) =
          ∫ y in (a - r)..(a - x), (fun v : ℝ => exp (C - k * v)) (a - y) := rfl
      _ = ∫ v in x..r, exp (C - k * v) := by
        have h := intervalIntegral.integral_comp_sub_mul
          (f := fun v : ℝ => exp (C - k * v)) (a := a - r) (b := a - x)
          (c := (1 : ℝ)) (d := a) one_ne_zero
        simpa using h
      _ = (exp (C - k * x) - exp (C - k * r)) / k :=
        putnam_1983_a6_exp_const_sub_mul_integral C k x r hk
  simp_rw [hinner]
  calc
    (∫ x in (0)..r, (exp (C - k * x) - exp (C - k * r)) / k) =
        (1 / k) * ∫ x in (0)..r, (exp (C - k * x) - exp (C - k * r)) := by
      simp [div_eq_mul_inv, mul_comm]
    _ = (1 / k) * ((∫ x in (0)..r, exp (C - k * x)) -
          ∫ x in (0)..r, exp (C - k * r)) := by
      rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun x : ℝ => exp (C - k * x)).intervalIntegrable 0 r)
        (continuous_const.intervalIntegrable 0 r)]
    _ = (1 / k) * (((exp C - exp (C - k * r)) / k) - r * exp (C - k * r)) := by
      rw [putnam_1983_a6_exp_const_sub_mul_integral C k 0 r hk]
      simp
    _ = exp C * (1 - (k * r + 1) * exp (-k * r)) / k ^ 2 := by
      rw [show exp (C - k * r) = exp C * exp (-k * r) by
        rw [show C - k * r = C + (-k * r) by ring]
        rw [exp_add]]
      field_simp [hk]
      ring

private lemma putnam_1983_a6_x_lower_exponent
    {a x y : ℝ} (ha : 2 ≤ a) (hxlo : a - a⁻¹ ≤ x) (hxhi : x ≤ a)
    (hy0 : 0 ≤ y) :
    a ^ 3 - (3 * a ^ 2 + 1) * (a - x) ≤ x ^ 3 + y ^ 3 := by
  have ha_pos : 0 < a := by linarith
  have hu0 : 0 ≤ a - x := sub_nonneg.mpr hxhi
  have hur : a - x ≤ a⁻¹ := by linarith
  have hle1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ a)
  have h3 : 0 ≤ 3 * a - (a - x) := by nlinarith
  have hy3 : 0 ≤ y ^ 3 := pow_nonneg hy0 3
  nlinarith [mul_nonneg (pow_nonneg hu0 2) h3]

private lemma putnam_1983_a6_x_upper_exponent
    {a x y : ℝ} (ha : 2 ≤ a) (hxlo : a - a⁻¹ ≤ x) (hxhi : x ≤ a)
    (hy0 : 0 ≤ y) (hyu : y ≤ a - x) :
    x ^ 3 + y ^ 3 ≤ a ^ 3 - (3 * a ^ 2 - 3) * (a - x) := by
  have ha_pos : 0 < a := by linarith
  have hu0 : 0 ≤ a - x := sub_nonneg.mpr hxhi
  have hur : a - x ≤ a⁻¹ := by linarith
  have hy3 : y ^ 3 ≤ (a - x) ^ 3 := pow_le_pow_left₀ hy0 hyu 3
  have hau : a * (a - x) ≤ 1 := by
    calc
      a * (a - x) ≤ a * a⁻¹ := mul_le_mul_of_nonneg_left hur ha_pos.le
      _ = 1 := mul_inv_cancel₀ ha_pos.ne'
  have hau2 : a * (a - x) ^ 2 ≤ (a - x) := by
    have hmul := mul_le_mul_of_nonneg_right hau hu0
    nlinarith
  nlinarith

private lemma putnam_1983_a6_y_lower_exponent
    {a x y : ℝ} (ha : 2 ≤ a) (hylo : a - a⁻¹ ≤ y) (hyhi : y ≤ a)
    (hx0 : 0 ≤ x) :
    a ^ 3 - (3 * a ^ 2 + 1) * (a - y) ≤ x ^ 3 + y ^ 3 := by
  have ha_pos : 0 < a := by linarith
  have hv0 : 0 ≤ a - y := sub_nonneg.mpr hyhi
  have hvr : a - y ≤ a⁻¹ := by linarith
  have h3 : 0 ≤ 3 * a - (a - y) := by
    have hle1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ a)
    nlinarith
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
  nlinarith [mul_nonneg (pow_nonneg hv0 2) h3]

private lemma putnam_1983_a6_y_upper_exponent
    {a x y : ℝ} (ha : 2 ≤ a) (hylo : a - a⁻¹ ≤ y) (hyhi : y ≤ a)
    (hx0 : 0 ≤ x) (hxy : x ≤ a - y) :
    x ^ 3 + y ^ 3 ≤ a ^ 3 - (3 * a ^ 2 - 3) * (a - y) := by
  have ha_pos : 0 < a := by linarith
  have hv0 : 0 ≤ a - y := sub_nonneg.mpr hyhi
  have hvr : a - y ≤ a⁻¹ := by linarith
  have hx3 : x ^ 3 ≤ (a - y) ^ 3 := pow_le_pow_left₀ hx0 hxy 3
  have hav : a * (a - y) ≤ 1 := by
    calc
      a * (a - y) ≤ a * a⁻¹ := mul_le_mul_of_nonneg_left hvr ha_pos.le
      _ = 1 := mul_inv_cancel₀ ha_pos.ne'
  have hav2 : a * (a - y) ^ 2 ≤ (a - y) := by
    have hmul := mul_le_mul_of_nonneg_right hav hv0
    nlinarith
  nlinarith

private lemma putnam_1983_a6_left_tail_exponent
    {a x y : ℝ} (ha : 2 ≤ a) (hx0 : 0 ≤ x) (hxr : x ≤ a⁻¹)
    (hy0 : 0 ≤ y) (hyr : y ≤ a - a⁻¹) :
    x ^ 3 + y ^ 3 ≤ a ^ 3 - a := by
  have ha_pos : 0 < a := by linarith
  have hx3 : x ^ 3 ≤ (a⁻¹) ^ 3 := pow_le_pow_left₀ hx0 hxr 3
  have hy3 : y ^ 3 ≤ (a - a⁻¹) ^ 3 := pow_le_pow_left₀ hy0 hyr 3
  have hcalc_eq : (a⁻¹) ^ 3 + (a - a⁻¹) ^ 3 = a ^ 3 - 3 * a + 3 / a := by
    field_simp [ha_pos.ne']
    ring
  have hle : 3 / a ≤ 2 * a := by
    rw [div_le_iff₀ ha_pos]
    nlinarith
  nlinarith

private lemma putnam_1983_a6_middle_tail_exponent
    {a x y : ℝ} (ha : 2 ≤ a) (hxr : a⁻¹ ≤ x) (hxa : x ≤ a - a⁻¹)
    (hy0 : 0 ≤ y) (hyu : y ≤ a - x) :
    x ^ 3 + y ^ 3 ≤ a ^ 3 - a := by
  have ha_pos : 0 < a := by linarith
  have hx0 : 0 ≤ x := le_trans (inv_nonneg.mpr ha_pos.le) hxr
  have hy3 : y ^ 3 ≤ (a - x) ^ 3 := pow_le_pow_left₀ hy0 hyu 3
  have hprod0 : 0 ≤ (x - a⁻¹) * (a - a⁻¹ - x) := by
    exact mul_nonneg (sub_nonneg.mpr hxr) (sub_nonneg.mpr hxa)
  have hprod : a⁻¹ * (a - a⁻¹) ≤ x * (a - x) := by nlinarith
  have hbase : a ≤ 3 * a * (a⁻¹ * (a - a⁻¹)) := by
    field_simp [ha_pos.ne']
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) ha_pos.le)
  nlinarith

private lemma putnam_1983_a6_scaled_exp_tail :
    Tendsto (fun a : ℝ => a ^ 6 * exp (-a)) atTop (𝓝 (0 : ℝ)) := by
  simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6

private lemma putnam_1983_a6_raw_lower_bound (a : ℝ) (ha : 2 ≤ a) :
    2 * (exp (a ^ 3) *
        ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u)) ≤
      ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) := by
  let r : ℝ := a⁻¹
  let k : ℝ := 3 * a ^ 2 + 1
  let inner : ℝ → ℝ := fun x => ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)
  let Xmodel : ℝ :=
    ∫ x in (a - r)..a, (a - x) * exp (a ^ 3 - k * (a - x))
  let Ymodel : ℝ :=
    ∫ x in (0)..r, ∫ y in (a - r)..(a - x), exp (a ^ 3 - k * (a - y))
  have ha_pos : 0 < a := by linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact inv_nonneg.mpr ha_pos.le
  have h0r : 0 ≤ r := hr_nonneg
  have hr_le_a : r ≤ a := by
    dsimp [r]
    exact (inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ a)).trans (by linarith)
  have h0_ar : 0 ≤ a - r := sub_nonneg.mpr hr_le_a
  have hr_ar : r ≤ a - r := by
    have h2r : 2 * r ≤ a := by
      dsimp [r]
      rw [mul_inv_le_iff₀ ha_pos]
      nlinarith
    linarith
  have har_a : a - r ≤ a := sub_le_self a hr_nonneg
  have hk : k ≠ 0 := by
    dsimp [k]
    positivity
  have hcont_inner : Continuous inner := by
    dsimp [inner]
    fun_prop
  have hsplit :
      (∫ x in (0)..a, inner x) =
        ((∫ x in (0)..r, inner x) + ∫ x in r..(a - r), inner x) +
          ∫ x in (a - r)..a, inner x := by
    have h0r_int : IntervalIntegrable inner MeasureTheory.volume 0 r :=
      hcont_inner.intervalIntegrable 0 r
    have hr_ar_int : IntervalIntegrable inner MeasureTheory.volume r (a - r) :=
      hcont_inner.intervalIntegrable r (a - r)
    have h0_ar_int : IntervalIntegrable inner MeasureTheory.volume 0 (a - r) :=
      hcont_inner.intervalIntegrable 0 (a - r)
    have har_a_int : IntervalIntegrable inner MeasureTheory.volume (a - r) a :=
      hcont_inner.intervalIntegrable (a - r) a
    have h01 := intervalIntegral.integral_add_adjacent_intervals
      (f := inner) (a := 0) (b := r) (c := a - r) h0r_int hr_ar_int
    have h02 := intervalIntegral.integral_add_adjacent_intervals
      (f := inner) (a := 0) (b := a - r) (c := a) h0_ar_int har_a_int
    rw [← h02, ← h01]
  have hM_nonneg : 0 ≤ ∫ x in r..(a - r), inner x := by
    refine intervalIntegral.integral_nonneg hr_ar ?_
    intro x hx
    dsimp [inner]
    have hx_a : x ≤ a := hx.2.trans har_a
    have hax : 0 ≤ a - x := sub_nonneg.mpr hx_a
    exact intervalIntegral.integral_nonneg hax (fun y hy => (exp_pos _).le)
  have hXle : Xmodel ≤ ∫ x in (a - r)..a, inner x := by
    dsimp [Xmodel, inner]
    refine intervalIntegral.integral_mono_on har_a
      ((by fun_prop : Continuous fun x : ℝ => (a - x) * exp (a ^ 3 - k * (a - x))).intervalIntegrable (a - r) a)
      (hcont_inner.intervalIntegrable (a - r) a) ?_
    intro x hx
    have hxlo : a - a⁻¹ ≤ x := by simpa [r] using hx.1
    have hxhi : x ≤ a := hx.2
    have hax : 0 ≤ a - x := sub_nonneg.mpr hxhi
    calc
      (a - x) * exp (a ^ 3 - k * (a - x)) =
          ∫ y in (0)..(a - x), exp (a ^ 3 - k * (a - x)) := by
        simp
      _ ≤ ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) := by
        refine intervalIntegral.integral_mono_on hax
          (continuous_const.intervalIntegrable 0 (a - x))
          ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3)).intervalIntegrable 0 (a - x))
          ?_
        intro y hy
        exact Real.exp_le_exp.mpr
          (by
            dsimp [k]
            exact putnam_1983_a6_x_lower_exponent ha hxlo hxhi hy.1)
  have hYle : Ymodel ≤ ∫ x in (0)..r, inner x := by
    dsimp [Ymodel, inner]
    refine intervalIntegral.integral_mono_on h0r
      ((by fun_prop :
        Continuous fun x : ℝ => ∫ y in (a - r)..(a - x), exp (a ^ 3 - k * (a - y))).intervalIntegrable 0 r)
      (hcont_inner.intervalIntegrable 0 r) ?_
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxr : x ≤ r := hx.2
    have hsub : a - r ≤ a - x := by linarith
    have hax : 0 ≤ a - x := by linarith [hr_le_a]
    have hsubint :
        (∫ y in (a - r)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
          ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) := by
      refine intervalIntegral.integral_mono_interval h0_ar hsub le_rfl
        (Eventually.of_forall (fun y => (exp_pos _).le))
        ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3)).intervalIntegrable 0 (a - x))
    calc
      (∫ y in (a - r)..(a - x), exp (a ^ 3 - k * (a - y))) ≤
          ∫ y in (a - r)..(a - x), exp (x ^ 3 + y ^ 3) := by
        refine intervalIntegral.integral_mono_on hsub
          ((by fun_prop : Continuous fun y : ℝ => exp (a ^ 3 - k * (a - y))).intervalIntegrable (a - r) (a - x))
          ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3)).intervalIntegrable (a - r) (a - x))
          ?_
        intro y hy
        have hylo : a - a⁻¹ ≤ y := by simpa [r] using hy.1
        have hyhi : y ≤ a := hy.2.trans (by linarith : a - x ≤ a)
        exact Real.exp_le_exp.mpr
          (by
            dsimp [k]
            exact putnam_1983_a6_y_lower_exponent ha hylo hyhi hx0)
      _ ≤ ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) := hsubint
  have hXeq : Xmodel =
      exp (a ^ 3) * ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u) := by
    dsimp [Xmodel, r, k]
    rw [putnam_1983_a6_x_model_integral (C := a ^ 3) (k := 3 * a ^ 2 + 1)
      (r := a⁻¹) (a := a) hk]
    rw [putnam_1983_a6_integral_id_mul_exp_neg_mul (k := 3 * a ^ 2 + 1)
      (r := a⁻¹) hk]
    ring
  have hYeq : Ymodel =
      exp (a ^ 3) * ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u) := by
    dsimp [Ymodel, r, k]
    rw [putnam_1983_a6_y_model_integral (C := a ^ 3) (k := 3 * a ^ 2 + 1)
      (r := a⁻¹) (a := a) hk]
    rw [putnam_1983_a6_integral_id_mul_exp_neg_mul (k := 3 * a ^ 2 + 1)
      (r := a⁻¹) hk]
    ring
  dsimp [inner] at hsplit
  rw [hsplit]
  nlinarith [hXle, hYle, hM_nonneg, hXeq, hYeq]

private lemma putnam_1983_a6_raw_upper_bound (a : ℝ) (ha : 2 ≤ a) :
    (∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
      2 * (exp (a ^ 3) *
          ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u)) +
        2 * (a ^ 2 * exp (a ^ 3 - a)) := by
  let r : ℝ := a⁻¹
  let k : ℝ := 3 * a ^ 2 - 3
  let tail : ℝ := exp (a ^ 3 - a)
  let inner : ℝ → ℝ := fun x => ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)
  let Xmodel : ℝ :=
    ∫ x in (a - r)..a, (a - x) * exp (a ^ 3 - k * (a - x))
  let Ymodel : ℝ :=
    ∫ x in (0)..r, ∫ y in (a - r)..(a - x), exp (a ^ 3 - k * (a - y))
  have ha_pos : 0 < a := by linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact inv_nonneg.mpr ha_pos.le
  have h0r : 0 ≤ r := hr_nonneg
  have hr_le_a : r ≤ a := by
    dsimp [r]
    exact (inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ a)).trans (by linarith)
  have h0_ar : 0 ≤ a - r := sub_nonneg.mpr hr_le_a
  have hr_ar : r ≤ a - r := by
    have h2r : 2 * r ≤ a := by
      dsimp [r]
      rw [mul_inv_le_iff₀ ha_pos]
      nlinarith
    linarith
  have har_a : a - r ≤ a := sub_le_self a hr_nonneg
  have hk : k ≠ 0 := by
    dsimp [k]
    have ha0 : a ≠ 0 := ne_of_gt ha_pos
    nlinarith [sq_pos_of_ne_zero ha0]
  have htail_nonneg : 0 ≤ tail := by
    dsimp [tail]
    exact (exp_pos _).le
  have hcont_inner : Continuous inner := by
    dsimp [inner]
    fun_prop
  have hsplit :
      (∫ x in (0)..a, inner x) =
        ((∫ x in (0)..r, inner x) + ∫ x in r..(a - r), inner x) +
          ∫ x in (a - r)..a, inner x := by
    have h0r_int : IntervalIntegrable inner MeasureTheory.volume 0 r :=
      hcont_inner.intervalIntegrable 0 r
    have hr_ar_int : IntervalIntegrable inner MeasureTheory.volume r (a - r) :=
      hcont_inner.intervalIntegrable r (a - r)
    have h0_ar_int : IntervalIntegrable inner MeasureTheory.volume 0 (a - r) :=
      hcont_inner.intervalIntegrable 0 (a - r)
    have har_a_int : IntervalIntegrable inner MeasureTheory.volume (a - r) a :=
      hcont_inner.intervalIntegrable (a - r) a
    have h01 := intervalIntegral.integral_add_adjacent_intervals
      (f := inner) (a := 0) (b := r) (c := a - r) h0r_int hr_ar_int
    have h02 := intervalIntegral.integral_add_adjacent_intervals
      (f := inner) (a := 0) (b := a - r) (c := a) h0_ar_int har_a_int
    rw [← h02, ← h01]
  have hXle : (∫ x in (a - r)..a, inner x) ≤ Xmodel := by
    dsimp [Xmodel, inner]
    refine intervalIntegral.integral_mono_on har_a
      (hcont_inner.intervalIntegrable (a - r) a)
      ((by fun_prop : Continuous fun x : ℝ => (a - x) * exp (a ^ 3 - k * (a - x))).intervalIntegrable (a - r) a)
      ?_
    intro x hx
    have hxlo : a - a⁻¹ ≤ x := by simpa [r] using hx.1
    have hxhi : x ≤ a := hx.2
    have hax : 0 ≤ a - x := sub_nonneg.mpr hxhi
    calc
      (∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
          ∫ y in (0)..(a - x), exp (a ^ 3 - k * (a - x)) := by
        refine intervalIntegral.integral_mono_on hax
          ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3)).intervalIntegrable 0 (a - x))
          (continuous_const.intervalIntegrable 0 (a - x))
          ?_
        intro y hy
        exact Real.exp_le_exp.mpr
          (by
            dsimp [k]
            exact putnam_1983_a6_x_upper_exponent ha hxlo hxhi hy.1 hy.2)
      _ = (a - x) * exp (a ^ 3 - k * (a - x)) := by
        simp
  have hAle : (∫ x in (0)..r, inner x) ≤ r * ((a - r) * tail) + Ymodel := by
    dsimp [Ymodel, inner, tail]
    let yPart : ℝ → ℝ :=
      fun x => ∫ y in (a - r)..(a - x), exp (a ^ 3 - k * (a - y))
    have hpoint : ∀ x ∈ Set.Icc 0 r,
        (∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
          (a - r) * exp (a ^ 3 - a) + yPart x := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hxr : x ≤ r := hx.2
      have hsub : a - r ≤ a - x := by linarith
      have hax : 0 ≤ a - x := by linarith [hr_le_a]
      have hsplit_inner :
          (∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) =
            (∫ y in (0)..(a - r), exp (x ^ 3 + y ^ 3)) +
              ∫ y in (a - r)..(a - x), exp (x ^ 3 + y ^ 3) := by
        have h01 : IntervalIntegrable (fun y : ℝ => exp (x ^ 3 + y ^ 3))
            MeasureTheory.volume 0 (a - r) :=
          ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3))).intervalIntegrable 0 (a - r)
        have h12 : IntervalIntegrable (fun y : ℝ => exp (x ^ 3 + y ^ 3))
            MeasureTheory.volume (a - r) (a - x) :=
          ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3))).intervalIntegrable (a - r) (a - x)
        exact (intervalIntegral.integral_add_adjacent_intervals
          (f := fun y : ℝ => exp (x ^ 3 + y ^ 3))
          (a := 0) (b := a - r) (c := a - x) h01 h12).symm
      have hleft :
          (∫ y in (0)..(a - r), exp (x ^ 3 + y ^ 3)) ≤
            (a - r) * exp (a ^ 3 - a) := by
        calc
          (∫ y in (0)..(a - r), exp (x ^ 3 + y ^ 3)) ≤
              ∫ y in (0)..(a - r), exp (a ^ 3 - a) := by
            refine intervalIntegral.integral_mono_on h0_ar
              ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3)).intervalIntegrable 0 (a - r))
              (continuous_const.intervalIntegrable 0 (a - r))
              ?_
            intro y hy
            exact Real.exp_le_exp.mpr
              (putnam_1983_a6_left_tail_exponent ha hx0 hxr hy.1 hy.2)
          _ = (a - r) * exp (a ^ 3 - a) := by
            simp
      have hyupper :
          (∫ y in (a - r)..(a - x), exp (x ^ 3 + y ^ 3)) ≤ yPart x := by
        dsimp [yPart]
        refine intervalIntegral.integral_mono_on hsub
          ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3)).intervalIntegrable (a - r) (a - x))
          ((by fun_prop : Continuous fun y : ℝ => exp (a ^ 3 - k * (a - y))).intervalIntegrable (a - r) (a - x))
          ?_
        intro y hy
        have hylo : a - a⁻¹ ≤ y := by simpa [r] using hy.1
        have hyhi : y ≤ a := hy.2.trans (by linarith : a - x ≤ a)
        have hyle : y ≤ a - x := hy.2
        have hxy : x ≤ a - y := by linarith
        exact Real.exp_le_exp.mpr
          (by
            dsimp [k]
            exact putnam_1983_a6_y_upper_exponent ha hylo hyhi hx0 hxy)
      rw [hsplit_inner]
      nlinarith
    have hmono :
        (∫ x in (0)..r, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
          ∫ x in (0)..r, ((a - r) * exp (a ^ 3 - a) + yPart x) := by
      refine intervalIntegral.integral_mono_on h0r
        (hcont_inner.intervalIntegrable 0 r)
        ((by fun_prop : Continuous fun x : ℝ => (a - r) * exp (a ^ 3 - a) + yPart x).intervalIntegrable 0 r)
        hpoint
    calc
      (∫ x in (0)..r, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
          ∫ x in (0)..r, ((a - r) * exp (a ^ 3 - a) + yPart x) := hmono
      _ = r * ((a - r) * exp (a ^ 3 - a)) + ∫ x in (0)..r, yPart x := by
        rw [intervalIntegral.integral_add
          (continuous_const.intervalIntegrable 0 r)
          ((by fun_prop : Continuous fun x : ℝ => yPart x).intervalIntegrable 0 r)]
        simp
        ring
      _ = r * ((a - r) * exp (a ^ 3 - a)) + Ymodel := by
        rfl
  have hMle : (∫ x in r..(a - r), inner x) ≤ a ^ 2 * tail := by
    dsimp [inner, tail]
    have hinner_le : ∀ x ∈ Set.Icc r (a - r),
        (∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤ a * exp (a ^ 3 - a) := by
      intro x hx
      have hxr : a⁻¹ ≤ x := by simpa [r] using hx.1
      have hxa : x ≤ a - a⁻¹ := by simpa [r] using hx.2
      have hx_a : x ≤ a := hx.2.trans har_a
      have hax : 0 ≤ a - x := sub_nonneg.mpr hx_a
      have hax_le_a : a - x ≤ a := by linarith [le_trans (inv_nonneg.mpr ha_pos.le) hxr]
      calc
        (∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
            ∫ y in (0)..(a - x), exp (a ^ 3 - a) := by
          refine intervalIntegral.integral_mono_on hax
            ((by fun_prop : Continuous fun y : ℝ => exp (x ^ 3 + y ^ 3)).intervalIntegrable 0 (a - x))
            (continuous_const.intervalIntegrable 0 (a - x))
            ?_
          intro y hy
          exact Real.exp_le_exp.mpr
            (putnam_1983_a6_middle_tail_exponent ha hxr hxa hy.1 hy.2)
        _ = (a - x) * exp (a ^ 3 - a) := by simp
        _ ≤ a * exp (a ^ 3 - a) :=
          mul_le_mul_of_nonneg_right hax_le_a (exp_pos _).le
    calc
      (∫ x in r..(a - r), ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) ≤
          ∫ x in r..(a - r), a * exp (a ^ 3 - a) := by
        refine intervalIntegral.integral_mono_on hr_ar
          (hcont_inner.intervalIntegrable r (a - r))
          (continuous_const.intervalIntegrable r (a - r))
          hinner_le
      _ = (a - r - r) * (a * exp (a ^ 3 - a)) := by
        simp
        ring
      _ ≤ a ^ 2 * exp (a ^ 3 - a) := by
        have hlen_nonneg : 0 ≤ a - r - r := by linarith
        have hlen_le : a - r - r ≤ a := by linarith [hr_nonneg]
        have hmul := mul_le_mul_of_nonneg_right hlen_le
          (mul_nonneg ha_pos.le (exp_pos (a ^ 3 - a)).le)
        calc
          (a - r - r) * (a * exp (a ^ 3 - a)) ≤ a * (a * exp (a ^ 3 - a)) := hmul
          _ = a ^ 2 * exp (a ^ 3 - a) := by ring
  have hA_tail : r * ((a - r) * tail) ≤ a ^ 2 * tail := by
    have hprod : r * (a - r) ≤ a * a :=
      mul_le_mul hr_le_a har_a h0_ar ha_pos.le
    have hmul := mul_le_mul_of_nonneg_right hprod htail_nonneg
    nlinarith
  have hXeq : Xmodel =
      exp (a ^ 3) * ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u) := by
    dsimp [Xmodel, r, k]
    rw [putnam_1983_a6_x_model_integral (C := a ^ 3) (k := 3 * a ^ 2 - 3)
      (r := a⁻¹) (a := a) hk]
    rw [putnam_1983_a6_integral_id_mul_exp_neg_mul (k := 3 * a ^ 2 - 3)
      (r := a⁻¹) hk]
    ring
  have hYeq : Ymodel =
      exp (a ^ 3) * ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u) := by
    dsimp [Ymodel, r, k]
    rw [putnam_1983_a6_y_model_integral (C := a ^ 3) (k := 3 * a ^ 2 - 3)
      (r := a⁻¹) (a := a) hk]
    rw [putnam_1983_a6_integral_id_mul_exp_neg_mul (k := 3 * a ^ 2 - 3)
      (r := a⁻¹) hk]
    ring
  dsimp [inner] at hsplit
  rw [hsplit]
  nlinarith [hXle, hAle, hMle, hA_tail, hXeq, hYeq]

-- 2 / 9
/--
Let $T$ be the triangle with vertices $(0, 0)$, $(a, 0)$, and $(0, a)$. Find $\lim_{a \to \infty} a^4 \exp(-a^3) \int_T \exp(x^3+y^3) \, dx \, dy$.
-/
theorem putnam_1983_a6
(F : ℝ → ℝ)
(hF : F = fun a ↦ (a ^ 4 / exp (a ^ 3)) * ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3))
: (Tendsto F atTop (𝓝 ((2 / 9) : ℝ ))) := by
  rw [hF]
  have hlowlim :
      Tendsto
        (fun a : ℝ =>
          2 * (a ^ 4 *
            ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u)))
        atTop (𝓝 ((2 / 9 : ℝ))) := by
    simpa using putnam_1983_a6_lower_strip_limit.const_mul (2 : ℝ)
  have hupperlim :
      Tendsto
        (fun a : ℝ =>
          2 * (a ^ 4 *
            ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u)) +
          2 * (a ^ 6 * exp (-a)))
        atTop (𝓝 ((2 / 9 : ℝ))) := by
    have h1 := putnam_1983_a6_upper_strip_limit.const_mul (2 : ℝ)
    have h2 := putnam_1983_a6_scaled_exp_tail.const_mul (2 : ℝ)
    have h := h1.add h2
    simpa using h
  have hlower :
      ∀ᶠ a in atTop,
        2 * (a ^ 4 *
          ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u)) ≤
        (a ^ 4 / exp (a ^ 3)) *
          ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with a ha
    have hraw := putnam_1983_a6_raw_lower_bound a ha
    have hfactor : 0 ≤ a ^ 4 / exp (a ^ 3) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hraw hfactor
    calc
      2 * (a ^ 4 * ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u)) =
          (a ^ 4 / exp (a ^ 3)) *
            (2 * (exp (a ^ 3) *
              ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u))) := by
        let S : ℝ := ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 + 1) * u)
        change 2 * (a ^ 4 * S) =
          (a ^ 4 / exp (a ^ 3)) * (2 * (exp (a ^ 3) * S))
        field_simp [exp_ne_zero (a ^ 3)]
      _ ≤ (a ^ 4 / exp (a ^ 3)) *
          ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) := hmul
  have hupper :
      ∀ᶠ a in atTop,
        (a ^ 4 / exp (a ^ 3)) *
          ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) ≤
        2 * (a ^ 4 *
          ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u)) +
          2 * (a ^ 6 * exp (-a)) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with a ha
    have hraw := putnam_1983_a6_raw_upper_bound a ha
    have hfactor : 0 ≤ a ^ 4 / exp (a ^ 3) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hraw hfactor
    calc
      (a ^ 4 / exp (a ^ 3)) *
          ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3) ≤
          (a ^ 4 / exp (a ^ 3)) *
            (2 * (exp (a ^ 3) *
              ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u)) +
              2 * (a ^ 2 * exp (a ^ 3 - a))) := hmul
      _ = 2 * (a ^ 4 *
            ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u)) +
          2 * (a ^ 6 * exp (-a)) := by
        rw [show exp (a ^ 3 - a) = exp (a ^ 3) * exp (-a) by
          rw [show a ^ 3 - a = a ^ 3 + (-a) by ring]
          rw [exp_add]]
        let S : ℝ := ∫ u in (0)..a⁻¹, u * exp (-(3 * a ^ 2 - 3) * u)
        change (a ^ 4 / exp (a ^ 3)) *
            (2 * (exp (a ^ 3) * S) + 2 * (a ^ 2 * (exp (a ^ 3) * exp (-a)))) =
          2 * (a ^ 4 * S) + 2 * (a ^ 6 * exp (-a))
        field_simp [exp_ne_zero (a ^ 3)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim hupperlim hlower hupper
