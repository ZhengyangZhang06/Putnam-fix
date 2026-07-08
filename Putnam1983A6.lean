import Mathlib

open Nat Filter Topology Real

noncomputable abbrev putnam_1983_a6_solution : ℝ := 2 / 9

open Set MeasureTheory

private lemma exp_add_ge_add_exp_sub_one {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    exp (u + v) ≥ exp u + exp v - 1 := by
  have hu1 : 1 ≤ exp u := by
    simpa using exp_le_exp.mpr hu
  have hv1 : 1 ≤ exp v := by
    simpa using exp_le_exp.mpr hv
  have hmul : 0 ≤ (exp u - 1) * (exp v - 1) :=
    mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1)
  rw [exp_add]
  nlinarith

private lemma cubic_endpoint_lower {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    x ^ 3 - a ^ 3 ≥ -3 * a ^ 2 * (a - x) := by
  nlinarith [sq_nonneg (a - x), sq_nonneg x, sq_nonneg a]

private lemma cubic_near_x
    {a x y c δ : ℝ} (ha : 0 ≤ a) (hδ : δ ≤ (3 - c) / 3)
    (hxnear : a - x ≤ δ * a) (hy : y ≤ a - x)
    (hx0 : 0 ≤ a - x) (hy0 : 0 ≤ y) :
    x ^ 3 + y ^ 3 - a ^ 3 ≤ -c * a ^ 2 * (a - x) := by
  have hy3 : y ^ 3 ≤ (a - x) ^ 3 := by gcongr
  have hxge : c / 3 * a ≤ x := by nlinarith
  have hcalc : x ^ 3 + (a - x) ^ 3 - a ^ 3 = -3 * a * x * (a - x) := by ring
  calc
    x ^ 3 + y ^ 3 - a ^ 3 ≤ x ^ 3 + (a - x) ^ 3 - a ^ 3 := by nlinarith
    _ = -3 * a * x * (a - x) := hcalc
    _ ≤ -c * a ^ 2 * (a - x) := by
      have hright_nonneg : 0 ≤ 3 * a * (a - x) := by nlinarith [mul_nonneg ha hx0]
      have hprod := mul_le_mul_of_nonneg_right hxge hright_nonneg
      nlinarith

private lemma cubic_middle
    {a x y δ d : ℝ} (ha : 0 ≤ a) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxa : x ≤ (1 - δ) * a) (hya : y ≤ (1 - δ) * a) (hxy : x + y ≤ a)
    (hd : d = 1 - (1 - δ) ^ 2) :
    x ^ 3 + y ^ 3 - a ^ 3 ≤ -d * a ^ 3 := by
  have hone : 0 ≤ 1 - δ := by linarith
  have hx2 : x ^ 2 ≤ ((1 - δ) * a) ^ 2 := by gcongr
  have hy2 : y ^ 2 ≤ ((1 - δ) * a) ^ 2 := by gcongr
  have hx3 : x ^ 3 ≤ ((1 - δ) * a) ^ 2 * x := by
    have := mul_le_mul_of_nonneg_right hx2 hx0
    nlinarith
  have hy3 : y ^ 3 ≤ ((1 - δ) * a) ^ 2 * y := by
    have := mul_le_mul_of_nonneg_right hy2 hy0
    nlinarith
  have hsum : x ^ 3 + y ^ 3 ≤ ((1 - δ) * a) ^ 2 * (x + y) := by nlinarith
  have hsum2 : ((1 - δ) * a) ^ 2 * (x + y) ≤ ((1 - δ) * a) ^ 2 * a := by
    exact mul_le_mul_of_nonneg_left hxy (sq_nonneg _)
  have hcalc : ((1 - δ) * a) ^ 2 * a - a ^ 3 = -d * a ^ 3 := by
    subst d
    ring
  nlinarith

private lemma exp_two_corner_lower {a x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    exp (x ^ 3 - a ^ 3) + exp (y ^ 3 - a ^ 3) - exp (-a ^ 3)
      ≤ exp (x ^ 3 + y ^ 3 - a ^ 3) := by
  have hbase := exp_add_ge_add_exp_sub_one (u := x ^ 3) (v := y ^ 3)
    (pow_nonneg hx0 3) (pow_nonneg hy0 3)
  have hmul := mul_le_mul_of_nonneg_left hbase (le_of_lt (exp_pos (-a ^ 3)))
  rw [mul_sub, mul_add, ← exp_add, ← exp_add, ← exp_add] at hmul
  convert hmul using 1 <;> ring

private lemma scaled_linear_exp_tendsto (k : ℝ) (hk : 0 < k) :
    Tendsto (fun a : ℝ => a ^ 4 * (∫ s in (0)..a, s * exp (-(k * a ^ 2) * s)))
      atTop (𝓝 (1 / k ^ 2)) := by
  have hscale : (fun a : ℝ => a ^ 4 * (∫ s in (0)..a, s * exp (-(k * a ^ 2) * s)))
      =ᶠ[atTop] (fun a : ℝ => ∫ u in (0)..(a ^ 3), u * exp (-(k * u))) := by
    refine Eventually.of_forall ?_
    intro a
    calc
      a ^ 4 * (∫ s in (0)..a, s * exp (-(k * a ^ 2) * s))
          = a ^ 2 * (∫ s in (0)..a, (s * a ^ 2) * exp (-k * (s * a ^ 2))) := by
            rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro s hs
            ring_nf
      _ = ∫ u in (0 * a ^ 2)..(a * a ^ 2), u * exp (-k * u) := by
            simpa [smul_eq_mul] using (intervalIntegral.smul_integral_comp_mul_right
              (f := fun u : ℝ => u * exp (-k * u)) (a := (0 : ℝ)) (b := a) (c := a ^ 2))
      _ = ∫ u in (0)..(a ^ 3), u * exp (-k * u) := by
            ring_nf
      _ = ∫ u in (0)..(a ^ 3), u * exp (-(k * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            ring_nf
  have hint : IntegrableOn (fun u : ℝ => u * exp (-(k * u))) (Ioi 0) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ)) (b := k)
        (by norm_num : (-1 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1) hk)
  have hlim0 : Tendsto (fun b : ℝ => ∫ u in (0)..b, u * exp (-(k * u))) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), u * exp (-(k * u)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hcube : Tendsto (fun a : ℝ => a ^ 3) atTop atTop :=
    tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)
  have hlim := hlim0.comp hcube
  have hval : (∫ u in Ioi (0 : ℝ), u * exp (-(k * u))) = 1 / k ^ 2 := by
    calc
      (∫ u in Ioi (0 : ℝ), u * exp (-(k * u)))
          = ∫ u in Ioi (0 : ℝ), u ^ (1 : ℝ) * exp (-k * u ^ (1 : ℝ)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            simp [Real.rpow_one]
      _ = k ^ (-(1 + 1) / 1 : ℝ) * (1 / 1) * Gamma ((1 + 1) / 1) := by
            exact integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (1 : ℝ)) (b := k)
              (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hk
      _ = 1 / k ^ 2 := by
            norm_num [Gamma_two, Real.rpow_neg hk.le, Real.rpow_two]
  exact Tendsto.congr' hscale.symm (by simpa [hval, one_div] using hlim)

private lemma scaled_plain_exp_tendsto (k : ℝ) (hk : 0 < k) :
    Tendsto (fun a : ℝ => a ^ 2 * (∫ x in (0)..a, exp (-(k * a ^ 2) * x)))
      atTop (𝓝 (1 / k)) := by
  have hscale : (fun a : ℝ => a ^ 2 * (∫ x in (0)..a, exp (-(k * a ^ 2) * x)))
      =ᶠ[atTop] (fun a : ℝ => ∫ u in (0)..(a ^ 3), exp (-(k * u))) := by
    refine Eventually.of_forall ?_
    intro a
    calc
      a ^ 2 * (∫ x in (0)..a, exp (-(k * a ^ 2) * x))
          = a ^ 2 * (∫ x in (0)..a, exp (-k * (x * a ^ 2))) := by
            apply congrArg (fun z => a ^ 2 * z)
            apply intervalIntegral.integral_congr
            intro x hx
            ring_nf
      _ = ∫ u in (0 * a ^ 2)..(a * a ^ 2), exp (-k * u) := by
            simpa [smul_eq_mul] using (intervalIntegral.smul_integral_comp_mul_right
              (f := fun u : ℝ => exp (-k * u)) (a := (0 : ℝ)) (b := a) (c := a ^ 2))
      _ = ∫ u in (0)..(a ^ 3), exp (-k * u) := by
            ring_nf
      _ = ∫ u in (0)..(a ^ 3), exp (-(k * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            ring_nf
  have hint : IntegrableOn (fun u : ℝ => exp (-(k * u))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -k) (by linarith) (c := 0)
  have hlim0 : Tendsto (fun b : ℝ => ∫ u in (0)..b, exp (-(k * u))) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), exp (-(k * u)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hcube : Tendsto (fun a : ℝ => a ^ 3) atTop atTop :=
    tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)
  have hlim := hlim0.comp hcube
  have hval : (∫ u in Ioi (0 : ℝ), exp (-(k * u))) = 1 / k := by
    simpa [neg_mul] using integral_exp_mul_Ioi (a := -k) (by linarith) (c := 0)
  exact Tendsto.congr' hscale.symm (by simpa [hval] using hlim)

private lemma exp_poly_decay3 (k : ℝ) (hk : 0 < k) :
    Tendsto (fun a : ℝ => a ^ 3 * exp (-k * a ^ 3)) atTop (𝓝 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) k hk
  have hcube : Tendsto (fun a : ℝ => a ^ 3) atTop atTop :=
    tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)
  have hcomp := hbase.comp hcube
  refine hcomp.congr' ?_
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with a ha
  simp [Real.rpow_one]

private lemma exp_poly_decay6 (k : ℝ) (hk : 0 < k) :
    Tendsto (fun a : ℝ => a ^ 6 * exp (-k * a ^ 3)) atTop (𝓝 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) k hk
  have hcube : Tendsto (fun a : ℝ => a ^ 3) atTop atTop :=
    tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)
  have hcomp := hbase.comp hcube
  refine hcomp.congr' ?_
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with a ha
  simp [pow_succ]
  ring_nf

private lemma inner_y_exp (a x k : ℝ) (ha : a ≠ 0) (hk : k ≠ 0) :
    (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y))) =
      (exp (-(k * a ^ 2) * x) - exp (-(k * a ^ 2) * a)) / (k * a ^ 2) := by
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun z : ℝ => exp (-(k * a ^ 2) * z)) (a := (0 : ℝ)) (b := a - x) (d := a)
  have hsub' : (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y))) =
      ∫ z in x..a, exp (-(k * a ^ 2) * z) := by
    convert hsub using 1 <;> ring_nf
  rw [hsub']
  rw [intervalIntegral.integral_comp_mul_left (f := fun u : ℝ => exp u)
    (a := x) (b := a) (c := -(k * a ^ 2))
    (by exact neg_ne_zero.mpr (mul_ne_zero hk (pow_ne_zero 2 ha)))]
  rw [integral_exp]
  simp only [smul_eq_mul]
  field_simp [hk, pow_ne_zero 2 ha]
  ring_nf

private lemma xterm_tendsto (k : ℝ) (hk : 0 < k) :
    Tendsto
      (fun a : ℝ => a ^ 4 *
        (∫ x in (0)..a, ∫ _y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x))))
      atTop (𝓝 (1 / k ^ 2)) := by
  have heq :
      (fun a : ℝ => a ^ 4 *
        (∫ x in (0)..a, ∫ _y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x))))
        =ᶠ[atTop]
      (fun a : ℝ => a ^ 4 * (∫ s in (0)..a, s * exp (-(k * a ^ 2) * s))) := by
    refine Eventually.of_forall ?_
    intro a
    calc
      a ^ 4 * (∫ x in (0)..a, ∫ _y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x)))
          = a ^ 4 * (∫ x in (0)..a, (a - x) * exp (-(k * a ^ 2) * (a - x))) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro x hx
            simpa [smul_eq_mul] using (intervalIntegral.integral_const
              (a := (0 : ℝ)) (b := a - x) (c := exp (-(k * a ^ 2) * (a - x))))
      _ = a ^ 4 * (∫ s in (0)..a, s * exp (-(k * a ^ 2) * s)) := by
            congr 1
            convert (intervalIntegral.integral_comp_sub_left
              (f := fun s : ℝ => s * exp (-(k * a ^ 2) * s))
              (a := (0 : ℝ)) (b := a) (d := a)) using 1 <;> ring_nf
  exact Tendsto.congr' heq.symm (scaled_linear_exp_tendsto k hk)

private lemma yterm_tendsto (k : ℝ) (hk : 0 < k) :
    Tendsto
      (fun a : ℝ => a ^ 4 *
        (∫ x in (0)..a, ∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y))))
      atTop (𝓝 (1 / k ^ 2)) := by
  have heq :
      (fun a : ℝ => a ^ 4 *
        (∫ x in (0)..a, ∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y))))
        =ᶠ[atTop]
      (fun a : ℝ =>
        (1 / k) * (a ^ 2 * ∫ x in (0)..a, exp (-(k * a ^ 2) * x))
          - (1 / k) * (a ^ 3 * exp (-k * a ^ 3))) := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with a ha
    have ha_ne : a ≠ 0 := ne_of_gt ha
    calc
      a ^ 4 * (∫ x in (0)..a, ∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y)))
          = a ^ 4 * (∫ x in (0)..a,
              (exp (-(k * a ^ 2) * x) - exp (-(k * a ^ 2) * a)) / (k * a ^ 2)) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro x hx
            exact inner_y_exp a x k ha_ne hk.ne'
      _ = (1 / k) * (a ^ 2 * ∫ x in (0)..a, exp (-(k * a ^ 2) * x))
            - (1 / k) * (a ^ 3 * exp (-k * a ^ 3)) := by
            rw [intervalIntegral.integral_div]
            rw [intervalIntegral.integral_sub]
            · rw [intervalIntegral.integral_const]
              simp only [smul_eq_mul]
              field_simp [hk.ne', ha_ne]
              ring_nf
            · apply Continuous.intervalIntegrable; fun_prop
            · apply Continuous.intervalIntegrable; fun_prop
  have h1 := (scaled_plain_exp_tendsto k hk).const_mul (1 / k)
  have h2 := (exp_poly_decay3 k hk).const_mul (1 / k)
  have hsub := h1.sub h2
  refine Tendsto.congr' heq.symm ?_
  convert hsub using 1 <;> field_simp [hk.ne'] <;> ring

private lemma tri_const_integral (a C : ℝ) :
    (∫ x in (0)..a, ∫ _y in (0)..(a - x), C) = (a ^ 2 / 2) * C := by
  calc
    (∫ x in (0)..a, ∫ _y in (0)..(a - x), C)
        = ∫ x in (0)..a, (a - x) * C := by
          apply intervalIntegral.integral_congr
          intro x hx
          simpa [smul_eq_mul] using (intervalIntegral.integral_const
            (a := (0 : ℝ)) (b := a - x) (c := C))
    _ = (∫ x in (0)..a, (a - x)) * C := by
          rw [intervalIntegral.integral_mul_const]
    _ = (a ^ 2 / 2) * C := by
          congr 1
          calc
            (∫ x in (0)..a, (a - x)) = (∫ x in (0)..a, a) - ∫ x in (0)..a, x := by
              rw [← intervalIntegral.integral_sub
                (by apply Continuous.intervalIntegrable; fun_prop)
                (by apply Continuous.intervalIntegrable; fun_prop)]
            _ = a ^ 2 / 2 := by
              rw [intervalIntegral.integral_const, integral_id]
              simp [smul_eq_mul]
              ring

private noncomputable def scaledTri (a : ℝ) : ℝ :=
  a ^ 4 * ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3 - a ^ 3)

private noncomputable def xTerm (k a : ℝ) : ℝ :=
  a ^ 4 * ∫ x in (0)..a, ∫ _y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x))

private noncomputable def yTerm (k a : ℝ) : ℝ :=
  a ^ 4 * ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y))

private noncomputable def constTerm (d a : ℝ) : ℝ :=
  a ^ 4 * ∫ x in (0)..a, ∫ _y in (0)..(a - x), exp (-d * a ^ 3)

private lemma xTerm_tendsto' (k : ℝ) (hk : 0 < k) :
    Tendsto (fun a : ℝ => xTerm k a) atTop (𝓝 (1 / k ^ 2)) := by
  simpa [xTerm] using xterm_tendsto k hk

private lemma yTerm_tendsto' (k : ℝ) (hk : 0 < k) :
    Tendsto (fun a : ℝ => yTerm k a) atTop (𝓝 (1 / k ^ 2)) := by
  simpa [yTerm] using yterm_tendsto k hk

private lemma constTerm_tendsto (d : ℝ) (hd : 0 < d) :
    Tendsto (fun a : ℝ => constTerm d a) atTop (𝓝 0) := by
  have heq : (fun a : ℝ => constTerm d a)
      =ᶠ[atTop] (fun a : ℝ => (1 / 2) * (a ^ 6 * exp (-d * a ^ 3))) := by
    refine Eventually.of_forall ?_
    intro a
    dsimp [constTerm]
    rw [tri_const_integral]
    ring
  refine Tendsto.congr' heq.symm ?_
  convert (exp_poly_decay6 d hd).const_mul (1 / 2) using 1 <;> norm_num

private lemma split_sub_terms (k d a : ℝ) :
    xTerm k a + yTerm k a - constTerm d a =
      a ^ 4 * ∫ x in (0)..a, ∫ y in (0)..(a - x),
        (exp (-(k * a ^ 2) * (a - x)) + exp (-(k * a ^ 2) * (a - y))
          - exp (-d * a ^ 3)) := by
  unfold xTerm yTerm constTerm
  have hinner : (fun x : ℝ => ∫ y in (0)..(a - x),
        (exp (-(k * a ^ 2) * (a - x)) + exp (-(k * a ^ 2) * (a - y))
          - exp (-d * a ^ 3)))
      = fun x : ℝ => (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x)))
          + (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y)))
          - (∫ y in (0)..(a - x), exp (-d * a ^ 3)) := by
    funext x
    rw [intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [show (∫ x in (0)..a, ∫ y in (0)..(a - x),
        (exp (-(k * a ^ 2) * (a - x)) + exp (-(k * a ^ 2) * (a - y))
          - exp (-d * a ^ 3)))
      = ∫ x in (0)..a, ((∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x)))
          + (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y)))
          - (∫ y in (0)..(a - x), exp (-d * a ^ 3))) by rw [hinner]]
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

private lemma split_add_terms (k d a : ℝ) :
    xTerm k a + yTerm k a + constTerm d a =
      a ^ 4 * ∫ x in (0)..a, ∫ y in (0)..(a - x),
        (exp (-(k * a ^ 2) * (a - x)) + exp (-(k * a ^ 2) * (a - y))
          + exp (-d * a ^ 3)) := by
  unfold xTerm yTerm constTerm
  have hinner : (fun x : ℝ => ∫ y in (0)..(a - x),
        (exp (-(k * a ^ 2) * (a - x)) + exp (-(k * a ^ 2) * (a - y))
          + exp (-d * a ^ 3)))
      = fun x : ℝ => (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x)))
          + (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y)))
          + (∫ y in (0)..(a - x), exp (-d * a ^ 3)) := by
    funext x
    rw [intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [show (∫ x in (0)..a, ∫ y in (0)..(a - x),
        (exp (-(k * a ^ 2) * (a - x)) + exp (-(k * a ^ 2) * (a - y))
          + exp (-d * a ^ 3)))
      = ∫ x in (0)..a, ((∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - x)))
          + (∫ y in (0)..(a - x), exp (-(k * a ^ 2) * (a - y)))
          + (∫ y in (0)..(a - x), exp (-d * a ^ 3))) by rw [hinner]]
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

private lemma lower_bound_eventually :
    ∀ᶠ a in atTop, xTerm 3 a + yTerm 3 a - constTerm 1 a ≤ scaledTri a := by
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with a ha
  rw [split_sub_terms]
  unfold scaledTri
  apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg ha 4)
  apply intervalIntegral.integral_mono_on ha
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hxa : x ≤ a := hx.2
  have hax : 0 ≤ a - x := sub_nonneg.mpr hxa
  apply intervalIntegral.integral_mono_on hax
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro y hy
  have hy0 : 0 ≤ y := hy.1
  have hxexp : exp (-(3 * a ^ 2) * (a - x)) ≤ exp (x ^ 3 - a ^ 3) := by
    apply exp_le_exp.mpr
    have := cubic_endpoint_lower (a := a) (x := x) ha hx0
    nlinarith
  have hyexp : exp (-(3 * a ^ 2) * (a - y)) ≤ exp (y ^ 3 - a ^ 3) := by
    apply exp_le_exp.mpr
    have := cubic_endpoint_lower (a := a) (x := y) ha hy0
    nlinarith
  calc
    exp (-(3 * a ^ 2) * (a - x)) + exp (-(3 * a ^ 2) * (a - y)) - exp (-1 * a ^ 3)
        ≤ exp (x ^ 3 - a ^ 3) + exp (y ^ 3 - a ^ 3) - exp (-a ^ 3) := by
          have hone : exp (-1 * a ^ 3) = exp (-a ^ 3) := by ring_nf
          rw [hone]
          nlinarith
    _ ≤ exp (x ^ 3 + y ^ 3 - a ^ 3) := exp_two_corner_lower hx0 hy0

private lemma upper_bound_eventually {c δ d : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (3 - c) / 3)
    (hd : d = 1 - (1 - δ) ^ 2) :
    ∀ᶠ a in atTop, scaledTri a ≤ xTerm c a + yTerm c a + constTerm d a := by
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with a ha
  rw [split_add_terms]
  unfold scaledTri
  apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg ha 4)
  apply intervalIntegral.integral_mono_on ha
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hxa : x ≤ a := hx.2
  have hax : 0 ≤ a - x := sub_nonneg.mpr hxa
  apply intervalIntegral.integral_mono_on hax
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro y hy
  have hy0 : 0 ≤ y := hy.1
  have hya_x : y ≤ a - x := hy.2
  have hxy : x + y ≤ a := by linarith
  by_cases hxnear : a - x ≤ δ * a
  · have hmain : x ^ 3 + y ^ 3 - a ^ 3 ≤ -c * a ^ 2 * (a - x) :=
      cubic_near_x (a := a) (x := x) (y := y) (c := c) (δ := δ)
        ha hδc hxnear hya_x hax hy0
    have hexp : exp (x ^ 3 + y ^ 3 - a ^ 3) ≤ exp (-(c * a ^ 2) * (a - x)) := by
      apply exp_le_exp.mpr
      nlinarith
    have hpos1 : 0 ≤ exp (-(c * a ^ 2) * (a - y)) := le_of_lt (exp_pos _)
    have hpos2 : 0 ≤ exp (-d * a ^ 3) := le_of_lt (exp_pos _)
    nlinarith
  · by_cases hynear : a - y ≤ δ * a
    · have hay : 0 ≤ a - y := by linarith
      have hxy' : x ≤ a - y := by linarith
      have hmain : y ^ 3 + x ^ 3 - a ^ 3 ≤ -c * a ^ 2 * (a - y) :=
        cubic_near_x (a := a) (x := y) (y := x) (c := c) (δ := δ)
          ha hδc hynear hxy' hay hx0
      have hexp : exp (x ^ 3 + y ^ 3 - a ^ 3) ≤ exp (-(c * a ^ 2) * (a - y)) := by
        apply exp_le_exp.mpr
        nlinarith
      have hpos1 : 0 ≤ exp (-(c * a ^ 2) * (a - x)) := le_of_lt (exp_pos _)
      have hpos2 : 0 ≤ exp (-d * a ^ 3) := le_of_lt (exp_pos _)
      nlinarith
    · have hxmid : x ≤ (1 - δ) * a := by
        have : δ * a < a - x := lt_of_not_ge hxnear
        nlinarith
      have hymid : y ≤ (1 - δ) * a := by
        have : δ * a < a - y := lt_of_not_ge hynear
        nlinarith
      have hmain : x ^ 3 + y ^ 3 - a ^ 3 ≤ -d * a ^ 3 :=
        cubic_middle (a := a) (x := x) (y := y) (δ := δ) (d := d)
          ha hδ0 hδ1 hx0 hy0 hxmid hymid hxy hd
      have hexp : exp (x ^ 3 + y ^ 3 - a ^ 3) ≤ exp (-d * a ^ 3) :=
        exp_le_exp.mpr hmain
      have hpos1 : 0 ≤ exp (-(c * a ^ 2) * (a - x)) := le_of_lt (exp_pos _)
      have hpos2 : 0 ≤ exp (-(c * a ^ 2) * (a - y)) := le_of_lt (exp_pos _)
      nlinarith

private lemma exists_rate_for_upper {b : ℝ} (hb : (2 / 9 : ℝ) < b) :
    ∃ c, 0 < c ∧ c < 3 ∧ 2 / c ^ 2 < b := by
  have hbpos : 0 < b := by nlinarith
  let r := sqrt (2 / b)
  have hr0 : 0 ≤ r := sqrt_nonneg _
  have hrlt : r < 3 := by
    dsimp [r]
    rw [sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
    field_simp [hbpos.ne']
    nlinarith
  let c := (r + 3) / 2
  have hcpos : 0 < c := by dsimp [c]; nlinarith
  have hc3 : c < 3 := by dsimp [c]; nlinarith
  have hrc : r < c := by dsimp [c]; nlinarith
  refine ⟨c, hcpos, hc3, ?_⟩
  have hsqr : 2 / b < c ^ 2 := by
    have hr_sq : r ^ 2 = 2 / b := by
      dsimp [r]
      rw [sq_sqrt]
      positivity
    nlinarith [sq_nonneg (c - r), mul_pos (sub_pos.mpr hrc) (by nlinarith : 0 < c + r)]
  have hbmul : (2 / b) * b < c ^ 2 * b := mul_lt_mul_of_pos_right hsqr hbpos
  have h2 : 2 < c ^ 2 * b := by
    simpa [div_mul_cancel₀ _ hbpos.ne'] using hbmul
  rw [div_lt_iff₀ (sq_pos_of_pos hcpos)]
  nlinarith

private lemma original_eq_scaled (a : ℝ) :
    (a ^ 4 / exp (a ^ 3)) *
        (∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3)) =
      scaledTri a := by
  unfold scaledTri
  calc
    (a ^ 4 / exp (a ^ 3)) *
        (∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3))
        = a ^ 4 * ((exp (a ^ 3))⁻¹ *
            (∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3))) := by
          ring
    _ = a ^ 4 * (∫ x in (0)..a,
          (exp (a ^ 3))⁻¹ * (∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3))) := by
          congr 1
          rw [← intervalIntegral.integral_const_mul]
    _ = a ^ 4 * (∫ x in (0)..a, ∫ y in (0)..(a - x),
          (exp (a ^ 3))⁻¹ * exp (x ^ 3 + y ^ 3)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro x hx
          simpa using (intervalIntegral.integral_const_mul (r := (exp (a ^ 3))⁻¹)
            (f := fun y : ℝ => exp (x ^ 3 + y ^ 3)) (a := (0 : ℝ)) (b := a - x)).symm
    _ = a ^ 4 * (∫ x in (0)..a, ∫ y in (0)..(a - x),
          exp (x ^ 3 + y ^ 3 - a ^ 3)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro x hx
          apply intervalIntegral.integral_congr
          intro y hy
          calc
            (exp (a ^ 3))⁻¹ * exp (x ^ 3 + y ^ 3)
                = exp (-a ^ 3) * exp (x ^ 3 + y ^ 3) := by rw [exp_neg]
            _ = exp (x ^ 3 + y ^ 3 - a ^ 3) := by
                rw [← exp_add]
                congr 1
                ring

/--
Let $T$ be the triangle with vertices $(0, 0)$, $(a, 0)$, and $(0, a)$. Find $\lim_{a \to \infty} a^4 \exp(-a^3) \int_T \exp(x^3+y^3) \, dx \, dy$.
-/
theorem putnam_1983_a6
(F : ℝ → ℝ)
(hF : F = fun a ↦ (a ^ 4 / exp (a ^ 3)) * ∫ x in (0)..a, ∫ y in (0)..(a - x), exp (x ^ 3 + y ^ 3))
: (Tendsto F atTop (𝓝 putnam_1983_a6_solution)) :=
by
  subst F
  have hlow_lim :
      Tendsto (fun a : ℝ => xTerm 3 a + yTerm 3 a - constTerm 1 a)
        atTop (𝓝 (2 / 9)) := by
    have hx := xTerm_tendsto' 3 (by norm_num : (0 : ℝ) < 3)
    have hy := yTerm_tendsto' 3 (by norm_num : (0 : ℝ) < 3)
    have hc := constTerm_tendsto 1 (by norm_num : (0 : ℝ) < 1)
    convert (hx.add hy).sub hc using 1 <;> norm_num
  have hscaled : Tendsto scaledTri atTop (𝓝 (2 / 9)) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb
      filter_upwards [(tendsto_order.1 hlow_lim).1 b hb, lower_bound_eventually] with a hb_low hle
      exact lt_of_lt_of_le hb_low hle
    · intro b hb
      rcases exists_rate_for_upper hb with ⟨c, hc0, hc3, hcb⟩
      let δ : ℝ := (3 - c) / 6
      let d : ℝ := 1 - (1 - δ) ^ 2
      have hδ0 : 0 ≤ δ := by dsimp [δ]; nlinarith
      have hδpos : 0 < δ := by dsimp [δ]; nlinarith
      have hδ1 : δ ≤ 1 := by dsimp [δ]; nlinarith
      have hδc : δ ≤ (3 - c) / 3 := by dsimp [δ]; nlinarith
      have hdpos : 0 < d := by
        dsimp [d]
        nlinarith [sq_nonneg (δ - 1), mul_pos hδpos (by nlinarith : 0 < 2 - δ)]
      have hupper_lim :
          Tendsto (fun a : ℝ => xTerm c a + yTerm c a + constTerm d a)
            atTop (𝓝 (2 / c ^ 2)) := by
        have hx := xTerm_tendsto' c hc0
        have hy := yTerm_tendsto' c hc0
        have hdlim := constTerm_tendsto d hdpos
        convert (hx.add hy).add hdlim using 1 <;> field_simp [hc0.ne'] <;> ring
      filter_upwards [(tendsto_order.1 hupper_lim).2 b hcb,
        upper_bound_eventually (c := c) (δ := δ) (d := d) hδ0 hδ1 hδc rfl] with a hb_up hle
      exact lt_of_le_of_lt hle hb_up
  refine Tendsto.congr' ?_ hscaled
  exact Eventually.of_forall fun a => (original_eq_scaled a).symm
