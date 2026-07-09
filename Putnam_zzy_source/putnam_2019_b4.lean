import Mathlib

open Topology Filter Set Matrix

noncomputable abbrev putnam_2019_b4_solution : ℝ := (Real.log ((2 : ℝ) ^ 4) - 1) / 2

private noncomputable def putnam_2019_b4_pairToVec : ℝ × ℝ →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin 2 =>
    if i = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ else ContinuousLinearMap.snd ℝ ℝ ℝ

private lemma putnam_2019_b4_pairToVec_zero (x y : ℝ) :
    putnam_2019_b4_pairToVec (x, y) 0 = x := by
  simp [putnam_2019_b4_pairToVec]

private lemma putnam_2019_b4_pairToVec_one (x y : ℝ) :
    putnam_2019_b4_pairToVec (x, y) 1 = y := by
  simp [putnam_2019_b4_pairToVec]

private lemma putnam_2019_b4_log_rhs_deriv_x {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    deriv (fun z : ℝ => z * y * Real.log (z * y)) x =
      y * (Real.log (x * y) + 1) := by
  have hxy : x * y ≠ 0 := by positivity
  have hlin : HasDerivAt (fun z : ℝ => z * y) y x := by
    simpa using (hasDerivAt_id x).mul_const y
  have hlog : HasDerivAt (fun z : ℝ => Real.log (z * y)) ((x * y)⁻¹ * y) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_log hxy).comp x hlin
  have hprod :
      HasDerivAt (fun z : ℝ => (z * y) * Real.log (z * y))
        (y * Real.log (x * y) + (x * y) * ((x * y)⁻¹ * y)) x :=
    hlin.mul hlog
  rw [hprod.deriv]
  field_simp [hxy]

private lemma putnam_2019_b4_log_rhs_deriv_y {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    deriv (fun z : ℝ => x * z * Real.log (x * z)) y =
      x * (Real.log (x * y) + 1) := by
  have hxy : x * y ≠ 0 := by positivity
  have hlin : HasDerivAt (fun z : ℝ => x * z) x y := by
    simpa using (hasDerivAt_id y).const_mul x
  have hlog : HasDerivAt (fun z : ℝ => Real.log (x * z)) ((x * y)⁻¹ * x) y := by
    simpa [Function.comp_def] using (Real.hasDerivAt_log hxy).comp y hlin
  have hprod :
      HasDerivAt (fun z : ℝ => (x * z) * Real.log (x * z))
        (x * Real.log (x * y) + (x * y) * ((x * y)⁻¹ * x)) y :=
    hlin.mul hlog
  rw [hprod.deriv]
  field_simp [hxy]

private lemma putnam_2019_b4_partial_x_eq_fderiv
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (x y : ℝ) :
    deriv (fun xx : ℝ => F (xx, y)) x = fderiv ℝ F (x, y) (1, 0) := by
  rw [← fderiv_apply_one_eq_deriv]
  change (fderiv ℝ (F ∘ fun xx : ℝ => (xx, y)) x) 1 = _
  rw [fderiv_comp]
  · change (fderiv ℝ F (x, y)) ((fderiv ℝ (fun xx : ℝ => (xx, y)) x) 1) = _
    rw [fderiv_apply_one_eq_deriv]
    have hpair : deriv (fun xx : ℝ => (xx, y)) x = (1, 0) :=
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)).deriv
    rw [hpair]
  · exact (hF.differentiable (by norm_num)).differentiableAt
  · fun_prop

private lemma putnam_2019_b4_partial_y_eq_fderiv
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (x y : ℝ) :
    deriv (fun yy : ℝ => F (x, yy)) y = fderiv ℝ F (x, y) (0, 1) := by
  rw [← fderiv_apply_one_eq_deriv]
  change (fderiv ℝ (F ∘ fun yy : ℝ => (x, yy)) y) 1 = _
  rw [fderiv_comp]
  · change (fderiv ℝ F (x, y)) ((fderiv ℝ (fun yy : ℝ => (x, yy)) y) 1) = _
    rw [fderiv_apply_one_eq_deriv]
    have hpair : deriv (fun yy : ℝ => (x, yy)) y = (0, 1) :=
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)).deriv
    rw [hpair]
  · exact (hF.differentiable (by norm_num)).differentiableAt
  · fun_prop

private lemma putnam_2019_b4_deriv_fderiv_y_along_x
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (x y : ℝ) :
    deriv (fun xx : ℝ => fderiv ℝ F (xx, y) (0, 1)) x =
      ((fderiv ℝ (fderiv ℝ F) (x, y)) (1, 0)) (0, 1) := by
  rw [← fderiv_apply_one_eq_deriv]
  change
    (fderiv ℝ ((fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1)) ∘
      fun xx : ℝ => (xx, y)) x) 1 = _
  rw [fderiv_comp]
  · change
      (fderiv ℝ (fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1)) (x, y))
        ((fderiv ℝ (fun xx : ℝ => (xx, y)) x) 1) = _
    rw [fderiv_apply_one_eq_deriv]
    have hpair : deriv (fun xx : ℝ => (xx, y)) x = (1, 0) :=
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)).deriv
    rw [hpair]
    rw [fderiv_clm_apply]
    · simp
    · exact
        (hF.contDiffAt.fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
          (by norm_num)
    · fun_prop
  · fun_prop
  · fun_prop

private lemma putnam_2019_b4_deriv_fderiv_x_along_y
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (x y : ℝ) :
    deriv (fun yy : ℝ => fderiv ℝ F (x, yy) (1, 0)) y =
      ((fderiv ℝ (fderiv ℝ F) (x, y)) (0, 1)) (1, 0) := by
  rw [← fderiv_apply_one_eq_deriv]
  change
    (fderiv ℝ ((fun p : ℝ × ℝ => (fderiv ℝ F p) (1, 0)) ∘
      fun yy : ℝ => (x, yy)) y) 1 = _
  rw [fderiv_comp]
  · change
      (fderiv ℝ (fun p : ℝ × ℝ => (fderiv ℝ F p) (1, 0)) (x, y))
        ((fderiv ℝ (fun yy : ℝ => (x, yy)) y) 1) = _
    rw [fderiv_apply_one_eq_deriv]
    have hpair : deriv (fun yy : ℝ => (x, yy)) y = (0, 1) :=
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)).deriv
    rw [hpair]
    rw [fderiv_clm_apply]
    · simp
    · exact
        (hF.contDiffAt.fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
          (by norm_num)
    · fun_prop
  · fun_prop
  · fun_prop

private lemma putnam_2019_b4_mixed_comm
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (x y : ℝ) :
    deriv (fun xx : ℝ => deriv (fun yy : ℝ => F (xx, yy)) y) x =
      deriv (fun yy : ℝ => deriv (fun xx : ℝ => F (xx, yy)) x) y := by
  have hyfun :
      (fun xx : ℝ => deriv (fun yy : ℝ => F (xx, yy)) y) =
        fun xx : ℝ => fderiv ℝ F (xx, y) (0, 1) := by
    funext xx
    exact putnam_2019_b4_partial_y_eq_fderiv F hF xx y
  have hxfun :
      (fun yy : ℝ => deriv (fun xx : ℝ => F (xx, yy)) x) =
        fun yy : ℝ => fderiv ℝ F (x, yy) (1, 0) := by
    funext yy
    exact putnam_2019_b4_partial_x_eq_fderiv F hF x yy
  rw [hyfun, hxfun,
    putnam_2019_b4_deriv_fderiv_y_along_x F hF x y,
    putnam_2019_b4_deriv_fderiv_x_along_y F hF x y]
  exact
    (hF.contDiffAt.isSymmSndFDerivAt
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))).eq (1, 0) (0, 1)

private lemma putnam_2019_b4_mixed_formula
    (F : ℝ × ℝ → ℝ)
    (hF : ContDiff ℝ 2 F)
    (h1 : ∀ x ≥ 1, ∀ y ≥ 1,
      x * deriv (fun xx : ℝ => F (xx, y)) x +
        y * deriv (fun yy : ℝ => F (x, yy)) y =
          x * y * Real.log (x * y))
    (h2 : ∀ x ≥ 1, ∀ y ≥ 1,
      x ^ 2 * iteratedDeriv 2 (fun xx : ℝ => F (xx, y)) x +
        y ^ 2 * iteratedDeriv 2 (fun yy : ℝ => F (x, yy)) y =
          x * y)
    {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    deriv (fun xx : ℝ => deriv (fun yy : ℝ => F (xx, yy)) y) x =
      (Real.log (x * y) + 1) / 2 := by
  let A : ℝ := deriv (fun xx : ℝ => F (xx, y)) x
  let B : ℝ := deriv (fun yy : ℝ => F (x, yy)) y
  let Fxx : ℝ := iteratedDeriv 2 (fun xx : ℝ => F (xx, y)) x
  let Fyy : ℝ := iteratedDeriv 2 (fun yy : ℝ => F (x, yy)) y
  let H : ℝ := deriv (fun xx : ℝ => deriv (fun yy : ℝ => F (xx, yy)) y) x
  let L : ℝ := Real.log (x * y)
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hxy_ne : x * y ≠ 0 := by positivity
  have hFx_diff :
      DifferentiableAt ℝ (fun z : ℝ => deriv (fun xx : ℝ => F (xx, y)) z) x := by
    exact
      ((hF.comp (by fun_prop : ContDiff ℝ 2 (fun z : ℝ => (z, y)))).differentiable_deriv_two).differentiableAt
  have hFy_eq :
      (fun z : ℝ => deriv (fun yy : ℝ => F (z, yy)) y) =
        fun z : ℝ => fderiv ℝ F (z, y) (0, 1) := by
    funext z
    exact putnam_2019_b4_partial_y_eq_fderiv F hF z y
  have hFy_diff :
      DifferentiableAt ℝ (fun z : ℝ => deriv (fun yy : ℝ => F (z, yy)) y) x := by
    rw [hFy_eq]
    fun_prop
  have hderiv_lhs_x :
      deriv
        (fun z : ℝ =>
          z * deriv (fun xx : ℝ => F (xx, y)) z +
            y * deriv (fun yy : ℝ => F (z, yy)) y) x =
        A + x * Fxx + y * H := by
    change
      deriv
        ((fun z : ℝ => z * deriv (fun xx : ℝ => F (xx, y)) z) +
          fun z : ℝ => y * deriv (fun yy : ℝ => F (z, yy)) y) x = _
    rw [deriv_add]
    · have hA :
          deriv (fun z : ℝ => z * deriv (fun xx : ℝ => F (xx, y)) z) x =
            1 * deriv (fun xx : ℝ => F (xx, y)) x +
              x * deriv (fun z : ℝ => deriv (fun xx : ℝ => F (xx, y)) z) x := by
        simpa using
          (deriv_fun_mul (𝕜 := ℝ) (x := x) (c := fun z : ℝ => z)
            (d := fun z : ℝ => deriv (fun xx : ℝ => F (xx, y)) z)
            differentiableAt_id hFx_diff)
      have hB :
          deriv (fun z : ℝ => y * deriv (fun yy : ℝ => F (z, yy)) y) x =
            y * deriv (fun z : ℝ => deriv (fun yy : ℝ => F (z, yy)) y) x := by
        simpa using
          (deriv_const_mul (𝕜 := ℝ) (x := x)
            (d := fun z : ℝ => deriv (fun yy : ℝ => F (z, yy)) y) y hFy_diff)
      have hFxx :
          deriv (fun z : ℝ => deriv (fun xx : ℝ => F (xx, y)) z) x = Fxx := by
        dsimp [Fxx]
        rw [iteratedDeriv_eq_iterate]
        rfl
      rw [hA, hB, hFxx]
      ring
    · exact differentiableAt_id.mul hFx_diff
    · exact (by fun_prop : DifferentiableAt ℝ
        (fun z : ℝ => y * deriv (fun yy : ℝ => F (z, yy)) y) x)
  have hloc_x :
      (fun z : ℝ =>
        z * deriv (fun xx : ℝ => F (xx, y)) z +
          y * deriv (fun yy : ℝ => F (z, yy)) y) =ᶠ[𝓝 x]
        fun z : ℝ => z * y * Real.log (z * y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
    exact h1 z (le_of_lt hz) y (le_of_lt hy)
  have hx_eq :
      A + x * Fxx + y * H = y * (L + 1) := by
    have hderiv := hloc_x.deriv_eq
    rw [hderiv_lhs_x, putnam_2019_b4_log_rhs_deriv_x hx0 hy0] at hderiv
    simpa [A, Fxx, H, L] using hderiv
  have hFy_diff_y :
      DifferentiableAt ℝ (fun z : ℝ => deriv (fun yy : ℝ => F (x, yy)) z) y := by
    exact
      ((hF.comp (by fun_prop : ContDiff ℝ 2 (fun z : ℝ => (x, z)))).differentiable_deriv_two).differentiableAt
  have hFx_eq_y :
      (fun z : ℝ => deriv (fun xx : ℝ => F (xx, z)) x) =
        fun z : ℝ => fderiv ℝ F (x, z) (1, 0) := by
    funext z
    exact putnam_2019_b4_partial_x_eq_fderiv F hF x z
  have hFx_diff_y :
      DifferentiableAt ℝ (fun z : ℝ => deriv (fun xx : ℝ => F (xx, z)) x) y := by
    rw [hFx_eq_y]
    fun_prop
  have hcomm :
      deriv (fun z : ℝ => deriv (fun xx : ℝ => F (xx, z)) x) y = H := by
    dsimp [H]
    exact (putnam_2019_b4_mixed_comm F hF x y).symm
  have hderiv_lhs_y :
      deriv
        (fun z : ℝ =>
          x * deriv (fun xx : ℝ => F (xx, z)) x +
            z * deriv (fun yy : ℝ => F (x, yy)) z) y =
        x * H + B + y * Fyy := by
    change
      deriv
        ((fun z : ℝ => x * deriv (fun xx : ℝ => F (xx, z)) x) +
          fun z : ℝ => z * deriv (fun yy : ℝ => F (x, yy)) z) y = _
    rw [deriv_add]
    · have hA :
          deriv (fun z : ℝ => x * deriv (fun xx : ℝ => F (xx, z)) x) y =
            x * deriv (fun z : ℝ => deriv (fun xx : ℝ => F (xx, z)) x) y := by
        simpa using
          (deriv_const_mul (𝕜 := ℝ) (x := y)
            (d := fun z : ℝ => deriv (fun xx : ℝ => F (xx, z)) x) x hFx_diff_y)
      have hB :
          deriv (fun z : ℝ => z * deriv (fun yy : ℝ => F (x, yy)) z) y =
            1 * deriv (fun yy : ℝ => F (x, yy)) y +
              y * deriv (fun z : ℝ => deriv (fun yy : ℝ => F (x, yy)) z) y := by
        simpa using
          (deriv_fun_mul (𝕜 := ℝ) (x := y) (c := fun z : ℝ => z)
            (d := fun z : ℝ => deriv (fun yy : ℝ => F (x, yy)) z)
            differentiableAt_id hFy_diff_y)
      have hFyy :
          deriv (fun z : ℝ => deriv (fun yy : ℝ => F (x, yy)) z) y = Fyy := by
        dsimp [Fyy]
        rw [iteratedDeriv_eq_iterate]
        rfl
      rw [hA, hB, hcomm, hFyy]
      ring
    · exact (by fun_prop : DifferentiableAt ℝ
        (fun z : ℝ => x * deriv (fun xx : ℝ => F (xx, z)) x) y)
    · exact differentiableAt_id.mul hFy_diff_y
  have hloc_y :
      (fun z : ℝ =>
        x * deriv (fun xx : ℝ => F (xx, z)) x +
          z * deriv (fun yy : ℝ => F (x, yy)) z) =ᶠ[𝓝 y]
        fun z : ℝ => x * z * Real.log (x * z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact h1 x (le_of_lt hx) z (le_of_lt hz)
  have hy_eq :
      x * H + B + y * Fyy = x * (L + 1) := by
    have hderiv := hloc_y.deriv_eq
    rw [hderiv_lhs_y, putnam_2019_b4_log_rhs_deriv_y hx0 hy0] at hderiv
    simpa [B, Fyy, H, L] using hderiv
  have hfirst : x * A + y * B = x * y * L := by
    simpa [A, B, L] using h1 x (le_of_lt hx) y (le_of_lt hy)
  have hsecond : x ^ 2 * Fxx + y ^ 2 * Fyy = x * y := by
    simpa [Fxx, Fyy] using h2 x (le_of_lt hx) y (le_of_lt hy)
  have hresult : H = (L + 1) / 2 := by
    have hx_eq' : x * (A + x * Fxx + y * H) = x * (y * (L + 1)) := by
      rw [hx_eq]
    have hy_eq' : y * (x * H + B + y * Fyy) = y * (x * (L + 1)) := by
      rw [hy_eq]
    have hxyeq : x * y * (2 * H) = x * y * (L + 1) := by
      nlinarith [hfirst, hsecond, hx_eq', hy_eq']
    have hcancel : 2 * H = L + 1 := by
      apply mul_left_cancel₀ hxy_ne
      simpa [mul_assoc] using hxyeq
    linarith
  simpa [H, L] using hresult

private lemma putnam_2019_b4_log_inner_integral {s y : ℝ}
    (hs : 1 ≤ s) (hy : 0 < y) :
    (∫ x in s..s + 1, (Real.log (x * y) + 1) / 2) =
      (((s + 1) * Real.log (s + 1) - s * Real.log s) + Real.log y) / 2 := by
  have hsle : s ≤ s + 1 := by linarith
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hcongr :
      (∫ x in s..s + 1, (Real.log (x * y) + 1) / 2) =
        ∫ x in s..s + 1, (Real.log x + Real.log y + 1) / 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have hxI : x ∈ Ioc s (s + 1) := by
      simpa [Set.uIoc_of_le hsle] using hx
    have hxpos : 0 < x := lt_trans hspos hxI.1
    rw [Real.log_mul hxpos.ne' hy.ne']
  rw [hcongr]
  have hlog :
      (∫ x in s..s + 1, Real.log x) =
        (s + 1) * Real.log (s + 1) - s * Real.log s - (s + 1) + s := by
    simpa using (Real.integral_log (a := s) (b := s + 1))
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_add]
    · rw [hlog]
      simp [intervalIntegral.integral_const]
      ring
    · exact intervalIntegral.intervalIntegrable_log'
    · exact intervalIntegrable_const
  · exact intervalIntegral.intervalIntegrable_log'.add intervalIntegrable_const
  · exact intervalIntegrable_const

private lemma putnam_2019_b4_log_double_integral {s : ℝ} (hs : 1 ≤ s) :
    (∫ y in s..s + 1, ∫ x in s..s + 1, (Real.log (x * y) + 1) / 2) =
      (s + 1) * Real.log (s + 1) - s * Real.log s - 1 / 2 := by
  have hsle : s ≤ s + 1 := by linarith
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  let A : ℝ := (s + 1) * Real.log (s + 1) - s * Real.log s
  have hcongr :
      (∫ y in s..s + 1, ∫ x in s..s + 1, (Real.log (x * y) + 1) / 2) =
        ∫ y in s..s + 1, (A + Real.log y) / 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y hy
    have hyI : y ∈ Ioc s (s + 1) := by
      simpa [Set.uIoc_of_le hsle] using hy
    have hypos : 0 < y := lt_trans hspos hyI.1
    simpa [A] using putnam_2019_b4_log_inner_integral (s := s) (y := y) hs hypos
  rw [hcongr]
  have hlog :
      (∫ y in s..s + 1, Real.log y) =
        (s + 1) * Real.log (s + 1) - s * Real.log s - (s + 1) + s := by
    simpa using (Real.integral_log (a := s) (b := s + 1))
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add]
  · rw [hlog]
    simp [A, intervalIntegral.integral_const]
    ring
  · exact intervalIntegrable_const
  · exact intervalIntegral.intervalIntegrable_log'

private lemma putnam_2019_b4_aux_contDiff_y_deriv
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (y : ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => deriv (fun yy : ℝ => F (x, yy)) y) := by
  have hEq :
      (fun x : ℝ => deriv (fun yy : ℝ => F (x, yy)) y) =
        fun x : ℝ => fderiv ℝ F (x, y) (0, 1) := by
    funext x
    exact putnam_2019_b4_partial_y_eq_fderiv F hF x y
  rw [hEq]
  fun_prop

private lemma putnam_2019_b4_rect_increment
    (F : ℝ × ℝ → ℝ)
    (hF : ContDiff ℝ 2 F)
    (hmix : ∀ {x y : ℝ}, 1 < x → 1 < y →
      deriv (fun xx : ℝ => deriv (fun yy : ℝ => F (xx, yy)) y) x =
        (Real.log (x * y) + 1) / 2)
    {s : ℝ} (hs : 1 ≤ s) :
    F (s + 1, s + 1) - F (s + 1, s) - F (s, s + 1) + F (s, s) =
      (s + 1) * Real.log (s + 1) - s * Real.log s - 1 / 2 := by
  have hsle : s ≤ s + 1 := by linarith
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  let G : ℝ → ℝ := fun y => F (s + 1, y) - F (s, y)
  have hGcd : ContDiff ℝ 2 G := by
    dsimp [G]
    exact
      (hF.comp (by fun_prop : ContDiff ℝ 2 (fun y : ℝ => (s + 1, y)))).sub
        (hF.comp (by fun_prop : ContDiff ℝ 2 (fun y : ℝ => (s, y))))
  have hFTC_y :
      (∫ y in s..s + 1, deriv G y) = G (s + 1) - G s := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun y _ => (hGcd.differentiable (by norm_num)).differentiableAt)
      ((hGcd.continuous_deriv (by norm_num)).intervalIntegrable _ _)
  have hinner (y : ℝ) (hyI : y ∈ Ioc s (s + 1)) :
      deriv G y = ∫ x in s..s + 1, (Real.log (x * y) + 1) / 2 := by
    have hypos : 0 < y := lt_trans hspos hyI.1
    have hy1 : 1 < y := lt_of_le_of_lt hs hyI.1
    let P : ℝ → ℝ := fun x => deriv (fun yy : ℝ => F (x, yy)) y
    have hPcd : ContDiff ℝ 1 P := by
      dsimp [P]
      exact putnam_2019_b4_aux_contDiff_y_deriv F hF y
    have hFTC_x :
        (∫ x in s..s + 1, deriv P x) = P (s + 1) - P s := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsle
        (hPcd.continuous.continuousOn) ?_
        ((hPcd.continuous_deriv (by norm_num)).intervalIntegrable _ _)
      intro x hx
      exact ((hPcd.differentiable (by norm_num)).differentiableAt).hasDerivAt
    have hactual_to_formula :
        (∫ x in s..s + 1, deriv P x) =
          ∫ x in s..s + 1, (Real.log (x * y) + 1) / 2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      have hxI : x ∈ Ioc s (s + 1) := by
        simpa [Set.uIoc_of_le hsle] using hx
      have hx1 : 1 < x := lt_of_le_of_lt hs hxI.1
      dsimp [P]
      exact hmix hx1 hy1
    have hGderiv :
        deriv G y =
          deriv (fun yy : ℝ => F (s + 1, yy)) y -
            deriv (fun yy : ℝ => F (s, yy)) y := by
      dsimp [G]
      have h₁ : DifferentiableAt ℝ (fun yy : ℝ => F (s + 1, yy)) y := by
        have hcd : ContDiff ℝ 2 (fun yy : ℝ => F (s + 1, yy)) :=
          hF.comp (by fun_prop : ContDiff ℝ 2 (fun yy : ℝ => (s + 1, yy)))
        exact (hcd.differentiable (by norm_num)).differentiableAt
      have h₂ : DifferentiableAt ℝ (fun yy : ℝ => F (s, yy)) y := by
        have hcd : ContDiff ℝ 2 (fun yy : ℝ => F (s, yy)) :=
          hF.comp (by fun_prop : ContDiff ℝ 2 (fun yy : ℝ => (s, yy)))
        exact (hcd.differentiable (by norm_num)).differentiableAt
      simpa using (deriv_sub h₁ h₂)
    calc
      deriv G y =
          deriv (fun yy : ℝ => F (s + 1, yy)) y -
            deriv (fun yy : ℝ => F (s, yy)) y := hGderiv
      _ = ∫ x in s..s + 1, deriv P x := by
        dsimp [P] at hFTC_x
        exact hFTC_x.symm
      _ = ∫ x in s..s + 1, (Real.log (x * y) + 1) / 2 := hactual_to_formula
  have houter_congr :
      (∫ y in s..s + 1, deriv G y) =
        ∫ y in s..s + 1, ∫ x in s..s + 1, (Real.log (x * y) + 1) / 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y hy
    have hyI : y ∈ Ioc s (s + 1) := by
      simpa [Set.uIoc_of_le hsle] using hy
    exact hinner y hyI
  have hdelta :
      F (s + 1, s + 1) - F (s + 1, s) - F (s, s + 1) + F (s, s) =
        ∫ y in s..s + 1, deriv G y := by
    rw [hFTC_y]
    dsimp [G]
    ring
  rw [hdelta, houter_congr, putnam_2019_b4_log_double_integral hs]

private lemma putnam_2019_b4_phi_mono :
    MonotoneOn
      (fun s : ℝ => (s + 1) * Real.log (s + 1) - s * Real.log s) (Ici 1) := by
  let φ : ℝ → ℝ := fun s => (s + 1) * Real.log (s + 1) - s * Real.log s
  have hcont : ContinuousOn φ (Ici 1) := by
    dsimp [φ]
    exact
      ((Real.Continuous.mul_log (continuous_id.add continuous_const)).sub
        (Real.Continuous.mul_log continuous_id)).continuousOn
  change MonotoneOn φ (Ici 1)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Ici 1) (f := φ)
    (f' := fun x => Real.log (x + 1) - Real.log x) (convex_Ici 1) hcont ?_ ?_
  · intro x hx
    have hx1 : 1 < x := by
      simpa using hx
    have hx0 : x ≠ 0 := by positivity
    have hx10 : x + 1 ≠ 0 := by positivity
    have hshift :
        HasDerivAt (fun t : ℝ => (t + 1) * Real.log (t + 1))
          (Real.log (x + 1) + 1) x := by
      have hlin : HasDerivAt (fun t : ℝ => t + 1) 1 x := by
        simpa using (hasDerivAt_id x).add_const 1
      simpa using (Real.hasDerivAt_mul_log hx10).comp x hlin
    have hbase :
        HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x :=
      Real.hasDerivAt_mul_log hx0
    have hder :
        HasDerivAt φ (Real.log (x + 1) - Real.log x) x := by
      dsimp [φ]
      convert hshift.sub hbase using 1
      ring
    exact hder.hasDerivWithinAt
  · intro x hx
    have hx1 : 1 < x := by
      simpa using hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx1
    have hle : x ≤ x + 1 := by linarith
    have hlog := Real.log_le_log hxpos hle
    linarith

/--
Let $\mathcal{F}$ be the set of functions $f(x,y)$ that are twice continuously differentiable for $x \geq 1,y \geq 1$ and that satisfy the following two equations (where subscripts denote partial derivatives):
\begin{gather*}
xf_x+yf_y=xy\ln(xy), \\
x^2f_{xx}+y^2f_{yy}=xy.
\end{gather*}
For each $f \in \mathcal{F}$, let $m(f)=\min_{s \geq 1} (f(s+1,s+1)-f(s+1,s)-f(s,s+1)+f(s,s))$. Determine $m(f)$, and show that it is independent of the choice of $f$.
-/
theorem putnam_2019_b4
(f : (Fin 2 → ℝ) → ℝ)
(vec : ℝ → ℝ → (Fin 2 → ℝ))
(fdiff : ContDiff ℝ 2 f)
(hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y 1) = y)
(feq1 : ∀ x ≥ 1, ∀ y ≥ 1, x * deriv (fun x' : ℝ => f (vec x' y)) x + y * deriv (fun y' : ℝ => f (vec x y')) y = x * y * Real.log (x * y))
(feq2 : ∀ x ≥ 1, ∀ y ≥ 1, x ^ 2 * iteratedDeriv 2 (fun x' : ℝ => f (vec x' y)) x + y ^ 2 * iteratedDeriv 2 (fun y' : ℝ => f (vec x y')) y = x * y)
: sInf {f (vec (s + 1) (s + 1)) - f (vec (s + 1) s) - f (vec s (s + 1)) + f (vec s s) | s ≥ 1} = putnam_2019_b4_solution :=
by
  let F : ℝ × ℝ → ℝ := fun p => f (putnam_2019_b4_pairToVec p)
  have hvec_eq (x y : ℝ) : vec x y = putnam_2019_b4_pairToVec (x, y) := by
    funext i
    fin_cases i
    · simp [putnam_2019_b4_pairToVec, (hvec x y).1]
    · simp [putnam_2019_b4_pairToVec, (hvec x y).2]
  have hF_eq (x y : ℝ) : F (x, y) = f (vec x y) := by
    dsimp [F]
    rw [hvec_eq x y]
  have hF : ContDiff ℝ 2 F := by
    dsimp [F]
    exact fdiff.comp putnam_2019_b4_pairToVec.contDiff
  have h1F :
      ∀ x ≥ 1, ∀ y ≥ 1,
        x * deriv (fun xx : ℝ => F (xx, y)) x +
          y * deriv (fun yy : ℝ => F (x, yy)) y =
            x * y * Real.log (x * y) := by
    intro x hx y hy
    have hxfun : (fun xx : ℝ => F (xx, y)) = fun xx : ℝ => f (vec xx y) := by
      funext xx
      exact hF_eq xx y
    have hyfun : (fun yy : ℝ => F (x, yy)) = fun yy : ℝ => f (vec x yy) := by
      funext yy
      exact hF_eq x yy
    simpa [hxfun, hyfun] using feq1 x hx y hy
  have h2F :
      ∀ x ≥ 1, ∀ y ≥ 1,
        x ^ 2 * iteratedDeriv 2 (fun xx : ℝ => F (xx, y)) x +
          y ^ 2 * iteratedDeriv 2 (fun yy : ℝ => F (x, yy)) y =
            x * y := by
    intro x hx y hy
    have hxfun : (fun xx : ℝ => F (xx, y)) = fun xx : ℝ => f (vec xx y) := by
      funext xx
      exact hF_eq xx y
    have hyfun : (fun yy : ℝ => F (x, yy)) = fun yy : ℝ => f (vec x yy) := by
      funext yy
      exact hF_eq x yy
    simpa [hxfun, hyfun] using feq2 x hx y hy
  have hmix :
      ∀ {x y : ℝ}, 1 < x → 1 < y →
        deriv (fun xx : ℝ => deriv (fun yy : ℝ => F (xx, yy)) y) x =
          (Real.log (x * y) + 1) / 2 := by
    intro x y hx hy
    exact putnam_2019_b4_mixed_formula F hF h1F h2F hx hy
  have hrectF (s : ℝ) (hs : 1 ≤ s) :
      F (s + 1, s + 1) - F (s + 1, s) - F (s, s + 1) + F (s, s) =
        (s + 1) * Real.log (s + 1) - s * Real.log s - 1 / 2 :=
    putnam_2019_b4_rect_increment F hF hmix hs
  have hrect (s : ℝ) (hs : 1 ≤ s) :
      f (vec (s + 1) (s + 1)) - f (vec (s + 1) s) -
          f (vec s (s + 1)) + f (vec s s) =
        (s + 1) * Real.log (s + 1) - s * Real.log s - 1 / 2 := by
    rw [← hF_eq (s + 1) (s + 1), ← hF_eq (s + 1) s,
      ← hF_eq s (s + 1), ← hF_eq s s]
    exact hrectF s hs
  let φ : ℝ → ℝ := fun s => (s + 1) * Real.log (s + 1) - s * Real.log s
  have hphi_mono : MonotoneOn φ (Ici 1) := by
    simpa [φ] using putnam_2019_b4_phi_mono
  have hphi_ge (s : ℝ) (hs : 1 ≤ s) :
      2 * Real.log 2 ≤ φ s := by
    have hmono := hphi_mono (show (1 : ℝ) ∈ Ici 1 by simp) (show s ∈ Ici 1 by exact hs) hs
    have hφ1 : φ 1 = 2 * Real.log 2 := by
      simp [φ]
      ring_nf
    simpa [hφ1] using hmono
  have hsol :
      (Real.log ((2 : ℝ) ^ 4) - 1) / 2 = 2 * Real.log 2 - 1 / 2 := by
    rw [Real.log_pow]
    norm_num
    ring
  refine IsLeast.csInf_eq ?_
  constructor
  · refine ⟨1, le_rfl, ?_⟩
    rw [hrect 1 le_rfl, putnam_2019_b4_solution, hsol]
    norm_num
  · intro z hz
    rcases hz with ⟨s, hs, rfl⟩
    rw [hrect s hs, putnam_2019_b4_solution, hsol]
    have hge := hphi_ge s hs
    dsimp [φ] at hge
    linarith
