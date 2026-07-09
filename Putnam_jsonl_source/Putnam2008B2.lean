import Mathlib

open Filter Topology Set Nat

-- -1
/--
Let $F_0(x)=\ln x$. For $n \geq 0$ and $x>0$, let $F_{n+1}(x)=\int_0^x F_n(t)\,dt$. Evaluate $\lim_{n \to \infty} \frac{n!F_n(1)}{\ln n}$.
-/
theorem putnam_2008_b2
(F : ℕ → ℝ → ℝ)
(hF0 : ∀ x : ℝ, F 0 x = Real.log x)
(hFn : ∀ n : ℕ, ∀ x > 0, F (n + 1) x = ∫ t in Set.Ioo 0 x, F n t)
: Tendsto (fun n : ℕ => ((n)! * F n 1) / Real.log n) atTop (𝓝 ((-1) : ℝ )) := by
  let G : ℕ → ℝ → ℝ :=
    fun n x => x ^ n / (n)! * (Real.log x - (harmonic n : ℝ))
  have hG_deriv : ∀ n : ℕ, ∀ y > 0, HasDerivAt (G (n + 1)) (G n y) y := by
    intro n y hy
    have hpow :
        HasDerivAt (fun z : ℝ => z ^ (n + 1) / ((n + 1)! : ℝ))
          (((n + 1 : ℝ) * y ^ n) / ((n + 1)! : ℝ)) y := by
      simpa using ((hasDerivAt_id y).pow (n + 1)).div_const (((n + 1)! : ℝ))
    have hlog :
        HasDerivAt (fun z : ℝ => Real.log z - (harmonic (n + 1) : ℝ))
          (y⁻¹ - 0) y :=
      (Real.hasDerivAt_log hy.ne').sub (hasDerivAt_const y (harmonic (n + 1) : ℝ))
    convert hpow.mul hlog using 1
    simp only [G, harmonic_succ]
    push_cast
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp [hy.ne']
    ring
  have hG_integrable : ∀ n : ℕ, ∀ x : ℝ, IntervalIntegrable (G n) MeasureTheory.volume 0 x := by
    intro n x
    have hlogsub :
        IntervalIntegrable (fun t : ℝ => Real.log t - (harmonic n : ℝ))
          MeasureTheory.volume 0 x :=
      (intervalIntegral.intervalIntegrable_log' (a := 0) (b := x)).sub
        (intervalIntegral.intervalIntegrable_const (a := 0) (b := x) (c := (harmonic n : ℝ)))
    have hpoly : ContinuousOn (fun t : ℝ => t ^ n / ((n)! : ℝ)) (Set.uIcc 0 x) :=
      ((continuous_id.pow n).div_const ((n)! : ℝ)).continuousOn
    simpa [G] using hlogsub.continuousOn_mul hpoly
  have hG_zero : ∀ n : ℕ, Tendsto (G (n + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro n
    have hlogpow :
        Tendsto (fun z : ℝ => z ^ (n + 1) * Real.log z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h :=
        tendsto_log_mul_rpow_nhdsGT_zero (r := (n + 1 : ℝ)) (by positivity)
      refine Filter.Tendsto.congr' ?_ h
      filter_upwards [eventually_mem_nhdsWithin] with z hz
      rw [← Nat.cast_add_one (R := ℝ), Real.rpow_natCast]
      ring
    have hpow :
        Tendsto (fun z : ℝ => z ^ (n + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using
        tendsto_nhdsWithin_of_tendsto_nhds
          (((continuousAt_id : ContinuousAt (fun z : ℝ => z) 0).pow (n + 1)).tendsto)
    have hmain :
        Tendsto
          (fun z : ℝ =>
            (z ^ (n + 1) * Real.log z - z ^ (n + 1) * (harmonic (n + 1) : ℝ)) /
              ((n + 1)! : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hlogpow.sub (hpow.mul_const (harmonic (n + 1) : ℝ))).div_const ((n + 1)! : ℝ)
    refine Filter.Tendsto.congr' ?_ hmain
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    simp [G]
    ring
  have hG_integral :
      ∀ n : ℕ, ∀ x > 0, ∫ t in Set.Ioo 0 x, G n t = G (n + 1) x := by
    intro n x hx
    have hright :
        Tendsto (G (n + 1)) (𝓝[<] x) (𝓝 (G (n + 1) x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds ((hG_deriv n x hx).continuousAt.tendsto)
    have hftc :
        ∫ t in (0 : ℝ)..x, G n t = G (n + 1) x := by
      have h :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
          (a := (0 : ℝ)) (b := x) (f := G (n + 1)) (f' := G n)
          (fa := (0 : ℝ)) (fb := G (n + 1) x) hx
          (fun y hy => hG_deriv n y hy.1) (hG_integrable n x) (hG_zero n) hright
      simpa using h
    calc
      ∫ t in Set.Ioo 0 x, G n t = ∫ t in Set.Ioc 0 x, G n t := by
        rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = ∫ t in (0 : ℝ)..x, G n t := by
        rw [← intervalIntegral.integral_of_le hx.le]
      _ = G (n + 1) x := hftc
  have hF_eq_G : ∀ n : ℕ, ∀ x > 0, F n x = G n x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simp [G, hF0 x, harmonic_zero]
    | succ n ih =>
        intro x hx
        rw [hFn n x hx]
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ih t ht.1)]
        exact hG_integral n x hx
  have hF_one : ∀ n : ℕ, F n 1 = - (harmonic n : ℝ) / (n)! := by
    intro n
    rw [hF_eq_G n 1 zero_lt_one]
    simp [G, Real.log_one]
    ring
  have hseq_eq :
      (fun n : ℕ => ((n)! * F n 1) / Real.log n)
        =ᶠ[atTop] fun n : ℕ => - (harmonic n : ℝ) / Real.log n := by
    refine Eventually.of_forall ?_
    intro n
    have hfac : ((n)! : ℝ) ≠ 0 := by positivity
    have hnum : ((n)! : ℝ) * F n 1 = - (harmonic n : ℝ) := by
      rw [hF_one n]
      field_simp [hfac]
    change (((n)! : ℝ) * F n 1) / Real.log (n : ℝ) =
      - (harmonic n : ℝ) / Real.log (n : ℝ)
    rw [hnum]
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff_div :
      Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.log n)
        atTop (𝓝 0) :=
    Real.tendsto_harmonic_sub_log.div_atTop hlog_atTop
  have hratio :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
    have hsum :
        Tendsto (fun n : ℕ => 1 + ((harmonic n : ℝ) - Real.log n) / Real.log n)
          atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hdiff_div
    refine Filter.Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
    have hnreal : (1 : ℝ) < n := by exact_mod_cast (Nat.lt_of_succ_le hn)
    have hlogne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hnreal).ne'
    field_simp [hlogne]
    ring
  have hlim :
      Tendsto (fun n : ℕ => - (harmonic n : ℝ) / Real.log n) atTop (𝓝 (-1 : ℝ)) := by
    simpa [neg_div] using hratio.neg
  exact Filter.Tendsto.congr' hseq_eq.symm hlim
