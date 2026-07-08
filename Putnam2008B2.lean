import Mathlib

open Filter Topology Set Nat MeasureTheory

abbrev putnam_2008_b2_solution : ℝ := -1

private lemma putnam_2008_b2_aux_integral (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ∫ t in (0)..x, t ^ n / (n)! * (Real.log t - (harmonic n : ℝ)) =
      x ^ (n + 1) / (n + 1)! * (Real.log x - (harmonic (n + 1) : ℝ)) := by
  let A : ℝ → ℝ :=
    fun t => t ^ (n + 1) / ((↑(n + 1) : ℝ) * (n)! ) *
      (Real.log t - (harmonic n : ℝ) - (↑(n + 1) : ℝ)⁻¹)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) x,
      HasDerivAt A (t ^ n / (n)! * (Real.log t - (harmonic n : ℝ))) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have hlog :
        HasDerivAt
          (fun u : ℝ => Real.log u - (harmonic n : ℝ) - (↑(n + 1) : ℝ)⁻¹)
          t⁻¹ t := by
      simpa using ((Real.hasDerivAt_log ht0).sub_const (harmonic n : ℝ)).sub_const
        ((↑(n + 1) : ℝ)⁻¹)
    have hpow : HasDerivAt (fun u : ℝ => u ^ (n + 1))
        ((↑(n + 1) : ℝ) * t ^ n) t := by
      simpa using (hasDerivAt_pow (n + 1) t : HasDerivAt
        (fun u : ℝ => u ^ (n + 1)) ((↑(n + 1) : ℝ) * t ^ ((n + 1) - 1)) t)
    have h :=
      (hpow.div_const ((↑(n + 1) : ℝ) * (n)!)).mul hlog
    convert h using 1
    field_simp [Nat.cast_ne_zero.mpr (factorial_ne_zero n),
      Nat.cast_ne_zero.mpr (succ_ne_zero n), ht0]
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ => t ^ n / (n)! * (Real.log t - (harmonic n : ℝ))) volume 0 x := by
    have hlogint : IntervalIntegrable
        (fun t : ℝ => Real.log t - (harmonic n : ℝ)) volume 0 x :=
      (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := x)).sub
        intervalIntegral.intervalIntegrable_const
    exact hlogint.continuousOn_mul
      ((continuousOn_id.pow n).div_const ((n)! : ℝ))
  have hlim0 : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hpowlog :
        Tendsto (fun t : ℝ => Real.log t * t ^ (((n + 1 : ℕ) : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_log_mul_rpow_nhdsGT_zero (by exact_mod_cast Nat.succ_pos n)
    have hnatpow0 :
        Tendsto (fun t : ℝ => t ^ (n + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ((tendsto_nhdsWithin_of_tendsto_nhds
        (continuousAt_id : ContinuousAt (fun t : ℝ => t) 0)).pow (n + 1))
    have hmain :
        Tendsto
          (fun t : ℝ => t ^ (n + 1) *
            (Real.log t - (harmonic n : ℝ) - (↑(n + 1) : ℝ)⁻¹))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 :
          Tendsto (fun t : ℝ => t ^ (n + 1) * Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hpowlog_nat :
            Tendsto (fun t : ℝ => Real.log t * t ^ (n + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          exact hpowlog.congr' (Eventually.of_forall fun t => by
            congr 1
            rw [Real.rpow_natCast])
        simpa [mul_comm] using hpowlog_nat
      have h2 :
          Tendsto (fun t : ℝ => t ^ (n + 1) *
            ((harmonic n : ℝ) + (↑(n + 1) : ℝ)⁻¹))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hnatpow0.mul tendsto_const_nhds
      have hsub : Tendsto
          (fun t : ℝ => t ^ (n + 1) * Real.log t -
            t ^ (n + 1) * ((harmonic n : ℝ) + (↑(n + 1) : ℝ)⁻¹))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using h1.sub h2
      exact hsub.congr' (Eventually.of_forall fun t => by ring_nf)
    have hcmul : Tendsto
        (fun t : ℝ => (((↑(n + 1) : ℝ) * (n)! )⁻¹) *
          (t ^ (n + 1) *
            (Real.log t - (harmonic n : ℝ) - (↑(n + 1) : ℝ)⁻¹)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hmain.const_mul (((↑(n + 1) : ℝ) * (n)! )⁻¹)
    exact hcmul.congr' (Eventually.of_forall fun t => by
      dsimp [A]
      ring_nf)
  have hlimx : Tendsto A (𝓝[<] x) (𝓝 (A x)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    ·
      have hx0 : x ≠ 0 := ne_of_gt hx
      dsimp [A]
      exact (((continuousAt_id.pow (n + 1)).div_const _).mul
        (((Real.continuousAt_log hx0).sub continuousAt_const).sub continuousAt_const))
  calc
    ∫ t in (0)..x, t ^ n / (n)! * (Real.log t - (harmonic n : ℝ))
        = A x - 0 := by
          simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx hderiv hint
            hlim0 hlimx
    _ = x ^ (n + 1) / (n + 1)! * (Real.log x - (harmonic (n + 1) : ℝ)) := by
      rw [show ((n + 1)! : ℝ) = (↑(n + 1) : ℝ) * (n)! by
        norm_num [factorial_succ]]
      dsimp [A]
      have hpar :
          Real.log x - (harmonic n : ℝ) - (↑(n + 1) : ℝ)⁻¹ =
            Real.log x - (harmonic (n + 1) : ℝ) := by
        simp [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
        ring
      rw [hpar]
      simp

private lemma putnam_2008_b2_closed_form
    (F : ℕ → ℝ → ℝ)
    (hF0 : ∀ x : ℝ, F 0 x = Real.log x)
    (hFn : ∀ n : ℕ, ∀ x > 0, F (n + 1) x = ∫ t in Set.Ioo 0 x, F n t) :
    ∀ n : ℕ, ∀ x > 0,
      F n x = x ^ n / (n)! * (Real.log x - (harmonic n : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp [hF0 x]
  | succ n ih =>
      intro x hx
      rw [hFn n x hx]
      calc
        ∫ t in Set.Ioo 0 x, F n t
            = ∫ t in Set.Ioo 0 x, t ^ n / (n)! * (Real.log t - (harmonic n : ℝ)) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
                (fun t ht => ih t ht.1)
        _ = ∫ t in (0)..x, t ^ n / (n)! * (Real.log t - (harmonic n : ℝ)) := by
              rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
                ← intervalIntegral.integral_of_le hx.le]
        _ = x ^ (n + 1) / (n + 1)! * (Real.log x - (harmonic (n + 1) : ℝ)) :=
              putnam_2008_b2_aux_integral n x hx

private lemma putnam_2008_b2_harmonic_div_log :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hdiff :
      Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.log n) atTop (𝓝 0) :=
    Real.tendsto_harmonic_sub_log.div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hcongr : (fun n : ℕ => (harmonic n : ℝ) / Real.log n) =ᶠ[atTop]
      fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.log n + 1 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp [hlog]
    ring
  have hsum : Tendsto
      (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.log n + 1) atTop (𝓝 1) := by
    simpa using
      (hdiff.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  exact hsum.congr' hcongr.symm

/--
Let $F_0(x)=\ln x$. For $n \geq 0$ and $x>0$, let $F_{n+1}(x)=\int_0^x F_n(t)\,dt$. Evaluate $\lim_{n \to \infty} \frac{n!F_n(1)}{\ln n}$.
-/
theorem putnam_2008_b2
(F : ℕ → ℝ → ℝ)
(hF0 : ∀ x : ℝ, F 0 x = Real.log x)
(hFn : ∀ n : ℕ, ∀ x > 0, F (n + 1) x = ∫ t in Set.Ioo 0 x, F n t)
: Tendsto (fun n : ℕ => ((n)! * F n 1) / Real.log n) atTop (𝓝 putnam_2008_b2_solution) :=
by
  have hclosed := putnam_2008_b2_closed_form F hF0 hFn
  have hseq : (fun n : ℕ => ((n)! * F n 1) / Real.log n) =ᶠ[atTop]
      fun n : ℕ => -((harmonic n : ℝ) / Real.log n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hfac : ((n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero n)
    rw [hclosed n 1 zero_lt_one]
    field_simp [hfac]
    rw [Real.log_one]
    ring_nf
  exact (putnam_2008_b2_harmonic_div_log.neg).congr' hseq.symm
