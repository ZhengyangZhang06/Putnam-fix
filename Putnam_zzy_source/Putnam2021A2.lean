import Mathlib

open Filter Topology

noncomputable abbrev putnam_2021_a2_solution : ℝ := Real.exp 1

private lemma putnam_2021_a2_inner_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun r : ℝ => ((x + 1) ^ (r + 1) - x ^ (r + 1)) ^ (1 / r))
      (𝓝[>] 0)
      (𝓝 (Real.exp ((x + 1) * Real.log (x + 1) - x * Real.log x))) := by
  let A : ℝ := (x + 1) * Real.log (x + 1) - x * Real.log x
  let u : ℝ → ℝ := fun r => (x + 1) ^ (r + 1) - x ^ (r + 1)
  have hx1 : 0 < x + 1 := by linarith
  have hderiv₁ :
      HasDerivAt (fun r : ℝ => (x + 1) ^ (r + 1)) ((x + 1) * Real.log (x + 1)) 0 := by
    simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.const_rpow (a := x + 1) hx1
        ((hasDerivAt_id (0 : ℝ)).add_const (1 : ℝ)))
  have hderiv₂ : HasDerivAt (fun r : ℝ => x ^ (r + 1)) (x * Real.log x) 0 := by
    simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.const_rpow (a := x) hx ((hasDerivAt_id (0 : ℝ)).add_const (1 : ℝ)))
  have hderiv_u : HasDerivAt u A 0 := by
    simpa [u, A] using hderiv₁.sub hderiv₂
  have hu0 : u 0 = 1 := by
    simp [u, Real.rpow_one]
  have hderiv_log : HasDerivAt (fun r : ℝ => Real.log (u r)) A 0 := by
    simpa [hu0, A] using hderiv_u.log (by simp [hu0])
  have hloglim : Tendsto (fun r : ℝ => Real.log (u r) / r) (𝓝[>] 0) (𝓝 A) := by
    convert hderiv_log.tendsto_slope_zero_right using 1 with r
    simp [u, div_eq_mul_inv, mul_comm, sub_eq_add_neg]
  have hexplim :
      Tendsto (fun r : ℝ => Real.exp (Real.log (u r) / r)) (𝓝[>] 0) (𝓝 (Real.exp A)) := by
    exact (Real.continuous_exp.tendsto A).comp hloglim
  have hulim : Tendsto u (𝓝[>] 0) (𝓝 1) := by
    simpa [hu0] using hderiv_u.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hu_pos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < u r :=
    hulim.eventually (eventually_gt_nhds zero_lt_one)
  have heq : (fun r : ℝ => u r ^ (1 / r)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => Real.exp (Real.log (u r) / r)) := by
    filter_upwards [hu_pos] with r hur
    rw [Real.rpow_def_of_pos hur]
    congr 1
    ring
  simpa [u, A] using Tendsto.congr' heq.symm hexplim

private lemma putnam_2021_a2_exp_div_eq (x : ℝ) (hx : 0 < x) :
    Real.exp ((x + 1) * Real.log (x + 1) - x * Real.log x) / x =
      (1 + 1 / x) ^ (x + 1) := by
  let A : ℝ := (x + 1) * Real.log (x + 1) - x * Real.log x
  have hx1 : 0 < x + 1 := by linarith
  have hbase : 0 < 1 + 1 / x := by
    have h : 0 < 1 / x := one_div_pos.mpr hx
    linarith
  have hlogbase : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [one_add_div (a := (1 : ℝ)) hx.ne']
    exact Real.log_div hx1.ne' hx.ne'
  have hA : A - Real.log x = Real.log (1 + 1 / x) * (x + 1) := by
    rw [hlogbase]
    ring
  calc
    Real.exp ((x + 1) * Real.log (x + 1) - x * Real.log x) / x = Real.exp A / x := rfl
    _ = Real.exp A / Real.exp (Real.log x) := by rw [Real.exp_log hx]
    _ = Real.exp (A - Real.log x) := (Real.exp_sub A (Real.log x)).symm
    _ = (1 + 1 / x) ^ (x + 1) := by
      rw [Real.rpow_def_of_pos hbase, hA]

private lemma putnam_2021_a2_final_tendsto :
    Tendsto (fun x : ℝ => (1 + 1 / x) ^ (x + 1)) atTop (𝓝 (Real.exp 1)) := by
  have hbase : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop tendsto_id
    simpa using tendsto_const_nhds.add hdiv
  have hprod :
      Tendsto (fun x : ℝ => (1 + 1 / x) ^ x * (1 + 1 / x)) atTop (𝓝 (Real.exp 1)) := by
    simpa using (Real.tendsto_one_add_div_rpow_exp (1 : ℝ)).mul hbase
  have heq : (fun x : ℝ => (1 + 1 / x) ^ (x + 1)) =ᶠ[atTop]
      (fun x : ℝ => (1 + 1 / x) ^ x * (1 + 1 / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hbase_pos : 0 < 1 + 1 / x := by
      have h : 0 < 1 / x := one_div_pos.mpr hx
      linarith
    rw [Real.rpow_add hbase_pos, Real.rpow_one]
  exact Tendsto.congr' heq.symm hprod

/--
For every positive real number $x$, let $g(x)=\lim_{r \to 0}((x+1)^{r+1}-x^{r+1})^\frac{1}{r}$. Find $\lim_{x \to \infty}\frac{g(x)}{x}$.
-/
theorem putnam_2021_a2
(g : ℝ → ℝ)
(hg : ∀ x > 0, Tendsto (fun r : ℝ => ((x + 1) ^ (r + 1) - x ^ (r + 1)) ^ (1 / r)) (𝓝[>] 0) (𝓝 (g x)))
: Tendsto (fun x : ℝ => g x / x) atTop (𝓝 putnam_2021_a2_solution) :=
by
  have hg_formula : ∀ x > 0,
      g x = Real.exp ((x + 1) * Real.log (x + 1) - x * Real.log x) := by
    intro x hx
    exact tendsto_nhds_unique (hg x hx) (putnam_2021_a2_inner_tendsto x hx)
  have heq : (fun x : ℝ => (1 + 1 / x) ^ (x + 1)) =ᶠ[atTop] (fun x : ℝ => g x / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hg_formula x hx]
    exact (putnam_2021_a2_exp_div_eq x hx).symm
  exact Tendsto.congr' heq putnam_2021_a2_final_tendsto
