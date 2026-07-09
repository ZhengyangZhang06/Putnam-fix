import Mathlib

open Filter Topology

-- Real.exp 1
/--
For every positive real number $x$, let $g(x)=\lim_{r \to 0}((x+1)^{r+1}-x^{r+1})^\frac{1}{r}$. Find $\lim_{x \to \infty}\frac{g(x)}{x}$.
-/
theorem putnam_2021_a2
(g : ℝ → ℝ)
(hg : ∀ x > 0, Tendsto (fun r : ℝ => ((x + 1) ^ (r + 1) - x ^ (r + 1)) ^ (1 / r)) (𝓝[>] 0) (𝓝 (g x)))
: Tendsto (fun x : ℝ => g x / x) atTop (𝓝 ((Real.exp 1) : ℝ )) := by
  have hg_eval :
      ∀ x > 0, g x =
        Real.exp (Real.log (x + 1) * (x + 1) - Real.log x * x) := by
    intro x hx
    let H : ℝ → ℝ := fun r => (x + 1) ^ (r + 1) - x ^ (r + 1)
    let c : ℝ := Real.log (x + 1) * (x + 1) - Real.log x * x
    let F : ℝ → ℝ := fun r => r⁻¹ * (H r - 1)
    have hx1 : 0 < x + 1 := by linarith
    have hH0 : H 0 = 1 := by
      simp [H, Real.rpow_one]
    have hderiv1 :
        HasDerivAt (fun r : ℝ => (x + 1) ^ (r + 1))
          (Real.log (x + 1) * (x + 1)) 0 := by
      simpa [Real.rpow_one, mul_assoc] using
        (HasDerivAt.const_rpow hx1 ((hasDerivAt_id (0 : ℝ)).add_const 1))
    have hderiv2 :
        HasDerivAt (fun r : ℝ => x ^ (r + 1))
          (Real.log x * x) 0 := by
      simpa [Real.rpow_one, mul_assoc] using
        (HasDerivAt.const_rpow hx ((hasDerivAt_id (0 : ℝ)).add_const 1))
    have hderivH : HasDerivAt H c 0 := by
      simpa [H, c] using hderiv1.sub hderiv2
    have hF : Tendsto F (𝓝[>] 0) (𝓝 c) := by
      have hslope := hderivH.tendsto_slope_zero_right
      refine Tendsto.congr' ?_ hslope
      filter_upwards with r
      simp [F, H, hH0]
    have htop :
        Tendsto (fun y : ℝ => (1 + y⁻¹ * F y⁻¹) ^ y) atTop
          (𝓝 (Real.exp c)) := by
      have hmul :
          Tendsto (fun y : ℝ => y * (y⁻¹ * F y⁻¹)) atTop (𝓝 c) := by
        refine Tendsto.congr' ?_ (hF.comp tendsto_inv_atTop_nhdsGT_zero)
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with y hy
        rw [← mul_assoc, mul_inv_cancel₀ hy, one_mul]
        rfl
      exact Real.tendsto_one_add_rpow_exp_of_tendsto hmul
    have hHlim :
        Tendsto (fun r : ℝ => (H r) ^ (1 / r)) (𝓝[>] 0) (𝓝 (Real.exp c)) := by
      refine Tendsto.congr' ?_ (htop.comp tendsto_inv_nhdsGT_zero)
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : r ≠ 0 := ne_of_gt hr
      simp [F, H, hr0, one_div]
    have hgiven : Tendsto (fun r : ℝ => (H r) ^ (1 / r)) (𝓝[>] 0) (𝓝 (g x)) := by
      simpa [H] using hg x hx
    have : g x = Real.exp c := tendsto_nhds_unique hgiven hHlim
    simpa [c] using this
  have harg :
      Tendsto (fun x : ℝ => (x + 1) * Real.log (1 + 1 / x)) atTop (𝓝 1) := by
    have hmain : Tendsto (fun x : ℝ => x * Real.log (1 + 1 / x)) atTop (𝓝 1) := by
      simpa using (Real.tendsto_mul_log_one_add_div_atTop (1 : ℝ))
    have hlog0 : Tendsto (fun x : ℝ => Real.log (1 + 1 / x)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
      simpa [Real.log_one] using hbase.log (by norm_num : (1 + 0 : ℝ) ≠ 0)
    simpa [add_mul] using hmain.add hlog0
  have hexp :
      Tendsto (fun x : ℝ => Real.exp ((x + 1) * Real.log (1 + 1 / x)))
        atTop (𝓝 (Real.exp 1)) :=
    (Real.continuous_exp.tendsto 1).comp harg
  refine Tendsto.congr' ?_ hexp
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  calc
    Real.exp ((x + 1) * Real.log (1 + 1 / x))
        = Real.exp (Real.log (x + 1) * (x + 1) - Real.log x * x - Real.log x) := by
          congr 1
          rw [show 1 + 1 / x = (x + 1) / x by field_simp [hx0],
            Real.log_div hx1 hx0]
          ring
    _ = Real.exp (Real.log (x + 1) * (x + 1) - Real.log x * x) / x := by
          rw [Real.exp_sub, Real.exp_log hx]
    _ = g x / x := by
          rw [hg_eval x hx]
