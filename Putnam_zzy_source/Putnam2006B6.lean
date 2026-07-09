import Mathlib

open Set Topology Filter

noncomputable abbrev putnam_2006_b6_solution : ℕ → ℝ := fun k => (1 + (1 : ℝ) / (k : ℝ)) ^ k

/--
Let $k$ be an integer greater than 1. Suppose $a_0 > 0$, and define \[ a_{n+1} = a_n + \frac{1}{\sqrt[k]{a_n}} \] for $n > 0$. Evaluate \[\lim_{n \to \infty} \frac{a_n^{k+1}}{n^k}.\]
-/
theorem putnam_2006_b6
(k : ℕ)
(hk : k > 1)
(a : ℕ → ℝ)
(ha0 : a 0 > 0)
(ha : ∀ n : ℕ, a (n + 1) = a n + 1/((a n)^((1 : ℝ)/k)))
: Tendsto (fun n => (a n)^(k+1)/(n ^ k)) atTop (𝓝 (putnam_2006_b6_solution k)) :=
by
  let q : ℝ := (1 : ℝ) / (k : ℝ)
  let p : ℝ := 1 + q
  let b : ℕ → ℝ := fun n => (a n) ^ p
  have hk0_nat : 0 < k := Nat.lt_trans Nat.zero_lt_one hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0_nat
  have hq_pos : 0 < q := by
    dsimp [q]
    exact one_div_pos.mpr hk0
  have hp_pos : 0 < p := by
    dsimp [p]
    linarith
  have hp_ge_one : 1 ≤ p := by
    dsimp [p]
    linarith
  have hp_mul : p * (k : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    calc
      p * (k : ℝ) = (1 + (1 : ℝ) / (k : ℝ)) * (k : ℝ) := by rfl
      _ = (k : ℝ) + 1 := by
        field_simp [hk0.ne']
      _ = ((k + 1 : ℕ) : ℝ) := by
        norm_num
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
        rw [ha n]
        exact add_pos ih (one_div_pos.mpr (Real.rpow_pos_of_pos ih q))
  have hb_eq : ∀ n, b n = a n * (a n) ^ q := by
    intro n
    dsimp [b, p]
    rw [Real.rpow_add (ha_pos n) 1 q]
    simp
  have hb_pos : ∀ n, 0 < b n := by
    intro n
    exact Real.rpow_pos_of_pos (ha_pos n) p
  have hstep_mul : ∀ n, a (n + 1) = a n * (1 + (b n)⁻¹) := by
    intro n
    rw [ha n]
    rw [hb_eq n]
    rw [mul_add, mul_one]
    congr 1
    dsimp [q]
    field_simp [(ha_pos n).ne', (Real.rpow_pos_of_pos (ha_pos n) ((1 : ℝ) / (k : ℝ))).ne']
  have hb_succ : ∀ n, b (n + 1) = b n * (1 + (b n)⁻¹) ^ p := by
    intro n
    dsimp [b]
    rw [hstep_mul n]
    rw [Real.mul_rpow (le_of_lt (ha_pos n))
      (le_of_lt (add_pos zero_lt_one (inv_pos.mpr (hb_pos n))))]
  have hb_succ_ge : ∀ n, b n + p ≤ b (n + 1) := by
    intro n
    rw [hb_succ n]
    have hbern : 1 + p * (b n)⁻¹ ≤ (1 + (b n)⁻¹) ^ p := by
      exact one_add_mul_self_le_rpow_one_add
        (by linarith [inv_pos.mpr (hb_pos n)]) hp_ge_one
    have hmul := mul_le_mul_of_nonneg_left hbern (le_of_lt (hb_pos n))
    have hleft : b n * (1 + p * (b n)⁻¹) = b n + p := by
      field_simp [(hb_pos n).ne']
    simpa [hleft] using hmul
  have hb_lower : ∀ n : ℕ, b 0 + (n : ℝ) * p ≤ b n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          b 0 + ((n + 1 : ℕ) : ℝ) * p = b 0 + (n : ℝ) * p + p := by
            norm_num
            ring
          _ ≤ b n + p := by linarith
          _ ≤ b (n + 1) := hb_succ_ge n
  have hb_atTop : Tendsto b atTop atTop := by
    have hlinear : Tendsto (fun n : ℕ => b 0 + (n : ℝ) * p) atTop atTop := by
      exact tendsto_atTop_add_const_left atTop (b 0)
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hp_pos)
    exact tendsto_atTop_mono hb_lower hlinear
  have hbasic : Tendsto (fun y : ℝ => y * ((1 + y⁻¹) ^ p - 1)) atTop (𝓝 p) := by
    have hder : HasDerivAt (fun t : ℝ => (1 + t) ^ p) p 0 := by
      have hlin : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
      simpa using hlin.rpow_const (p := p) (Or.inl (by norm_num : (1 + (0 : ℝ)) ≠ 0))
    have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
      exact tendsto_inv_atTop_nhdsGT_zero.mono_right
        (nhdsWithin_mono _ (by intro x hx; exact ne_of_gt hx))
    have hcomp := hder.tendsto_slope_zero.comp hinv
    refine hcomp.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with y hy
    simp
  have hincrement : Tendsto (fun n : ℕ => b (n + 1) - b n) atTop (𝓝 p) := by
    have hcomp := hbasic.comp hb_atTop
    refine hcomp.congr' ?_
    filter_upwards with n
    change b n * ((1 + (b n)⁻¹) ^ p - 1) = b (n + 1) - b n
    rw [hb_succ n]
    ring
  have hb_avg : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * (b n - b 0)) atTop (𝓝 p) := by
    refine hincrement.cesaro.congr' ?_
    filter_upwards with n
    rw [Finset.sum_range_sub b n]
  have hb_inv_mul : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * b n) atTop (𝓝 p) := by
    have hconst : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * b 0) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul
        (tendsto_const_nhds (x := b 0))
    have hsum := hb_avg.add hconst
    simpa using hsum.congr' (by
      filter_upwards with n
      ring)
  have hb_div : Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop (𝓝 p) := by
    simpa [div_eq_mul_inv, mul_comm] using hb_inv_mul
  have hpow : Tendsto (fun n : ℕ => (b n / (n : ℝ)) ^ k) atTop (𝓝 (p ^ k)) :=
    hb_div.pow k
  have htarget : Tendsto (fun n : ℕ => (a n) ^ (k + 1) / (n ^ k)) atTop (𝓝 (p ^ k)) := by
    refine hpow.congr' ?_
    filter_upwards with n
    dsimp [b]
    rw [div_pow]
    congr 1
    calc
      ((a n) ^ p) ^ k = ((a n) ^ p) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (a n) ^ (p * (k : ℝ)) := by
        rw [← Real.rpow_mul (le_of_lt (ha_pos n))]
      _ = (a n) ^ (((k + 1 : ℕ) : ℝ)) := by
        rw [hp_mul]
      _ = (a n) ^ (k + 1) := by
        rw [Real.rpow_natCast]
  simpa [putnam_2006_b6_solution, p, q] using htarget
