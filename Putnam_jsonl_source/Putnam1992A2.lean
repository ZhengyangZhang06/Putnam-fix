import Mathlib

open Topology Filter

private lemma putnam_1992_a2_desc_neg (n : ℕ) (y : ℝ) :
    (descPochhammer ℝ n).eval (-y - 1) =
      (-1 : ℝ) ^ n * ∏ k ∈ Finset.Icc (1 : ℕ) n, (y + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [descPochhammer_succ_eval, ih, Finset.prod_Icc_succ_top (by omega)]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private lemma putnam_1992_a2_taylor_coeff
    (C : ℝ → ℝ)
    (hC : C = fun α ↦ taylorCoeffWithin (fun x ↦ (1 + x) ^ α) 1992 Set.univ 0)
    (y : ℝ) :
    C (-y - 1) = (Nat.factorial 1992 : ℝ)⁻¹ *
      ∏ k ∈ Finset.Icc (1 : ℕ) 1992, (y + k) := by
  rw [hC]
  unfold taylorCoeffWithin
  simp only [iteratedDerivWithin_univ, smul_eq_mul]
  congr 1
  calc
    iteratedDeriv 1992 (fun x : ℝ => (1 + x) ^ (-y - 1)) 0
        = (descPochhammer ℝ 1992).eval (-y - 1) := by
          have hshift := congr_fun
            (iteratedDeriv_comp_const_add 1992 (fun t : ℝ => t ^ (-y - 1)) (1 : ℝ)) 0
          rw [hshift]
          rw [iteratedDeriv_eq_iterate]
          rw [Real.iter_deriv_rpow_const]
          norm_num
    _ = ∏ k ∈ Finset.Icc (1 : ℕ) 1992, (y + k) := by
          rw [putnam_1992_a2_desc_neg]
          norm_num

private lemma putnam_1992_a2_hasDerivAt_prod_Icc_one (n : ℕ) (y : ℝ)
    (hne : ∀ k ∈ Finset.Icc (1 : ℕ) n, y + (k : ℝ) ≠ 0) :
    HasDerivAt (fun t : ℝ => ∏ k ∈ Finset.Icc (1 : ℕ) n, (t + k))
      ((∏ k ∈ Finset.Icc (1 : ℕ) n, (y + k)) *
        ∑ k ∈ Finset.Icc (1 : ℕ) n, 1 / (y + k)) y := by
  induction n with
  | zero => simpa using (hasDerivAt_const (x := y) (c := (1 : ℝ)))
  | succ n ih =>
      have hne_old : ∀ k ∈ Finset.Icc (1 : ℕ) n, y + (k : ℝ) ≠ 0 := by
        intro k hk
        exact hne k (by
          rw [Finset.mem_Icc] at hk ⊢
          omega)
      have hne_top : y + ((n + 1 : ℕ) : ℝ) ≠ 0 := by
        exact hne (n + 1) (by simp)
      have hprod_ne : (∏ k ∈ Finset.Icc (1 : ℕ) n, (y + k)) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr hne_old
      have hmul := (ih hne_old).mul ((hasDerivAt_id y).add_const (((n + 1 : ℕ) : ℝ)))
      convert hmul using 1
      · ext t
        rw [Finset.prod_Icc_succ_top (by omega)]
        simp [Pi.mul_apply]
      · rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
        field_simp [hne_top, hprod_ne]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring

private lemma putnam_1992_a2_prod_Icc_one_eq_factorial (n : ℕ) :
    (∏ k ∈ Finset.Icc (1 : ℕ) n, (k : ℝ)) = (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private lemma putnam_1992_a2_prod_Icc_zero_add_eq_factorial (n : ℕ) :
    (∏ k ∈ Finset.Icc (1 : ℕ) n, ((0 : ℝ) + k)) = (Nat.factorial n : ℝ) := by
  simpa only [zero_add] using putnam_1992_a2_prod_Icc_one_eq_factorial n

private lemma putnam_1992_a2_prod_Icc_one_add_eq_factorial_succ (n : ℕ) :
    (∏ k ∈ Finset.Icc (1 : ℕ) n, (1 + (k : ℝ))) = (Nat.factorial (n + 1) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      rw [Nat.factorial_succ (n + 1)]
      norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      ring

-- 1992
/--
Define $C(\alpha)$ to be the coefficient of $x^{1992}$ in the power series about $x=0$ of $(1 + x)^\alpha$. Evaluate
\[
\int_0^1 \left( C(-y-1) \sum_{k=1}^{1992} \frac{1}{y+k} \right)\,dy.
\]
-/
theorem putnam_1992_a2
(C : ℝ → ℝ)
(hC : C = fun α ↦ taylorCoeffWithin (fun x ↦ (1 + x) ^ α) 1992 Set.univ 0)
: (∫ y in (0)..1, C (-y - 1) * ∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k) = ((1992) : ℝ )) := by
  let G : ℝ → ℝ := fun y => (Nat.factorial 1992 : ℝ)⁻¹ *
    ((∏ k ∈ Finset.Icc (1 : ℕ) 1992, (y + k)) *
      ∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k))
  let F : ℝ → ℝ := fun y => (Nat.factorial 1992 : ℝ)⁻¹ *
    ∏ k ∈ Finset.Icc (1 : ℕ) 1992, (y + k)
  have hden_ne : ∀ k ∈ Finset.Icc (1 : ℕ) 1992, ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      y + (k : ℝ) ≠ 0 := by
    intro k hk y hy
    have hy0 : 0 ≤ y := by
      have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le zero_le_one] using hy
      exact hy'.1
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).1
    exact ne_of_gt (by linarith : 0 < y + (k : ℝ))
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (G y) y := by
    intro y hy
    have hne : ∀ k ∈ Finset.Icc (1 : ℕ) 1992, y + (k : ℝ) ≠ 0 := by
      intro k hk
      exact hden_ne k hk y hy
    exact (putnam_1992_a2_hasDerivAt_prod_Icc_one 1992 y hne).const_mul
      ((Nat.factorial 1992 : ℝ)⁻¹)
  have hcont_prod : ContinuousOn
      (fun y : ℝ => ∏ k ∈ Finset.Icc (1 : ℕ) 1992, (y + k)) (Set.uIcc (0 : ℝ) 1) := by
    exact continuousOn_finset_prod (Finset.Icc (1 : ℕ) 1992)
      (fun k hk => continuousOn_id.add continuousOn_const)
  have hcont_sum : ContinuousOn
      (fun y : ℝ => ∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k)) (Set.uIcc (0 : ℝ) 1) := by
    exact continuousOn_finset_sum (Finset.Icc (1 : ℕ) 1992)
      (fun k hk => continuousOn_const.div₀ (continuousOn_id.add continuousOn_const)
        (hden_ne k hk))
  have hG_int : IntervalIntegrable G MeasureTheory.volume 0 1 := by
    exact ContinuousOn.intervalIntegrable (μ := MeasureTheory.volume)
      (continuousOn_const.mul (hcont_prod.mul hcont_sum))
  have hFTC : ∫ y in (0)..1, G y = F 1 - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hG_int
  have hcongr : Set.EqOn
      (fun y : ℝ => C (-y - 1) * ∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k))
      G (Set.uIcc (0 : ℝ) 1) := by
    intro y hy
    change C (-y - 1) * (∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k)) = G y
    rw [putnam_1992_a2_taylor_coeff C hC y]
    ring
  calc
    ∫ y in (0)..1, C (-y - 1) * ∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k)
        = ∫ y in (0)..1, G y := intervalIntegral.integral_congr hcongr
    _ = F 1 - F 0 := hFTC
    _ = (1992 : ℝ) := by
      dsimp [F]
      rw [putnam_1992_a2_prod_Icc_one_add_eq_factorial_succ,
        putnam_1992_a2_prod_Icc_zero_add_eq_factorial]
      rw [Nat.factorial_succ 1992]
      have hfact : (Nat.factorial 1992 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero 1992
      field_simp [hfact]
      norm_num
