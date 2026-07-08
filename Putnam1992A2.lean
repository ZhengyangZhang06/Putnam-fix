import Mathlib

open Topology Filter

abbrev putnam_1992_a2_solution : ℝ := 1992

private lemma putnam_1992_a2_ascPochhammer_eval_eq_prod_range {R : Type*} [CommSemiring R]
    (n : ℕ) (r : R) :
    (ascPochhammer R n).eval r = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

private lemma putnam_1992_a2_coeff (y : ℝ) :
    taylorCoeffWithin (fun x : ℝ => (1 + x) ^ (-y - 1)) 1992 Set.univ 0 =
      (Nat.factorial 1992 : ℝ)⁻¹ * (ascPochhammer ℝ 1992).eval (y + 1) := by
  rw [taylorCoeffWithin]
  simp only [iteratedDerivWithin_univ, smul_eq_mul]
  rw [iteratedDeriv_comp_const_add (n := 1992) (f := fun x : ℝ => x ^ (-y - 1)) (s := 1)]
  rw [iteratedDeriv_eq_iterate]
  change (Nat.factorial 1992 : ℝ)⁻¹ *
      (deriv^[1992] (fun x : ℝ => x ^ (-y - 1)) (1 + 0)) =
    (Nat.factorial 1992 : ℝ)⁻¹ * (ascPochhammer ℝ 1992).eval (y + 1)
  rw [add_zero]
  rw [Real.iter_deriv_rpow_const]
  rw [Real.one_rpow, mul_one]
  congr 1
  have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℝ) (-y - 1) 1992
  norm_num at h
  convert h.symm using 2
  ring

private lemma putnam_1992_a2_sum_Icc_eq_range (y : ℝ) :
    (∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k)) =
      ∑ j ∈ Finset.range 1992, 1 / (y + (j + 1 : ℕ)) := by
  refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    change k - 1 < 1992
    omega
  · intro a₁ ha₁ a₂ ha₂ h
    rw [Finset.mem_Icc] at ha₁ ha₂
    change a₁ - 1 = a₂ - 1 at h
    omega
  · intro b hb
    refine ⟨b + 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      rw [Finset.mem_range] at hb
      omega
    · change b + 1 - 1 = b
      omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hsub : k - 1 + 1 = k := by omega
    simp [hsub]

private lemma putnam_1992_a2_deriv_num (y : ℝ) (hy : 0 ≤ y) :
    deriv (fun t : ℝ => (ascPochhammer ℝ 1992).eval (t + 1)) y =
      (ascPochhammer ℝ 1992).eval (y + 1) *
        ∑ j ∈ Finset.range 1992, 1 / (y + (j + 1 : ℕ)) := by
  have hfun : (fun t : ℝ => (ascPochhammer ℝ 1992).eval (t + 1)) =
      fun t : ℝ => ∏ j ∈ Finset.range 1992, (t + 1 + (j : ℝ)) := by
    funext t
    rw [putnam_1992_a2_ascPochhammer_eval_eq_prod_range]
  rw [hfun]
  rw [putnam_1992_a2_ascPochhammer_eval_eq_prod_range]
  have hne : (∏ j ∈ Finset.range 1992, (y + 1 + (j : ℝ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := by exact_mod_cast Nat.zero_le j
    have hpos : 0 < y + 1 + (j : ℝ) := by linarith
    exact hpos.ne'
  have hlog := logDeriv_prod (Finset.range 1992)
      (fun (j : ℕ) (t : ℝ) => t + 1 + (j : ℝ)) y
      (by
        intro j hj
        have hj0 : (0 : ℝ) ≤ j := by exact_mod_cast Nat.zero_le j
        have hpos : 0 < y + 1 + (j : ℝ) := by linarith
        exact hpos.ne')
      (by intro j hj; fun_prop)
  rw [logDeriv_apply] at hlog
  have hlog' :
      deriv (fun t : ℝ => ∏ j ∈ Finset.range 1992, (t + 1 + (j : ℝ))) y /
          (∏ j ∈ Finset.range 1992, (y + 1 + (j : ℝ))) =
        ∑ j ∈ Finset.range 1992, 1 / (y + (j + 1 : ℕ)) := by
    rw [hlog]
    apply Finset.sum_congr rfl
    intro j hj
    simp [logDeriv_apply]
    ring
  rw [div_eq_iff hne] at hlog'
  rw [hlog']
  ring

/--
Define $C(\alpha)$ to be the coefficient of $x^{1992}$ in the power series about $x=0$ of $(1 + x)^\alpha$. Evaluate
\[
\int_0^1 \left( C(-y-1) \sum_{k=1}^{1992} \frac{1}{y+k} \right)\,dy.
\]
-/
theorem putnam_1992_a2
(C : ℝ → ℝ)
(hC : C = fun α ↦ taylorCoeffWithin (fun x ↦ (1 + x) ^ α) 1992 Set.univ 0)
: (∫ y in (0)..1, C (-y - 1) * ∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k) = putnam_1992_a2_solution) :=
by
  rw [hC]
  let F : ℝ → ℝ := fun t =>
    (Nat.factorial 1992 : ℝ)⁻¹ * (ascPochhammer ℝ 1992).eval (t + 1)
  have hFcont : ContDiffOn ℝ 1 F (Set.Icc (0 : ℝ) 1) := by
    dsimp [F]
    have hp : ContDiff ℝ 1 (fun x : ℝ => (ascPochhammer ℝ 1992).eval x) := by
      simpa using (Polynomial.contDiff_aeval (ascPochhammer ℝ 1992) (1 : WithTop ℕ∞) :
        ContDiff ℝ 1 (fun x : ℝ => (Polynomial.aeval x) (ascPochhammer ℝ 1992)))
    have hshift : ContDiff ℝ 1 (fun t : ℝ => t + 1) := by fun_prop
    exact (contDiff_const.mul (hp.comp hshift)).contDiffOn
  calc
    ∫ y in (0)..1,
        taylorCoeffWithin (fun x ↦ (1 + x) ^ (-y - 1)) 1992 Set.univ 0 *
          ∑ k ∈ Finset.Icc (1 : ℕ) 1992, 1 / (y + k) =
        ∫ y in (0)..1, deriv F y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
      dsimp [F]
      rw [putnam_1992_a2_coeff y, putnam_1992_a2_sum_Icc_eq_range y]
      rw [deriv_const_mul_field]
      rw [putnam_1992_a2_deriv_num y hy.1]
      ring
    _ = F 1 - F 0 := by
      exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hFcont (by norm_num)
    _ = putnam_1992_a2_solution := by
      dsimp [F, putnam_1992_a2_solution]
      have h1 : (ascPochhammer ℝ 1992).eval (1 : ℝ) = (Nat.factorial 1992 : ℝ) := by
        exact ascPochhammer_eval_one ℝ 1992
      have h2rel : (ascPochhammer ℝ 1992).eval (2 : ℝ) =
          (1993 : ℝ) * (ascPochhammer ℝ 1992).eval (1 : ℝ) := by
        have h := ascPochhammer_eval_succ ℝ 1992 1
        convert h using 1 <;> norm_num
      have h2 : (ascPochhammer ℝ 1992).eval (2 : ℝ) =
          (1993 : ℝ) * (Nat.factorial 1992 : ℝ) := by
        rw [h2rel, h1]
      rw [show (1 : ℝ) + 1 = 2 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num]
      rw [h2, h1]
      have hfact : (Nat.factorial 1992 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero 1992
      field_simp [hfact]
      ring
