import Mathlib

open Nat

-- 18
/--
For a positive integer $n$, let $f_n(x) = \cos(x) \cos(2x) \cos(3x) \cdots \cos(nx)$. Find the smallest $n$ such that $|f_n''(0)| > 2023$.
-/
theorem putnam_2023_a1
  (f : ℕ → ℝ → ℝ)
  (hf : ∀ n > 0, f n = fun x : ℝ => ∏ i ∈ Finset.Icc 1 n, Real.cos (i * x)) :
  IsLeast {n | 0 < n ∧ |iteratedDeriv 2 (f n) 0| > 2023} ((18) : ℕ ) := by
  have hprodSecond (n : ℕ) :
      iteratedDeriv 2 (fun x : ℝ => ∏ i ∈ Finset.Icc 1 n, Real.cos ((i : ℝ) * x)) 0 =
        ∑ i ∈ Finset.Icc 1 n, -((i : ℝ)^2) := by
    let S : Finset ℕ := Finset.Icc 1 n
    let P : ℝ → ℝ := fun x : ℝ => ∏ i ∈ S, Real.cos ((i : ℝ) * x)
    have hderiv : deriv P = fun x : ℝ =>
        ∑ i ∈ S,
          (∏ j ∈ S.erase i, Real.cos ((j : ℝ) * x)) *
            (-Real.sin ((i : ℝ) * x) * (i : ℝ)) := by
      funext x
      rw [show P = (fun x : ℝ => ∏ i ∈ S, Real.cos ((i : ℝ) * x)) by rfl]
      rw [deriv_fun_finset_prod]
      · apply Finset.sum_congr rfl
        intro i hi
        have hci : deriv (fun x : ℝ => Real.cos ((i : ℝ) * x)) x =
            -Real.sin ((i : ℝ) * x) * (i : ℝ) := by
          simpa using (((hasDerivAt_id x).const_mul (i : ℝ)).cos).deriv
        simp [hci]
      · intro i hi
        exact (((hasDerivAt_id x).const_mul (i : ℝ)).cos).differentiableAt
    have hmain : iteratedDeriv 2 P 0 = ∑ i ∈ S, -((i : ℝ)^2) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
      rw [hderiv]
      rw [deriv_fun_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        let A : ℝ → ℝ := fun x : ℝ => ∏ j ∈ S.erase i, Real.cos ((j : ℝ) * x)
        let B : ℝ → ℝ := fun x : ℝ => -Real.sin ((i : ℝ) * x) * (i : ℝ)
        have hA : DifferentiableAt ℝ A 0 := by
          dsimp [A]
          exact DifferentiableAt.fun_finset_prod (fun j hj =>
            (((hasDerivAt_id (0 : ℝ)).const_mul (j : ℝ)).cos).differentiableAt)
        have hB : DifferentiableAt ℝ B 0 := by
          dsimp [B]
          exact (((((hasDerivAt_id (0 : ℝ)).const_mul (i : ℝ)).sin).neg).mul_const (i : ℝ)).differentiableAt
        have hBderiv : deriv B 0 = -((i : ℝ)^2) := by
          dsimp [B]
          have h0 : HasDerivAt (fun x : ℝ => -Real.sin ((i : ℝ) * x) * (i : ℝ))
              ((-(Real.cos ((i : ℝ) * 0) * (i : ℝ)) * (i : ℝ))) 0 := by
            simpa using (((((hasDerivAt_id (0 : ℝ)).const_mul (i : ℝ)).sin).neg).mul_const (i : ℝ))
          rw [h0.deriv]
          simp [pow_two]
        change deriv (A * B) 0 = -((i : ℝ)^2)
        rw [deriv_mul hA hB]
        rw [hBderiv]
        simp [A, B]
      · intro i hi
        let A : ℝ → ℝ := fun x : ℝ => ∏ j ∈ S.erase i, Real.cos ((j : ℝ) * x)
        let B : ℝ → ℝ := fun x : ℝ => -Real.sin ((i : ℝ) * x) * (i : ℝ)
        change DifferentiableAt ℝ (A * B) 0
        apply DifferentiableAt.mul
        · dsimp [A]
          exact DifferentiableAt.fun_finset_prod (fun j hj =>
            (((hasDerivAt_id (0 : ℝ)).const_mul (j : ℝ)).cos).differentiableAt)
        · dsimp [B]
          exact (((((hasDerivAt_id (0 : ℝ)).const_mul (i : ℝ)).sin).neg).mul_const (i : ℝ)).differentiableAt
    simpa [P, S] using hmain
  have hsumSquares (n : ℕ) :
      (∑ i ∈ Finset.Icc 1 n, ((i : ℝ)^2)) =
        (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top]
        · rw [ih]
          norm_num
          ring
        · omega
  have hsecond (n : ℕ) (hn : 0 < n) :
      iteratedDeriv 2 (f n) 0 = ∑ i ∈ Finset.Icc 1 n, -((i : ℝ)^2) := by
    rw [hf n hn]
    exact hprodSecond n
  have hsecondAbs (n : ℕ) (hn : 0 < n) :
      |iteratedDeriv 2 (f n) 0| = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
    rw [hsecond n hn]
    rw [show (∑ i ∈ Finset.Icc 1 n, -((i : ℝ)^2)) =
        -(∑ i ∈ Finset.Icc 1 n, ((i : ℝ)^2)) by simp]
    rw [abs_neg, hsumSquares]
    rw [abs_of_nonneg]
    positivity
  constructor
  · constructor
    · norm_num
    · have h18 := hsecondAbs 18 (by norm_num)
      norm_num [h18]
  · intro m hm
    rcases hm with ⟨hmpos, hmabs⟩
    by_contra hnot
    have hlt : m < 18 := Nat.lt_of_not_ge hnot
    have hmval := hsecondAbs m hmpos
    interval_cases m <;> norm_num [hmval] at hmabs
