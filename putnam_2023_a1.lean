import Mathlib

open Nat

abbrev putnam_2023_a1_solution : ℕ := 18

/--
For a positive integer $n$, let $f_n(x) = \cos(x) \cos(2x) \cos(3x) \cdots \cos(nx)$. Find the smallest $n$ such that $|f_n''(0)| > 2023$.
-/
theorem putnam_2023_a1
  (f : ℕ → ℝ → ℝ)
  (hf : ∀ n > 0, f n = fun x : ℝ => ∏ i ∈ Finset.Icc 1 n, Real.cos (i * x)) :
  IsLeast {n | 0 < n ∧ |iteratedDeriv 2 (f n) 0| > 2023} putnam_2023_a1_solution :=
by
  have hsecond : ∀ n : ℕ,
      iteratedDeriv 2
          (fun x : ℝ => ∏ i ∈ Finset.Icc (1 : ℕ) n, Real.cos ((i : ℝ) * x)) 0 =
        -∑ i ∈ Finset.Icc (1 : ℕ) n, (i : ℝ) ^ 2 := by
    intro n
    let s : Finset ℕ := Finset.Icc (1 : ℕ) n
    have hcos_deriv : ∀ (i : ℕ) (x : ℝ),
        deriv (fun y : ℝ => Real.cos ((i : ℝ) * y)) x =
          -(i : ℝ) * Real.sin ((i : ℝ) * x) := by
      intro i x
      change deriv (Real.cos ∘ fun y : ℝ => (i : ℝ) * y) x = _
      rw [deriv_comp]
      · rw [Real.deriv_cos]
        rw [deriv_const_mul]
        · simp
          ring
        · fun_prop
      · fun_prop
      · fun_prop
    have hterm_deriv : ∀ i : ℕ,
        deriv
            (fun x : ℝ =>
              (∏ j ∈ s.erase i, Real.cos ((j : ℝ) * x)) *
                (-(i : ℝ) * Real.sin ((i : ℝ) * x))) 0 =
          -(i : ℝ) ^ 2 := by
      intro i
      rw [deriv_fun_mul]
      · simp
        rw [deriv_sin]
        · rw [deriv_const_mul]
          · simp
            ring
          · fun_prop
        · fun_prop
      · exact DifferentiableAt.fun_finset_prod (fun j hj => by fun_prop)
      · fun_prop
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    change deriv
        (deriv (fun x : ℝ => ∏ i ∈ s, Real.cos ((i : ℝ) * x))) 0 =
      -∑ i ∈ s, (i : ℝ) ^ 2
    have hfirst : deriv (fun x : ℝ => ∏ i ∈ s, Real.cos ((i : ℝ) * x)) =
        fun x : ℝ =>
          ∑ i ∈ s,
            (∏ j ∈ s.erase i, Real.cos ((j : ℝ) * x)) *
              (-(i : ℝ) * Real.sin ((i : ℝ) * x)) := by
      funext x
      rw [deriv_fun_finset_prod]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hcos_deriv i x]
        simp [smul_eq_mul, mul_comm, mul_assoc]
      · intro i hi
        fun_prop
    rw [hfirst]
    rw [deriv_fun_sum]
    · calc
        ∑ i ∈ s,
            deriv
              (fun x : ℝ =>
                (∏ j ∈ s.erase i, Real.cos ((j : ℝ) * x)) *
                  (-(i : ℝ) * Real.sin ((i : ℝ) * x))) 0 =
            ∑ i ∈ s, -(i : ℝ) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm_deriv i
        _ = -∑ i ∈ s, (i : ℝ) ^ 2 := by
              exact Finset.sum_neg_distrib (fun i : ℕ => (i : ℝ) ^ 2)
    · intro i hi
      rw [show
          (fun x : ℝ =>
            (∏ j ∈ s.erase i, Real.cos ((j : ℝ) * x)) *
              (-(i : ℝ) * Real.sin ((i : ℝ) * x))) =
            (fun x : ℝ => ∏ j ∈ s.erase i, Real.cos ((j : ℝ) * x)) *
              (fun x : ℝ => -(i : ℝ) * Real.sin ((i : ℝ) * x)) by
        rfl]
      exact DifferentiableAt.mul
        (DifferentiableAt.fun_finset_prod (fun j hj => by fun_prop)) (by fun_prop)
  constructor
  · constructor
    · norm_num [putnam_2023_a1_solution]
    · rw [putnam_2023_a1_solution]
      rw [hf 18 (by norm_num)]
      rw [hsecond 18]
      norm_num [Finset.sum_Icc_succ_top]
  · intro m hm
    rw [putnam_2023_a1_solution]
    by_cases hm18 : 18 ≤ m
    · exact hm18
    · have hmle : m ≤ 17 := by omega
      have hmpos : 0 < m := hm.1
      have hbad : |(-∑ i ∈ Finset.Icc (1 : ℕ) m, (i : ℝ) ^ 2)| > 2023 := by
        rw [← hsecond m]
        rw [← hf m hmpos]
        exact hm.2
      interval_cases m <;> norm_num [Finset.sum_Icc_succ_top] at hbad
