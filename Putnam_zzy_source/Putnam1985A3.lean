import Mathlib

open Set Filter Topology Real

noncomputable abbrev putnam_1985_a3_solution : ℝ → ℝ := fun d ↦ Real.exp d - 1

/--
Let $d$ be a real number. For each integer $m \geq 0$, define a sequence $\{a_m(j)\}$, $j=0,1,2,\dots$ by the condition
\begin{align*}
a_m(0) &= d/2^m, \\
a_m(j+1) &= (a_m(j))^2 + 2a_m(j), \qquad j \geq 0.
\end{align*}
Evaluate $\lim_{n \to \infty} a_n(n)$.
-/
theorem putnam_1985_a3
(d : ℝ)
(a : ℕ → ℕ → ℝ)
(ha0 : ∀ m : ℕ, a m 0 = d / 2 ^ m)
(ha : ∀ m : ℕ, ∀ j : ℕ, a m (j + 1) = (a m j) ^ 2 + 2 * a m j)
: Tendsto (fun n ↦ a n n) atTop (𝓝 (putnam_1985_a3_solution d)) :=
by
  have hclosed : ∀ m j : ℕ, a m j + 1 = (1 + d / (2 : ℝ) ^ m) ^ ((2 : ℕ) ^ j) := by
    intro m j
    induction j with
    | zero =>
        rw [ha0 m]
        norm_num
        ring
    | succ j ih =>
        calc
          a m (j + 1) + 1 = (a m j + 1) ^ 2 := by
            rw [ha m j]
            ring
          _ = ((1 + d / (2 : ℝ) ^ m) ^ ((2 : ℕ) ^ j)) ^ 2 := by
            rw [ih]
          _ = (1 + d / (2 : ℝ) ^ m) ^ (((2 : ℕ) ^ j) * 2) := by
            rw [pow_mul]
          _ = (1 + d / (2 : ℝ) ^ m) ^ ((2 : ℕ) ^ (j + 1)) := by
            rw [Nat.pow_succ]
  have hdiag : ∀ n : ℕ, a n n = (1 + d / (2 : ℝ) ^ n) ^ ((2 : ℕ) ^ n) - 1 := by
    intro n
    have hn := hclosed n n
    linarith
  have hlim_cast :
      Tendsto
        (fun n : ℕ => (1 + d / (((2 : ℕ) ^ n : ℕ) : ℝ)) ^ ((2 : ℕ) ^ n))
        atTop (𝓝 (Real.exp d)) := by
    change
      Tendsto (((fun m : ℕ => (1 + d / (m : ℝ)) ^ m) ∘ fun n : ℕ => (2 : ℕ) ^ n))
        atTop (𝓝 (Real.exp d))
    exact (Real.tendsto_one_add_div_pow_exp d).comp
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) one_lt_two)
  have hlim_pow :
      Tendsto (fun n : ℕ => (1 + d / (2 : ℝ) ^ n) ^ ((2 : ℕ) ^ n)) atTop
        (𝓝 (Real.exp d)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlim_cast
  have hlim :
      Tendsto (fun n : ℕ => (1 + d / (2 : ℝ) ^ n) ^ ((2 : ℕ) ^ n) - 1) atTop
        (𝓝 (Real.exp d - 1)) := by
    exact hlim_pow.sub_const 1
  simpa [putnam_1985_a3_solution] using hlim.congr (fun n => (hdiag n).symm)
