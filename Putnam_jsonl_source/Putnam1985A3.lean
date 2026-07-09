import Mathlib

open Set Filter Topology Real

-- fun d ↦ exp d - 1
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
: Tendsto (fun n ↦ a n n) atTop (𝓝 (((fun d ↦ exp d - 1) : ℝ → ℝ ) d)) := by
  have h_formula : ∀ m j : ℕ, a m j + 1 = (1 + d / 2 ^ m) ^ (2 ^ j) := by
    intro m j
    induction j with
    | zero =>
        rw [ha0 m]
        norm_num
        ring
    | succ j ih =>
        calc
          a m (j + 1) + 1 = (a m j) ^ 2 + 2 * a m j + 1 := by rw [ha m j]
          _ = (a m j + 1) ^ 2 := by ring
          _ = ((1 + d / 2 ^ m) ^ (2 ^ j)) ^ 2 := by rw [ih]
          _ = (1 + d / 2 ^ m) ^ (2 ^ j * 2) := by rw [pow_mul]
          _ = (1 + d / 2 ^ m) ^ (2 ^ (j + 1)) := by simp [pow_succ]
  have h_diag : ∀ n : ℕ, a n n = (1 + d / 2 ^ n) ^ (2 ^ n) - 1 := by
    intro n
    have h := h_formula n n
    linarith
  have hpow : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  have hlim0 :
      Tendsto (fun n : ℕ => (1 + d / (((2 : ℕ) ^ n : ℕ))) ^ ((2 : ℕ) ^ n)) atTop
        (𝓝 (exp d)) := by
    exact (Real.tendsto_one_add_div_pow_exp d).comp hpow
  have hlim : Tendsto (fun n : ℕ => (1 + d / 2 ^ n) ^ (2 ^ n) - 1) atTop
      (𝓝 (exp d - 1)) := by
    simpa [Nat.cast_pow] using hlim0.sub tendsto_const_nhds
  exact hlim.congr' (Eventually.of_forall fun n => (h_diag n).symm)
