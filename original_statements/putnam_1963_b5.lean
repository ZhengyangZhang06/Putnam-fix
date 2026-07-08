import Mathlib

open Topology Filter Polynomial

/--
Let $\{a_n\}$ be a sequence of real numbers satisfying the inequalities $0 \leq a_k \leq 100a_n$ for $n \leq k \leq 2n$ and $n=1,2,\dots$, and such that the series $\sum_{n=0}^\infty a_n$ converges. Prove that $\lim_{n \to \infty}na_n=0$.
-/
theorem putnam_1963_b5
(a : ℤ → ℝ)
(haineq : ∀ n ≥ 1, ∀ k : ℤ, (n ≤ k ∧ k ≤ 2 * n) → (0 ≤ a k ∧ a k ≤ 100 * a n))
(haseries : ∃ S : ℝ, Tendsto (fun N : ℕ => ∑ n : Fin N, a n) atTop (𝓝 S))
: Tendsto (fun n : ℤ => n * a n) atTop (𝓝 0) :=
sorry
