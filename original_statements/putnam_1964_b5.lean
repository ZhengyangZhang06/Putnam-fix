import Mathlib

open Set Function Filter Topology

/--
Let $a_n$ be a strictly monotonic increasing sequence of positive integers. Let $b_n$ be the least common multiple of $a_1, a_2, \dots , a_n$. Prove that $\sum_{n=1}^{\infty} 1/b_n$ converges.
-/
theorem putnam_1964_b5
(a b : ℕ → ℕ)
(ha : StrictMono a ∧ ∀ n : ℕ, a n > 0)
(hb : b 0 = a 0 ∧ ∀ n : ℕ, b (n + 1) = lcm (b n) (a (n + 1)))
: (∃ L : ℝ, Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (1 : ℝ) / b n) atTop (𝓝 L)) :=
sorry
