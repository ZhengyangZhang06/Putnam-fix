import Mathlib

open Set Real Filter Topology Polynomial

/--
The polynomials $P_n(x)$ are defined by
\begin{align*}
P_1(x) &= 1 + x, \\
P_2(x) &= 1 + 2x, \\
P_{2n+1}(x) &= P_{2n}(x) + (n + 1) x P_{2n-1}(x), \\
P_{2n+2}(x) &= P_{2n+1}(x) + (n + 1) x P_{2n}(x).
\end{align*}
Let $a_n$ be the largest real root of $P_n(x)$. Prove that $a_n$ is strictly monotonically increasing and tends to zero.
-/
theorem putnam_1978_b3
(P : ℕ+ → Polynomial ℝ)
(hP1 : P 1 = 1 + X)
(hP2 : P 2 = 1 + 2 * X)
(hPodd : ∀ n, P (2 * n + 1) = P (2 * n) + C ((n : ℝ) + 1) * X * P (2 * n - 1))
(hPeven : ∀ n, P (2 * n + 2) = P (2 * n + 1) + C ((n : ℝ) + 1) * X * P (2 * n))
(a : ℕ+ → ℝ)
(haroot : ∀ n, (P n).eval (a n) = 0)
(haub : ∀ n, ∀ x, (P n).eval x = 0 → x ≤ a n)
: (StrictMono a ∧ Tendsto a atTop (𝓝 0)) :=
sorry
