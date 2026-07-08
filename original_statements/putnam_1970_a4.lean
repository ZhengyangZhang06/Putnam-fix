import Mathlib

open Metric Set EuclideanGeometry Filter Topology

/--
Suppose $(x_n)$ is a sequence such that $\lim_{n \to \infty} (x_n - x_{n-2} = 0$. Prove that $\lim_{n \to \infty} \frac{x_n - x_{n-1}}{n} = 0$.
-/
theorem putnam_1970_a4
(x : ℕ → ℝ)
(hxlim : Tendsto (fun n => x (n+2) - x n) atTop (𝓝 0))
: Tendsto (fun n => (x (n+1) - x (n))/(n+1)) atTop (𝓝 0) :=
sorry
