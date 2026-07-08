import Mathlib

open Topology Filter

/--
Let \( g \) be a real-valued function that is continuous on the closed interval \([0,1]\) and twice differentiable on the open interval \((0,1)\). Suppose that for some real number $\( r > 1 \),\lim_{{x \to 0^+}} \frac{g(x)}{x^r} = 0.$ Prove that either $\lim_{{x \to 0^+}} g'(x) = 0$ or $\limsup_{{x \to 0^+}} x^r |g''(x)| = \infty.$
-/
theorem putnam_2019_a6
(g : ℝ → ℝ)
(r : ℝ)
(hcont : ContinuousOn g (Set.Icc 0 1))
(hdiff : ContDiffOn ℝ 1 g (Set.Ioo 0 1) ∧ DifferentiableOn ℝ (deriv g) (Set.Ioo 0 1))
(hr : r > 1)
(hlim : Tendsto (fun x => g x / x ^ r) (𝓝[>] 0) (𝓝 0))
: (Tendsto (deriv g) (𝓝[>] 0) (𝓝 0)) ∨ (Tendsto (fun x : ℝ => sSup {((x' ^ r * abs (iteratedDeriv 2 g x') : ℝ) : WithTop ℝ) | x' ∈ Set.Ioc 0 x}) (𝓝[>] 0) atTop) :=
sorry
