import Mathlib

open Topology Filter Set Polynomial Function

-- -1
/--
Find the value of $$\lim_{n \rightarrow \infty} \frac{1}{n^5}\sum_{h=1}^{n}\sum_{k=1}^{n}(5h^4 - 18h^2k^2 + 5k^4).$$
-/
theorem putnam_1981_b1
(f : ℕ → ℝ)
(hf : f = fun n : ℕ => ((1 : ℝ)/n^5) * ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4))
: Tendsto f atTop (𝓝 ((-1) : ℝ )) := by
  rw [hf]
  have hsum_sq : ∀ n : ℕ,
      (∑ i ∈ Finset.Icc 1 n, (i : ℝ)^2) =
        (n : ℝ) * (n + 1) * (2*n + 1) / 6 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top]
        · rw [ih]
          norm_num
          ring
        · omega
  have hsum_four : ∀ n : ℕ,
      (∑ i ∈ Finset.Icc 1 n, (i : ℝ)^4) =
        (n : ℝ) * (n + 1) * (2*n + 1) *
          (3*(n : ℝ)^2 + 3*n - 1) / 30 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top]
        · rw [ih]
          norm_num
          ring
        · omega
  have hsum : ∀ n : ℕ,
      (∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
        (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4)) =
        - ((n : ℝ)^2 * (n + 1) * (2*n + 1) * (3*n + 5)) / 6 := by
    intro n
    ring_nf
    simp_rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib]
    simp_rw [← Finset.sum_mul]
    rw [← Finset.sum_mul_sum]
    simp [Finset.sum_const, Nat.card_Icc]
    rw [← Finset.mul_sum]
    rw [hsum_sq n, hsum_four n]
    ring
  have heq :
      (fun n : ℕ => ((1 : ℝ)/n^5) *
        ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
          (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4)) =ᶠ[atTop]
      (fun n : ℕ => (-1 : ℝ) - (19/6 : ℝ) / n -
        (3 : ℝ) / (n : ℝ)^2 - (5/6 : ℝ) / (n : ℝ)^3) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [hsum n]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    field_simp [hn0]
    ring
  have hlim1 : Tendsto (fun n : ℕ => (19/6 : ℝ) / n) atTop (𝓝 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (19/6 : ℝ)
  have hlim2 : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ)^2) atTop (𝓝 0) := by
    simpa using tendsto_const_div_pow (3 : ℝ) 2 (by norm_num)
  have hlim3 : Tendsto (fun n : ℕ => (5/6 : ℝ) / (n : ℝ)^3) atTop (𝓝 0) := by
    simpa using tendsto_const_div_pow (5/6 : ℝ) 3 (by norm_num)
  have hlim :
      Tendsto (fun n : ℕ => (-1 : ℝ) - (19/6 : ℝ) / n -
        (3 : ℝ) / (n : ℝ)^2 - (5/6 : ℝ) / (n : ℝ)^3)
        atTop (𝓝 ((-1 : ℝ) - 0 - 0 - 0)) := by
    exact (((tendsto_const_nhds.sub hlim1).sub hlim2).sub hlim3)
  exact Filter.Tendsto.congr' heq.symm (by simpa using hlim)
