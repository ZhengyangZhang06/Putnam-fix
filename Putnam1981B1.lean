import Mathlib

open Topology Filter Set Polynomial Function

abbrev putnam_1981_b1_solution : ℝ := -1

private lemma putnam_1981_b1_sum_sq_rat (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℚ) ^ 2) =
      (n : ℚ) * (n + 1) * (2 * n + 1) / 6 := by
  rw [← Finset.Ico_succ_right_eq_Icc (1 : ℕ) n]
  rw [show Order.succ n = n + 1 by rfl]
  rw [sum_Ico_pow]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two]
  ring

private lemma putnam_1981_b1_sum_four_rat (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℚ) ^ 4) =
      (n : ℚ) * (n + 1) * (2 * n + 1) * (3 * (n : ℚ)^2 + 3 * n - 1) / 30 := by
  rw [← Finset.Ico_succ_right_eq_Icc (1 : ℕ) n]
  rw [show Order.succ n = n + 1 by rfl]
  rw [sum_Ico_pow]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, Nat.choose]
  ring_nf

private lemma putnam_1981_b1_sum_sq (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ 2) =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  have hq := congrArg (fun x : ℚ => (x : ℝ)) (putnam_1981_b1_sum_sq_rat n)
  norm_num at hq
  simpa using hq

private lemma putnam_1981_b1_sum_four (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ 4) =
      (n : ℝ) * (n + 1) * (2 * n + 1) * (3 * (n : ℝ)^2 + 3 * n - 1) / 30 := by
  have hq := congrArg (fun x : ℚ => (x : ℝ)) (putnam_1981_b1_sum_four_rat n)
  norm_num at hq
  simpa using hq

private lemma putnam_1981_b1_double_sum (n : ℕ) :
    (∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
      (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4)) =
    10 * (n : ℝ) * (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^4) -
      18 * (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^2)^2 := by
  have hmixed :
      (∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (h : ℝ)^2 * (k : ℝ)^2 * 18) =
      (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^2)^2 * 18 := by
    calc
      (∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (h : ℝ)^2 * (k : ℝ)^2 * 18)
          = ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
              (h : ℝ)^2 * ((k : ℝ)^2 * 18) := by
              apply Finset.sum_congr rfl
              intro h hh
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^2) *
            (∑ k ∈ Finset.Icc 1 n, (k : ℝ)^2 * 18) := by
              rw [Finset.sum_mul_sum]
      _ = (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^2)^2 * 18 := by
              rw [← Finset.sum_mul]
              ring
  have h5 :
      (∑ h ∈ Finset.Icc 1 n, (n : ℝ) * (5 * (h : ℝ)^4)) =
      5 * (n : ℝ) * (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^4) := by
    calc
      (∑ h ∈ Finset.Icc 1 n, (n : ℝ) * (5 * (h : ℝ)^4))
          = ∑ h ∈ Finset.Icc 1 n, (5 * (n : ℝ)) * (h : ℝ)^4 := by
              apply Finset.sum_congr rfl
              intro h hh
              ring
      _ = 5 * (n : ℝ) * (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^4) := by
              rw [← Finset.mul_sum]
  have h10 :
      (∑ h ∈ Finset.Icc 1 n, 10 * (n : ℝ) * (h : ℝ)^4) =
      10 * (n : ℝ) * (∑ h ∈ Finset.Icc 1 n, (h : ℝ)^4) := by
    rw [← Finset.mul_sum]
  simp_rw [show ∀ h k : ℕ,
    (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4) =
      5*(h : ℝ)^4 - ((h : ℝ)^2 * (k : ℝ)^2 * 18) + 5*((k : ℝ)^4) by
      intro h k; ring]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hmixed]
  simp [Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
  rw [h5, h10]
  ring

private lemma putnam_1981_b1_eventual_formula {n : ℕ} (hn : 0 < n) :
    ((1 : ℝ) / n^5) * ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
      (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4) =
    -1 - (19 / 6 : ℝ) * (1 / (n : ℝ)) - 3 * (1 / (n : ℝ))^2 -
      (5 / 6 : ℝ) * (1 / (n : ℝ))^3 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [putnam_1981_b1_double_sum, putnam_1981_b1_sum_four, putnam_1981_b1_sum_sq]
  field_simp [hn0]
  ring

/--
Find the value of $$\lim_{n \rightarrow \infty} \frac{1}{n^5}\sum_{h=1}^{n}\sum_{k=1}^{n}(5h^4 - 18h^2k^2 + 5k^4).$$
-/
theorem putnam_1981_b1
(f : ℕ → ℝ)
(hf : f = fun n : ℕ => ((1 : ℝ)/n^5) * ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4))
: Tendsto f atTop (𝓝 putnam_1981_b1_solution) :=
by
  rw [hf]
  have hlim :
      Tendsto (fun n : ℕ =>
        (-1 : ℝ) - (19 / 6 : ℝ) * (1 / (n : ℝ)) - 3 * (1 / (n : ℝ))^2 -
          (5 / 6 : ℝ) * (1 / (n : ℝ))^3) atTop (𝓝 (-1)) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using
      (((tendsto_const_nhds.sub (hbase.const_mul (19 / 6 : ℝ))).sub
        ((hbase.pow 2).const_mul (3 : ℝ))).sub
        ((hbase.pow 3).const_mul (5 / 6 : ℝ)))
  have hformula :
      (fun n : ℕ => ((1 : ℝ)/n^5) * ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
        (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4)) =ᶠ[atTop]
      (fun n : ℕ =>
        (-1 : ℝ) - (19 / 6 : ℝ) * (1 / (n : ℝ)) - 3 * (1 / (n : ℝ))^2 -
          (5 / 6 : ℝ) * (1 / (n : ℝ))^3) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => lt_of_lt_of_le Nat.zero_lt_one hn⟩]
      with n hn
    exact putnam_1981_b1_eventual_formula hn
  simpa [putnam_1981_b1_solution] using hlim.congr' hformula.symm
