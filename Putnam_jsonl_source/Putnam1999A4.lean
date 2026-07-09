import Mathlib

open Filter Topology Metric

-- Note: This is done assuming that the series converges, otherwise it is unclear in which order to sum. The problem statement assumes convergence.
-- 9/32
/--
Sum the series \[\sum_{m=1}^\infty \sum_{n=1}^\infty \frac{m^2 n}{3^m(n3^m+m3^n)}.\]
-/
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 ((9/32) : ℝ )) := by
  let x : ℕ → ℝ := fun k => (k + 1 : ℝ) / (3 : ℝ) ^ (k + 1)
  let A : ℕ × ℕ → ℝ := fun p => x p.1 ^ 2 * x p.2 / (x p.1 + x p.2)
  let T : ℕ → ℕ → ℝ := fun m n =>
    (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
  have hx_pos : ∀ n, 0 < x n := by
    intro n
    dsimp [x]
    positivity
  have hx_nonneg : ∀ n, 0 ≤ x n := fun n => (hx_pos n).le
  have hT_eq_A : ∀ m n, T m n = A (m, n) := by
    intro m n
    have hsum : x m + x n ≠ 0 := by
      apply ne_of_gt
      exact add_pos (hx_pos m) (hx_pos n)
    dsimp [T, A, x]
    field_simp
    ring
  let f : ℕ → ℝ := fun n => (n : ℝ) * (1 / 3 : ℝ) ^ n
  have hr : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have hf : Summable f := by
    simpa [f] using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)
  have hx_eq : x = fun n => f (n + 1) := by
    funext n
    dsimp [x, f]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  have hx_summable : Summable x := by
    rw [hx_eq]
    exact (summable_nat_add_iff 1).2 hf
  have htsum_f : (∑' n, f n) = (3 / 4 : ℝ) := by
    calc
      (∑' n, f n) = (∑' n : ℕ, (n : ℝ) * (1 / 3 : ℝ) ^ n) := rfl
      _ = (1 / 3 : ℝ) / (1 - (1 / 3 : ℝ)) ^ 2 := by
        exact tsum_coe_mul_geometric_of_norm_lt_one hr
      _ = (3 / 4 : ℝ) := by norm_num
  have hx_tsum : (∑' n, x n) = (3 / 4 : ℝ) := by
    rw [hx_eq]
    have h0 : (∑ i ∈ Finset.range 1, f i) = 0 := by simp [f]
    have hshift := hf.sum_add_tsum_nat_add 1
    rw [h0, zero_add] at hshift
    exact hshift.trans htsum_f
  have hB_summable : Summable (fun p : ℕ × ℕ => x p.1 * x p.2) := by
    exact hx_summable.mul_of_nonneg hx_summable hx_nonneg hx_nonneg
  have hB_tsum : (∑' p : ℕ × ℕ, x p.1 * x p.2) = (9 / 16 : ℝ) := by
    calc
      (∑' p : ℕ × ℕ, x p.1 * x p.2) = (∑' n, x n) * (∑' n, x n) := by
        exact (hx_summable.tsum_mul_tsum hx_summable hB_summable).symm
      _ = (3 / 4 : ℝ) * (3 / 4 : ℝ) := by rw [hx_tsum]
      _ = (9 / 16 : ℝ) := by norm_num
  have hA_nonneg : ∀ p : ℕ × ℕ, 0 ≤ A p := by
    intro p
    dsimp [A]
    positivity
  have hA_le_B : ∀ p : ℕ × ℕ, A p ≤ x p.1 * x p.2 := by
    intro p
    have hden_pos : 0 < x p.1 + x p.2 := add_pos (hx_pos p.1) (hx_pos p.2)
    have hx1_nonneg : 0 ≤ x p.1 := hx_nonneg p.1
    have hx2_nonneg : 0 ≤ x p.2 := hx_nonneg p.2
    dsimp [A]
    field_simp [hden_pos.ne']
    nlinarith [mul_nonneg hx1_nonneg (mul_nonneg hx2_nonneg hx2_nonneg)]
  have hA_summable : Summable A :=
    Summable.of_nonneg_of_le hA_nonneg hA_le_B hB_summable
  have hpair : ∀ p : ℕ × ℕ, A p + A (Prod.swap p) = x p.1 * x p.2 := by
    intro p
    have hsum : x p.1 + x p.2 ≠ 0 := by
      apply ne_of_gt
      exact add_pos (hx_pos p.1) (hx_pos p.2)
    dsimp [A]
    field_simp [hsum, add_comm]
    ring
  have hA_swap_summable : Summable (fun p : ℕ × ℕ => A (Prod.swap p)) :=
    hA_summable.prod_symm
  have hswap_tsum : (∑' p : ℕ × ℕ, A (Prod.swap p)) = (∑' p : ℕ × ℕ, A p) := by
    simpa using (Equiv.prodComm ℕ ℕ).tsum_eq A
  have htwoA : 2 * (∑' p : ℕ × ℕ, A p) = (9 / 16 : ℝ) := by
    calc
      2 * (∑' p : ℕ × ℕ, A p)
          = (∑' p : ℕ × ℕ, A p) + (∑' p : ℕ × ℕ, A p) := by ring
      _ = (∑' p : ℕ × ℕ, A p) + (∑' p : ℕ × ℕ, A (Prod.swap p)) := by rw [hswap_tsum]
      _ = (∑' p : ℕ × ℕ, (A p + A (Prod.swap p))) := by
        exact (hA_summable.tsum_add hA_swap_summable).symm
      _ = (∑' p : ℕ × ℕ, x p.1 * x p.2) := by
        exact tsum_congr hpair
      _ = (9 / 16 : ℝ) := hB_tsum
  have hA_tsum : (∑' p : ℕ × ℕ, A p) = (9 / 32 : ℝ) := by
    nlinarith
  have hrows_tsum : (∑' m : ℕ, ∑' n : ℕ, A (m, n)) = (9 / 32 : ℝ) := by
    exact (hA_summable.tsum_prod).symm.trans hA_tsum
  have hrows_hasSum : HasSum (fun m : ℕ => ∑' n : ℕ, A (m, n)) (9 / 32 : ℝ) := by
    have hrow_summable : Summable (fun m : ℕ => ∑' n : ℕ, A (m, n)) := hA_summable.prod
    rw [← hrows_tsum]
    exact hrow_summable.hasSum
  have hT_hasSum : HasSum (fun m : ℕ => ∑' n : ℕ, T m n) (9 / 32 : ℝ) := by
    refine hrows_hasSum.congr_fun ?_
    intro m
    exact tsum_congr (hT_eq_A m)
  simpa [T] using hT_hasSum.tendsto_sum_nat
