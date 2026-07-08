import Mathlib

open Filter Topology Metric

noncomputable abbrev putnam_1999_a4_solution : ℝ := 9 / 32

/--
Sum the series \[\sum_{m=1}^\infty \sum_{n=1}^\infty \frac{m^2 n}{3^m(n3^m+m3^n)}.\]
-/
theorem putnam_1999_a4
: Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)) atTop (𝓝 putnam_1999_a4_solution) :=
by
  let x : ℕ → ℝ := fun k => ((k : ℝ) + 1) / (3 : ℝ) ^ (k + 1)
  let f : ℕ × ℕ → ℝ := fun p => x p.1 ^ 2 * x p.2 / (x p.1 + x p.2)
  have hx_pos : ∀ k, 0 < x k := by
    intro k
    dsimp [x]
    positivity
  have hx_nonneg : ∀ k, 0 ≤ x k := fun k => le_of_lt (hx_pos k)
  have hx_summable : Summable x := by
    let y : ℕ → ℝ := fun n => (n : ℝ) * (1 / 3 : ℝ) ^ n
    have hy : Summable y := by
      simpa [y] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / 3 : ℝ)) (by norm_num))
    have hshift : Summable (fun n => y (n + 1)) :=
      (summable_nat_add_iff (G := ℝ) (f := y) 1).2 hy
    convert hshift using 1
    ext n
    simp [x, y, div_eq_mul_inv, pow_succ]
  have hx_tsum : (∑' k : ℕ, x k) = 3 / 4 := by
    let y : ℕ → ℝ := fun n => (n : ℝ) * (1 / 3 : ℝ) ^ n
    have hy : Summable y := by
      simpa [y] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / 3 : ℝ)) (by norm_num))
    have hy_tsum : (∑' n : ℕ, y n) = 3 / 4 := by
      have h := tsum_coe_mul_geometric_of_norm_lt_one (r := (1 / 3 : ℝ)) (by norm_num)
      norm_num at h ⊢
      simpa [y] using h
    have hshift_tsum : (∑' n : ℕ, y (n + 1)) = 3 / 4 := by
      have hzeroadd := hy.tsum_eq_zero_add
      rw [hy_tsum] at hzeroadd
      simpa [y] using hzeroadd.symm
    calc
      (∑' k : ℕ, x k) = ∑' n : ℕ, y (n + 1) := by
        apply tsum_congr
        intro n
        simp [x, y, div_eq_mul_inv, pow_succ]
      _ = 3 / 4 := hshift_tsum
  have hterm : ∀ m n : ℕ,
      (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ)
        = f (m, n) := by
    intro m n
    dsimp [f, x]
    field_simp [pow_succ]
    ring
  have hf_nonneg : ∀ p : ℕ × ℕ, 0 ≤ f p := by
    intro p
    dsimp [f]
    positivity
  have hf_le : ∀ p : ℕ × ℕ, f p ≤ x p.1 * x p.2 := by
    intro p
    have hx1 : 0 ≤ x p.1 := hx_nonneg p.1
    have hx2 : 0 ≤ x p.2 := hx_nonneg p.2
    have hspos : 0 < x p.1 + x p.2 := add_pos (hx_pos p.1) (hx_pos p.2)
    dsimp [f]
    rw [div_le_iff₀ hspos]
    nlinarith [mul_nonneg hx1 hx2, mul_nonneg (sq_nonneg (x p.1)) hx2]
  have hprod_summable : Summable (fun p : ℕ × ℕ => x p.1 * x p.2) :=
    hx_summable.mul_of_nonneg hx_summable hx_nonneg hx_nonneg
  have hf_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hf_le hprod_summable
  have hswap_tsum : (∑' p : ℕ × ℕ, f p.swap) = ∑' p : ℕ × ℕ, f p := by
    simpa using (Equiv.prodComm ℕ ℕ).tsum_eq f
  have hpair : ∀ p : ℕ × ℕ, f p + f p.swap = x p.1 * x p.2 := by
    intro p
    have hx1 : 0 < x p.1 := hx_pos p.1
    have hx2 : 0 < x p.2 := hx_pos p.2
    have hsum : x p.1 + x p.2 ≠ 0 := ne_of_gt (add_pos hx1 hx2)
    dsimp [f]
    field_simp [hsum, add_comm]
    ring
  have hprod_tsum : (∑' p : ℕ × ℕ, x p.1 * x p.2) = (3 / 4) * (3 / 4) := by
    calc
      (∑' p : ℕ × ℕ, x p.1 * x p.2) = (∑' k : ℕ, x k) * (∑' k : ℕ, x k) := by
        exact (hx_summable.tsum_mul_tsum hx_summable hprod_summable).symm
      _ = (3 / 4) * (3 / 4) := by rw [hx_tsum]
  have hf_tsum : (∑' p : ℕ × ℕ, f p) = 9 / 32 := by
    have hf_swap_summable : Summable (fun p : ℕ × ℕ => f p.swap) := hf_summable.prod_symm
    have htwo : 2 * (∑' p : ℕ × ℕ, f p) = ∑' p : ℕ × ℕ, x p.1 * x p.2 := by
      calc
        2 * (∑' p : ℕ × ℕ, f p)
            = (∑' p : ℕ × ℕ, f p) + (∑' p : ℕ × ℕ, f p.swap) := by
              rw [hswap_tsum]
              ring
        _ = ∑' p : ℕ × ℕ, (f p + f p.swap) := by
              exact (hf_summable.tsum_add hf_swap_summable).symm
        _ = ∑' p : ℕ × ℕ, x p.1 * x p.2 := tsum_congr hpair
    rw [hprod_tsum] at htwo
    nlinarith
  have hrow_summable : Summable (fun m : ℕ => ∑' n : ℕ, f (m, n)) := hf_summable.prod
  have hrow_tsum : (∑' m : ℕ, ∑' n : ℕ, f (m, n)) = 9 / 32 := by
    rw [← hf_summable.tsum_prod, hf_tsum]
  have hlim : Tendsto (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, f (m, n)) atTop (𝓝 (9 / 32)) := by
    simpa [hrow_tsum] using hrow_summable.hasSum.tendsto_sum_nat
  have hfun :
      (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ,
        (((m + 1)^2*(n+1))/(3^(m + 1) * ((n+1)*3^(m + 1) + (m + 1)*3^(n+1))) : ℝ))
      = (fun i => ∑ m ∈ Finset.range i, ∑' n : ℕ, f (m, n)) := by
    funext i
    apply Finset.sum_congr rfl
    intro m hm
    apply tsum_congr
    intro n
    exact hterm m n
  rw [hfun]
  simpa [putnam_1999_a4_solution] using hlim
