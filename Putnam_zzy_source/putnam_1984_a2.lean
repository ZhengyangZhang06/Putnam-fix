import Mathlib

abbrev putnam_1984_a2_solution : ℚ := (1 - (2 : ℚ) / 3)⁻¹ - (1 : ℚ)⁻¹

/--
Express $\sum_{k=1}^\infty (6^k/(3^{k+1}-2^{k+1})(3^k-2^k))$ as a rational number.
-/
theorem putnam_1984_a2
: ∑' k : Set.Ici 1, ((6 : ℝ) ^ (k : ℕ) / ((3 ^ ((k : ℕ) + 1) - 2 ^ ((k : ℕ) + 1)) * (3 ^ (k : ℕ) - 2 ^ (k : ℕ)))) = putnam_1984_a2_solution :=
by
  let e : ℕ ≃ Set.Ici (1 : ℕ) :=
    { toFun := fun n => ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩
      invFun := fun k => k.1 - 1
      left_inv := by
        intro n
        simp
      right_inv := by
        intro k
        ext
        exact Nat.sub_add_cancel k.2 }
  rw [← e.tsum_eq (fun k : Set.Ici (1 : ℕ) =>
    ((6 : ℝ) ^ (k : ℕ) /
      ((3 ^ ((k : ℕ) + 1) - 2 ^ ((k : ℕ) + 1)) *
        (3 ^ (k : ℕ) - 2 ^ (k : ℕ)))))]
  let q : ℝ := (2 : ℝ) / 3
  let g : ℕ → ℝ := fun n => (1 - q ^ (n + 1))⁻¹ - (1 - q ^ ((n + 1) + 1))⁻¹
  have htel (k : ℕ) (hk : k ≠ 0) :
      (6 : ℝ) ^ k / ((3 ^ (k + 1) - 2 ^ (k + 1)) * (3 ^ k - 2 ^ k)) =
        (1 - ((2 : ℝ) / 3) ^ k)⁻¹ - (1 - ((2 : ℝ) / 3) ^ (k + 1))⁻¹ := by
    have hpow (m : ℕ) (hm : m ≠ 0) : (3 : ℝ) ^ m - 2 ^ m ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr
        (pow_lt_pow_left₀ (by norm_num : (2 : ℝ) < 3) (by norm_num : (0 : ℝ) ≤ 2) hm))
    have hq (m : ℕ) (hm : m ≠ 0) : 1 - ((2 : ℝ) / 3) ^ m ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr
        (pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 3)
          (by norm_num : ((2 : ℝ) / 3) < 1) hm))
    field_simp [hpow k hk, hpow (k + 1) (by omega), hq k hk, hq (k + 1) (by omega)]
    rw [div_pow, div_pow, show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]
    field_simp [pow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0),
      pow_ne_zero (k * 2) (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hpoint : ∀ n : ℕ,
      ((6 : ℝ) ^ (e n : ℕ) /
        ((3 ^ ((e n : ℕ) + 1) - 2 ^ ((e n : ℕ) + 1)) *
          (3 ^ (e n : ℕ) - 2 ^ (e n : ℕ)))) = g n := by
    intro n
    simpa [e, g, q, add_comm, add_left_comm, add_assoc] using htel (n + 1) (by omega)
  have hg : HasSum g (2 : ℝ) := by
    have hnonneg : ∀ i, 0 ≤ g i := by
      intro i
      have hq0 : 0 ≤ q := by norm_num [q]
      have hq1 : q < 1 := by norm_num [q]
      have hqle : q ≤ 1 := hq1.le
      have hpow_le : q ^ ((i + 1) + 1) ≤ q ^ (i + 1) := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hq0 (i + 1)) hqle
      have hden_le : 1 - q ^ (i + 1) ≤ 1 - q ^ ((i + 1) + 1) := by linarith
      have hden1 : 0 < 1 - q ^ (i + 1) := by
        exact sub_pos.mpr (pow_lt_one₀ hq0 hq1 (by omega))
      have hden2 : 0 < 1 - q ^ ((i + 1) + 1) := by
        exact sub_pos.mpr (pow_lt_one₀ hq0 hq1 (by omega))
      have hinv_le : (1 - q ^ ((i + 1) + 1))⁻¹ ≤ (1 - q ^ (i + 1))⁻¹ := by
        exact (inv_le_inv₀ hden2 hden1).2 hden_le
      exact sub_nonneg.mpr hinv_le
    refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg 2).2 ?_
    have hpow : Filter.Tendsto (fun n : ℕ => q ^ (n + 1)) Filter.atTop (nhds 0) := by
      have hbase : Filter.Tendsto (fun n : ℕ => q ^ n) Filter.atTop (nhds 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num [q] : 0 ≤ q) (by norm_num [q] : q < 1)
      exact hbase.comp (Filter.tendsto_add_atTop_nat 1)
    have hinv : Filter.Tendsto (fun n : ℕ => (1 - q ^ (n + 1))⁻¹) Filter.atTop
        (nhds 1) := by
      have hden : Filter.Tendsto (fun n : ℕ => 1 - q ^ (n + 1)) Filter.atTop
          (nhds (1 : ℝ)) := by
        simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow)
      simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hlim : Filter.Tendsto
        (fun n : ℕ => (3 : ℝ) - (1 - q ^ (n + 1))⁻¹) Filter.atTop (nhds 2) := by
      convert ((tendsto_const_nhds (x := (3 : ℝ))).sub hinv) using 1
      norm_num
    convert hlim using 1
    ext n
    calc
      ∑ i ∈ Finset.range n, g i = (1 - q)⁻¹ - (1 - q ^ (n + 1))⁻¹ := by
        have h := Finset.sum_range_sub (fun m : ℕ => -((1 - q ^ (m + 1))⁻¹)) n
        simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      _ = 3 - (1 - q ^ (n + 1))⁻¹ := by
        norm_num [q]
  have hmain : HasSum (fun n : ℕ =>
      ((6 : ℝ) ^ (e n : ℕ) /
        ((3 ^ ((e n : ℕ) + 1) - 2 ^ ((e n : ℕ) + 1)) *
          (3 ^ (e n : ℕ) - 2 ^ (e n : ℕ))))) (2 : ℝ) := by
    exact hg.congr_fun hpoint
  rw [hmain.tsum_eq]
  norm_num [putnam_1984_a2_solution]
