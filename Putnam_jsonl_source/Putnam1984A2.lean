import Mathlib

-- 2
/--
Express $\sum_{k=1}^\infty (6^k/(3^{k+1}-2^{k+1})(3^k-2^k))$ as a rational number.
-/
theorem putnam_1984_a2
: ∑' k : Set.Ici 1, (6 ^ (k : ℕ) / ((3 ^ ((k : ℕ) + 1) - 2 ^ ((k : ℕ) + 1)) * (3 ^ (k : ℕ) - 2 ^ (k : ℕ)))) = ((2) : ℚ ) := by
  let e : ℕ ≃ Set.Ici (1 : ℕ) :=
  { toFun := fun n => ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩
    invFun := fun k => k.1 - 1
    left_inv := by
      intro n
      exact Nat.add_sub_cancel n 1
    right_inv := by
      intro k
      ext
      exact Nat.sub_add_cancel k.2 }
  let fQ : Set.Ici (1 : ℕ) → ℚ := fun k =>
    (6 ^ (k : ℕ) /
      ((3 ^ ((k : ℕ) + 1) - 2 ^ ((k : ℕ) + 1)) * (3 ^ (k : ℕ) - 2 ^ (k : ℕ))))
  let fNQ : ℕ → ℚ := fQ ∘ e
  let g : ℕ → ℝ := fun n =>
    (6 : ℝ) ^ (n + 1) /
      (((3 : ℝ) ^ ((n + 1) + 1) - 2 ^ ((n + 1) + 1)) *
        ((3 : ℝ) ^ (n + 1) - 2 ^ (n + 1)))
  let A : ℕ → ℝ := fun n =>
    (3 : ℝ) ^ (n + 1) / ((3 : ℝ) ^ (n + 1) - 2 ^ (n + 1))
  have hcast : ∀ n, ((fNQ n : ℚ) : ℝ) = g n := by
    intro n
    simp [fNQ, fQ, e, g, Rat.cast_pow, Rat.cast_div, Rat.cast_sub, Rat.cast_mul]
  have hterm : ∀ n, g n = A n - A (n + 1) := by
    intro n
    have hk : n + 1 ≠ 0 := by omega
    have h32k : (3 : ℝ) ^ (n + 1) - 2 ^ (n + 1) ≠ 0 := by
      have hlt : (2 : ℝ) ^ (n + 1) < 3 ^ (n + 1) :=
        pow_lt_pow_left₀ (by norm_num) (by norm_num) hk
      exact ne_of_gt (sub_pos.mpr hlt)
    have h32ks : (3 : ℝ) ^ ((n + 1) + 1) - 2 ^ ((n + 1) + 1) ≠ 0 := by
      have hks : (n + 1) + 1 ≠ 0 := by omega
      have hlt : (2 : ℝ) ^ ((n + 1) + 1) < 3 ^ ((n + 1) + 1) :=
        pow_lt_pow_left₀ (by norm_num) (by norm_num) hks
      exact ne_of_gt (sub_pos.mpr hlt)
    dsimp [g, A]
    field_simp [h32k, h32ks]
    rw [show (6 : ℝ) ^ (n + 1) = 2 ^ (n + 1) * 3 ^ (n + 1) by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]]
    rw [pow_succ, pow_succ]
    ring
  have hnonneg : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g]
    have hnum : 0 ≤ (6 : ℝ) ^ (n + 1) := pow_nonneg (by norm_num) _
    have hden₁ : 0 < (3 : ℝ) ^ ((n + 1) + 1) - 2 ^ ((n + 1) + 1) := by
      have hks : (n + 1) + 1 ≠ 0 := by omega
      exact sub_pos.mpr (pow_lt_pow_left₀ (by norm_num : (2 : ℝ) < 3) (by norm_num) hks)
    have hden₂ : 0 < (3 : ℝ) ^ (n + 1) - 2 ^ (n + 1) := by
      have hk : n + 1 ≠ 0 := by omega
      exact sub_pos.mpr (pow_lt_pow_left₀ (by norm_num : (2 : ℝ) < 3) (by norm_num) hk)
    exact div_nonneg hnum (le_of_lt (mul_pos hden₁ hden₂))
  have hA_as_B : ∀ n,
      A n = (1 - ((2 : ℝ) / 3) ^ (n + 1))⁻¹ := by
    intro n
    have hk : n + 1 ≠ 0 := by omega
    have h3 : (3 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h32 : (3 : ℝ) ^ (n + 1) - 2 ^ (n + 1) ≠ 0 := by
      have hlt : (2 : ℝ) ^ (n + 1) < 3 ^ (n + 1) :=
        pow_lt_pow_left₀ (by norm_num) (by norm_num) hk
      exact ne_of_gt (sub_pos.mpr hlt)
    have h1 : 1 - ((2 : ℝ) / 3) ^ (n + 1) ≠ 0 := by
      have hlt : ((2 : ℝ) / 3) ^ (n + 1) < 1 := by
        have hpow : ((2 : ℝ) / 3) ^ (n + 1) < (1 : ℝ) ^ (n + 1) :=
          pow_lt_pow_left₀ (by norm_num) (by norm_num) hk
        simpa using hpow
      exact ne_of_gt (sub_pos.mpr hlt)
    dsimp [A]
    field_simp [h3, h32, h1]
    rw [div_pow]
    field_simp [h3]
  have hA_tendsto : Filter.Tendsto A Filter.atTop (nhds (1 : ℝ)) := by
    have hpow :
        Filter.Tendsto (fun n : ℕ => ((2 : ℝ) / 3) ^ (n + 1)) Filter.atTop
          (nhds (0 : ℝ)) := by
      have hbase : ‖((2 : ℝ) / 3)‖ < 1 := by norm_num
      simpa [Function.comp_def] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hbase).comp (Filter.tendsto_add_atTop_nat 1)
    have hB :
        Filter.Tendsto (fun n : ℕ => (1 - ((2 : ℝ) / 3) ^ (n + 1))⁻¹) Filter.atTop
          (nhds (1 : ℝ)) := by
      have hden :
          Filter.Tendsto (fun n : ℕ => 1 - ((2 : ℝ) / 3) ^ (n + 1)) Filter.atTop
            (nhds ((1 : ℝ) - 0)) :=
        tendsto_const_nhds.sub hpow
      simpa using hden.inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    exact Filter.Tendsto.congr (fun n => (hA_as_B n).symm) hB
  have hsum : ∀ N, ∑ i ∈ Finset.range N, g i = A 0 - A N := by
    intro N
    calc
      ∑ i ∈ Finset.range N, g i = ∑ i ∈ Finset.range N, (A i - A (i + 1)) := by
        exact Finset.sum_congr rfl (fun i _ => hterm i)
      _ = A 0 - A N := Finset.sum_range_sub' A N
  have hg : HasSum g (2 : ℝ) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg (2 : ℝ)).mpr ?_
    have hlim : Filter.Tendsto (fun N : ℕ => A 0 - A N) Filter.atTop (nhds (2 : ℝ)) := by
      have h := Filter.Tendsto.const_sub (A 0) hA_tendsto
      convert h using 1
      norm_num [A]
    exact Filter.Tendsto.congr (fun N => (hsum N).symm) hlim
  have hReal : HasSum (fun n : ℕ => ((fNQ n : ℚ) : ℝ)) (2 : ℝ) :=
    hg.congr_fun hcast
  have hQNat : HasSum fNQ (2 : ℚ) := by
    exact (Rat.isUniformEmbedding_coe_real.isInducing.hasSum_iff (g := Rat.castHom ℝ) fNQ (2 : ℚ)).mp
      (by simpa [Function.comp_def] using hReal)
  have hQSub : HasSum fQ (2 : ℚ) := (e.hasSum_iff).mp hQNat
  simpa [fQ] using hQSub.tsum_eq
