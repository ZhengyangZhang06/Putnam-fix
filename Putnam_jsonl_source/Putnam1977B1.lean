import Mathlib

open RingHom Set Nat Filter Topology

-- 2 / 3
/--
Find $\prod_{n=2}^{\infty} \frac{(n^3 - 1)}{(n^3 + 1)}$.
-/
theorem putnam_1977_b1
: Tendsto (fun N ↦ ∏ n ∈ Finset.Icc (2 : ℤ) N, ((n : ℝ) ^ 3 - 1) / (n ^ 3 + 1)) atTop (𝓝 ((2 / 3) : ℝ )) := by
  have hprod : ∀ N : ℤ, (2 : ℤ) ≤ N →
      (∏ n ∈ Finset.Icc (2 : ℤ) N, ((n : ℝ) ^ 3 - 1) / (n ^ 3 + 1)) =
        (2 * ((N : ℝ) ^ 2 + (N : ℝ) + 1)) / (3 * (N : ℝ) * ((N : ℝ) + 1)) := by
    intro N hN
    induction N, hN using Int.le_induction with
    | base =>
        norm_num
    | succ N hN ih =>
        have hsucc : (2 : ℤ) ≤ Order.succ N := by
          simpa [Order.succ_eq_add_one] using (show (2 : ℤ) ≤ N + 1 by omega)
        rw [← Order.succ_eq_add_one N]
        rw [← Finset.insert_Icc_right_eq_Icc_succ (a := (2 : ℤ)) (b := N) hsucc]
        rw [Finset.prod_insert]
        · rw [ih]
          simp only [Order.succ_eq_add_one, Int.cast_add, Int.cast_one]
          have hN0 : (N : ℝ) ≠ 0 := by
            norm_cast
            omega
          have hN1 : (N : ℝ) + 1 ≠ 0 := by
            norm_cast
            omega
          have hN2 : (N : ℝ) + 2 ≠ 0 := by
            norm_cast
            omega
          have hden : ((N : ℝ) + 1) ^ 3 + 1 ≠ 0 := by
            have hpos : 0 < (N : ℝ) + 1 := by
              norm_cast
              omega
            positivity
          field_simp [hN0, hN1, hN2, hden]
          ring
        · simp [Finset.mem_Icc, Order.succ_eq_add_one]
  have hlim : Tendsto (fun N : ℤ ↦
      (2 * ((N : ℝ) ^ 2 + (N : ℝ) + 1)) / (3 * (N : ℝ) * ((N : ℝ) + 1)))
      atTop (𝓝 ((2 / 3) : ℝ)) := by
    have hcast : Tendsto (fun N : ℤ ↦ (N : ℝ)) atTop atTop := tendsto_intCast_atTop_atTop
    have hcast1 : Tendsto (fun N : ℤ ↦ (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) hcast
    have hmul : Tendsto (fun N : ℤ ↦ (N : ℝ) * ((N : ℝ) + 1)) atTop atTop :=
      hcast.atTop_mul_atTop₀ hcast1
    have hden : Tendsto (fun N : ℤ ↦ (3 : ℝ) * ((N : ℝ) * ((N : ℝ) + 1))) atTop atTop :=
      hmul.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
    have herr : Tendsto (fun N : ℤ ↦
        (2 : ℝ) / ((3 : ℝ) * ((N : ℝ) * ((N : ℝ) + 1)))) atTop (𝓝 0) :=
      hden.const_div_atTop (2 : ℝ)
    have hsum : Tendsto (fun N : ℤ ↦
        (2 : ℝ) / 3 + (2 : ℝ) / ((3 : ℝ) * ((N : ℝ) * ((N : ℝ) + 1))))
        atTop (𝓝 ((2 : ℝ) / 3 + 0)) :=
      tendsto_const_nhds.add herr
    have hcongr : (fun N : ℤ ↦
        (2 * ((N : ℝ) ^ 2 + (N : ℝ) + 1)) / (3 * (N : ℝ) * ((N : ℝ) + 1)))
        =ᶠ[atTop] (fun N : ℤ ↦
          (2 : ℝ) / 3 + (2 : ℝ) / ((3 : ℝ) * ((N : ℝ) * ((N : ℝ) + 1)))) := by
      filter_upwards [eventually_ge_atTop (2 : ℤ)] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by
        norm_cast
        omega
      have hN1 : (N : ℝ) + 1 ≠ 0 := by
        norm_cast
        omega
      field_simp [hN0, hN1]
    refine Tendsto.congr' hcongr.symm ?_
    simpa using hsum
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop (2 : ℤ)] with N hN
  exact (hprod N hN).symm
