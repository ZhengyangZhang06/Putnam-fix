import Mathlib

open Set Function Metric

-- 1
/--
Let $N$ be the positive integer with 1998 decimal digits, all of them 1; that is, \[N=1111\cdots 11.\] Find the thousandth digit after the decimal point of $\sqrt N$.
-/
theorem putnam_1998_b5
(N : ℕ)
(hN : N = ∑ i ∈ Finset.range 1998, 10^i)
: ((1) : ℕ ) = (Nat.floor (10^1000 * Real.sqrt N)) % 10 := by
  let A : ℕ := ((10 : ℕ) ^ 1999 - 7) / 3
  have hNreal : (N : ℝ) = ∑ i ∈ Finset.range 1998, (10 : ℝ) ^ i := by
    rw [hN]
    exact_mod_cast rfl
  have hN9 : (N : ℝ) * 9 = (10 : ℝ) ^ 1998 - 1 := by
    rw [hNreal]
    have hgeom := geom_sum_mul (x := (10 : ℝ)) 1998
    norm_num at hgeom
    simpa [mul_comm] using hgeom
  have hA_dvd : 3 ∣ (10 : ℕ) ^ 1999 - 7 := by
    let P : ℕ := (10 : ℕ) ^ 1999
    change 3 ∣ P - 7
    have hP : 7 ≤ P := by
      dsimp [P]
      exact le_trans (by norm_num : 7 ≤ (10 : ℕ) ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 1999))
    have h9dvd : 9 ∣ P - 1 := by
      change 9 ∣ (10 : ℕ) ^ 1999 - 1
      simpa using ((10 : ℕ).sub_one_dvd_pow_sub_one 1999)
    have h3dvd1 : 3 ∣ P - 1 := dvd_trans (by norm_num : 3 ∣ 9) h9dvd
    have h3dvd6 : 3 ∣ (6 : ℕ) := by norm_num
    have h := Nat.dvd_sub h3dvd1 h3dvd6
    rwa [show P - 7 = (P - 1) - 6 by omega]
  have hA3nat : 3 * A = (10 : ℕ) ^ 1999 - 7 := by
    dsimp [A]
    exact Nat.mul_div_cancel' hA_dvd
  have hA3 : (3 : ℝ) * (A : ℝ) = (10 : ℝ) ^ 1999 - 7 := by
    have hpow : 7 ≤ (10 : ℕ) ^ 1999 := by
      exact le_trans (by norm_num : 7 ≤ (10 : ℕ) ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 1999))
    have hcast : ((3 * A : ℕ) : ℝ) = (((10 : ℕ) ^ 1999 - 7 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hA3nat
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat] at hcast
    exact hcast
  have hA3succ : (3 : ℝ) * ((A : ℝ) + 1) = (10 : ℝ) ^ 1999 - 4 := by
    have h : (3 : ℕ) * (A + 1) = (10 : ℕ) ^ 1999 - 4 := by
      have hpow : 7 ≤ (10 : ℕ) ^ 1999 := by
        exact le_trans (by norm_num : 7 ≤ (10 : ℕ) ^ 1)
          (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 1999))
      omega
    have hpow : 4 ≤ (10 : ℕ) ^ 1999 := by
      exact le_trans (by norm_num : 4 ≤ (10 : ℕ) ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 1999))
    have hcast : (((3 : ℕ) * (A + 1) : ℕ) : ℝ) =
        (((10 : ℕ) ^ 1999 - 4 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) h
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sub hpow,
      Nat.cast_pow, Nat.cast_ofNat] at hcast
    exact hcast
  have hpowprod :
      ((10 : ℝ) ^ 1000) ^ 2 * ((10 : ℝ) ^ 1998 - 1) =
        ((10 : ℝ) ^ 1999) ^ 2 - 10 * (10 : ℝ) ^ 1999 := by
    have h1999 : (10 : ℝ) ^ 1999 = 10 * (10 : ℝ) ^ 1998 := by
      rw [show 1999 = 1 + 1998 by norm_num, pow_add]
      ring
    have h2000 : (10 : ℝ) ^ 2000 = 10 * (10 : ℝ) ^ 1999 := by
      rw [show 2000 = 1 + 1999 by norm_num, pow_add]
      ring
    rw [pow_two, ← pow_add]
    norm_num only
    rw [h2000, h1999]
    ring
  have hsq_lower :
      ((10 : ℝ) ^ 1999 - 7) ^ 2 ≤
        ((10 : ℝ) ^ 1000) ^ 2 * ((10 : ℝ) ^ 1998 - 1) := by
    set T : ℝ := (10 : ℝ) ^ 1999 with hTdef
    have hTge : (13 : ℝ) ≤ T := by
      rw [hTdef]
      have h : (10 : ℝ) ^ 2 ≤ (10 : ℝ) ^ 1999 := by
        exact pow_le_pow_right₀ (by norm_num) (by norm_num : 2 ≤ 1999)
      rw [show (10 : ℝ) ^ 2 = 100 by norm_num] at h
      exact (by norm_num : (13 : ℝ) ≤ 100).trans h
    have hleft : ((10 : ℝ) ^ 1999 - 7) ^ 2 = T ^ 2 - 14 * T + 49 := by
      rw [hTdef]
      ring
    rw [hleft, hpowprod, hTdef]
    rw [← hTdef]
    have hsmall : (49 : ℝ) ≤ 4 * T := by
      have hmul := mul_le_mul_of_nonneg_left hTge (by norm_num : (0 : ℝ) ≤ 4)
      norm_num at hmul
      exact (by norm_num : (49 : ℝ) ≤ 52).trans hmul
    have hstep' := add_le_add_left hsmall (T ^ 2 - 14 * T)
    have hstep : T ^ 2 - 14 * T + 49 ≤ T ^ 2 - 14 * T + 4 * T := by
      simpa [add_comm, add_left_comm, add_assoc] using hstep'
    have hrewrite : T ^ 2 - 14 * T + 4 * T = T ^ 2 - 10 * T := by ring
    rwa [hrewrite] at hstep
  have hsq_upper :
      ((10 : ℝ) ^ 1000) ^ 2 * ((10 : ℝ) ^ 1998 - 1) <
        ((10 : ℝ) ^ 1999 - 4) ^ 2 := by
    set T : ℝ := (10 : ℝ) ^ 1999 with hTdef
    have hTpos : (0 : ℝ) < T := by
      rw [hTdef]
      positivity
    have hright : ((10 : ℝ) ^ 1999 - 4) ^ 2 = T ^ 2 - 8 * T + 16 := by
      rw [hTdef]
      ring
    rw [hpowprod, hright, hTdef]
    rw [← hTdef]
    have hpos : (0 : ℝ) < 2 * T + 16 := by positivity
    have hrewrite : T ^ 2 - 8 * T + 16 = T ^ 2 - 10 * T + (2 * T + 16) := by
      ring
    rw [hrewrite]
    exact lt_add_of_pos_right _ hpos
  have hscaled_lower : (A : ℝ) ≤ (10 : ℝ) ^ 1000 * Real.sqrt (N : ℝ) := by
    have hsq : ((A : ℝ) / (10 : ℝ) ^ 1000) ^ 2 ≤ (N : ℝ) := by
      have hmain : ((3 : ℝ) * (A : ℝ)) ^ 2 ≤
          ((10 : ℝ) ^ 1000) ^ 2 * ((N : ℝ) * 9) := by
        rw [hA3, hN9]
        exact hsq_lower
      have hdenpos : 0 < ((10 : ℝ) ^ 1000) ^ 2 := by positivity
      rw [div_pow]
      rw [div_le_iff₀ hdenpos]
      have h9main : (9 : ℝ) * (A : ℝ) ^ 2 ≤
          9 * ((N : ℝ) * ((10 : ℝ) ^ 1000) ^ 2) := by
        calc
          (9 : ℝ) * (A : ℝ) ^ 2 = ((3 : ℝ) * (A : ℝ)) ^ 2 := by ring
          _ ≤ ((10 : ℝ) ^ 1000) ^ 2 * ((N : ℝ) * 9) := hmain
          _ = 9 * ((N : ℝ) * ((10 : ℝ) ^ 1000) ^ 2) := by ring
      exact le_of_mul_le_mul_left h9main (by norm_num : (0 : ℝ) < 9)
    have hs := Real.le_sqrt_of_sq_le hsq
    have hpos : 0 < (10 : ℝ) ^ 1000 := by positivity
    calc
      (A : ℝ) = (10 : ℝ) ^ 1000 * ((A : ℝ) / (10 : ℝ) ^ 1000) := by
        field_simp [hpos.ne']
      _ ≤ (10 : ℝ) ^ 1000 * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hs hpos.le
  have hscaled_upper : (10 : ℝ) ^ 1000 * Real.sqrt (N : ℝ) < (A : ℝ) + 1 := by
    have hsq : (N : ℝ) < (((A : ℝ) + 1) / (10 : ℝ) ^ 1000) ^ 2 := by
      have hmain : ((10 : ℝ) ^ 1000) ^ 2 * ((N : ℝ) * 9) <
          ((3 : ℝ) * ((A : ℝ) + 1)) ^ 2 := by
        rw [hA3succ, hN9]
        exact hsq_upper
      have hdenpos : 0 < ((10 : ℝ) ^ 1000) ^ 2 := by positivity
      rw [div_pow]
      rw [lt_div_iff₀' hdenpos]
      have h9main : (9 : ℝ) * (((10 : ℝ) ^ 1000) ^ 2 * (N : ℝ)) <
          9 * (((A : ℝ) + 1) ^ 2) := by
        calc
          (9 : ℝ) * (((10 : ℝ) ^ 1000) ^ 2 * (N : ℝ)) =
              ((10 : ℝ) ^ 1000) ^ 2 * ((N : ℝ) * 9) := by ring
          _ < ((3 : ℝ) * ((A : ℝ) + 1)) ^ 2 := hmain
          _ = 9 * (((A : ℝ) + 1) ^ 2) := by ring
      exact lt_of_mul_lt_mul_left h9main (by norm_num : (0 : ℝ) ≤ 9)
    have hpos : 0 < ((A : ℝ) + 1) / (10 : ℝ) ^ 1000 := by
      exact div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg A) zero_lt_one)
        (pow_pos (by norm_num : (0 : ℝ) < 10) 1000)
    have hs := (Real.sqrt_lt' hpos).2 hsq
    have hpowpos : 0 < (10 : ℝ) ^ 1000 := by
      exact pow_pos (by norm_num : (0 : ℝ) < 10) 1000
    calc
      (10 : ℝ) ^ 1000 * Real.sqrt (N : ℝ) <
          (10 : ℝ) ^ 1000 * (((A : ℝ) + 1) / (10 : ℝ) ^ 1000) :=
        mul_lt_mul_of_pos_left hs hpowpos
      _ = (A : ℝ) + 1 := by
        field_simp [hpowpos.ne']
  have hfloor : Nat.floor ((10 : ℝ) ^ 1000 * Real.sqrt (N : ℝ)) = A := by
    have hxnonneg : 0 ≤ (10 : ℝ) ^ 1000 * Real.sqrt (N : ℝ) := by
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    rw [Nat.floor_eq_iff hxnonneg]
    exact ⟨hscaled_lower, hscaled_upper⟩
  have hmod : A % 10 = 1 := by
    have hAform : A = 10 * (((10 : ℕ) ^ 1998 - 1) / 3) + 1 := by
      have h3dvd : 3 ∣ (10 : ℕ) ^ 1998 - 1 := by
        have h9dvd : 9 ∣ (10 : ℕ) ^ 1998 - 1 := by
          simpa using ((10 : ℕ).sub_one_dvd_pow_sub_one 1998)
        exact dvd_trans (by norm_num : 3 ∣ 9) h9dvd
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
      rw [hA3nat]
      have hmul := Nat.mul_div_cancel' h3dvd
      omega
    rw [hAform]
    omega
  rw [hfloor]
  exact hmod.symm
