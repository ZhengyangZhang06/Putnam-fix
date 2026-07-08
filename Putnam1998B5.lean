import Mathlib

open Set Function Metric

abbrev putnam_1998_b5_solution : ℕ := 1

/--
Let $N$ be the positive integer with 1998 decimal digits, all of them 1; that is, \[N=1111\cdots 11.\] Find the thousandth digit after the decimal point of $\sqrt N$.
-/
theorem putnam_1998_b5
(N : ℕ)
(hN : N = ∑ i ∈ Finset.range 1998, 10^i)
: putnam_1998_b5_solution = (Nat.floor (10^1000 * Real.sqrt N)) % 10 :=
by
  subst N
  let T : ℕ := ∑ i ∈ Finset.range 1998, 10 ^ i
  let S : ℕ := 10 * T
  let a : ℕ := 1 + 3 * S
  have hTsum : T = (10 ^ 1998 - 1) / 9 := by
    dsimp [T]
    simpa using (Nat.geomSum_eq (m := 10) (n := 1998) (by norm_num : 2 ≤ 10))
  have hdiv9 : 9 ∣ 10 ^ 1998 - 1 := by
    simpa using (Nat.sub_one_dvd_pow_sub_one (x := 10) (n := 1998))
  have hT : T * 9 + 1 = 10 ^ 1998 := by
    calc
      T * 9 + 1 = ((10 ^ 1998 - 1) / 9) * 9 + 1 := by rw [hTsum]
      _ = (10 ^ 1998 - 1) + 1 := by rw [Nat.div_mul_cancel hdiv9]
      _ = 10 ^ 1998 := Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (by norm_num) 1998))
  have hTge1 : 1 ≤ T := by
    dsimp [T]
    simpa using
      (Finset.single_le_sum (s := Finset.range 1998) (f := fun i : ℕ => 10 ^ i)
        (a := 0) (fun i _ => by positivity) (by norm_num))
  have hSge1 : 1 ≤ S := by
    dsimp [S]
    omega
  have hA : 9 * S + 10 = 10 ^ 1999 := by
    calc
      9 * S + 10 = (T * 9 + 1) * 10 := by
        dsimp [S]
        ring
      _ = 10 ^ 1998 * 10 := by rw [hT]
      _ = 10 ^ 1999 := by
        exact (pow_succ (10 : ℕ) 1998).symm
  have hpow2000 : (10 : ℕ) ^ 2000 = 10 * 10 ^ 1999 := by
    rw [show (2000 : ℕ) = 1999 + 1 by norm_num, pow_succ']
  have hM : T * 10 ^ 2000 = S * (9 * S + 10) := by
    calc
      T * 10 ^ 2000 = S * 10 ^ 1999 := by
        dsimp [S]
        rw [hpow2000]
        ring
      _ = S * (9 * S + 10) := by rw [hA]
  have hsqrt : Nat.sqrt (T * 10 ^ 2000) = a := by
    symm
    rw [Nat.eq_sqrt']
    constructor
    · rw [hM]
      dsimp [a]
      have hlin : 6 * S + 1 ≤ 10 * S := by omega
      calc
        (1 + 3 * S) ^ 2 = 9 * S ^ 2 + 6 * S + 1 := by ring
        _ = 9 * S ^ 2 + (6 * S + 1) := by ring
        _ ≤ 9 * S ^ 2 + 10 * S := Nat.add_le_add_left hlin _
        _ = S * (9 * S + 10) := by ring
    · rw [hM]
      dsimp [a]
      have hlin : 10 * S < 12 * S + 4 := by omega
      calc
        S * (9 * S + 10) = 9 * S ^ 2 + 10 * S := by ring
        _ < 9 * S ^ 2 + (12 * S + 4) := Nat.add_lt_add_left hlin _
        _ = 9 * S ^ 2 + 12 * S + 4 := by ring
        _ = (1 + 3 * S + 1) ^ 2 := by ring
  have hsqrtpow : Real.sqrt ((10 : ℝ) ^ 2000) = (10 : ℝ) ^ 1000 := by
    rw [show (2000 : ℕ) = 1000 * 2 by norm_num, pow_mul,
      Real.sqrt_sq (by positivity : 0 ≤ (10 : ℝ) ^ 1000)]
  have hx_eq :
      (10 : ℝ) ^ 1000 * Real.sqrt (T : ℝ) =
        Real.sqrt ((T * 10 ^ 2000 : ℕ) : ℝ) := by
    calc
      (10 : ℝ) ^ 1000 * Real.sqrt (T : ℝ)
          = Real.sqrt ((10 : ℝ) ^ 2000) * Real.sqrt (T : ℝ) := by rw [hsqrtpow]
      _ = Real.sqrt (((10 : ℝ) ^ 2000) * (T : ℝ)) := by
        rw [Real.sqrt_mul (pow_nonneg (by norm_num) 2000)]
      _ = Real.sqrt ((T * 10 ^ 2000 : ℕ) : ℝ) := by
        have hcast :
            ((10 : ℝ) ^ 2000) * (T : ℝ) = ((T * 10 ^ 2000 : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_pow]
          ring
        rw [hcast]
  have hfloor : Nat.floor ((10 : ℝ) ^ 1000 * Real.sqrt (T : ℝ)) = a := by
    rw [hx_eq]
    exact (Real.nat_floor_real_sqrt_eq_nat_sqrt (a := T * 10 ^ 2000)).trans hsqrt
  have hmod : a % 10 = 1 := by
    dsimp [a, S]
    rw [show 1 + 3 * (10 * T) = 1 + 10 * (3 * T) by ring]
    rw [Nat.add_mul_mod_self_left]
  change putnam_1998_b5_solution =
    Nat.floor ((10 : ℝ) ^ 1000 * Real.sqrt (T : ℝ)) % 10
  rw [hfloor, hmod]
