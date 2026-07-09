import Mathlib

open Set Nat Function

private lemma putnam_2007_b3_floor_sqrt5 : (((⌊Real.sqrt 5⌋ : ℤ) : ℝ) = 2) := by
  have hfloor : ⌊Real.sqrt 5⌋ = (2 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 5)).2
        (by norm_num)
    · norm_num
      exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)).2 (by norm_num)
  exact_mod_cast hfloor

private lemma putnam_2007_b3_cassini_odd (n : ℕ) :
    ((Nat.fib (2 * n + 6) : ℤ) * (Nat.fib (2 * n + 4) : ℤ) -
        (Nat.fib (2 * n + 5) : ℤ) ^ 2 = -1) := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq ((2 * n + 5 : ℕ) : ℤ)
  have hpow : ((-1 : ℤ) ^ Int.natAbs ((2 * n + 5 : ℕ) : ℤ)) = -1 := by
    have habs : Int.natAbs ((2 * n + 5 : ℕ) : ℤ) = 2 * n + 5 := by
      exact Int.natAbs_natCast (2 * n + 5)
    rw [habs]
    have hodd : Odd (2 * n + 5) := by
      simpa only [Nat.cast_ofNat] using (odd_two_mul_add_one (n + 2) :
        Odd (2 * (n + 2) + 1))
    exact hodd.neg_one_pow
  rw [hpow] at h
  have h1 : (((2 * n + 5 : ℕ) : ℤ) + 1) = ((2 * n + 6 : ℕ) : ℤ) := by omega
  have h2 : (((2 * n + 5 : ℕ) : ℤ) - 1) = ((2 * n + 4 : ℕ) : ℤ) := by omega
  rw [h1, h2] at h
  simpa using h

private lemma putnam_2007_b3_lucas_sq (n : ℕ) :
    ((Nat.fib (2 * n + 4) + Nat.fib (2 * n + 6) : ℕ) : ℝ) ^ 2 + 4 =
      5 * ((Nat.fib (2 * n + 5) : ℕ) : ℝ) ^ 2 := by
  have hcassZ := putnam_2007_b3_cassini_odd n
  have hcassR : ((Nat.fib (2 * n + 6) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) -
        (Nat.fib (2 * n + 5) : ℝ) ^ 2 = -1) := by
    exact_mod_cast hcassZ
  have hQ : (Nat.fib (2 * n + 6) : ℝ) =
      Nat.fib (2 * n + 4) + Nat.fib (2 * n + 5) := by
    rw [show 2 * n + 6 = (2 * n + 4) + 2 by ring]
    rw [Nat.fib_add_two]
    norm_num
  have hL : ((Nat.fib (2 * n + 4) + Nat.fib (2 * n + 6) : ℕ) : ℝ) =
      (Nat.fib (2 * n + 4) : ℝ) + (Nat.fib (2 * n + 6) : ℝ) := by norm_num
  nlinarith

private lemma putnam_2007_b3_pow_le_fib_even :
    ∀ k : ℕ, (2 : ℕ) ^ (k + 1) ≤ Nat.fib (2 * k + 4)
  | 0 => by norm_num
  | k + 1 => by
      have ih : (2 : ℕ) ^ (k + 1) ≤ Nat.fib (2 * k + 4) :=
        putnam_2007_b3_pow_le_fib_even k
      have hmono : Nat.fib (2 * k + 4) ≤ Nat.fib (2 * k + 5) := by
        simpa [show 2 * k + 5 = (2 * k + 4) + 1 by ring] using
          (Nat.fib_le_fib_succ (n := 2 * k + 4))
      have hstep : 2 * Nat.fib (2 * k + 4) ≤ Nat.fib (2 * (k + 1) + 4) := by
        rw [show 2 * (k + 1) + 4 = (2 * k + 4) + 2 by ring]
        conv_rhs => rw [Nat.fib_add_two]
        nlinarith
      calc
        (2 : ℕ) ^ ((k + 1) + 1) = 2 * (2 : ℕ) ^ (k + 1) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * Nat.fib (2 * k + 4) := Nat.mul_le_mul_left 2 ih
        _ ≤ Nat.fib (2 * (k + 1) + 4) := hstep

private lemma putnam_2007_b3_floor_fib (k : ℕ) :
    (((⌊(((2 : ℕ) ^ k * Nat.fib (2 * k + 5) : ℕ) : ℝ) *
      Real.sqrt 5⌋ : ℤ) : ℝ) =
      (((2 : ℕ) ^ k * (Nat.fib (2 * k + 4) + Nat.fib (2 * k + 6)) : ℕ) : ℝ)) := by
  let A : ℝ := ((2 : ℕ) ^ k : ℝ)
  let F : ℝ := (Nat.fib (2 * k + 5) : ℝ)
  let L : ℝ := ((Nat.fib (2 * k + 4) + Nat.fib (2 * k + 6) : ℕ) : ℝ)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hC0 : 0 ≤ A * F * Real.sqrt 5 := by
    exact mul_nonneg (mul_nonneg hA0 hF0) (Real.sqrt_nonneg 5)
  have hB0 : 0 ≤ A * L := mul_nonneg hA0 hL0
  have hsq : L ^ 2 + 4 = 5 * F ^ 2 := by
    simpa [L, F] using putnam_2007_b3_lucas_sq k
  have hsqA : (A * L) ^ 2 + 4 * A ^ 2 = 5 * (A * F) ^ 2 := by
    nlinarith [sq_nonneg A, hsq]
  have hsqrt : (A * F * Real.sqrt 5) ^ 2 = 5 * (A * F) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  have hLgeNat : (2 : ℕ) ^ (k + 1) ≤ Nat.fib (2 * k + 4) + Nat.fib (2 * k + 6) := by
    exact le_trans (putnam_2007_b3_pow_le_fib_even k) (Nat.le_add_right _ _)
  have hLge : (2 : ℝ) ^ (k + 1) ≤ L := by
    dsimp [L]
    exact_mod_cast hLgeNat
  have htwoA : 2 * A = (2 : ℝ) ^ (k + 1) := by
    dsimp [A]
    rw [pow_succ]
    ring
  have hAle : 2 * A ≤ L := by
    rwa [htwoA]
  have hfourAle : 4 * A ^ 2 ≤ 2 * (A * L) := by
    have hmul := mul_le_mul_of_nonneg_left hAle (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA0)
    nlinarith
  have hfloorInt :
      ⌊(((2 : ℕ) ^ k * Nat.fib (2 * k + 5) : ℕ) : ℝ) * Real.sqrt 5⌋ =
        (((2 : ℕ) ^ k * (Nat.fib (2 * k + 4) + Nat.fib (2 * k + 6)) : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · have hle : A * L ≤ A * F * Real.sqrt 5 := by
        have hsqle : (A * L) ^ 2 ≤ (A * F * Real.sqrt 5) ^ 2 := by
          rw [hsqrt]
          nlinarith [sq_nonneg A]
        have habs : |A * L| ≤ |A * F * Real.sqrt 5| := (sq_le_sq).mp hsqle
        rwa [abs_of_nonneg hB0, abs_of_nonneg hC0] at habs
      simpa [A, F, L, Nat.cast_mul, Int.cast_mul] using hle
    · have hlt : A * F * Real.sqrt 5 < A * L + 1 := by
        have hsqupper : (A * F * Real.sqrt 5) ^ 2 < (A * L + 1) ^ 2 := by
          rw [hsqrt]
          nlinarith
        have hD0 : 0 ≤ A * L + 1 := by nlinarith
        have habs : |A * F * Real.sqrt 5| < |A * L + 1| := (sq_lt_sq).mp hsqupper
        rwa [abs_of_nonneg hC0, abs_of_nonneg hD0] at habs
      simpa [A, F, L, Nat.cast_mul, Int.cast_mul] using hlt
  exact_mod_cast hfloorInt

private lemma putnam_2007_b3_fib_step (k : ℕ) :
    3 * (((2 : ℕ) ^ k * Nat.fib (2 * k + 5) : ℕ) : ℝ) +
        (((2 : ℕ) ^ k * (Nat.fib (2 * k + 4) + Nat.fib (2 * k + 6)) : ℕ) : ℝ) =
      (((2 : ℕ) ^ (k + 1) * Nat.fib (2 * (k + 1) + 5) : ℕ) : ℝ) := by
  have hQ : (Nat.fib (2 * k + 6) : ℝ) =
      Nat.fib (2 * k + 4) + Nat.fib (2 * k + 5) := by
    rw [show 2 * k + 6 = (2 * k + 4) + 2 by ring]
    rw [Nat.fib_add_two]
    norm_num
  have hR : (Nat.fib (2 * (k + 1) + 5) : ℝ) =
      Nat.fib (2 * k + 5) + Nat.fib (2 * k + 6) := by
    rw [show 2 * (k + 1) + 5 = (2 * k + 5) + 2 by ring]
    rw [Nat.fib_add_two]
    norm_num
  have hpow : ((2 : ℝ) ^ (k + 1)) = 2 * (2 : ℝ) ^ k := by
    rw [pow_succ]
    ring
  norm_num [Nat.cast_mul, Nat.cast_add]
  rw [hR, hpow, hQ]
  ring

private lemma putnam_2007_b3_final_closed :
    (((2 : ℕ) ^ 2006 * Nat.fib 4017 : ℕ) : ℝ) =
      ((2 ^ 2006 / Real.sqrt 5) *
        (((1 + Real.sqrt 5) / 2) ^ 4017 + ((1 + Real.sqrt 5) / 2) ^ (-4017 : ℤ)) : ℝ) := by
  have hphineg : Real.goldenRatio ^ (-4017 : ℤ) = - Real.goldenConj ^ 4017 := by
    rw [zpow_neg]
    calc
      (Real.goldenRatio ^ 4017)⁻¹ = Real.goldenRatio⁻¹ ^ 4017 :=
        (inv_pow Real.goldenRatio 4017).symm
      _ = (-Real.goldenConj) ^ 4017 := by rw [Real.inv_goldenRatio]
      _ = - Real.goldenConj ^ 4017 := Odd.neg_pow (by norm_num : Odd 4017) Real.goldenConj
  have hfib : (Nat.fib 4017 : ℝ) =
      (Real.goldenRatio ^ 4017 + Real.goldenRatio ^ (-4017 : ℤ)) / Real.sqrt 5 := by
    rw [Real.coe_fib_eq 4017, hphineg]
    rw [sub_eq_add_neg]
  calc
    (((2 : ℕ) ^ 2006 * Nat.fib 4017 : ℕ) : ℝ)
        = (2 : ℝ) ^ 2006 * (Nat.fib 4017 : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_pow]
          rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
    _ = (2 : ℝ) ^ 2006 *
          ((Real.goldenRatio ^ 4017 + Real.goldenRatio ^ (-4017 : ℤ)) / Real.sqrt 5) := by
        rw [hfib]
    _ = ((2 : ℝ) ^ 2006 / Real.sqrt 5) *
          (Real.goldenRatio ^ 4017 + Real.goldenRatio ^ (-4017 : ℤ)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ac_rfl
    _ = ((2 ^ 2006 / Real.sqrt 5) *
        (((1 + Real.sqrt 5) / 2) ^ 4017 + ((1 + Real.sqrt 5) / 2) ^ (-4017 : ℤ)) : ℝ) := by
        rfl

-- (2 ^ 2006 / Real.sqrt 5) * (((1 + Real.sqrt 5) / 2) ^ 4017 + ((1 + Real.sqrt 5) / 2) ^ (-4017 : ℤ))
/--
Let $x_0 = 1$ and for $n \geq 0$, let $x_{n+1} = 3x_n + \lfloor x_n \sqrt{5} \rfloor$. In particular, $x_1 = 5$, $x_2 = 26$, $x_3 = 136$, $x_4 = 712$. Find a closed-form expression for $x_{2007}$. ($\lfloor a \rfloor$ means the largest integer $\leq a$.)
-/
theorem putnam_2007_b3
(x : ℕ → ℝ)
(hx0 : x 0 = 1)
(hx : ∀ n : ℕ, x (n + 1) = 3 * (x n) + ⌊(x n) * Real.sqrt 5⌋)
: (x 2007 = ((2 ^ 2006 / Real.sqrt 5) * (((1 + Real.sqrt 5) / 2) ^ 4017 + ((1 + Real.sqrt 5) / 2) ^ (-4017 : ℤ)) : ℝ )) := by
  have hx1 : x 1 = 5 := by
    have h := hx 0
    norm_num [hx0, putnam_2007_b3_floor_sqrt5] at h
    exact h
  have hseq : ∀ k : ℕ,
      x (k + 1) = (((2 : ℕ) ^ k * Nat.fib (2 * k + 5) : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero =>
        norm_num
        exact hx1
    | succ k ih =>
        calc
          x (k.succ + 1) = 3 * x (k + 1) + ⌊(x (k + 1)) * Real.sqrt 5⌋ := by
            simpa [Nat.succ_eq_add_one, add_assoc] using hx (k + 1)
          _ = 3 * (((2 : ℕ) ^ k * Nat.fib (2 * k + 5) : ℕ) : ℝ) +
                (((2 : ℕ) ^ k * (Nat.fib (2 * k + 4) + Nat.fib (2 * k + 6)) : ℕ) : ℝ) := by
            rw [ih]
            rw [putnam_2007_b3_floor_fib k]
          _ = (((2 : ℕ) ^ (k + 1) * Nat.fib (2 * (k + 1) + 5) : ℕ) : ℝ) :=
            putnam_2007_b3_fib_step k
  have hx2007 : x 2007 = (((2 : ℕ) ^ 2006 * Nat.fib 4017 : ℕ) : ℝ) := by
    have h := hseq 2006
    simpa only [show 2006 + 1 = 2007 by norm_num,
      show 2 * 2006 + 5 = 4017 by norm_num] using h
  exact hx2007.trans putnam_2007_b3_final_closed
