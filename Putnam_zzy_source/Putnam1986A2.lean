import Mathlib

abbrev putnam_1986_a2_solution : ℕ := 3

/--
What is the units (i.e., rightmost) digit of
\[
\left\lfloor \frac{10^{20000}}{10^{100}+3}\right\rfloor ?
\]
-/
theorem putnam_1986_a2
: (Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = putnam_1986_a2_solution) :=
by
  rw [show (10 ^ 20000 : ℝ) = ((10 ^ 20000 : ℕ) : ℝ) by
    exact (Nat.cast_pow (α := ℝ) 10 20000).symm]
  rw [show (10 ^ 100 + 3 : ℝ) = ((10 ^ 100 + 3 : ℕ) : ℝ) by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]]
  rw [Nat.floor_div_eq_div]
  have hrem : (10 ^ 20000 : ℕ) % (10 ^ 100 + 3) = 3 ^ 200 := by
    have hlt : (3 : ℕ) ^ 200 < 10 ^ 100 + 3 := by
      calc
        (3 : ℕ) ^ 200 = 9 ^ 100 := by
          change (3 : ℕ) ^ (2 * 100) = 9 ^ 100
          rw [pow_mul]
          rfl
        _ < 10 ^ 100 := by
          exact Nat.pow_lt_pow_left (show (9 : ℕ) < 10 by exact Nat.lt_succ_self 9)
            (Nat.succ_ne_zero 99)
        _ < 10 ^ 100 + 3 := Nat.lt_add_of_pos_right (Nat.succ_pos 2)
    have hmodZ : ((10 ^ 20000 : ℕ) : ZMod (10 ^ 100 + 3)) =
        ((3 ^ 200 : ℕ) : ZMod (10 ^ 100 + 3)) := by
      have hbase : ((10 ^ 100 : ℕ) : ZMod (10 ^ 100 + 3)) =
          -((3 : ℕ) : ZMod (10 ^ 100 + 3)) := by
        apply eq_neg_iff_add_eq_zero.mpr
        change (((10 ^ 100 : ℕ) + (3 : ℕ) : ℕ) : ZMod (10 ^ 100 + 3)) = 0
        exact ZMod.natCast_self (10 ^ 100 + 3)
      have hpow : (10 ^ 20000 : ℕ) = (10 ^ 100 : ℕ) ^ 200 := by
        rw [← pow_mul]
      have heven : Even 200 := ⟨100, rfl⟩
      rw [hpow, Nat.cast_pow, hbase, heven.neg_pow, ← Nat.cast_pow]
    have hmodNat : (10 ^ 20000 : ℕ) ≡ 3 ^ 200 [MOD (10 ^ 100 + 3)] := by
      exact (ZMod.natCast_eq_natCast_iff (10 ^ 20000) (3 ^ 200) (10 ^ 100 + 3)).mp hmodZ
    rw [Nat.ModEq] at hmodNat
    rw [Nat.mod_eq_of_lt hlt] at hmodNat
    exact hmodNat
  have hdiv : (10 ^ 100 + 3 : ℕ) * ((10 ^ 20000 : ℕ) / (10 ^ 100 + 3)) +
      (10 ^ 20000 : ℕ) % (10 ^ 100 + 3) = (10 ^ 20000 : ℕ) :=
    Nat.div_add_mod (10 ^ 20000) (10 ^ 100 + 3)
  have hdivZ : (((10 ^ 100 + 3 : ℕ) : ZMod 10) *
        (((10 ^ 20000 : ℕ) / (10 ^ 100 + 3) : ℕ) : ZMod 10) +
      (((10 ^ 20000 : ℕ) % (10 ^ 100 + 3) : ℕ) : ZMod 10) =
      ((10 ^ 20000 : ℕ) : ZMod 10)) := by
    have hraw := congrArg (fun x : ℕ => (x : ZMod 10)) hdiv
    change ((((10 ^ 100 + 3 : ℕ) * ((10 ^ 20000 : ℕ) / (10 ^ 100 + 3)) +
        (10 ^ 20000 : ℕ) % (10 ^ 100 + 3) : ℕ) : ZMod 10) =
        ((10 ^ 20000 : ℕ) : ZMod 10)) at hraw
    rw [Nat.cast_add, Nat.cast_mul] at hraw
    exact hraw
  have hten : ((10 : ℕ) : ZMod 10) = 0 := ZMod.natCast_self 10
  have hdZ : (((10 ^ 100 + 3 : ℕ) : ZMod 10) = ((3 : ℕ) : ZMod 10)) := by
    change (((10 ^ 100 : ℕ) + (3 : ℕ) : ℕ) : ZMod 10) = ((3 : ℕ) : ZMod 10)
    rw [Nat.cast_add, Nat.cast_pow, hten, zero_pow (Nat.succ_ne_zero 99), zero_add]
  have hnZ : (((10 ^ 20000 : ℕ) : ZMod 10) = 0) := by
    rw [Nat.cast_pow, hten, zero_pow (Nat.succ_ne_zero 19999)]
  have h3powZ : (((3 ^ 200 : ℕ) : ZMod 10) = 1) := by
    rw [Nat.cast_pow]
    rw [show (200 : ℕ) = 2 * 100 by rfl, pow_mul]
    have hsq : (((3 : ℕ) : ZMod 10) ^ 2) = -1 := by
      change (((9 : ℕ) : ZMod 10) = -1)
      apply eq_neg_iff_add_eq_zero.mpr
      change (((10 : ℕ) : ZMod 10) = 0)
      exact ZMod.natCast_self 10
    rw [hsq]
    exact Even.neg_one_pow (⟨50, rfl⟩ : Even 100)
  have hrZ : ((((10 ^ 20000 : ℕ) % (10 ^ 100 + 3) : ℕ) : ZMod 10) = 1) := by
    rw [hrem]
    exact h3powZ
  rw [hdZ, hrZ, hnZ] at hdivZ
  have hqZ : ((((10 ^ 20000 : ℕ) / (10 ^ 100 + 3) : ℕ) : ZMod 10) =
      ((3 : ℕ) : ZMod 10)) := by
    have h3q : (((3 : ℕ) : ZMod 10) *
        (((10 ^ 20000 : ℕ) / (10 ^ 100 + 3) : ℕ) : ZMod 10)) = -1 := by
      exact eq_neg_iff_add_eq_zero.mpr hdivZ
    have h73 : (((7 : ℕ) : ZMod 10) * ((3 : ℕ) : ZMod 10)) = 1 := by
      change (((21 : ℕ) : ZMod 10) = ((1 : ℕ) : ZMod 10))
      exact (ZMod.natCast_eq_natCast_iff 21 1 10).2 rfl
    have h7neg : (((7 : ℕ) : ZMod 10) * (-1 : ZMod 10)) = ((3 : ℕ) : ZMod 10) := by
      rw [mul_neg, mul_one]
      symm
      apply eq_neg_iff_add_eq_zero.mpr
      change (((10 : ℕ) : ZMod 10) = 0)
      exact ZMod.natCast_self 10
    calc
      (((10 ^ 20000 : ℕ) / (10 ^ 100 + 3) : ℕ) : ZMod 10) =
          1 * (((10 ^ 20000 : ℕ) / (10 ^ 100 + 3) : ℕ) : ZMod 10) := by rw [one_mul]
      _ = (((7 : ℕ) : ZMod 10) * ((3 : ℕ) : ZMod 10)) *
          (((10 ^ 20000 : ℕ) / (10 ^ 100 + 3) : ℕ) : ZMod 10) := by rw [h73]
      _ = ((7 : ℕ) : ZMod 10) * (((3 : ℕ) : ZMod 10) *
          (((10 ^ 20000 : ℕ) / (10 ^ 100 + 3) : ℕ) : ZMod 10)) := by rw [mul_assoc]
      _ = ((7 : ℕ) : ZMod 10) * (-1 : ZMod 10) := by rw [h3q]
      _ = ((3 : ℕ) : ZMod 10) := h7neg
  have hmod : ((10 ^ 20000 : ℕ) / (10 ^ 100 + 3)) ≡ 3 [MOD 10] :=
    (ZMod.natCast_eq_natCast_iff ((10 ^ 20000 : ℕ) / (10 ^ 100 + 3)) 3 10).mp hqZ
  rw [Nat.ModEq] at hmod
  rw [show (3 : ℕ) % 10 = 3 by rfl] at hmod
  exact hmod
