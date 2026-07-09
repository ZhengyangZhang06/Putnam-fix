import Mathlib

-- 3
/--
What is the units (i.e., rightmost) digit of
\[
\left\lfloor \frac{10^{20000}}{10^{100}+3}\right\rfloor ?
\]
-/
theorem putnam_1986_a2
: (Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) % 10 = ((3) : ℕ )) := by
  have hfloor : Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) =
      (10 ^ 20000 : ℕ) / (10 ^ 100 + 3 : ℕ) := by
    rw [show (10 ^ 20000 : ℝ) = ((10 ^ 20000 : ℕ) : ℝ) by
          norm_num only [Nat.cast_ofNat, Nat.cast_pow],
        show (10 ^ 100 + 3 : ℝ) = ((10 ^ 100 + 3 : ℕ) : ℝ) by
          norm_num only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add]]
    exact Nat.floor_div_eq_div (K := ℝ) (10 ^ 20000) (10 ^ 100 + 3)
  rw [hfloor]
  rw [show (10 ^ 20000 : ℕ) = (10 ^ 100 : ℕ) ^ 200 by rw [← pow_mul]]
  let x : ℕ := 10 ^ 100
  change (x ^ 200 / (x + 3)) % 10 = 3
  have hx3 : 3 ≤ x := by
    dsimp [x]
    norm_num
  have hsq_mod : x ^ 2 ≡ 9 [MOD x + 3] := by
    have hdiff : x ^ 2 - 9 = (x + 3) * (x - 3) := by
      have hsq : x ^ 2 = 9 + (x + 3) * (x - 3) := by
        rw [pow_two]
        nlinarith [Nat.sub_add_cancel hx3]
      omega
    symm
    rw [Nat.modEq_iff_dvd' (show 9 ≤ x ^ 2 by nlinarith [hx3])]
    use x - 3
  have hpow_mod : x ^ 200 ≡ 3 ^ 200 [MOD x + 3] := by
    have hleft : (x ^ 2) ^ 100 = x ^ 200 := by
      rw [← pow_mul]
    have hright : (9 : ℕ) ^ 100 = 3 ^ 200 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      rw [← pow_mul]
    simpa [hleft, hright] using (Nat.ModEq.pow 100 hsq_mod)
  have hsmall : 3 ^ 200 < x + 3 := by
    dsimp [x]
    norm_num
  have hrem : x ^ 200 % (x + 3) = 3 ^ 200 :=
    Nat.mod_eq_of_modEq hpow_mod hsmall
  let q : ℕ := x ^ 200 / (x + 3)
  have hdivid : (x + 3) * q + 3 ^ 200 = x ^ 200 := by
    dsimp [q]
    have hbase := Nat.div_add_mod (x ^ 200) (x + 3)
    omega
  have hqres : (3 * (q % 10) + 1) % 10 = 0 := by
    have hmod_eq : ((x + 3) * q + 3 ^ 200) % 10 = 0 := by
      rw [hdivid]
      norm_num [x]
    simpa [x, Nat.add_mod, Nat.mul_mod] using hmod_eq
  have hq : q % 10 = 3 := by
    let r := q % 10
    have hr : r < 10 := by
      dsimp [r]
      exact Nat.mod_lt _ (by norm_num)
    have h' : (3 * r + 1) % 10 = 0 := by
      simpa [r] using hqres
    change r = 3
    interval_cases r <;> simp at h' ⊢
  simpa [q] using hq
