import Mathlib

noncomputable abbrev putnam_2015_a3_solution : ℂ := (13725 : ℂ)

open scoped BigOperators

private lemma prod_range_shift_of_period {M : Type*} [CommMonoid M] {m : ℕ}
    (hm : 0 < m) {f : ℕ → M} (hper : f m = f 0) :
    (∏ i ∈ Finset.range m, f (i + 1)) = ∏ i ∈ Finset.range m, f i := by
  cases m with
  | zero => exact (Nat.not_lt_zero _ hm).elim
  | succ k =>
      rw [Finset.prod_range_succ (fun i ↦ f (i + 1)) k, Finset.prod_range_succ' f k]
      simp [hper]

private lemma prod_range_mul_periodic_pow {M : Type*} [CommMonoid M] (m : ℕ)
    {f : ℕ → M} (hper : ∀ q r : ℕ, f (q * m + r) = f r) :
    ∀ d : ℕ, (∏ i ∈ Finset.range (d * m), f i) =
      (∏ i ∈ Finset.range m, f i) ^ d
  | 0 => by simp
  | d + 1 => by
      rw [Nat.succ_mul, Finset.prod_range_add, prod_range_mul_periodic_pow m hper d]
      have hblock : (∏ x ∈ Finset.range m, f (d * m + x)) =
          ∏ x ∈ Finset.range m, f x := by
        refine Finset.prod_congr rfl ?_
        intro x hx
        exact hper d x
      rw [hblock, pow_succ]

private lemma prod_one_add_primitive_powers {m : ℕ} {η : ℂ}
    (hm : Odd m) (hη : IsPrimitiveRoot η m) :
    (∏ i ∈ Finset.range m, (1 + η ^ i)) = (2 : ℂ) := by
  classical
  haveI : NeZero m := ⟨Nat.ne_of_gt hm.pos⟩
  have hroots :
      (∏ μ ∈ Polynomial.nthRootsFinset m (1 : ℂ), (1 + μ)) = (2 : ℂ) := by
    have h := hη.pow_add_pow_eq_prod_add_mul (x := (1 : ℂ)) (y := (1 : ℂ)) hm
    norm_num [one_pow, mul_one] at h
    exact h.symm
  have hpowers :
      (∏ i ∈ Finset.range m, (1 + η ^ i)) =
        ∏ μ ∈ Polynomial.nthRootsFinset m (1 : ℂ), (1 + μ) := by
    refine Finset.prod_bij (fun i _ ↦ η ^ i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Polynomial.mem_nthRootsFinset hm.pos]
      rw [← pow_mul, mul_comm i m, pow_mul, hη.pow_eq_one, one_pow]
    · intro i hi j hj hij
      exact hη.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    · intro μ hμ
      rw [Polynomial.mem_nthRootsFinset hm.pos] at hμ
      obtain ⟨i, hi, hpow⟩ := hη.eq_pow_of_pow_eq_one hμ
      exact ⟨i, Finset.mem_range.mpr hi, hpow⟩
    · intro i hi
      rfl
  exact hpowers.trans hroots

private lemma prod_one_add_primitive_powers_shift {m : ℕ} {η : ℂ}
    (hm : Odd m) (hη : IsPrimitiveRoot η m) :
    (∏ i ∈ Finset.range m, (1 + η ^ (i + 1))) = (2 : ℂ) := by
  have hper : (fun i : ℕ ↦ (1 : ℂ) + η ^ i) m = (fun i : ℕ ↦ (1 : ℂ) + η ^ i) 0 := by
    simp [hη.pow_eq_one]
  simpa using
    (prod_range_shift_of_period hm.pos (f := fun i : ℕ ↦ (1 : ℂ) + η ^ i) hper).trans
      (prod_one_add_primitive_powers hm hη)

private lemma prod_one_add_periods {m d : ℕ} {η : ℂ}
    (hm : Odd m) (hη : IsPrimitiveRoot η m) :
    (∏ i ∈ Finset.range (d * m), (1 + η ^ (i + 1))) = (2 : ℂ) ^ d := by
  have hper : ∀ q r : ℕ,
      (1 : ℂ) + η ^ (q * m + r + 1) = 1 + η ^ (r + 1) := by
    intro q r
    have hpow : η ^ (q * m + r + 1) = η ^ (r + 1) := by
      rw [mul_comm q m, Nat.add_assoc, pow_add, pow_mul, hη.pow_eq_one, one_pow, one_mul]
    rw [hpow]
  rw [prod_range_mul_periodic_pow m hper d, prod_one_add_primitive_powers_shift hm hη]

private lemma complex_exp_mul_nat_nat (a b : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (a + 1) * (b + 1) / 2015) =
      (Complex.exp (2 * Real.pi * Complex.I / 2015) ^ (a + 1)) ^ (b + 1) := by
  rw [← pow_mul, ← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

private lemma odd_div_gcd_2015 (a : ℕ) : Odd (2015 / Nat.gcd 2015 a) := by
  have hodd : Odd 2015 := by norm_num
  exact hodd.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 2015 a))

private lemma sum_gcd_2015 :
    (∑ a : Fin 2015, Nat.gcd 2015 (a.1 + 1)) = 13725 := by
  set_option maxRecDepth 1000000 in
  decide

private lemma prod_rows :
    (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp
          (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      (2 : ℂ) ^ 13725 := by
  classical
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 2015)
  have hζ : IsPrimitiveRoot ζ 2015 := by
    exact Complex.isPrimitiveRoot_exp 2015 (by norm_num)
  have hrow : ∀ a : Fin 2015,
      (∏ b : Fin 2015,
        (1 + Complex.exp
          (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
        (2 : ℂ) ^ Nat.gcd 2015 (a.1 + 1) := by
    intro a
    let k : ℕ := a.1 + 1
    let m : ℕ := 2015 / Nat.gcd 2015 k
    let d : ℕ := Nat.gcd 2015 k
    have hkpos : 0 < k := by dsimp [k]; omega
    have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
    have hdvd : d ∣ 2015 := by
      dsimp [d]
      exact Nat.gcd_dvd_left 2015 k
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.gcd_pos_of_pos_left k (by norm_num : 0 < 2015)
    have hdm : d * m = 2015 := by
      dsimp [d, m]
      exact Nat.mul_div_cancel' hdvd
    have hm_order : orderOf (ζ ^ k) = m := by
      dsimp [m, ζ]
      rw [orderOf_pow' ζ hkne, ← hζ.eq_orderOf]
    have hη : IsPrimitiveRoot (ζ ^ k) m := by
      rw [← hm_order]
      exact IsPrimitiveRoot.orderOf (ζ ^ k)
    have hm_odd : Odd m := by
      dsimp [m, k]
      exact odd_div_gcd_2015 (a.1 + 1)
    rw [Finset.prod_fin_eq_prod_range]
    have hfin :
        (∏ i ∈ Finset.range 2015,
          (if h : i < 2015 then
            (1 + Complex.exp
              (2 * Real.pi * Complex.I * (a.1 + 1) *
                (↑(⟨i, h⟩ : Fin 2015).1 + 1) / 2015))
          else 1)) =
          (∏ x ∈ Finset.range 2015,
            (1 + Complex.exp
              (2 * Real.pi * Complex.I * (a.1 + 1) * (x + 1) / 2015))) := by
      refine Finset.prod_congr rfl ?_
      intro x hx
      have hxlt : x < 2015 := Finset.mem_range.mp hx
      simp [hxlt]
    have hconv :
        (∏ x ∈ Finset.range 2015,
          (1 + Complex.exp
            (2 * Real.pi * Complex.I * (a.1 + 1) * (x + 1) / 2015))) =
          ∏ x ∈ Finset.range 2015, (1 + (ζ ^ k) ^ (x + 1)) := by
      refine Finset.prod_congr rfl ?_
      intro x hx
      dsimp [ζ, k]
      rw [complex_exp_mul_nat_nat (a.1) x]
    rw [hfin, hconv]
    have hperiod := prod_one_add_periods (m := m) (d := d) (η := ζ ^ k) hm_odd hη
    rw [hdm] at hperiod
    simpa [d] using hperiod
  calc
    (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp
          (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015)))
        = ∏ a : Fin 2015, (2 : ℂ) ^ Nat.gcd 2015 (a.1 + 1) := by
          exact Finset.prod_congr rfl (fun a _ ↦ hrow a)
    _ = (2 : ℂ) ^ (∑ a : Fin 2015, Nat.gcd 2015 (a.1 + 1)) := by
          exact Finset.prod_pow_eq_pow_sum Finset.univ (fun a : Fin 2015 ↦ Nat.gcd 2015 (a.1 + 1)) (2 : ℂ)
    _ = (2 : ℂ) ^ 13725 := by rw [sum_gcd_2015]

private lemma log_two_pow_13725 :
    Complex.log ((2 : ℂ) ^ 13725) / Complex.log 2 = (13725 : ℂ) := by
  have hlog2_ne : Complex.log (2 : ℂ) ≠ 0 := by
    change Complex.log (((2 : ℝ) : ℂ)) ≠ 0
    rw [← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
  change Complex.log (((2 : ℝ) : ℂ) ^ 13725) / Complex.log (((2 : ℝ) : ℂ)) = (13725 : ℂ)
  rw [← Complex.ofReal_pow (2 : ℝ) 13725,
    ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 ^ 13725),
    Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_div_cancel_right₀ (13725 : ℂ) hlog2_ne

/--
Compute $\log_2 \left( \prod_{a=1}^{2015}\prod_{b=1}^{2015}(1+e^{2\pi iab/2015}) \right)$. Here $i$ is the imaginary unit (that is, $i^2=-1$).
-/
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution :=
by
  rw [putnam_2015_a3_solution, prod_rows]
  exact log_two_pow_13725
