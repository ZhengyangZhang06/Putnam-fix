import Mathlib

open RingHom Set Filter

-- RatFunc.X / (1 - RatFunc.X)
/--
Find $\sum_{n=0}^{\infty} \frac{x^{2^n}}{1 - x^{2^{n+1}}}$ as a rational function of $x$ for $x \in (0, 1)$.
-/
theorem putnam_1977_a4 :
    ∀ x ∈ Ioo 0 1,
      ((RatFunc.X / (1 - RatFunc.X)) : RatFunc ℝ ).eval (id ℝ) x = ∑' n : ℕ, x ^ 2 ^ n / (1 - x ^ 2 ^ (n + 1)) := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hrat : ((RatFunc.X / (1 - RatFunc.X)) : RatFunc ℝ).eval (id ℝ) x = x / (1 - x) := by
    have hgcd : gcd (Polynomial.X : Polynomial ℝ) (1 - Polynomial.X) = (1 : Polynomial ℝ) := by
      have hdvd1 : gcd (Polynomial.X : Polynomial ℝ) (1 - Polynomial.X) ∣ (1 : Polynomial ℝ) := by
        have hsum :
            gcd (Polynomial.X : Polynomial ℝ) (1 - Polynomial.X) ∣
              Polynomial.X + (1 - Polynomial.X) :=
          dvd_add (gcd_dvd_left _ _) (gcd_dvd_right _ _)
        simpa using hsum
      simpa using (gcd_eq_normalize hdvd1 (one_dvd _))
    have hlead : (1 - Polynomial.X : Polynomial ℝ).leadingCoeff = -1 := by
      rw [show (1 - Polynomial.X : Polynomial ℝ) = -(Polynomial.X - Polynomial.C 1) by
        ext n
        by_cases hn : n = 0
        · subst n
          simp
        · by_cases hn1 : n = 1
          · subst n
            simp
          · simp [Polynomial.coeff_X]]
      rw [Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X_sub_C]
    have hnum : ((RatFunc.X / (1 - RatFunc.X)) : RatFunc ℝ).num = -Polynomial.X := by
      rw [← RatFunc.algebraMap_X]
      rw [← map_one (algebraMap (Polynomial ℝ) (RatFunc ℝ)), ← map_sub]
      rw [RatFunc.num_div]
      rw [hgcd]
      simp [hlead]
    have hden : ((RatFunc.X / (1 - RatFunc.X)) : RatFunc ℝ).denom = Polynomial.X - 1 := by
      rw [← RatFunc.algebraMap_X]
      rw [← map_one (algebraMap (Polynomial ℝ) (RatFunc ℝ)), ← map_sub]
      rw [RatFunc.denom_div]
      · rw [hgcd]
        ext n
        by_cases hn : n = 0
        · subst n
          simp [hlead]
        · by_cases hn1 : n = 1
          · subst n
            simp [hlead]
          · simp [Polynomial.coeff_X, hlead]
      · intro h
        have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 1) h
        change (1 - Polynomial.X : Polynomial ℝ).coeff 1 = (0 : Polynomial ℝ).coeff 1 at hcoeff
        simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one] at hcoeff
    rw [RatFunc.eval, hnum, hden]
    simp
    rw [show (1 - x) = -(x - 1) by ring]
    have hxne : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx1)
    field_simp [hxne]
  let f : ℕ → ℝ := fun n => x ^ 2 ^ n / (1 - x ^ 2 ^ (n + 1))
  let g : ℕ → ℝ := fun n => 1 / (1 - x ^ 2 ^ n)
  have hterm : ∀ n : ℕ, f n = g n - g (n + 1) := by
    intro n
    change x ^ 2 ^ n / (1 - x ^ 2 ^ (n + 1)) =
      1 / (1 - x ^ 2 ^ n) - 1 / (1 - x ^ 2 ^ (n + 1))
    have hpow : x ^ 2 ^ (n + 1) = (x ^ 2 ^ n) ^ 2 := by
      rw [← pow_mul]
      congr 1
    have hnz0 : 1 - x ^ 2 ^ n ≠ 0 := by
      have hlt : x ^ 2 ^ n < 1 := pow_lt_one₀ hx0.le hx1 (ne_of_gt (Nat.two_pow_pos n))
      exact sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
    have hnz1 : 1 - x ^ 2 ^ (n + 1) ≠ 0 := by
      have hlt : x ^ 2 ^ (n + 1) < 1 :=
        pow_lt_one₀ hx0.le hx1 (ne_of_gt (Nat.two_pow_pos (n + 1)))
      exact sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
    have hnz2 : 1 - (x ^ 2 ^ n) ^ 2 ≠ 0 := by
      simpa [← hpow] using hnz1
    rw [hpow]
    field_simp [hnz0, hnz2]
    ring
  have hpartial :
      ∀ N : ℕ, (∑ n ∈ Finset.range N, f n) = g 0 - g N := by
    intro N
    calc
      (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range N, (g n - g (n + 1)) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact hterm n
      _ = g 0 - g N := Finset.sum_range_sub' g N
  have hxpow : Tendsto (fun N : ℕ => x ^ 2 ^ N) atTop (nhds 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
  have htail : Tendsto g atTop (nhds 1) := by
    have hdenlim : Tendsto (fun N : ℕ => 1 - x ^ 2 ^ N) atTop (nhds (1 - 0)) := by
      exact tendsto_const_nhds.sub hxpow
    have hdiv := (tendsto_const_nhds (x := (1 : ℝ))).div hdenlim
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using hdiv.congr (by intro N; simp [g])
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (nhds (x / (1 - x))) := by
    have hlim' : Tendsto (fun N : ℕ => g 0 - g N) atTop (nhds (g 0 - 1)) := by
      exact tendsto_const_nhds.sub htail
    have hlimsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (nhds (g 0 - 1)) := by
      exact hlim'.congr (by intro N; exact (hpartial N).symm)
    have hg0 : g 0 - 1 = x / (1 - x) := by
      have hxne : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hx1))
      simp [g]
      field_simp [hxne]
      ring
    simpa [hg0] using hlimsum
  have hnonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    have hnum_nonneg : 0 ≤ x ^ 2 ^ n := (pow_pos hx0 _).le
    have hdenpos : 0 < 1 - x ^ 2 ^ (n + 1) :=
      sub_pos.mpr (pow_lt_one₀ hx0.le hx1 (ne_of_gt (Nat.two_pow_pos (n + 1))))
    exact div_nonneg hnum_nonneg hdenpos.le
  have hsum : HasSum f (x / (1 - x)) :=
    (hasSum_iff_tendsto_nat_of_nonneg hnonneg (x / (1 - x))).2 hlim
  rw [hrat]
  exact hsum.tsum_eq.symm
