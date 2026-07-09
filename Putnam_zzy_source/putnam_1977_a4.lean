import Mathlib

open RingHom Set Polynomial
open Filter
open scoped Topology BigOperators

noncomputable abbrev putnam_1977_a4_solution : RatFunc ℝ :=
  -(RatFunc.X / (RatFunc.X - 1))

/--
Find $\sum_{n=0}^{\infty} \frac{x^{2^n}}{1 - x^{2^{n+1}}}$ as a rational function of $x$ for $x \in (0, 1)$.
-/
theorem putnam_1977_a4 :
    ∀ x ∈ Ioo 0 1,
      putnam_1977_a4_solution.eval (id ℝ) x = ∑' n : ℕ, x ^ 2 ^ n / (1 - x ^ 2 ^ (n + 1)) :=
  by
  intro x hx
  have hx0 : 0 ≤ x := le_of_lt hx.1
  have hx1 : x < 1 := hx.2
  have heval :
      putnam_1977_a4_solution.eval (id ℝ) x = x * (1 - x)⁻¹ := by
    have hexplicit :
        RatFunc.eval (id ℝ) x
            ((algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X) /
              (algebraMap ℝ[X] (RatFunc ℝ) (1 - Polynomial.X))) =
          x / (1 - x) := by
      let P : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X
      let Q : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) (1 - Polynomial.X)
      have hQpoly : (1 - Polynomial.X : ℝ[X]) ≠ 0 := by
        intro h
        have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) h
        simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X, ↓reduceIte] at hcoeff
        norm_num at hcoeff
      have hQne : Q ≠ 0 := RatFunc.algebraMap_ne_zero hQpoly
      have hdenQ : Polynomial.eval₂ (id ℝ) x (RatFunc.denom Q) ≠ 0 := by
        dsimp [Q]
        rw [RatFunc.denom_algebraMap]
        norm_num
      have hdenSol : Polynomial.eval₂ (id ℝ) x (RatFunc.denom (P / Q)) ≠ 0 := by
        change
          Polynomial.eval₂ (id ℝ) x
            (RatFunc.denom
              ((algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X) /
                (algebraMap ℝ[X] (RatFunc ℝ) (1 - Polynomial.X)))) ≠ 0
        intro hden
        rcases RatFunc.denom_div_dvd (K := ℝ) (Polynomial.X : ℝ[X])
            (1 - Polynomial.X : ℝ[X]) with ⟨r, hr⟩
        have hqeval : Polynomial.eval₂ (id ℝ) x (1 - Polynomial.X : ℝ[X]) = 0 := by
          rw [hr, Polynomial.eval₂_mul, hden, zero_mul]
        have : 1 - x = 0 := by
          simpa using hqeval
        linarith
      have hmul :=
        RatFunc.eval_mul (f := (id ℝ)) (a := x) (x := P / Q) (y := Q) hdenSol hdenQ
      have hQeval : RatFunc.eval (id ℝ) x Q = 1 - x := by
        change RatFunc.eval (id ℝ) x
          (algebraMap ℝ[X] (RatFunc ℝ) (1 - Polynomial.X)) = 1 - x
        rw [RatFunc.eval_algebraMap]
        simp
      have hPeval : RatFunc.eval (id ℝ) x P = x := by
        change RatFunc.eval (id ℝ) x (algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X) = x
        rw [RatFunc.eval_algebraMap]
        simp
      have hprod : RatFunc.eval (id ℝ) x (P / Q) * (1 - x) = x := by
        rw [← hQeval, ← hmul, div_mul_cancel₀ P hQne, hPeval]
      have h1x : 1 - x ≠ 0 := by linarith
      change RatFunc.eval (id ℝ) x (P / Q) = x / (1 - x)
      exact (eq_div_iff h1x).2 hprod
    have hsol :
        putnam_1977_a4_solution =
        (algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X) /
          (algebraMap ℝ[X] (RatFunc ℝ) (1 - Polynomial.X)) := by
      rw [putnam_1977_a4_solution, ← neg_div, ← RatFunc.algebraMap_X]
      have hden :
          ((algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X) - 1 : RatFunc ℝ) =
            -(algebraMap ℝ[X] (RatFunc ℝ) (1 - Polynomial.X)) := by
        simp [sub_eq_add_neg, add_comm]
      rw [hden]
      exact neg_div_neg_eq (algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X)
        (algebraMap ℝ[X] (RatFunc ℝ) (1 - Polynomial.X))
    rw [hsol]
    exact hexplicit.trans (by rw [div_eq_mul_inv])
  have hseries :
      (∑' n : ℕ, x ^ 2 ^ n / (1 - x ^ 2 ^ (n + 1))) = (1 - x)⁻¹ - 1 := by
    let f : ℕ → ℝ := fun n => x ^ 2 ^ n / (1 - x ^ 2 ^ (n + 1))
    let u : ℕ → ℝ := fun n => (1 - x ^ 2 ^ n)⁻¹
    have hterm (n : ℕ) : f n = u n - u (n + 1) := by
      dsimp [f]
      let y := x ^ 2 ^ n
      have hpow : x ^ 2 ^ (n + 1) = y ^ 2 := by
        dsimp [y]
        rw [show 2 ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
        rw [pow_mul]
      have hden1 : 1 - y ≠ 0 := by
        have hlt : y < 1 := by
          dsimp [y]
          exact pow_lt_one₀ hx0 hx1 (Nat.two_pow_pos n).ne'
        linarith
      have hden2 : 1 - y ^ 2 ≠ 0 := by
        have hlt : y ^ 2 < 1 := by
          rw [← hpow]
          exact pow_lt_one₀ hx0 hx1 (Nat.two_pow_pos (n + 1)).ne'
        linarith
      dsimp [u]
      rw [hpow]
      change y / (1 - y ^ 2) = (1 - y)⁻¹ - (1 - y ^ 2)⁻¹
      field_simp [hden1, hden2]
      ring
    have hnonneg : ∀ n, 0 ≤ f n := by
      intro n
      dsimp [f]
      have hnum : 0 ≤ x ^ 2 ^ n := pow_nonneg hx0 _
      have hdenpos : 0 < 1 - x ^ 2 ^ (n + 1) := by
        have hlt : x ^ 2 ^ (n + 1) < 1 :=
          pow_lt_one₀ hx0 hx1 (Nat.two_pow_pos (n + 1)).ne'
        linarith
      exact div_nonneg hnum hdenpos.le
    have hpartial (N : ℕ) :
        (∑ n ∈ Finset.range N, f n) = (1 - x)⁻¹ - (1 - x ^ 2 ^ N)⁻¹ := by
      calc
        (∑ n ∈ Finset.range N, f n) =
            ∑ n ∈ Finset.range N, (u n - u (n + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          exact hterm n
        _ = u 0 - u N := Finset.sum_range_sub' u N
        _ = (1 - x)⁻¹ - (1 - x ^ 2 ^ N)⁻¹ := by
          simp [u]
    have hpowlim : Tendsto (fun N : ℕ => x ^ ((2 : ℕ) ^ N)) atTop (𝓝 0) := by
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have htaillim : Tendsto (fun N : ℕ => (1 - x ^ 2 ^ N)⁻¹) atTop (𝓝 1) := by
      have hbase : Tendsto (fun N : ℕ => 1 - x ^ 2 ^ N) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub hpowlim
      have hinv := hbase.inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
      simpa using hinv
    have hpartiallim :
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop
          (𝓝 ((1 - x)⁻¹ - 1)) := by
      have hclosed :
          Tendsto (fun N : ℕ => (1 - x)⁻¹ - (1 - x ^ 2 ^ N)⁻¹) atTop
            (𝓝 ((1 - x)⁻¹ - 1)) :=
        tendsto_const_nhds.sub htaillim
      exact Filter.Tendsto.congr' (Eventually.of_forall fun N => (hpartial N).symm) hclosed
    have hhas : HasSum f ((1 - x)⁻¹ - 1) :=
      (hasSum_iff_tendsto_nat_of_nonneg hnonneg ((1 - x)⁻¹ - 1)).2 hpartiallim
    calc
      (∑' n : ℕ, x ^ 2 ^ n / (1 - x ^ 2 ^ (n + 1))) = ∑' n : ℕ, f n := by
        rfl
      _ = (1 - x)⁻¹ - 1 := hhas.tsum_eq
  have hclosed : (1 - x)⁻¹ - 1 = x * (1 - x)⁻¹ := by
    have h1x : 1 - x ≠ 0 := by linarith
    field_simp [h1x]
    ring
  exact heval.trans ((hclosed.symm).trans hseries.symm)
