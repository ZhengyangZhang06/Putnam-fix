import Mathlib

abbrev putnam_2006_a5_solution : ℕ → ℤ :=
  fun n => (-1 : ℤ) ^ (n / 2) * n

noncomputable section

open Polynomial Finset Complex

private noncomputable def putnam_2006_a5_finIccOneEquiv (n : ℕ) : Fin n ≃ Set.Icc 1 n where
  toFun i := ⟨i.1 + 1, by
    constructor
    · omega
    · exact Nat.succ_le_of_lt i.2⟩
  invFun k := ⟨k.1 - 1, by
    have hk1 : 1 ≤ k.1 := k.2.1
    have hkn : k.1 ≤ n := k.2.2
    omega⟩
  left_inv i := by
    ext
    simp
  right_inv k := by
    ext
    change (k.1 - 1) + 1 = k.1
    have hk1 : 1 ≤ k.1 := k.2.1
    omega

private def putnam_2006_a5_sample (theta : ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  theta + (((i.1 + 1 : ℕ) : ℝ) * Real.pi) / n

private lemma putnam_2006_a5_exp_two_sub_one (x : ℝ) :
    Complex.exp ((2*x : ℝ) * Complex.I) - 1 =
      2 * Complex.I * (Real.sin x : ℂ) * Complex.exp ((x : ℝ) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sin]
  rw [Complex.cos_two_mul, Complex.sin_two_mul]
  have hsq : Complex.cos (x : ℂ) ^ 2 = 1 - Complex.sin (x : ℂ) ^ 2 := by
    calc
      Complex.cos (x : ℂ) ^ 2 =
          (Complex.sin (x : ℂ) ^ 2 + Complex.cos (x : ℂ) ^ 2) -
            Complex.sin (x : ℂ) ^ 2 := by ring
      _ = 1 - Complex.sin (x : ℂ) ^ 2 := by rw [Complex.sin_sq_add_cos_sq]
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  rw [hsq]
  ring_nf
  rw [hI2]
  ring

private lemma putnam_2006_a5_exp_two_add_one (x : ℝ) :
    Complex.exp ((2*x : ℝ) * Complex.I) + 1 =
      2 * (Real.cos x : ℂ) * Complex.exp ((x : ℝ) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos]
  rw [Complex.cos_two_mul, Complex.sin_two_mul]
  ring_nf

private lemma putnam_2006_a5_tan_exp (x : ℝ) (hx : Real.cos x ≠ 0) :
    ((Real.tan x : ℂ) = -Complex.I *
      ((Complex.exp ((2*x : ℝ) * Complex.I) - 1) /
        (Complex.exp ((2*x : ℝ) * Complex.I) + 1))) := by
  rw [Real.tan_eq_sin_div_cos]
  rw [putnam_2006_a5_exp_two_sub_one x, putnam_2006_a5_exp_two_add_one x]
  simp only [Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_cos]
  have hcos : (Real.cos x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hexp : Complex.exp ((x : ℝ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  field_simp [hcos, hexp]
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  rw [hI2]
  ring

private lemma putnam_2006_a5_prod_one_sub_roots
    (n : ℕ) (hn : 0 < n) (α ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) :
    ∏ i ∈ Finset.range n, (1 - ζ ^ i * α) = 1 - α ^ n := by
  have hpoly : (Polynomial.X ^ n - Polynomial.C (α ^ n) : ℂ[X]) =
      ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * α)) :=
    X_pow_sub_C_eq_prod hζ hn rfl
  have h := congrArg (fun p : ℂ[X] => Polynomial.eval 1 p) hpoly
  simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.symm

private lemma putnam_2006_a5_prod_mobius
    (n : ℕ) (hn : 0 < n) (hnodd : Odd n) (α ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ n) :
    ∏ i ∈ Finset.range n, ((α * ζ ^ i - 1) / (α * ζ ^ i + 1)) =
      (α ^ n - 1) / (α ^ n + 1) := by
  have hnum0 := putnam_2006_a5_prod_one_sub_roots n hn α ζ hζ
  have hnum : ∏ i ∈ Finset.range n, (α * ζ ^ i - 1) = α ^ n - 1 := by
    calc
      ∏ i ∈ Finset.range n, (α * ζ ^ i - 1)
          = ∏ i ∈ Finset.range n, (-(1 - ζ ^ i * α)) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              ring
      _ = (-1 : ℂ) ^ (Finset.range n).card *
            ∏ i ∈ Finset.range n, (1 - ζ ^ i * α) := by
              rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl ?_
              intro i hi
              ring
      _ = (-1 : ℂ) ^ n * (1 - α ^ n) := by simp [hnum0]
      _ = α ^ n - 1 := by
              rw [hnodd.neg_one_pow]
              ring
  have hden0 := putnam_2006_a5_prod_one_sub_roots n hn (-α) ζ hζ
  have hden : ∏ i ∈ Finset.range n, (α * ζ ^ i + 1) = α ^ n + 1 := by
    calc
      ∏ i ∈ Finset.range n, (α * ζ ^ i + 1)
          = ∏ i ∈ Finset.range n, (1 - ζ ^ i * (-α)) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              ring
      _ = 1 - (-α) ^ n := hden0
      _ = α ^ n + 1 := by
              rw [hnodd.neg_pow]
              ring
  rw [Finset.prod_div_distrib, hnum, hden]

private lemma putnam_2006_a5_factor_ne
    (n i : ℕ) (hnodd : Odd n) (α ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ n) (hden : α ^ n + 1 ≠ 0) :
    α * ζ ^ i + 1 ≠ 0 := by
  intro hq
  have hqeq : α * ζ ^ i = -1 := eq_neg_of_add_eq_zero_left hq
  have hpow1 : (α * ζ ^ i) ^ n = α ^ n := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm i n, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hpow2 : (α * ζ ^ i) ^ n = (-1 : ℂ) ^ n := by rw [hqeq]
  have hα : α ^ n = -1 := by
    rw [← hpow1, hpow2, hnodd.neg_one_pow]
  apply hden
  rw [hα]
  ring

private lemma putnam_2006_a5_sum_inv_one_add_roots
    (n : ℕ) (hnodd : Odd n) (α ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ n) (hden : α ^ n + 1 ≠ 0) :
    ∑ i ∈ Finset.range n, (1 / (α * ζ ^ i + 1)) = (n : ℂ) / (α ^ n + 1) := by
  let f : ℂ[X] := Polynomial.X ^ n - Polynomial.C ((-α) ^ n)
  have hf : f.Splits :=
    X_pow_sub_C_splits_of_isPrimitiveRoot hζ (α := -α) (a := (-α)^n) rfl
  have hx : Polynomial.eval (1 : ℂ) f ≠ 0 := by
    dsimp [f]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [hnodd.neg_pow]
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using hden
  have h := hf.eval_derivative_div_eval_of_ne_zero hx
  have hroots : f.roots = (Multiset.range n).map (fun i => ζ ^ i * (-α)) := by
    dsimp [f]
    simpa [Polynomial.nthRoots] using hζ.nthRoots_eq (α := -α) (a := (-α)^n) rfl
  rw [hroots] at h
  dsimp [f] at h
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C] at h
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_zero, sub_zero] at h
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [hnodd.neg_pow] at h
  simp only [one_pow, mul_one] at h
  have h' : (n : ℂ) / (α ^ n + 1) =
      (Multiset.map (fun z => 1 / (1 - z))
        (Multiset.map (fun i => ζ ^ i * -α) (Multiset.range n))).sum := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using h
  rw [h']
  simp only [one_div]
  change (Multiset.map (fun x => (α * ζ ^ x + 1)⁻¹) (Multiset.range n)).sum =
    (Multiset.map (fun z => (1 - z)⁻¹)
      (Multiset.map (fun i => ζ ^ i * -α) (Multiset.range n))).sum
  simp [mul_comm, add_comm, sub_eq_add_neg]

private lemma putnam_2006_a5_sum_mobius
    (n : ℕ) (hnodd : Odd n) (α ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ n) (hden : α ^ n + 1 ≠ 0) :
    ∑ i ∈ Finset.range n, ((α * ζ ^ i - 1) / (α * ζ ^ i + 1)) =
      (n : ℂ) * (α ^ n - 1) / (α ^ n + 1) := by
  have hinv := putnam_2006_a5_sum_inv_one_add_roots n hnodd α ζ hζ hden
  calc
    ∑ i ∈ Finset.range n, ((α * ζ ^ i - 1) / (α * ζ ^ i + 1))
        = ∑ i ∈ Finset.range n, (1 - 2 * (1 / (α * ζ ^ i + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hq := putnam_2006_a5_factor_ne n i hnodd α ζ hζ hden
            field_simp [hq]
            ring
    _ = (n : ℂ) - 2 * ((n : ℂ) / (α ^ n + 1)) := by
            rw [Finset.sum_sub_distrib]
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
            rw [← Finset.mul_sum]
            rw [hinv]
    _ = (n : ℂ) * (α ^ n - 1) / (α ^ n + 1) := by
            field_simp [hden]
            ring

private lemma putnam_2006_a5_negI_pow_odd (n : ℕ) (hn : Odd n) :
    (-Complex.I : ℂ) ^ n = (-1 : ℂ) ^ ((n - 1) / 2) * (-Complex.I) := by
  rcases hn with ⟨m, rfl⟩
  have hm : ((2 * m + 1 - 1) / 2 : ℕ) = m := by omega
  rw [hm]
  calc
    (-Complex.I : ℂ) ^ (2 * m + 1) = (-Complex.I : ℂ) ^ (2 * m) * (-Complex.I) := by
      rw [pow_succ]
    _ = ((-Complex.I : ℂ) ^ 2) ^ m * (-Complex.I) := by
      rw [pow_mul]
    _ = (-1 : ℂ) ^ m * (-Complex.I) := by
      have hI2 : (-Complex.I : ℂ) ^ 2 = -1 := by
        rw [sq, neg_mul_neg, Complex.I_mul_I]
      rw [hI2]

private lemma putnam_2006_a5_cos_sample_ne_zero
    (theta : ℝ) (n i : ℕ) (hn : 0 < n)
    (hirr : Irrational (theta / Real.pi)) :
    Real.cos (theta + ((i + 1 : ℕ) : ℝ) * Real.pi / n) ≠ 0 := by
  intro hcos
  rcases Real.cos_eq_zero_iff.mp hcos with ⟨m, hm⟩
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have htheta : theta =
      (2 * (m : ℝ) + 1) * Real.pi / 2 - ((i + 1 : ℕ) : ℝ) * Real.pi / n := by
    linarith
  have hrat :
      theta / Real.pi =
        ((2 * m + 1 : ℤ) : ℝ) / 2 - ((i + 1 : ℕ) : ℝ) / (n : ℝ) := by
    rw [htheta]
    field_simp [Real.pi_ne_zero, hnR]
    norm_num
    ring
  exact hirr ⟨(((2 * m + 1 : ℤ) : ℚ) / 2 - ((i + 1 : ℕ) : ℚ) / (n : ℚ)), by
    rw [hrat]
    norm_num [Rat.cast_sub, Rat.cast_div]
  ⟩

private lemma putnam_2006_a5_exp_sample_eq (theta : ℝ) (n : ℕ) (i : ℕ) :
    Complex.exp (((2 * (theta + ((i + 1 : ℕ) : ℝ) * Real.pi / n) : ℝ) : ℂ) *
        Complex.I) =
      Complex.exp (((2 * (theta + Real.pi / n) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) ^ i := by
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring

private lemma putnam_2006_a5_alpha_pow (theta : ℝ) (n : ℕ) (hn : 0 < n) :
    Complex.exp (((2 * (theta + Real.pi / n) : ℝ) : ℂ) * Complex.I) ^ n =
      Complex.exp (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  trans Complex.exp ((((2 * (n : ℝ) * theta + 2 * Real.pi : ℝ) : ℂ) * Complex.I))
  · congr 1
    apply Complex.ext
    · simp
    · simp
      field_simp [hnR]
  · have harg : (((2 * (n : ℝ) * theta + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) +
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    rw [harg, Complex.exp_add]
    have htwopi : (((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        2 * ↑Real.pi * Complex.I := by
      apply Complex.ext <;> simp [mul_comm, mul_left_comm]
    rw [htwopi, Complex.exp_two_pi_mul_I]
    simp

private lemma putnam_2006_a5_exp_two_n_theta_ne_one
    (theta : ℝ) (n : ℕ) (hn : 0 < n)
    (hirr : Irrational (theta / Real.pi)) :
    Complex.exp (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  intro h
  rcases Complex.exp_eq_one_iff.mp h with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp at him
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrat : theta / Real.pi = (m : ℝ) / (n : ℝ) := by
    field_simp [Real.pi_ne_zero, hnR] at him ⊢
    linarith
  exact hirr.ne_rat (m / n) (by norm_num [Rat.cast_div, hrat])

private lemma putnam_2006_a5_exp_two_n_theta_ne_neg_one
    (theta : ℝ) (n : ℕ) (hn : 0 < n)
    (hirr : Irrational (theta / Real.pi)) :
    Complex.exp (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) ≠ -1 := by
  intro h
  have h' : Complex.exp (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [Complex.exp_pi_mul_I]
    exact h
  rcases Complex.exp_eq_exp_iff_exists_int.mp h' with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp at him
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrat : theta / Real.pi =
      ((2 * m + 1 : ℤ) : ℝ) / (2 * (n : ℝ)) := by
    field_simp [Real.pi_ne_zero, hnR]
    calc
      theta * 2 * (n : ℝ) = 2 * (n : ℝ) * theta := by ring
      _ = Real.pi + (m : ℝ) * (2 * Real.pi) := him
      _ = Real.pi * ((2 * m + 1 : ℤ) : ℝ) := by norm_num; ring_nf
  exact hirr ⟨(((2 * m + 1 : ℤ) : ℚ) / (2 * (n : ℚ))), by
    rw [hrat]
    norm_num [Rat.cast_div]
  ⟩

/--
Let $n$ be a positive odd integer and let $\theta$ be a real number such that $\theta/\pi$ is irrational. Set $a_k=\tan(\theta+k\pi/n)$, $k=1,2,\dots,n$. Prove that $\frac{a_1+a_2+\cdots+a_n}{a_1a_2 \cdots a_n}$ is an integer, and determine its value.
-/
theorem putnam_2006_a5
(n : ℕ)
(theta : ℝ)
(a : Set.Icc 1 n → ℝ)
(nodd : Odd n)
(thetairr : Irrational (theta / Real.pi))
(ha : ∀ k : Set.Icc 1 n, a k = Real.tan (theta + (k * Real.pi) / n))
: (∑ k : Set.Icc 1 n, a k) / (∏ k : Set.Icc 1 n, a k) = putnam_2006_a5_solution n :=
by
  have hnpos : 0 < n := nodd.pos
  let α : ℂ := Complex.exp (((2 * (theta + Real.pi / n) : ℝ) : ℂ) * Complex.I)
  let ζ : ℂ := Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I)
  have hζ : IsPrimitiveRoot ζ n := by
    dsimp [ζ]
    convert Complex.isPrimitiveRoot_exp n hnpos.ne' using 2
    norm_num
    ring
  have hαpow :
      α ^ n = Complex.exp (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
    dsimp [α]
    exact putnam_2006_a5_alpha_pow theta n hnpos
  have hden : α ^ n + 1 ≠ 0 := by
    rw [hαpow]
    intro h
    have hexp : Complex.exp (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) = -1 :=
      eq_neg_of_add_eq_zero_left h
    exact putnam_2006_a5_exp_two_n_theta_ne_neg_one theta n hnpos thetairr hexp
  have hnum : α ^ n - 1 ≠ 0 := by
    rw [hαpow]
    intro h
    have hexp : Complex.exp (((2 * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I) = 1 :=
      sub_eq_zero.mp h
    exact putnam_2006_a5_exp_two_n_theta_ne_one theta n hnpos thetairr hexp
  let T : ℂ := -Complex.I * ((α ^ n - 1) / (α ^ n + 1))
  have hT : T ≠ 0 := by
    dsimp [T]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (div_ne_zero hnum hden)
  have hsum_reindex :
      (∑ k : Set.Icc 1 n, a k) =
        ∑ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i) := by
    calc
      (∑ k : Set.Icc 1 n, a k) =
          ∑ i : Fin n, a (putnam_2006_a5_finIccOneEquiv n i) := by
            symm
            exact Fintype.sum_equiv (putnam_2006_a5_finIccOneEquiv n)
              (fun i => a (putnam_2006_a5_finIccOneEquiv n i)) a (by intro i; rfl)
      _ = ∑ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [ha]
            simp [putnam_2006_a5_finIccOneEquiv, putnam_2006_a5_sample]
  have hprod_reindex :
      (∏ k : Set.Icc 1 n, a k) =
        ∏ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i) := by
    calc
      (∏ k : Set.Icc 1 n, a k) =
          ∏ i : Fin n, a (putnam_2006_a5_finIccOneEquiv n i) := by
            symm
            exact Fintype.prod_equiv (putnam_2006_a5_finIccOneEquiv n)
              (fun i => a (putnam_2006_a5_finIccOneEquiv n i)) a (by intro i; rfl)
      _ = ∏ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [ha]
            simp [putnam_2006_a5_finIccOneEquiv, putnam_2006_a5_sample]
  have htan : ∀ i : Fin n,
      ((Real.tan (putnam_2006_a5_sample theta n i) : ℂ) =
        -Complex.I * ((α * ζ ^ (i.1) - 1) / (α * ζ ^ (i.1) + 1))) := by
    intro i
    have hc := putnam_2006_a5_cos_sample_ne_zero theta n i.1 hnpos thetairr
    rw [putnam_2006_a5_tan_exp (putnam_2006_a5_sample theta n i) hc]
    have hq := putnam_2006_a5_exp_sample_eq theta n i.1
    dsimp [putnam_2006_a5_sample, α, ζ] at hq ⊢
    rw [hq]
  have hsumC :
      (((∑ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) : ℝ) : ℂ) =
        (n : ℂ) * T := by
    calc
      (((∑ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) : ℝ) : ℂ)
          = ∑ i : Fin n, ((Real.tan (putnam_2006_a5_sample theta n i) : ℂ)) := by
              norm_cast
      _ = ∑ i : Fin n,
            (-Complex.I * ((α * ζ ^ (i.1) - 1) / (α * ζ ^ (i.1) + 1))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [htan]
      _ = -Complex.I *
            ∑ i : Fin n, ((α * ζ ^ (i.1) - 1) / (α * ζ ^ (i.1) + 1)) := by
              rw [Finset.mul_sum]
      _ = -Complex.I *
            (∑ i ∈ Finset.range n, ((α * ζ ^ i - 1) / (α * ζ ^ i + 1))) := by
              rw [Fin.sum_univ_eq_sum_range
                (fun i => ((α * ζ ^ i - 1) / (α * ζ ^ i + 1))) n]
      _ = -Complex.I * ((n : ℂ) * (α ^ n - 1) / (α ^ n + 1)) := by
              rw [putnam_2006_a5_sum_mobius n nodd α ζ hζ hden]
      _ = (n : ℂ) * T := by
              dsimp [T]
              ring
  have hprodC :
      (((∏ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) : ℝ) : ℂ) =
        (-1 : ℂ) ^ ((n - 1) / 2) * T := by
    calc
      (((∏ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) : ℝ) : ℂ)
          = ∏ i : Fin n, ((Real.tan (putnam_2006_a5_sample theta n i) : ℂ)) := by
              norm_cast
      _ = ∏ i : Fin n,
            (-Complex.I * ((α * ζ ^ (i.1) - 1) / (α * ζ ^ (i.1) + 1))) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              rw [htan]
      _ = (∏ _i : Fin n, (-Complex.I : ℂ)) *
            ∏ i : Fin n, ((α * ζ ^ (i.1) - 1) / (α * ζ ^ (i.1) + 1)) := by
              rw [← Finset.prod_mul_distrib]
      _ = (-Complex.I : ℂ) ^ n *
            ∏ i : Fin n, ((α * ζ ^ (i.1) - 1) / (α * ζ ^ (i.1) + 1)) := by
              simp
      _ = (-Complex.I : ℂ) ^ n * ((α ^ n - 1) / (α ^ n + 1)) := by
              rw [Fin.prod_univ_eq_prod_range
                (fun i => ((α * ζ ^ i - 1) / (α * ζ ^ i + 1))) n]
              rw [putnam_2006_a5_prod_mobius n hnpos nodd α ζ hζ]
      _ = (-1 : ℂ) ^ ((n - 1) / 2) * T := by
              rw [putnam_2006_a5_negI_pow_odd n nodd]
              dsimp [T]
              ring
  have hratioC :
      ((((∑ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) /
        (∏ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i))) : ℝ) : ℂ) =
        (((putnam_2006_a5_solution n : ℤ) : ℝ) : ℂ) := by
    calc
      ((((∑ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) /
        (∏ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i))) : ℝ) : ℂ)
          =
        (((∑ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) : ℝ) : ℂ) /
          (((∏ i : Fin n, Real.tan (putnam_2006_a5_sample theta n i)) : ℝ) : ℂ) := by
              norm_cast
      _ = ((n : ℂ) * T) / (((-1 : ℂ) ^ ((n - 1) / 2)) * T) := by
              rw [hsumC, hprodC]
      _ = (-1 : ℂ) ^ ((n - 1) / 2) * (n : ℂ) := by
              have hs : (-1 : ℂ) ^ ((n - 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
              field_simp [hT, hs]
              have hs2 : ((-1 : ℂ) ^ ((n - 1) / 2)) ^ 2 = 1 := by
                rcases neg_one_pow_eq_or ℂ ((n - 1) / 2) with h | h <;> rw [h] <;> norm_num
              rw [hs2, mul_one]
      _ = (((putnam_2006_a5_solution n : ℤ) : ℝ) : ℂ) := by
              have hsolZ : (-1 : ℤ) ^ ((n - 1) / 2) * (n : ℤ) =
                  putnam_2006_a5_solution n := by
                dsimp [putnam_2006_a5_solution]
                rcases nodd with ⟨m, rfl⟩
                have hleft : (((2 * m + 1 - 1) / 2 : ℕ) = m) := by omega
                have hright : (((2 * m + 1) / 2 : ℕ) = m) := by omega
                rw [hleft, hright]
              norm_num [← hsolZ]
  apply Complex.ofReal_injective
  rw [hsum_reindex, hprod_reindex]
  exact hratioC
