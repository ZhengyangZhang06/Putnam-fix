import Mathlib

private lemma putnam_2006_a5_complex_tan_eq_exp_ratio (z : ℂ) :
    Complex.tan z = Complex.I * (1 - Complex.exp (2 * Complex.I * z)) /
      (Complex.exp (2 * Complex.I * z) + 1) := by
  rw [← Complex.cot_inv_eq_tan, Complex.cot_eq_exp_ratio]
  field

private lemma putnam_2006_a5_exp_ne_one (n : ℕ) (theta : ℝ) (hn : n ≠ 0)
    (hθ : Irrational (theta / Real.pi)) :
    Complex.exp (((2 : ℝ) * (n : ℝ) * theta : ℝ) * Complex.I) ≠ 1 := by
  intro h
  rcases (Complex.exp_eq_one_iff.mp h) with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp at him
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hrat : theta / Real.pi = (m : ℝ) / (n : ℝ) := by
    field_simp [Real.pi_ne_zero, hnR] at him ⊢
    linarith
  exact hθ.ne_rational m (n : ℤ) hrat

private lemma putnam_2006_a5_exp_ne_neg_one (n : ℕ) (theta : ℝ) (hn : n ≠ 0)
    (hθ : Irrational (theta / Real.pi)) :
    Complex.exp (((2 : ℝ) * (n : ℝ) * theta : ℝ) * Complex.I) ≠ -1 := by
  intro h
  have h' : Complex.exp (((2 : ℝ) * (n : ℝ) * theta : ℝ) * Complex.I) =
      Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    simpa using h
  rcases (Complex.exp_eq_exp_iff_exists_int.mp h') with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp at him
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hden : (2 : ℝ) * (n : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hnR
  have hrat : theta / Real.pi = ((2 * m + 1 : ℤ) : ℝ) / ((2 * (n : ℤ) : ℤ) : ℝ) := by
    norm_num
    field_simp [Real.pi_ne_zero, hnR, hden] at him ⊢
    ring_nf at him ⊢
    linarith
  exact hθ.ne_rational (2 * m + 1) (2 * (n : ℤ)) hrat

private lemma putnam_2006_a5_alpha_pow (n : ℕ) (theta : ℝ) (hn : n ≠ 0) :
    (Complex.exp (((2 : ℝ) * (theta + Real.pi / (n : ℝ)) : ℝ) * Complex.I)) ^ n =
      Complex.exp (((2 : ℝ) * (n : ℝ) * theta : ℝ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have harg : (n : ℂ) * (↑(2 * (theta + Real.pi / (n : ℝ))) * Complex.I) =
      (↑(2 * (n : ℝ) * theta) * Complex.I) + 2 * Real.pi * Complex.I := by
    push_cast
    field_simp [hnR, hnC]
  rw [harg, Complex.exp_add]
  simp

private lemma putnam_2006_a5_tan_shift (n : ℕ) (theta : ℝ) (i : Fin n) :
    ((Real.tan (theta + (((i.1 + 1 : ℕ) : ℝ) * Real.pi) / (n : ℝ))) : ℂ) =
      Complex.I * (1 - (Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))) ^ i.1 *
        Complex.exp (((2 : ℝ) * (theta + Real.pi / (n : ℝ)) : ℝ) * Complex.I)) /
      (1 + (Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))) ^ i.1 *
        Complex.exp (((2 : ℝ) * (theta + Real.pi / (n : ℝ)) : ℝ) * Complex.I)) := by
  rw [Complex.ofReal_tan, putnam_2006_a5_complex_tan_eq_exp_ratio]
  have hExp : Complex.exp (2 * Complex.I * (↑(theta + (((i.1 + 1 : ℕ) : ℝ) * Real.pi) / (n : ℝ)) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))) ^ (i.1) *
        Complex.exp (((2 : ℝ) * (theta + Real.pi / (n : ℝ)) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hExp]
  ring

private lemma putnam_2006_a5_prod_one_add_roots (n : ℕ) (hn : 0 < n) (hnodd : Odd n)
    (ζ α : ℂ) (hζ : IsPrimitiveRoot ζ n) :
    (∏ i ∈ Finset.range n, (1 + ζ ^ i * α)) = 1 + α ^ n := by
  have hpoly : (Polynomial.X ^ n - Polynomial.C (α ^ n) : Polynomial ℂ) =
      ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * α)) := by
    simpa using (X_pow_sub_C_eq_prod (R := ℂ) hζ hn (α := α) (a := α ^ n) rfl)
  have heval := congrArg (fun p : Polynomial ℂ => p.eval (-1)) hpoly
  simp [Polynomial.eval_prod] at heval
  calc
    (∏ i ∈ Finset.range n, (1 + ζ ^ i * α))
        = ∏ i ∈ Finset.range n, -((-1 : ℂ) - ζ ^ i * α) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
    _ = (-1 : ℂ) ^ (Finset.range n).card * (∏ i ∈ Finset.range n, ((-1 : ℂ) - ζ ^ i * α)) := by
            rw [Finset.prod_neg]
    _ = (-1 : ℂ) ^ n * (∏ i ∈ Finset.range n, ((-1 : ℂ) - ζ ^ i * α)) := by simp
    _ = (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n - α ^ n) := by rw [heval]
    _ = 1 + α ^ n := by rw [hnodd.neg_one_pow]; ring

private lemma putnam_2006_a5_prod_one_sub_roots (n : ℕ) (hn : 0 < n)
    (ζ α : ℂ) (hζ : IsPrimitiveRoot ζ n) :
    (∏ i ∈ Finset.range n, (1 - ζ ^ i * α)) = 1 - α ^ n := by
  have hpoly : (Polynomial.X ^ n - Polynomial.C (α ^ n) : Polynomial ℂ) =
      ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * α)) := by
    simpa using (X_pow_sub_C_eq_prod (R := ℂ) hζ hn (α := α) (a := α ^ n) rfl)
  have heval := congrArg (fun p : Polynomial ℂ => p.eval 1) hpoly
  simpa [Polynomial.eval_prod] using heval.symm

private lemma putnam_2006_a5_sum_inv_one_add_roots (n : ℕ) (hn : 0 < n) (hnodd : Odd n)
    (ζ α : ℂ) (hζ : IsPrimitiveRoot ζ n) (hneg : α ^ n ≠ -1) :
    (∑ i ∈ Finset.range n, (1 / (1 + ζ ^ i * α))) = (n : ℂ) / (1 + α ^ n) := by
  let p : Polynomial ℂ := Polynomial.X ^ n - Polynomial.C (α ^ n)
  have hsplit : p.Splits := by
    dsimp [p]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot hζ rfl
  have hp_eval_ne : p.eval (-1) ≠ 0 := by
    dsimp [p]
    simp [hnodd.neg_one_pow]
    intro hz
    apply hneg
    linear_combination -hz
  have hroots : p.roots = (Finset.range n).val.map (fun i => ζ ^ i * α) := by
    dsimp [p]
    have hpoly : (Polynomial.X ^ n - Polynomial.C (α ^ n) : Polynomial ℂ) =
        ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * α)) := by
      simpa using (X_pow_sub_C_eq_prod (R := ℂ) hζ hn (α := α) (a := α ^ n) rfl)
    rw [hpoly]
    simpa [Finset.prod] using
      (Polynomial.roots_multiset_prod_X_sub_C ((Finset.range n).val.map (fun i => ζ ^ i * α)))
  have hEven : Even (n - 1) := by
    rcases hnodd with ⟨m, hm⟩
    use m
    omega
  have hpowm1 : ((-1 : ℂ) ^ (n - 1)) = 1 := hEven.neg_one_pow
  have hder := hsplit.eval_derivative_div_eval_of_ne_zero hp_eval_ne
  rw [hroots] at hder
  simp [p, Polynomial.derivative_pow, Polynomial.derivative_C,
    hpowm1, hnodd.neg_one_pow, sub_eq_add_neg] at hder
  have hder' : (n : ℂ) / (-1 + -α ^ n) = - (∑ i ∈ Finset.range n, (1 / (1 + ζ ^ i * α))) := by
    rw [hder]
    simp [Finset.sum, one_div]
    convert (Multiset.sum_map_neg (m := Multiset.range n)
      (f := fun x : ℕ => (1 + ζ ^ x * α)⁻¹)) using 2
    apply Multiset.map_congr rfl
    intro x hx
    rw [show (-1 : ℂ) + -(ζ ^ x * α) = -(1 + ζ ^ x * α) by ring, inv_neg]
  have hdenrewrite : (n : ℂ) / (-1 + -α ^ n) = -((n : ℂ) / (1 + α ^ n)) := by
    rw [show (-1 : ℂ) + -α ^ n = -(1 + α ^ n) by ring, div_neg]
  have hder'' : -((n : ℂ) / (1 + α ^ n)) = - (∑ i ∈ Finset.range n, (1 / (1 + ζ ^ i * α))) :=
    hdenrewrite.symm.trans hder'
  exact (neg_injective hder'').symm

private lemma putnam_2006_a5_sign (n : ℕ) (hnodd : Odd n) :
    (n : ℂ) * Complex.I / (Complex.I ^ n) =
      (((fun n : ℕ => if (n ≡ 1 [MOD 4]) then n else -n) : ℕ → ℤ) n : ℂ) := by
  have hoddmod : n % 4 = 1 ∨ n % 4 = 3 := (Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hnodd))
  rcases hoddmod with h1 | h3
  · have hmod : n ≡ 1 [MOD 4] := by
      simp [Nat.ModEq, h1]
    have hIpow : Complex.I ^ n = Complex.I := by
      rw [Complex.I_pow_eq_pow_mod, h1]
      norm_num
    simp [hmod, hIpow]
  · have hnotmod : ¬ n ≡ 1 [MOD 4] := by
      simp [Nat.ModEq, h3]
    have hIpow : Complex.I ^ n = -Complex.I := by
      rw [Complex.I_pow_eq_pow_mod, h3]
      norm_num [Complex.I_pow_three]
    simp [hnotmod, hIpow]
    field_simp [Complex.I_ne_zero]

-- (fun n : ℕ => if (n ≡ 1 [MOD 4]) then n else -n)
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
: (∑ k : Set.Icc 1 n, a k) / (∏ k : Set.Icc 1 n, a k) = ((fun n : ℕ => if (n ≡ 1 [MOD 4]) then n else -n) : ℕ → ℤ ) n := by
  have hnpos : 0 < n := by
    rcases nodd with ⟨m, hm⟩
    omega
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  let α : ℂ := Complex.exp (((2 : ℝ) * (theta + Real.pi / (n : ℝ)) : ℝ) * Complex.I)
  let Q : ℂ := Complex.exp (((2 : ℝ) * (n : ℝ) * theta : ℝ) * Complex.I)
  let B : ℂ := (1 - α ^ n) / (1 + α ^ n)
  have hζ : IsPrimitiveRoot ζ n := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp n hnne
  have hαpow : α ^ n = Q := by
    dsimp [α, Q]
    exact putnam_2006_a5_alpha_pow n theta hnne
  have hQne1 : Q ≠ 1 := by
    dsimp [Q]
    exact putnam_2006_a5_exp_ne_one n theta hnne thetairr
  have hQneneg : Q ≠ -1 := by
    dsimp [Q]
    exact putnam_2006_a5_exp_ne_neg_one n theta hnne thetairr
  have hαne1 : α ^ n ≠ 1 := by
    rw [hαpow]
    exact hQne1
  have hαneneg : α ^ n ≠ -1 := by
    rw [hαpow]
    exact hQneneg
  have hprodAdd := putnam_2006_a5_prod_one_add_roots n hnpos nodd ζ α hζ
  have hprodSub := putnam_2006_a5_prod_one_sub_roots n hnpos ζ α hζ
  have hdenRange : ∀ i ∈ Finset.range n, 1 + ζ ^ i * α ≠ 0 := by
    intro i hi hzero
    have hprodAdd_ne : (∏ i ∈ Finset.range n, (1 + ζ ^ i * α)) ≠ 0 := by
      rw [hprodAdd]
      intro hz
      apply hαneneg
      linear_combination hz
    exact hprodAdd_ne (Finset.prod_eq_zero hi hzero)
  have hsumInv := putnam_2006_a5_sum_inv_one_add_roots n hnpos nodd ζ α hζ hαneneg
  have hsumTan :
      (∑ i : Fin n, Complex.I * (1 - ζ ^ (i : ℕ) * α) / (1 + ζ ^ (i : ℕ) * α)) =
        (n : ℂ) * Complex.I * B := by
    have hsumRange :
        (∑ i : Fin n, Complex.I * (1 - ζ ^ (i : ℕ) * α) / (1 + ζ ^ (i : ℕ) * α)) =
          ∑ i ∈ Finset.range n, Complex.I * (1 - ζ ^ i * α) / (1 + ζ ^ i * α) := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => Complex.I * (1 - ζ ^ i * α) / (1 + ζ ^ i * α)) n)
    rw [hsumRange]
    calc
      (∑ i ∈ Finset.range n, Complex.I * (1 - ζ ^ i * α) / (1 + ζ ^ i * α))
          = Complex.I * (∑ i ∈ Finset.range n, ((1 - ζ ^ i * α) / (1 + ζ ^ i * α))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = Complex.I * (∑ i ∈ Finset.range n, (2 * (1 / (1 + ζ ^ i * α)) - 1)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              field_simp [hdenRange i hi]
              ring
      _ = Complex.I * (2 * (∑ i ∈ Finset.range n, (1 / (1 + ζ ^ i * α))) - n) := by
              rw [Finset.sum_sub_distrib]
              rw [← Finset.mul_sum]
              simp [Finset.card_range]
      _ = Complex.I * (2 * ((n : ℂ) / (1 + α ^ n)) - n) := by
              rw [hsumInv]
      _ = (n : ℂ) * Complex.I * B := by
              dsimp [B]
              have hden : 1 + α ^ n ≠ 0 := by
                intro hz
                apply hαneneg
                linear_combination hz
              field_simp [hden]
              ring
  have hprodTan :
      (∏ i : Fin n, Complex.I * (1 - ζ ^ (i : ℕ) * α) / (1 + ζ ^ (i : ℕ) * α)) =
        Complex.I ^ n * B := by
    have hprodRange :
        (∏ i : Fin n, Complex.I * (1 - ζ ^ (i : ℕ) * α) / (1 + ζ ^ (i : ℕ) * α)) =
          ∏ i ∈ Finset.range n, Complex.I * (1 - ζ ^ i * α) / (1 + ζ ^ i * α) := by
      simpa using (Fin.prod_univ_eq_prod_range
        (fun i : ℕ => Complex.I * (1 - ζ ^ i * α) / (1 + ζ ^ i * α)) n)
    rw [hprodRange]
    calc
      (∏ i ∈ Finset.range n, Complex.I * (1 - ζ ^ i * α) / (1 + ζ ^ i * α))
          = (∏ i ∈ Finset.range n, Complex.I) *
              (∏ i ∈ Finset.range n, ((1 - ζ ^ i * α) / (1 + ζ ^ i * α))) := by
              rw [← Finset.prod_mul_distrib]
              apply Finset.prod_congr rfl
              intro i hi
              ring
      _ = Complex.I ^ n *
              ((∏ i ∈ Finset.range n, (1 - ζ ^ i * α)) /
                (∏ i ∈ Finset.range n, (1 + ζ ^ i * α))) := by
              rw [Finset.prod_const, Finset.card_range, Finset.prod_div_distrib]
      _ = Complex.I ^ n * B := by
              dsimp [B]
              rw [hprodSub, hprodAdd]
  let e : Fin n ≃ Set.Icc 1 n :=
    { toFun := fun i => ⟨i.1 + 1, by
        constructor
        · omega
        · exact Nat.succ_le_of_lt i.2⟩
      invFun := fun k => ⟨k.1 - 1, by
        have hk1 : 1 ≤ k.1 := k.2.1
        have hkn : k.1 ≤ n := k.2.2
        omega⟩
      left_inv := by
        intro i
        ext
        simp
      right_inv := by
        intro k
        ext
        exact Nat.sub_add_cancel k.2.1 }
  have hpoint (i : Fin n) :
      (a (e i) : ℂ) = Complex.I * (1 - ζ ^ (i : ℕ) * α) / (1 + ζ ^ (i : ℕ) * α) := by
    rw [ha (e i)]
    dsimp [e, ζ, α]
    simpa using putnam_2006_a5_tan_shift n theta i
  have hsum_reindex : (∑ k : Set.Icc 1 n, (a k : ℂ)) = ∑ i : Fin n, (a (e i) : ℂ) := by
    simpa using (e.sum_comp (fun k : Set.Icc 1 n => (a k : ℂ))).symm
  have hprod_reindex : (∏ k : Set.Icc 1 n, (a k : ℂ)) = ∏ i : Fin n, (a (e i) : ℂ) := by
    simpa using (e.prod_comp (fun k : Set.Icc 1 n => (a k : ℂ))).symm
  have hBne : B ≠ 0 := by
    dsimp [B]
    apply div_ne_zero
    · intro hz
      apply hαne1
      linear_combination -hz
    · intro hz
      apply hαneneg
      linear_combination hz
  apply Complex.ofReal_injective
  calc
    (((∑ k : Set.Icc 1 n, a k) / (∏ k : Set.Icc 1 n, a k) : ℝ) : ℂ)
        = (∑ k : Set.Icc 1 n, (a k : ℂ)) / (∏ k : Set.Icc 1 n, (a k : ℂ)) := by
            simp
    _ = (∑ i : Fin n, (a (e i) : ℂ)) / (∏ i : Fin n, (a (e i) : ℂ)) := by
            rw [hsum_reindex, hprod_reindex]
    _ = (∑ i : Fin n, Complex.I * (1 - ζ ^ (i : ℕ) * α) / (1 + ζ ^ (i : ℕ) * α)) /
          (∏ i : Fin n, Complex.I * (1 - ζ ^ (i : ℕ) * α) / (1 + ζ ^ (i : ℕ) * α)) := by
            simp_rw [hpoint]
    _ = ((n : ℂ) * Complex.I * B) /
          (Complex.I ^ n * B) := by
            rw [hsumTan, hprodTan]
    _ = (n : ℂ) * Complex.I / (Complex.I ^ n) := by
            field_simp [hBne]
    _ = (((fun n : ℕ => if (n ≡ 1 [MOD 4]) then n else -n) : ℕ → ℤ) n : ℂ) := by
            exact putnam_2006_a5_sign n nodd
