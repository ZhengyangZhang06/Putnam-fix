import Mathlib

open  Real Equiv

-- fun b n ↦ (∏ i : Finset.Icc 1 n, b i) / Nat.factorial n
/--
Let $a_1, a_2, \dots, a_n$ be real numbers, and let $b_1, b_2, \dots, b_n$ be distinct positive integers. Suppose that there is a polynomial $f(x)$ satisfying the identity
\[
(1-x)^n f(x) = 1 + \sum_{i=1}^n a_i x^{b_i}.
\]
Find a simple expression (not involving any sums) for $f(1)$ in terms of $b_1, b_2, \dots, b_n$ and $n$ (but independent of $a_1, a_2, \dots, a_n$).
-/
theorem putnam_1986_a6
(n : ℕ)
(npos : n > 0)
(a : ℕ → ℝ)
(b : ℕ → ℕ)
(bpos : ∀ i ∈ Finset.Icc 1 n, b i > 0)
(binj : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, b i = b j → i = j)
(f : Polynomial ℝ)
(hf : ∀ x : ℝ, (1 - x) ^ n * f.eval x = 1 + ∑ i : Finset.Icc 1 n, (a i) * x ^ (b i))
: (f.eval 1 = ((fun b n ↦ (∏ i : Finset.Icc 1 n, b i) / Nat.factorial n) : (ℕ → ℕ) → ℕ → ℝ ) b n) := by
  classical
  let rhs : Polynomial ℝ := 1 + ∑ i : Finset.Icc 1 n, Polynomial.C (a i) * Polynomial.X ^ (b i)
  have hpoly : ((1 - Polynomial.X : Polynomial ℝ) ^ n * f) = rhs := by
    apply Polynomial.funext
    intro x
    specialize hf x
    simpa [rhs, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_finset_sum,
      Finset.sum_mul] using hf
  have hmap_factor : (((1 - Polynomial.X : Polynomial ℝ) ^ n * f).map (algebraMap ℝ ℝ)) =
      ((1 - Polynomial.X : Polynomial ℝ) ^ n * f) := by
    ext k
    simp
  have hfactor : ((1 - Polynomial.X : Polynomial ℝ) ^ n * f) =
      (Polynomial.X - Polynomial.C (1 : ℝ)) ^ n * (Polynomial.C ((-1 : ℝ) ^ n) * f) := by
    rw [show (1 - Polynomial.X : Polynomial ℝ) = -(Polynomial.X - Polynomial.C (1 : ℝ)) by
      simp [sub_eq_add_neg, add_comm]]
    rw [neg_pow]
    norm_num
    ring
  have hfactor_map : (((1 - Polynomial.X : Polynomial ℝ) ^ n * f).map (algebraMap ℝ ℝ)) =
      (Polynomial.X - Polynomial.C (1 : ℝ)) ^ n * (Polynomial.C ((-1 : ℝ) ^ n) * f) :=
    hmap_factor.trans hfactor
  have hleft_zero : ∀ k < n,
      (Polynomial.derivative^[k] ((1 - Polynomial.X : Polynomial ℝ) ^ n * f)).eval 1 = 0 := by
    intro k hk
    have h := Polynomial.aeval_iterate_derivative_of_lt
      (p := ((1 - Polynomial.X : Polynomial ℝ) ^ n * f)) (q := n) (r := (1 : ℝ))
      (p' := Polynomial.C ((-1 : ℝ) ^ n) * f) hfactor_map hk
    simpa [Polynomial.aeval_def] using h
  have hderiv_rhs : ∀ k : ℕ,
      (Polynomial.derivative^[k] rhs).eval 1 =
        (descPochhammer ℝ k).eval 0 +
          ∑ i : Finset.Icc 1 n, a i * (descPochhammer ℝ k).eval (b i : ℝ) := by
    intro k
    dsimp [rhs]
    rw [iterate_map_add Polynomial.derivative]
    rw [Polynomial.eval_add]
    have hone : (Polynomial.derivative^[k] (1 : Polynomial ℝ)).eval 1 =
        (descPochhammer ℝ k).eval 0 := by
      cases k with
      | zero => simp
      | succ k => simp
    rw [hone]
    congr 1
    simp only [Polynomial.iterate_derivative_sum, Polynomial.iterate_derivative_C_mul,
      Polynomial.iterate_derivative_X_pow_eq_smul, descPochhammer_eval_eq_descFactorial,
      Polynomial.eval_finset_sum, Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, one_pow, smul_eq_mul]
    exact Finset.sum_congr rfl (fun x hx => by ring)
  have hdesc : ∀ k < n,
      (descPochhammer ℝ k).eval 0 +
        ∑ i : Finset.Icc 1 n, a i * (descPochhammer ℝ k).eval (b i : ℝ) = 0 := by
    intro k hk
    have hder := congrArg (fun P : Polynomial ℝ => (Polynomial.derivative^[k] P).eval 1) hpoly
    have hder' :
        (Polynomial.derivative^[k] ((1 - Polynomial.X : Polynomial ℝ) ^ n * f)).eval 1 =
          (Polynomial.derivative^[k] rhs).eval 1 := by
      simpa using hder
    rw [hleft_zero k hk, hderiv_rhs k] at hder'
    exact hder'.symm
  let L : Polynomial ℝ → ℝ :=
    fun P => P.eval 0 + ∑ i : Finset.Icc 1 n, a i * P.eval (b i : ℝ)
  have hL_desc : ∀ k < n, L (descPochhammer ℝ k) = 0 := by
    intro k hk
    exact hdesc k hk
  have hL_add : ∀ P Q : Polynomial ℝ, L (P + Q) = L P + L Q := by
    intro P Q
    dsimp [L]
    simp [Polynomial.eval_add, mul_add, Finset.sum_add_distrib]
    ring
  have hL_C_mul : ∀ c : ℝ, ∀ P : Polynomial ℝ, L (Polynomial.C c * P) = c * L P := by
    intro c P
    dsimp [L]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x hx => by ring)
  have hL_all : ∀ P : Polynomial ℝ, P.natDegree < n → L P = 0 := by
    have main : ∀ d : ℕ, ∀ P : Polynomial ℝ, P.natDegree = d → P.natDegree < n → L P = 0 := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro P hd hdeg
        by_cases hP0 : P = 0
        · subst P
          dsimp [L]
          simp
        · by_cases hd0 : d = 0
          · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp (by simpa [hd0] using hd)
            rw [← hc]
            calc
              L (Polynomial.C c) = L (Polynomial.C c * (1 : Polynomial ℝ)) := by rw [mul_one]
              _ = c * L (1 : Polynomial ℝ) := hL_C_mul c 1
              _ = 0 := by
                have h1 : L (1 : Polynomial ℝ) = 0 := by
                  simpa [descPochhammer_zero] using hL_desc 0 npos
                rw [h1, mul_zero]
          · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
            let Q : Polynomial ℝ := P - Polynomial.C P.leadingCoeff * descPochhammer ℝ d
            have hmon : (descPochhammer ℝ d).Monic := monic_descPochhammer ℝ d
            have hdesc0 : descPochhammer ℝ d ≠ 0 := hmon.ne_zero
            have hdegP : P.degree = (d : WithBot ℕ) := by
              rw [Polynomial.degree_eq_natDegree hP0, hd]
            have hdegD : (descPochhammer ℝ d).degree = (d : WithBot ℕ) := by
              rw [Polynomial.degree_eq_natDegree hdesc0, descPochhammer_natDegree ℝ d]
            have hlc_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
            have hdegC : (Polynomial.C P.leadingCoeff * descPochhammer ℝ d).degree =
                (d : WithBot ℕ) := by
              rw [Polynomial.degree_C_mul hlc_ne, hdegD]
            have hdropDegree : Q.degree < P.degree := by
              dsimp [Q]
              refine Polynomial.degree_sub_lt ?_ hP0 ?_
              · rw [hdegP, hdegC]
              · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hmon.leadingCoeff,
                  mul_one]
            have hQdegd : Q.natDegree < d := by
              by_cases hQ0 : Q = 0
              · rw [hQ0]
                simpa using hdpos
              · exact (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr
                  (by rwa [hdegP] at hdropDegree)
            have hdlt : d < n := by omega
            have hQdeg : Q.natDegree < n := lt_trans hQdegd hdlt
            have hLQ : L Q = 0 := ih Q.natDegree hQdegd Q rfl hQdeg
            have hLd : L (descPochhammer ℝ d) = 0 := hL_desc d hdlt
            have hdecomp : P = Q + Polynomial.C P.leadingCoeff * descPochhammer ℝ d := by
              dsimp [Q]
              abel
            rw [hdecomp, hL_add, hL_C_mul, hLd, mul_zero, hLQ, zero_add]
    intro P hdeg
    exact main P.natDegree P rfl hdeg
  let G : Polynomial ℝ := ∏ i : Finset.Icc 1 n, (Polynomial.X - Polynomial.C (b i : ℝ))
  have hGmon : G.Monic := by
    dsimp [G]
    simpa using (Polynomial.monic_prod_X_sub_C (fun i : Finset.Icc 1 n => (b i : ℝ)) Finset.univ)
  have hGnat : G.natDegree = n := by
    dsimp [G]
    calc
      (∏ i : Finset.Icc 1 n, (Polynomial.X - Polynomial.C (b i : ℝ))).natDegree =
          Fintype.card (Finset.Icc 1 n) := by
        change (∏ x ∈ (Finset.Icc 1 n).attach,
          (Polynomial.X - Polynomial.C (b (x : ℕ) : ℝ))).natDegree = _
        rw [Polynomial.natDegree_finset_prod_X_sub_C_eq_card]
        simp
      _ = n := by
        rw [Fintype.card_coe, Nat.card_Icc]
        omega
  have hRdeg : (descPochhammer ℝ n - G).natDegree < n := by
    have hDmon : (descPochhammer ℝ n).Monic := monic_descPochhammer ℝ n
    have hD0 : descPochhammer ℝ n ≠ 0 := hDmon.ne_zero
    have hDdeg : (descPochhammer ℝ n).degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hD0, descPochhammer_natDegree ℝ n]
    have hG0 : G ≠ 0 := hGmon.ne_zero
    have hGdeg : G.degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hG0, hGnat]
    have hdrop : (descPochhammer ℝ n - G).degree < (descPochhammer ℝ n).degree := by
      refine Polynomial.degree_sub_lt ?_ hD0 ?_
      · rw [hDdeg, hGdeg]
      · rw [hDmon.leadingCoeff, hGmon.leadingCoeff]
    by_cases hzero : descPochhammer ℝ n - G = 0
    · rw [hzero]
      simpa using npos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (by rwa [hDdeg] at hdrop)
  have hGeval0 : G.eval 0 =
      (-1 : ℝ) ^ n * (∏ i : Finset.Icc 1 n, (b i : ℝ)) := by
    dsimp [G]
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    calc
      (∏ x ∈ (Finset.Icc 1 n).attach, -↑(b ↑x : ℝ))
          = ∏ x ∈ (Finset.Icc 1 n).attach, ((-1 : ℝ) * (b ↑x : ℝ)) := by
            exact Finset.prod_congr rfl (fun x hx => by ring)
      _ = (∏ x ∈ (Finset.Icc 1 n).attach, (-1 : ℝ)) *
            ∏ x ∈ (Finset.Icc 1 n).attach, (b ↑x : ℝ) := by
            rw [Finset.prod_mul_distrib]
      _ = (-1 : ℝ) ^ n * ∏ x ∈ (Finset.Icc 1 n).attach, (b ↑x : ℝ) := by
            rw [Finset.prod_const, Finset.card_attach, Nat.card_Icc]
            have hn : n + 1 - 1 = n := by omega
            rw [hn]
  have hGeval : ∀ i : Finset.Icc 1 n, G.eval (b i : ℝ) = 0 := by
    intro i
    dsimp [G]
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := i)
    · simp
    · simp
  have hD0eval : (descPochhammer ℝ n).eval 0 = 0 := by
    exact descPochhammer_ne_zero_eval_zero ℝ (Nat.ne_of_gt npos)
  have hsumD : ∑ i : Finset.Icc 1 n, a i * (descPochhammer ℝ n).eval (b i : ℝ) =
      (-1 : ℝ) ^ n * (∏ i : Finset.Icc 1 n, (b i : ℝ)) := by
    have h := hL_all (descPochhammer ℝ n - G) hRdeg
    dsimp [L] at h
    rw [Polynomial.eval_sub, hD0eval, hGeval0] at h
    simp only [zero_sub] at h
    have hsum : (∑ i : Finset.Icc 1 n,
        a i * ((descPochhammer ℝ n - G).eval (b i : ℝ))) =
        ∑ i : Finset.Icc 1 n, a i * (descPochhammer ℝ n).eval (b i : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Polynomial.eval_sub, hGeval x]
      ring
    change -((-1 : ℝ) ^ n * (∏ i : Finset.Icc 1 n, (b i : ℝ))) +
        (∑ i : Finset.Icc 1 n, a i * ((descPochhammer ℝ n - G).eval (b i : ℝ))) = 0 at h
    rw [hsum] at h
    linarith
  have hleft_n :
      (Polynomial.derivative^[n] ((1 - Polynomial.X : Polynomial ℝ) ^ n * f)).eval 1 =
        (Nat.factorial n : ℝ) * ((-1 : ℝ) ^ n * f.eval 1) := by
    have h := Polynomial.aeval_iterate_derivative_self
      (p := ((1 - Polynomial.X : Polynomial ℝ) ^ n * f)) (q := n) (r := (1 : ℝ))
      (p' := Polynomial.C ((-1 : ℝ) ^ n) * f) hfactor_map
    simpa [Polynomial.aeval_def, Polynomial.eval_mul, mul_assoc] using h
  have htop_der := congrArg (fun P : Polynomial ℝ => (Polynomial.derivative^[n] P).eval 1) hpoly
  have hmain : (Nat.factorial n : ℝ) * ((-1 : ℝ) ^ n * f.eval 1) =
      (-1 : ℝ) ^ n * (∏ i : Finset.Icc 1 n, (b i : ℝ)) := by
    calc
      (Nat.factorial n : ℝ) * ((-1 : ℝ) ^ n * f.eval 1)
          = (Polynomial.derivative^[n] ((1 - Polynomial.X : Polynomial ℝ) ^ n * f)).eval 1 :=
            hleft_n.symm
      _ = (Polynomial.derivative^[n] rhs).eval 1 := htop_der
      _ = (-1 : ℝ) ^ n * (∏ i : Finset.Icc 1 n, (b i : ℝ)) := by
        rw [hderiv_rhs n, hD0eval, zero_add, hsumD]
  have hfinal : f.eval 1 =
      (∏ i : Finset.Icc 1 n, (b i : ℝ)) / (Nat.factorial n : ℝ) := by
    have hsign : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp [hfac, hsign] at hmain ⊢
    linarith
  simpa using hfinal
