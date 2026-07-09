import Mathlib

open Nat

noncomputable abbrev putnam_2023_a2_aux (n : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (Polynomial.X ^ 2 - Polynomial.C ((i : ℝ) ^ 2))

lemma putnam_2023_a2_prod_Icc_nat_eq_factorial (n : ℕ) :
    (∏ i ∈ Finset.Icc 1 n, i) = Nat.factorial n := by
  rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) n]
  rw [Finset.prod_Ico_eq_prod_range (fun i : ℕ => i) 1 (n + 1)]
  simp [Nat.add_comm, Finset.prod_range_add_one_eq_factorial]

lemma putnam_2023_a2_prod_Icc_real_eq_factorial (n : ℕ) :
    (∏ i ∈ Finset.Icc 1 n, (i : ℝ)) = (Nat.factorial n : ℝ) := by
  rw [← Nat.cast_prod]
  rw [putnam_2023_a2_prod_Icc_nat_eq_factorial]

lemma putnam_2023_a2_prod_Icc_real_sq_eq_factorial_sq (n : ℕ) :
    (∏ i ∈ Finset.Icc 1 n, (i : ℝ) ^ 2) = (Nat.factorial n : ℝ) ^ 2 := by
  rw [Finset.prod_pow]
  rw [putnam_2023_a2_prod_Icc_real_eq_factorial]

lemma putnam_2023_a2_neg_one_pow_even_real {n : ℕ} (hn : Even n) :
    (-1 : ℝ) ^ n = 1 := by
  rw [neg_one_pow_eq_ite]
  simp [hn]

lemma putnam_2023_a2_next_quad (a : ℝ) :
    (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℝ).nextCoeff = 0 := by
  rw [Polynomial.nextCoeff_of_natDegree_pos]
  · rw [Polynomial.natDegree_X_pow_sub_C]
    norm_num
  · rw [Polynomial.natDegree_X_pow_sub_C]
    norm_num

lemma putnam_2023_a2_natDegree_quad_nat (i : ℕ) :
    (Polynomial.X ^ 2 - (i : Polynomial ℝ) ^ 2).natDegree = 2 := by
  rw [show (i : Polynomial ℝ) ^ 2 = Polynomial.C ((i : ℝ) ^ 2) by norm_num]
  rw [Polynomial.natDegree_X_pow_sub_C]

lemma putnam_2023_a2_nextCoeff_quad_nat (i : ℕ) :
    (Polynomial.X ^ 2 - (i : Polynomial ℝ) ^ 2).nextCoeff = 0 := by
  rw [show (i : Polynomial ℝ) ^ 2 = Polynomial.C ((i : ℝ) ^ 2) by norm_num]
  exact putnam_2023_a2_next_quad ((i : ℝ) ^ 2)

lemma putnam_2023_a2_aux_monic (n : ℕ) : (putnam_2023_a2_aux n).Monic := by
  unfold putnam_2023_a2_aux
  exact Polynomial.monic_prod_of_monic _ _ (by
    intro i _hi
    exact Polynomial.monic_X_pow_sub_C ((i : ℝ) ^ 2) (by norm_num : (2 : ℕ) ≠ 0))

lemma putnam_2023_a2_aux_natDegree (n : ℕ) :
    (putnam_2023_a2_aux n).natDegree = 2 * n := by
  unfold putnam_2023_a2_aux
  rw [Polynomial.natDegree_prod_of_monic]
  · simp [putnam_2023_a2_natDegree_quad_nat, mul_comm]
  · intro i _hi
    exact Polynomial.monic_X_pow_sub_C ((i : ℝ) ^ 2) (by norm_num : (2 : ℕ) ≠ 0)

lemma putnam_2023_a2_aux_nextCoeff (n : ℕ) :
    (putnam_2023_a2_aux n).nextCoeff = 0 := by
  unfold putnam_2023_a2_aux
  rw [Polynomial.Monic.nextCoeff_prod]
  · simp [putnam_2023_a2_nextCoeff_quad_nat]
  · intro i _hi
    exact Polynomial.monic_X_pow_sub_C ((i : ℝ) ^ 2) (by norm_num : (2 : ℕ) ≠ 0)

lemma putnam_2023_a2_aux_eval_zero (n : ℕ) (hn : Even n) :
    (putnam_2023_a2_aux n).eval 0 = (Nat.factorial n : ℝ) ^ 2 := by
  unfold putnam_2023_a2_aux
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  simp only [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_sub]
  rw [show (∏ x ∈ Finset.Icc 1 n, -((x : ℝ) ^ 2)) =
      (∏ _x ∈ Finset.Icc 1 n, (-1 : ℝ)) * ∏ x ∈ Finset.Icc 1 n, (x : ℝ) ^ 2 by
    conv_lhs =>
      arg 2
      intro x
      rw [show -((x : ℝ) ^ 2) = (-1 : ℝ) * (x : ℝ) ^ 2 by ring]
    rw [Finset.prod_mul_distrib]]
  rw [Finset.prod_const, putnam_2023_a2_prod_Icc_real_sq_eq_factorial_sq]
  have hcard : (Finset.Icc 1 n).card = n := by simp
  rw [hcard, putnam_2023_a2_neg_one_pow_even_real hn]
  ring

lemma putnam_2023_a2_reverse_eval (p : Polynomial ℝ) (x : ℝ) (hx : x ≠ 0) :
    p.reverse.eval x = x ^ p.natDegree * p.eval x⁻¹ := by
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℝ) x⁻¹ p
  simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id, invOf_eq_inv, inv_inv] at h
  calc
    p.reverse.eval x = p.reverse.eval x * (x ^ p.natDegree * (x⁻¹) ^ p.natDegree) := by
      rw [← mul_pow, mul_inv_cancel₀ hx, one_pow, mul_one]
    _ = x ^ p.natDegree * (p.reverse.eval x * (x⁻¹) ^ p.natDegree) := by ring
    _ = x ^ p.natDegree * p.eval x⁻¹ := by rw [h]

lemma putnam_2023_a2_cancel_natDegree_le
    (n : ℕ) (p : Polynomial ℝ) (hpdeg : p.natDegree = 2 * n) :
    (p.reverse - Polynomial.X ^ (2 * n + 2) +
        putnam_2023_a2_aux n *
          (Polynomial.X ^ 2 - Polynomial.C ((Nat.factorial n : ℝ)⁻¹ ^ 2))).natDegree ≤
      2 * n := by
  set q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C ((Nat.factorial n : ℝ)⁻¹ ^ 2)
  set b : Polynomial ℝ := putnam_2023_a2_aux n * q
  have hqmonic : q.Monic := by
    dsimp [q]
    exact Polynomial.monic_X_pow_sub_C ((Nat.factorial n : ℝ)⁻¹ ^ 2)
      (by norm_num : (2 : ℕ) ≠ 0)
  have hqdeg : q.natDegree = 2 := by
    dsimp [q]
    rw [Polynomial.natDegree_X_pow_sub_C]
  have hqnext : q.nextCoeff = 0 := by
    dsimp [q]
    exact putnam_2023_a2_next_quad ((Nat.factorial n : ℝ)⁻¹ ^ 2)
  have hamonic := putnam_2023_a2_aux_monic n
  have hadeg := putnam_2023_a2_aux_natDegree n
  have hanext := putnam_2023_a2_aux_nextCoeff n
  have hbmonic : b.Monic := by
    dsimp [b]
    exact hamonic.mul hqmonic
  have hbdeg : b.natDegree = 2 * n + 2 := by
    dsimp [b]
    rw [hamonic.natDegree_mul hqmonic, hadeg, hqdeg]
  have hbtop : b.coeff (2 * n + 2) = 1 := by
    simpa [hbdeg] using hbmonic.coeff_natDegree
  have hbnext : b.coeff (2 * n + 1) = 0 := by
    have hpos : 0 < b.natDegree := by rw [hbdeg]; omega
    have hnext := Polynomial.nextCoeff_of_natDegree_pos (p := b) hpos
    have hcoeff : b.coeff (b.natDegree - 1) = 0 := by
      simpa [hnext] using (show b.nextCoeff = 0 by
        dsimp [b]
        rw [hamonic.nextCoeff_mul hqmonic, hanext, hqnext]
        ring)
    simpa [hbdeg] using hcoeff
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hprev : p.reverse.coeff m = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (Polynomial.reverse_natDegree_le p) (hpdeg ▸ hm)
  by_cases htop : m = 2 * n + 2
  · subst m
    simp [Polynomial.coeff_add, Polynomial.coeff_sub, hprev, hbtop]
  by_cases hnext : m = 2 * n + 1
  · subst m
    have hx : (Polynomial.X ^ (2 * n + 2) : Polynomial ℝ).coeff (2 * n + 1) = 0 := by
      rw [Polynomial.coeff_X_pow]
      simp
    simp [Polynomial.coeff_add, Polynomial.coeff_sub, hprev, hx, hbnext]
  · have hgt : 2 * n + 2 < m := by omega
    have hx : (Polynomial.X ^ (2 * n + 2) : Polynomial ℝ).coeff m = 0 := by
      rw [Polynomial.coeff_X_pow]
      simp [htop]
    have hb : b.coeff m = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact hbdeg ▸ hgt
    simp [Polynomial.coeff_add, Polynomial.coeff_sub, hprev, hx, hb]

lemma putnam_2023_a2_aux_eval_int_zero
    (n : ℕ) {z : ℤ} (hz0 : z ≠ 0) (hzn : z.natAbs ≤ n) :
    (putnam_2023_a2_aux n).eval (z : ℝ) = 0 := by
  unfold putnam_2023_a2_aux
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨z.natAbs, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨by omega, hzn⟩
  · simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have hsq : (z : ℝ) ^ 2 = (z.natAbs : ℝ) ^ 2 := by
      rcases Int.natAbs_eq z with h | h
      · rw [h]
        norm_num
      · rw [h]
        norm_num
    rw [hsq, sub_self]

lemma putnam_2023_a2_identity
    (n : ℕ) (hn_even : Even n) (p : Polynomial ℝ)
    (hpmonic : p.Monic) (hpdeg : p.natDegree = 2 * n)
    (hpint : ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ n →
      p.eval ((z : ℝ)⁻¹) = (z : ℝ) ^ 2) :
    p.reverse - Polynomial.X ^ (2 * n + 2) =
      -putnam_2023_a2_aux n *
        (Polynomial.X ^ 2 - Polynomial.C ((Nat.factorial n : ℝ)⁻¹ ^ 2)) := by
  set q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C ((Nat.factorial n : ℝ)⁻¹ ^ 2)
  set b : Polynomial ℝ := putnam_2023_a2_aux n * q
  set d : Polynomial ℝ := p.reverse - Polynomial.X ^ (2 * n + 2) + b
  have hdeg : d.natDegree ≤ 2 * n := by
    dsimp [d, b, q]
    exact putnam_2023_a2_cancel_natDegree_le n p hpdeg
  let T : Finset ℝ := (Finset.Icc (-(n : ℤ)) (n : ℤ)).image fun z : ℤ => (z : ℝ)
  have hTcard : T.card = 2 * n + 1 := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ (Int.cast_injective (α := ℝ))]
    rw [Int.card_Icc]
    norm_num
    omega
  have hTroot : ∀ x ∈ T, d.eval x = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨z, hzmem, rfl⟩
    by_cases hz0 : z = 0
    · subst z
      have hrev0 : p.reverse.eval 0 = 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        rw [Polynomial.coeff_zero_reverse, hpmonic.leadingCoeff]
      have haux0 := putnam_2023_a2_aux_eval_zero n hn_even
      have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero n)
      dsimp [d, b, q]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      norm_num
      rw [hrev0, haux0]
      field_simp [hfac]
      ring
    · have hzabs_le : z.natAbs ≤ n := by
        have hbounds : -(n : ℤ) ≤ z ∧ z ≤ (n : ℤ) := by
          simpa using (Finset.mem_Icc.mp hzmem)
        have hzabs : |z| ≤ (n : ℤ) := abs_le.mpr hbounds
        have hzabs' : (z.natAbs : ℤ) ≤ (n : ℤ) := by
          simpa [Int.natCast_natAbs] using hzabs
        exact_mod_cast hzabs'
      have hx0 : (z : ℝ) ≠ 0 := by exact_mod_cast hz0
      have hrev := putnam_2023_a2_reverse_eval p (z : ℝ) hx0
      have hpz := hpint z hz0 hzabs_le
      have hauxz := putnam_2023_a2_aux_eval_int_zero n hz0 hzabs_le
      have hpow : (z : ℝ) ^ (2 * n) * (z : ℝ) ^ 2 = (z : ℝ) ^ (2 * n + 2) := by
        rw [← pow_add]
      dsimp [d, b, q]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, hauxz, zero_mul, add_zero]
      rw [hrev, hpdeg, hpz, hpow]
      ring
  have hd_zero : d = 0 := by
    by_contra hdne
    have hroots := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
      (p := d) (S := T) hTroot (by rw [hTcard]; omega) hdne
    have hcard_roots : d.roots.card = T.card := by
      rw [hroots]
      simp
    have hcard_le := Polynomial.card_roots' d
    omega
  calc
    p.reverse - Polynomial.X ^ (2 * n + 2)
        = (p.reverse - Polynomial.X ^ (2 * n + 2) + b) - b := by ring
    _ = -b := by
      change d - b = -b
      rw [hd_zero]
      ring
    _ = -putnam_2023_a2_aux n * q := by
      dsimp [b]
      ring

lemma putnam_2023_a2_mem_S_of_aux_eval_zero
    (n : ℕ) (S : Set ℝ)
    (hS : S = {x : ℝ | ∃ k : ℤ, x = k ∧ 1 ≤ |k| ∧ |k| ≤ n})
    {x : ℝ} (hx : (putnam_2023_a2_aux n).eval x = 0) :
    x ∈ S := by
  unfold putnam_2023_a2_aux at hx
  rw [Polynomial.eval_prod] at hx
  rcases Finset.prod_eq_zero_iff.mp hx with ⟨i, hi, hfac⟩
  rw [Finset.mem_Icc] at hi
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hfac
  have hsq : x ^ 2 = (i : ℝ) ^ 2 := sub_eq_zero.mp hfac
  rw [hS]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hxi | hxi
  · refine ⟨(i : ℤ), ?_, ?_, ?_⟩
    · simpa using hxi
    · exact_mod_cast hi.1
    · have habs : |(i : ℤ)| = (i : ℤ) := abs_of_nonneg (by exact_mod_cast (Nat.zero_le i))
      rw [habs]
      exact_mod_cast hi.2
  · refine ⟨-(i : ℤ), ?_, ?_, ?_⟩
    · simpa using hxi
    · have habs : |-(i : ℤ)| = (i : ℤ) := by
        rw [abs_neg, abs_of_nonneg]
        exact_mod_cast (Nat.zero_le i)
      rw [habs]
      exact_mod_cast hi.1
    · have habs : |-(i : ℤ)| = (i : ℤ) := by
        rw [abs_neg, abs_of_nonneg]
        exact_mod_cast (Nat.zero_le i)
      rw [habs]
      exact_mod_cast hi.2

lemma putnam_2023_a2_eval_iff
    (n : ℕ) (p : Polynomial ℝ) (hpdeg : p.natDegree = 2 * n)
    {x : ℝ} (hx0 : x ≠ 0) :
    p.eval (1 / x) = x ^ 2 ↔
      (p.reverse - Polynomial.X ^ (2 * n + 2)).eval x = 0 := by
  have hrev := putnam_2023_a2_reverse_eval p x hx0
  have hpow : x ^ (2 * n) * x ^ 2 = x ^ (2 * n + 2) := by
    rw [← pow_add]
  constructor
  · intro hpval
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hrev, hpdeg]
    rw [show x⁻¹ = 1 / x by rw [one_div], hpval, hpow]
    ring
  · intro hroot
    have hroot' : x ^ (2 * n) * (p.eval x⁻¹ - x ^ 2) = 0 := by
      have h := hroot
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hrev, hpdeg] at h
      calc
        x ^ (2 * n) * (p.eval x⁻¹ - x ^ 2)
            = x ^ (2 * n) * p.eval x⁻¹ - x ^ (2 * n) * x ^ 2 := by ring
        _ = x ^ (2 * n) * p.eval x⁻¹ - x ^ (2 * n + 2) := by rw [hpow]
        _ = 0 := h
    have hxpow : x ^ (2 * n) ≠ 0 := pow_ne_zero _ hx0
    have hdiff : p.eval x⁻¹ - x ^ 2 = 0 := (mul_eq_zero.mp hroot').resolve_left hxpow
    have hpval : p.eval x⁻¹ = x ^ 2 := sub_eq_zero.mp hdiff
    simpa [one_div] using hpval

abbrev putnam_2023_a2_solution : ℕ → Set ℝ :=
  fun n => if n > 0 ∧ Even n then
    {(Nat.factorial n : ℝ)⁻¹, -((Nat.factorial n : ℝ)⁻¹)}
  else
    ∅

/--
Let $n$ be an even positive integer. Let $p$ be a monic, real polynomial of degree $2n$; that is to say, $p(x) = x^{2n} + a_{2n-1} x^{2n-1} + \cdots + a_1 x + a_0$ for some real coefficients $a_0, \dots, a_{2n-1}$. Suppose that $p(1/k) = k^2$ for all integers $k$ such that $1 \leq |k| \leq n$. Find all other real numbers $x$ for which $p(1/x) = x^2$.
-/
theorem putnam_2023_a2
(n : ℕ)
(hn : n > 0 ∧ Even n)
(p : Polynomial ℝ)
(hp : Polynomial.Monic p ∧ p.degree = 2*n)
(S : Set ℝ)
(hS : S = {x : ℝ | ∃ k : ℤ, x = k ∧ 1 ≤ |k| ∧ |k| ≤ n})
(hpinv : ∀ k ∈ S, p.eval (1/k) = k^2)
: {x : ℝ | x ≠ 0 ∧ p.eval (1/x) = x^2} \ S = putnam_2023_a2_solution n :=
by
  have hp0 : p ≠ 0 := hp.1.ne_zero
  have hpdeg : p.natDegree = 2 * n := by
    have hdeg : (p.natDegree : WithBot ℕ) = (2 * n : ℕ) := by
      rw [← Polynomial.degree_eq_natDegree hp0, hp.2]
      norm_num
    exact WithBot.coe_eq_coe.mp hdeg
  have hpint : ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ n →
      p.eval ((z : ℝ)⁻¹) = (z : ℝ) ^ 2 := by
    intro z hz0 hzn
    have hzS : (z : ℝ) ∈ S := by
      rw [hS]
      refine ⟨z, rfl, ?_, ?_⟩
      · have hzpos : 1 ≤ z.natAbs := by
          have : 0 < z.natAbs := Int.natAbs_pos.mpr hz0
          omega
        have hzpos' : (1 : ℤ) ≤ (z.natAbs : ℤ) := by exact_mod_cast hzpos
        simpa [Int.natCast_natAbs] using hzpos'
      · have hzn' : (z.natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hzn
        simpa [Int.natCast_natAbs] using hzn'
    have hz := hpinv (z : ℝ) hzS
    simpa [one_div] using hz
  have hid := putnam_2023_a2_identity n hn.2 p hp.1 hpdeg hpint
  have hfac_ne : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  have hn_two : 2 ≤ n := by
    rcases hn.2 with ⟨m, hm⟩
    omega
  have hfac_ge_two : 2 ≤ Nat.factorial n := by
    have hle := Nat.factorial_le hn_two
    simpa [Nat.factorial_two] using hle
  have hfac_gt_one : (1 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hfac_ge_two)
  let a : ℝ := 1 / (Nat.factorial n : ℝ)
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    exact one_div_ne_zero hfac_ne
  have ha_pos : 0 < a := by
    dsimp [a]
    exact one_div_pos.mpr (by exact_mod_cast Nat.factorial_pos n)
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [one_div] using inv_lt_one_of_one_lt₀ hfac_gt_one
  have hnotS_of_abs_lt_one : ∀ {y : ℝ}, |y| < 1 → y ∉ S := by
    intro y hy hyS
    rw [hS] at hyS
    rcases hyS with ⟨k, hyk, hk1, _hkn⟩
    have hy_ge : (1 : ℝ) ≤ |y| := by
      rw [hyk]
      have hk1' : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk1
      simpa [Int.cast_abs] using hk1'
    linarith
  ext x
  simp only [Set.mem_diff, Set.mem_setOf_eq, putnam_2023_a2_solution]
  rw [if_pos hn]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx0, hxeq⟩, hxnotS⟩
    have hroot := (putnam_2023_a2_eval_iff n p hpdeg hx0).mp hxeq
    have hid_eval :
        (p.reverse - Polynomial.X ^ (2 * n + 2)).eval x =
          (-putnam_2023_a2_aux n *
            (Polynomial.X ^ 2 - Polynomial.C ((Nat.factorial n : ℝ)⁻¹ ^ 2))).eval x := by
      simpa using congrArg (fun r : Polynomial ℝ => r.eval x) hid
    rw [hroot] at hid_eval
    have hprod :
        (putnam_2023_a2_aux n).eval x *
          (x ^ 2 - ((Nat.factorial n : ℝ)⁻¹ ^ 2)) = 0 := by
      have hneg :
          -((putnam_2023_a2_aux n).eval x *
            (x ^ 2 - ((Nat.factorial n : ℝ)⁻¹ ^ 2))) = 0 := by
        simpa [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hid_eval.symm
      exact neg_eq_zero.mp hneg
    rcases mul_eq_zero.mp hprod with haux | hquad
    · exact False.elim (hxnotS (putnam_2023_a2_mem_S_of_aux_eval_zero n S hS haux))
    · have hx_sq : x ^ 2 = ((Nat.factorial n : ℝ)⁻¹) ^ 2 := sub_eq_zero.mp hquad
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp hx_sq)
  · intro hxsol
    have hx_sq : x ^ 2 = ((Nat.factorial n : ℝ)⁻¹) ^ 2 := by
      rcases hxsol with hx | hx
      · rw [hx]
      · rw [hx]
        ring
    have hx0 : x ≠ 0 := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx_sq with hx | hx
      · rw [hx]
        exact inv_ne_zero hfac_ne
      · rw [hx]
        exact neg_ne_zero.mpr (inv_ne_zero hfac_ne)
    have hnotS : x ∉ S := by
      apply hnotS_of_abs_lt_one
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx_sq with hx | hx
      · rw [hx]
        simpa [a, one_div, abs_of_pos ha_pos] using ha_lt_one
      · rw [hx]
        rw [abs_neg]
        simpa [a, one_div, abs_of_pos ha_pos] using ha_lt_one
    have hroot : (p.reverse - Polynomial.X ^ (2 * n + 2)).eval x = 0 := by
      rw [hid]
      simp [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hx_sq]
    have hxeq := (putnam_2023_a2_eval_iff n p hpdeg hx0).mpr hroot
    exact ⟨⟨hx0, hxeq⟩, hnotS⟩
