import Mathlib

open Nat
open scoped BigOperators

set_option maxHeartbeats 0

-- fun n => {(1 : ℝ)/(factorial n), -(1 : ℝ)/(factorial n)}
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
: {x : ℝ | x ≠ 0 ∧ p.eval (1/x) = x^2} \ S = ((fun n => {(1 : ℝ)/(factorial n), -(1 : ℝ)/(factorial n)}) : ℕ → Set ℝ ) n := by
  classical
  have hpdeg : p.natDegree = 2*n := by
    exact Polynomial.natDegree_eq_of_degree_eq_some hp.2
  let r : (Fin n ⊕ Fin n) → ℝ := fun u =>
    match u with
    | Sum.inl i => ((i.1 + 1 : ℕ) : ℝ)
    | Sum.inr i => -(((i.1 + 1 : ℕ) : ℝ))
  let z : Option (Fin n ⊕ Fin n) → ℝ := fun u =>
    match u with
    | none => 0
    | some v => r v
  let A : Polynomial ℝ := ∏ u : (Fin n ⊕ Fin n), (Polynomial.X - Polynomial.C (r u))
  let c : ℝ := ((1 : ℝ) / Nat.factorial n)^2
  let P : Polynomial ℝ := p.reflect (2*n) - Polynomial.X^(2*n+2)
  let R : Polynomial ℝ := -(Polynomial.X^2 - Polynomial.C c) * A
  have hroot_mem_S : ∀ u : (Fin n ⊕ Fin n), r u ∈ S := by
    intro u
    cases u with
    | inl i =>
        rw [hS]
        dsimp [r]
        refine ⟨((i.1 + 1 : ℕ) : ℤ), ?_, ?_, ?_⟩
        · norm_num
        · exact_mod_cast Nat.succ_pos i.1
        · exact_mod_cast Nat.succ_le_of_lt i.2
    | inr i =>
        rw [hS]
        dsimp [r]
        refine ⟨-(((i.1 + 1 : ℕ) : ℤ)), ?_, ?_, ?_⟩
        · norm_num
        · rw [abs_neg]
          exact_mod_cast Nat.succ_pos i.1
        · rw [abs_neg]
          exact_mod_cast Nat.succ_le_of_lt i.2
  have hz_inj : Function.Injective z := by
    intro a b h
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some sb =>
            cases sb with
            | inl j =>
                simp [z, r] at h
                have hj : (0 : ℝ) < ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j.1
                linarith
            | inr j =>
                simp [z, r] at h
                have hj : (0 : ℝ) < ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j.1
                linarith
    | some sa =>
        cases sa with
        | inl i =>
            cases b with
            | none =>
                simp [z, r] at h
                have hi : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i.1
                linarith
            | some sb =>
                cases sb with
                | inl j =>
                    simp [z, r] at h ⊢
                    apply Fin.ext
                    exact_mod_cast h
                | inr j =>
                    simp [z, r] at h
                    have hi : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i.1
                    have hj : (0 : ℝ) < ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j.1
                    linarith
        | inr i =>
            cases b with
            | none =>
                simp [z, r] at h
                have hi : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i.1
                linarith
            | some sb =>
                cases sb with
                | inl j =>
                    simp [z, r] at h
                    have hi : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i.1
                    have hj : (0 : ℝ) < ((j.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j.1
                    linarith
                | inr j =>
                    simp [z, r] at h ⊢
                    apply Fin.ext
                    exact_mod_cast h
  have hAmonic : A.Monic := by
    dsimp [A]
    exact Polynomial.monic_prod_of_monic _ _ (by intro u hu; exact Polynomial.monic_X_sub_C _)
  have hAdeg : A.natDegree = 2*n := by
    dsimp [A]
    rw [Polynomial.natDegree_prod_of_monic]
    · simp [Fintype.card_sum]
      omega
    · intro u hu
      exact Polynomial.monic_X_sub_C _
  have hAeval_root : ∀ u : (Fin n ⊕ Fin n), A.eval (r u) = 0 := by
    dsimp [A]
    intro u
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    simp
  have hAnext : A.nextCoeff = 0 := by
    dsimp [A, r]
    rw [Polynomial.Monic.nextCoeff_prod]
    · simp [Polynomial.nextCoeff_X_sub_C, Fintype.sum_sum_type]
      rw [← Finset.sum_neg_distrib]
      have hsum : (∑ x : Fin n, -(-1 + -(x:ℝ))) = ∑ x : Fin n, ((x:ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsum]
      ring
    · intro u hu
      exact Polynomial.monic_X_sub_C _
  have hprod_pos : (∏ x : Fin n, (1 + (x:ℝ))) = (Nat.factorial n : ℝ) := by
    rw [← Finset.prod_range (fun i : ℕ => (1 + (i:ℝ)))]
    trans ∏ i ∈ Finset.range n, (((i+1:ℕ):ℝ))
    · apply Finset.prod_congr rfl
      intro i hi
      rw [Nat.cast_add, Nat.cast_one]
      ring
    · exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  have hprod_neg : (∏ x : Fin n, (-1 - (x:ℝ))) = (-1:ℝ)^n * (Nat.factorial n : ℝ) := by
    calc
      (∏ x : Fin n, (-1 - (x:ℝ))) = ∏ x : Fin n, ((-1:ℝ) * (1 + (x:ℝ))) := by
        apply Finset.prod_congr rfl
        intro x hx
        ring
      _ = (∏ x : Fin n, (-1:ℝ)) * ∏ x : Fin n, (1 + (x:ℝ)) := by
        rw [← Finset.prod_mul_distrib]
      _ = (-1:ℝ)^n * (Nat.factorial n : ℝ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod_pos]
  have hAeval0_sign : A.eval 0 = (-1:ℝ)^n * (Nat.factorial n : ℝ)^2 := by
    dsimp [A, r]
    simp [Polynomial.eval_prod, Fintype.prod_sum_type]
    have hprod_pos' : (∏ x : Fin n, ((x:ℝ) + 1)) = (Nat.factorial n : ℝ) := by
      simpa [add_comm] using hprod_pos
    have hprod_neg' : (∏ x : Fin n, (-1 + -(x:ℝ))) = (-1:ℝ)^n * (Nat.factorial n : ℝ) := by
      simpa [sub_eq_add_neg] using hprod_neg
    rw [hprod_neg', hprod_pos']
    ring
  have hAeval0 : A.eval 0 = (Nat.factorial n : ℝ)^2 := by
    rw [hAeval0_sign, hn.2.neg_one_pow]
    ring
  have hP0 : P.eval 0 = 1 := by
    dsimp [P]
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    rw [Polynomial.coeff_sub]
    rw [Polynomial.coeff_reflect, Polynomial.revAt_zero]
    rw [← hpdeg, hp.1.coeff_natDegree]
    rw [Polynomial.coeff_X_pow]
    simp
  have hR0 : R.eval 0 = 1 := by
    dsimp [R, c]
    simp [hAeval0]
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
    field_simp [hfac]
  have hPeval : ∀ x : ℝ, x ≠ 0 → P.eval x = x^(2*n) * (p.eval (1/x) - x^2) := by
    intro x hx
    have hreflect : (p.reflect (2*n)).eval x = x^(2*n) * p.eval (1/x) := by
      haveI : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
      have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℝ) (x⁻¹) (2*n) p (by rw [hpdeg])
      simp [Polynomial.eval₂_id, invOf_eq_inv, div_eq_mul_inv] at h ⊢
      rw [← h]
      field_simp [hx]
    dsimp [P]
    simp [hreflect]
    ring
  have hP_root : ∀ u : (Fin n ⊕ Fin n), P.eval (r u) = 0 := by
    intro u
    have hs : r u ∈ S := hroot_mem_S u
    have hval := hpinv (r u) hs
    have hx : r u ≠ 0 := by
      cases u with
      | inl i =>
          dsimp [r]
          positivity
      | inr i =>
          dsimp [r]
          exact neg_ne_zero.mpr (by positivity)
    rw [hPeval (r u) hx, hval]
    ring
  have hR_root : ∀ u : (Fin n ⊕ Fin n), R.eval (r u) = 0 := by
    intro u
    dsimp [R]
    simp [hAeval_root u]
  have hDdeg : (P - R : Polynomial ℝ).natDegree ≤ 2*n := by
    have hreflect : (p.reflect (2*n)).natDegree ≤ 2*n := by
      have h := Polynomial.natDegree_reflect_le (N := 2*n) (p := p)
      rwa [hpdeg, max_self] at h
    have hXA : (Polynomial.X^2 * A - Polynomial.X^(2*n+2) : Polynomial ℝ).natDegree ≤ 2*n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [Polynomial.coeff_sub]
      have hk2 : 2 ≤ k := by omega
      rcases Nat.exists_eq_add_of_le hk2 with ⟨d, rfl⟩
      rw [show 2 + d = d + 2 by omega]
      rw [Polynomial.coeff_X_pow_mul]
      have hnextcoeff : A.coeff (2*n - 1) = 0 := by
        have hposA : 0 < A.natDegree := by rw [hAdeg]; omega
        have h := Polynomial.nextCoeff_of_natDegree_pos (p := A) hposA
        rw [hAdeg, hAnext] at h
        exact h.symm
      by_cases hdN : d = 2*n
      · subst d
        rw [← hAdeg, hAmonic.coeff_natDegree]
        rw [Polynomial.coeff_X_pow]
        simp
      · by_cases hdNm1 : d = 2*n - 1
        · subst d
          rw [hnextcoeff]
          rw [Polynomial.coeff_X_pow]
          simp [hdN]
        · have hlt : A.natDegree < d := by rw [hAdeg]; omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
          rw [Polynomial.coeff_X_pow]
          simp [hdN]
    have hCA : (Polynomial.C c * A : Polynomial ℝ).natDegree ≤ 2*n :=
      (Polynomial.natDegree_C_mul_le c A).trans_eq hAdeg
    have hrewrite : (P - R : Polynomial ℝ) =
        p.reflect (2*n) + (Polynomial.X^2 * A - Polynomial.X^(2*n+2)) - Polynomial.C c * A := by
      dsimp [P, R]
      ring
    rw [hrewrite]
    exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
      ((Polynomial.natDegree_add_le _ _).trans <| max_le hreflect hXA) hCA
  have hDzero : P - R = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P - R) hz_inj
    · intro u
      cases u with
      | none =>
          dsimp [z]
          simp [hP0, hR0]
      | some u =>
          dsimp [z]
          simp [hP_root u, hR_root u]
    · have hcard : Fintype.card (Option (Fin n ⊕ Fin n)) = 2*n + 1 := by
        simp
        omega
      rw [hcard]
      exact Nat.lt_succ_of_le hDdeg
  have hPoly : P = R := sub_eq_zero.mp hDzero
  have hS_abs_ge : ∀ {y : ℝ}, y ∈ S → (1 : ℝ) ≤ |y| := by
    intro y hy
    rw [hS] at hy
    rcases hy with ⟨k, rfl, hk1, hkn⟩
    exact_mod_cast hk1
  have hn_ge_two : 2 ≤ n := by
    rcases hn.2 with ⟨m, hm⟩
    omega
  have hfact_two : 2 ≤ Nat.factorial n := by
    have h := Nat.factorial_le hn_ge_two
    norm_num at h
    exact h
  have hfacne : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  have ha_abs_lt_one : |(1 : ℝ) / Nat.factorial n| < 1 := by
    have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hfacgt1 : (1 : ℝ) < (Nat.factorial n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hfact_two)
    rw [abs_of_pos (div_pos zero_lt_one hfacpos)]
    field_simp [ne_of_gt hfacpos]
    exact hfacgt1
  have hnotS_of_abs_lt_one : ∀ {y : ℝ}, |y| < 1 → y ∉ S := by
    intro y hylt hyS
    exact not_le_of_gt hylt (hS_abs_ge hyS)
  have heq_of_sq : ∀ {x : ℝ}, x ≠ 0 → x^2 = c → p.eval (1/x) = x^2 := by
    intro x hx0 hx_sq
    have hRzero : R.eval x = 0 := by
      dsimp [R]
      simp [hx_sq]
    have hPzero : P.eval x = 0 := by
      rw [hPoly]
      exact hRzero
    have htmp := hPeval x hx0
    rw [hPzero] at htmp
    have hxpow : x^(2*n) ≠ 0 := pow_ne_zero _ hx0
    have hdiff : p.eval (1/x) - x^2 = 0 := by
      exact (mul_eq_zero.mp htmp.symm).resolve_left hxpow
    exact sub_eq_zero.mp hdiff
  ext x
  constructor
  · intro hxmem
    rcases hxmem with ⟨hxmain, hxnotS⟩
    have hPzero : P.eval x = 0 := by
      rw [hPeval x hxmain.1, hxmain.2]
      ring
    have hRzero : R.eval x = 0 := by
      simpa [hPoly] using hPzero
    have hcases : c - x^2 = 0 ∨ A.eval x = 0 := by
      dsimp [R] at hRzero
      simpa using hRzero
    rcases hcases with hc | hAzero
    · have hx_sq : x^2 = c := by linarith
      have hx_sq_a : x^2 = ((Nat.factorial n : ℝ)⁻¹)^2 := by
        simpa [c, one_div] using hx_sq
      rcases eq_or_eq_neg_of_sq_eq_sq x ((Nat.factorial n : ℝ)⁻¹) hx_sq_a with hxpos | hxneg
      · subst x
        left
        simp [one_div]
      · subst x
        right
        rw [neg_div]
        simp [one_div]
    · have hAprod : ∏ u : (Fin n ⊕ Fin n), (x - r u) = 0 := by
        dsimp [A] at hAzero
        simpa [Polynomial.eval_prod] using hAzero
      rw [Finset.prod_eq_zero_iff] at hAprod
      rcases hAprod with ⟨u, hu, hxu⟩
      have hx_eq : x = r u := sub_eq_zero.mp hxu
      have hxS : x ∈ S := by
        rw [hx_eq]
        exact hroot_mem_S u
      exact False.elim (hxnotS hxS)
  · intro hxrhs
    have hxcases : x = (Nat.factorial n : ℝ)⁻¹ ∨ x = -1 / (Nat.factorial n : ℝ) := by
      simpa using hxrhs
    rcases hxcases with hxpos | hxneg
    · subst x
      have hx0 : (Nat.factorial n : ℝ)⁻¹ ≠ 0 := inv_ne_zero hfacne
      have hxsq : ((Nat.factorial n : ℝ)⁻¹)^2 = c := by
        dsimp [c]
        simp [one_div]
      refine ⟨⟨hx0, heq_of_sq hx0 hxsq⟩, ?_⟩
      apply hnotS_of_abs_lt_one
      simpa [one_div] using ha_abs_lt_one
    · subst x
      have hx0 : -1 / (Nat.factorial n : ℝ) ≠ 0 := by
        exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hfacne
      have hxsq : (-1 / (Nat.factorial n : ℝ))^2 = c := by
        dsimp [c]
        ring
      refine ⟨⟨hx0, heq_of_sq hx0 hxsq⟩, ?_⟩
      apply hnotS_of_abs_lt_one
      rw [neg_div, abs_neg]
      simpa [one_div] using ha_abs_lt_one
