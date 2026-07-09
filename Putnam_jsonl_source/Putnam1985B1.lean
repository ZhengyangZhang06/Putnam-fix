import Mathlib

open Set Filter Topology Real Polynomial Function

private lemma putnam_1985_b1_prod_natDegree (m : Fin 5 → ℤ) :
    (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))).natDegree = 5 := by
  rw [Polynomial.natDegree_prod_of_monic]
  · simp_rw [Polynomial.natDegree_X_sub_C]
    simp
  · intro i hi
    exact Polynomial.monic_X_sub_C _

private lemma putnam_1985_b1_prod_coeff5_ne (m : Fin 5 → ℤ) :
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 5 ≠ 0 := by
  let P : Polynomial ℝ := ∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))
  have hmonic : P.Monic := by
    dsimp [P]
    simpa using
      (Polynomial.monic_prod_of_monic (s := (Finset.univ : Finset (Fin 5)))
        (f := fun i => ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ)))
        (hs := by intro i hi; exact Polynomial.monic_X_sub_C _))
  have hdeg : P.natDegree = 5 := by
    dsimp [P]
    exact putnam_1985_b1_prod_natDegree m
  have hcoeff : P.coeff 5 = 1 := by
    calc
      P.coeff 5 = P.coeff P.natDegree := by rw [hdeg]
      _ = 1 := hmonic.coeff_natDegree
  change P.coeff 5 ≠ 0
  rw [hcoeff]
  norm_num

private lemma putnam_1985_b1_coeff0 (m : Fin 5 → ℤ) :
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 0 =
      - ((m 0 : ℝ) * (m 1 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ)) := by
  simp [Fin.prod_univ_succ]
  ring_nf

private lemma putnam_1985_b1_coeff1 (m : Fin 5 → ℤ) :
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 1 =
      ((m 0 : ℝ) * (m 1 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) +
       (m 0 : ℝ) * (m 1 : ℝ) * (m 2 : ℝ) * (m 4 : ℝ) +
       (m 0 : ℝ) * (m 1 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ) +
       (m 0 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ) +
       (m 1 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ)) := by
  simp [Fin.prod_univ_succ]
  ring_nf
  simp_rw [show ∀ z : ℤ, (z : Polynomial ℝ) = C ((z : ℤ) : ℝ) by intro z; rfl]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
    Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num

private lemma putnam_1985_b1_coeff3 (m : Fin 5 → ℤ) :
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 3 =
      ((m 0 : ℝ) * (m 1 : ℝ) + (m 0 : ℝ) * (m 2 : ℝ) +
       (m 0 : ℝ) * (m 3 : ℝ) + (m 0 : ℝ) * (m 4 : ℝ) +
       (m 1 : ℝ) * (m 2 : ℝ) + (m 1 : ℝ) * (m 3 : ℝ) +
       (m 1 : ℝ) * (m 4 : ℝ) + (m 2 : ℝ) * (m 3 : ℝ) +
       (m 2 : ℝ) * (m 4 : ℝ) + (m 3 : ℝ) * (m 4 : ℝ)) := by
  simp [Fin.prod_univ_succ]
  ring_nf
  simp_rw [show ∀ z : ℤ, (z : Polynomial ℝ) = C ((z : ℤ) : ℝ) by intro z; rfl]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
    Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num

private lemma putnam_1985_b1_coeff4 (m : Fin 5 → ℤ) :
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 4 =
      - ((m 0 : ℝ) + (m 1 : ℝ) + (m 2 : ℝ) + (m 3 : ℝ) + (m 4 : ℝ)) := by
  simp [Fin.prod_univ_succ]
  ring_nf
  simp_rw [show ∀ z : ℤ, (z : Polynomial ℝ) = C ((z : ℤ) : ℝ) by intro z; rfl]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
    Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num
  ring_nf

private lemma putnam_1985_b1_not_coeff01 (m : Fin 5 → ℤ) (hm : Injective m) :
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 0 ≠ 0 ∨
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 1 ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨h0, h1⟩
  rw [putnam_1985_b1_coeff0 m] at h0
  rw [putnam_1985_b1_coeff1 m] at h1
  have hprod : (m 0 : ℝ) * (m 1 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ) = 0 := by
    nlinarith
  have other_ne (i j : Fin 5) (hji : j ≠ i) (hi : m i = 0) : (m j : ℝ) ≠ 0 := by
    have hz : m j ≠ 0 := by
      intro hj
      have hmi : m j = m i := by rw [hj, hi]
      exact hji (hm hmi)
    exact_mod_cast hz
  rcases mul_eq_zero.mp hprod with hprod | h4r
  · rcases mul_eq_zero.mp hprod with hprod | h3r
    · rcases mul_eq_zero.mp hprod with hprod | h2r
      · rcases mul_eq_zero.mp hprod with h0r | h1r
        · have hm0 : m (0 : Fin 5) = 0 := by exact_mod_cast h0r
          have hquad : (m 1 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ) = 0 := by
            simpa [h0r] using h1
          exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (other_ne 0 1 (by decide) hm0)
            (other_ne 0 2 (by decide) hm0)) (other_ne 0 3 (by decide) hm0))
            (other_ne 0 4 (by decide) hm0)) hquad
        · have hm1 : m (1 : Fin 5) = 0 := by exact_mod_cast h1r
          have hquad : (m 0 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ) = 0 := by
            simpa [h1r] using h1
          exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (other_ne 1 0 (by decide) hm1)
            (other_ne 1 2 (by decide) hm1)) (other_ne 1 3 (by decide) hm1))
            (other_ne 1 4 (by decide) hm1)) hquad
      · have hm2 : m (2 : Fin 5) = 0 := by exact_mod_cast h2r
        have hquad : (m 0 : ℝ) * (m 1 : ℝ) * (m 3 : ℝ) * (m 4 : ℝ) = 0 := by
          simpa [h2r] using h1
        exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (other_ne 2 0 (by decide) hm2)
          (other_ne 2 1 (by decide) hm2)) (other_ne 2 3 (by decide) hm2))
          (other_ne 2 4 (by decide) hm2)) hquad
    · have hm3 : m (3 : Fin 5) = 0 := by exact_mod_cast h3r
      have hquad : (m 0 : ℝ) * (m 1 : ℝ) * (m 2 : ℝ) * (m 4 : ℝ) = 0 := by
        simpa [h3r] using h1
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (other_ne 3 0 (by decide) hm3)
        (other_ne 3 1 (by decide) hm3)) (other_ne 3 2 (by decide) hm3))
        (other_ne 3 4 (by decide) hm3)) hquad
  · have hm4 : m (4 : Fin 5) = 0 := by exact_mod_cast h4r
    have hquad : (m 0 : ℝ) * (m 1 : ℝ) * (m 2 : ℝ) * (m 3 : ℝ) = 0 := by
      simpa [h4r] using h1
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (other_ne 4 0 (by decide) hm4)
      (other_ne 4 1 (by decide) hm4)) (other_ne 4 2 (by decide) hm4))
      (other_ne 4 3 (by decide) hm4)) hquad

private lemma putnam_1985_b1_not_coeff34 (m : Fin 5 → ℤ) (hm : Injective m) :
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 3 ≠ 0 ∨
    coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) 4 ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨h3, h4⟩
  rw [putnam_1985_b1_coeff3 m] at h3
  rw [putnam_1985_b1_coeff4 m] at h4
  let a0 : ℝ := m 0
  let a1 : ℝ := m 1
  let a2 : ℝ := m 2
  let a3 : ℝ := m 3
  let a4 : ℝ := m 4
  have hsum : a0 + a1 + a2 + a3 + a4 = 0 := by
    dsimp [a0, a1, a2, a3, a4]
    nlinarith
  have hpair : a0 * a1 + a0 * a2 + a0 * a3 + a0 * a4 +
      a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4 = 0 := by
    dsimp [a0, a1, a2, a3, a4]
    simpa using h3
  have hident : (a0 + a1 + a2 + a3 + a4)^2 =
      (a0^2 + a1^2 + a2^2 + a3^2 + a4^2) +
      2 * (a0 * a1 + a0 * a2 + a0 * a3 + a0 * a4 +
      a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4) := by
    ring
  have hsumsq : a0^2 + a1^2 + a2^2 + a3^2 + a4^2 = 0 := by
    nlinarith
  have ha0sq : a0^2 = 0 := by
    nlinarith [sq_nonneg a1, sq_nonneg a2, sq_nonneg a3, sq_nonneg a4]
  have ha1sq : a1^2 = 0 := by
    nlinarith [sq_nonneg a0, sq_nonneg a2, sq_nonneg a3, sq_nonneg a4]
  have ha0 : a0 = 0 := sq_eq_zero_iff.mp ha0sq
  have ha1 : a1 = 0 := sq_eq_zero_iff.mp ha1sq
  have hm0 : m (0 : Fin 5) = 0 := by
    dsimp [a0] at ha0
    exact_mod_cast ha0
  have hm1 : m (1 : Fin 5) = 0 := by
    dsimp [a1] at ha1
    exact_mod_cast ha1
  have heq : m (0 : Fin 5) = m (1 : Fin 5) := by rw [hm0, hm1]
  have hfin : (0 : Fin 5) = 1 := hm heq
  norm_num at hfin

private lemma putnam_1985_b1_count_ge_three (m : Fin 5 → ℤ) (hm : Injective m) :
    3 ≤ ({j ∈ Finset.range (((∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))).natDegree) + 1) |
        coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) j ≠ 0}.card) := by
  let P : Polynomial ℝ := ∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))
  let S : Finset ℕ := {j ∈ Finset.range (P.natDegree + 1) | P.coeff j ≠ 0}
  have hdeg : P.natDegree = 5 := by
    dsimp [P]
    exact putnam_1985_b1_prod_natDegree m
  have h5 : P.coeff 5 ≠ 0 := by
    dsimp [P]
    exact putnam_1985_b1_prod_coeff5_ne m
  have h01 := putnam_1985_b1_not_coeff01 m hm
  have h34 := putnam_1985_b1_not_coeff34 m hm
  change 3 ≤ S.card
  rcases h01 with h0 | h1
  · have h0P : P.coeff 0 ≠ 0 := by dsimp [P]; exact h0
    rcases h34 with h3 | h4
    · have h3P : P.coeff 3 ≠ 0 := by dsimp [P]; exact h3
      have hsubset : ({0, 3, 5} : Finset ℕ) ⊆ S := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp [S, hdeg, h0P, h3P, h5]
      calc
        3 = ({0, 3, 5} : Finset ℕ).card := by norm_num
        _ ≤ S.card := Finset.card_le_card hsubset
    · have h4P : P.coeff 4 ≠ 0 := by dsimp [P]; exact h4
      have hsubset : ({0, 4, 5} : Finset ℕ) ⊆ S := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp [S, hdeg, h0P, h4P, h5]
      calc
        3 = ({0, 4, 5} : Finset ℕ).card := by norm_num
        _ ≤ S.card := Finset.card_le_card hsubset
  · have h1P : P.coeff 1 ≠ 0 := by dsimp [P]; exact h1
    rcases h34 with h3 | h4
    · have h3P : P.coeff 3 ≠ 0 := by dsimp [P]; exact h3
      have hsubset : ({1, 3, 5} : Finset ℕ) ⊆ S := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp [S, hdeg, h1P, h3P, h5]
      calc
        3 = ({1, 3, 5} : Finset ℕ).card := by norm_num
        _ ≤ S.card := Finset.card_le_card hsubset
    · have h4P : P.coeff 4 ≠ 0 := by dsimp [P]; exact h4
      have hsubset : ({1, 4, 5} : Finset ℕ) ⊆ S := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp [S, hdeg, h1P, h4P, h5]
      calc
        3 = ({1, 4, 5} : Finset ℕ).card := by norm_num
        _ ≤ S.card := Finset.card_le_card hsubset

private lemma putnam_1985_b1_candidate_poly :
    (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((((i : ℤ) - 2 : ℤ) : ℝ)))) =
      X^5 - (5 : Polynomial ℝ) * X^3 + (4 : Polynomial ℝ) * X := by
  norm_num [Fin.prod_univ_succ]
  ring_nf
  repeat rw [← map_pow]
  norm_num
  repeat rw [Polynomial.C_ofNat]
  ring_nf

private lemma putnam_1985_b1_candidate_count :
    ({j ∈ Finset.range (((∏ i : Fin 5, ((X : Polynomial ℝ) - C ((((i : ℤ) - 2 : ℤ) : ℝ)))).natDegree) + 1) |
        coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((((i : ℤ) - 2 : ℤ) : ℝ)))) j ≠ 0}.card = 3) := by
  rw [putnam_1985_b1_prod_natDegree (fun i : Fin 5 => (i : ℤ) - 2)]
  rw [putnam_1985_b1_candidate_poly]
  have hset :
      {j ∈ Finset.range (5 + 1) |
        coeff (X^5 - (5 : Polynomial ℝ) * X^3 + (4 : Polynomial ℝ) * X) j ≠ 0} =
        ({1, 3, 5} : Finset ℕ) := by
    ext j
    rw [← Polynomial.C_ofNat (R := ℝ) 5]
    rw [← Polynomial.C_ofNat (R := ℝ) 4]
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    constructor
    · intro h
      have hj : j < 6 := h.1
      interval_cases j <;> simp_all
    · intro h
      rcases h with rfl | rfl | rfl <;> norm_num
  rw [hset]
  norm_num

-- fun i ↦ i - 2
/--
Let $k$ be the smallest positive integer for which there exist distinct integers $m_1, m_2, m_3, m_4, m_5$ such that the polynomial
\[
p(x) = (x-m_1)(x-m_2)(x-m_3)(x-m_4)(x-m_5)
\]
has exactly $k$ nonzero coefficients. Find, with proof, a set of integers $m_1, m_2, m_3, m_4, m_5$ for which this minimum $k$ is achieved.
-/
theorem putnam_1985_b1
(p : (Fin 5 → ℤ) → (Polynomial ℝ))
(hp : p = fun m ↦ ∏ i : Fin 5, ((X : Polynomial ℝ) - m i))
(numnzcoeff : Polynomial ℝ → ℕ)
(hnumnzcoeff : numnzcoeff = fun p ↦ {j ∈ Finset.range (p.natDegree + 1) | coeff p j ≠ 0}.card)
: (Injective ((fun i ↦ i - 2) : Fin 5 → ℤ ) ∧ ∀ m : Fin 5 → ℤ, Injective m → numnzcoeff (p ((fun i ↦ i - 2) : Fin 5 → ℤ )) ≤ numnzcoeff (p m)) := by
  constructor
  · intro a b h
    change ((a : ℤ) - 2 = (b : ℤ) - 2) at h
    apply Fin.ext
    omega
  · intro m hm
    rw [hp, hnumnzcoeff]
    change
      ({j ∈ Finset.range (((∏ i : Fin 5,
          ((X : Polynomial ℝ) - C (((((fun i ↦ i - 2) : Fin 5 → ℤ) i : ℤ) : ℝ)))).natDegree) + 1) |
          coeff (∏ i : Fin 5,
            ((X : Polynomial ℝ) - C (((((fun i ↦ i - 2) : Fin 5 → ℤ) i : ℤ) : ℝ)))) j ≠ 0}.card) ≤
        ({j ∈ Finset.range (((∏ i : Fin 5,
          ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))).natDegree) + 1) |
          coeff (∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℤ) : ℝ))) j ≠ 0}.card)
    rw [putnam_1985_b1_candidate_count]
    exact putnam_1985_b1_count_ge_three m hm
