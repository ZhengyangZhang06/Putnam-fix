import Mathlib

open Nat Set

abbrev putnam_2005_b2_solution : Set (ℕ × (ℕ → ℤ)) :=
  {p | (p.1 = 1 ∧ [p.2 0] = [1]) ∨
    (p.1 = 3 ∧ ([p.2 0, p.2 1, p.2 2] : List ℤ) ∈
      [[2, 3, 6], [2, 6, 3], [3, 2, 6], [3, 6, 2], [6, 2, 3], [6, 3, 2]]) ∨
    (p.1 = 4 ∧ [p.2 0, p.2 1, p.2 2, p.2 3] = [4, 4, 4, 4])}

/--
Find all positive integers $n,k_1,\dots,k_n$ such that $k_1+\cdots+k_n=5n-4$ and $\frac{1}{k_1}+\cdots+\frac{1}{k_n}=1$.
-/
theorem putnam_2005_b2
: {((n : ℕ), (k : ℕ → ℤ)) | (n > 0) ∧ (∀ i ∈ Finset.range n, k i > 0) ∧ (∑ i ∈ Finset.range n, k i = 5 * n - 4) ∧ (∑ i : Finset.range n, (1 : ℝ) / (k i) = 1)} = putnam_2005_b2_solution :=
by
  ext p
  constructor
  · intro hp
    rcases p with ⟨n, k⟩
    simp only [Set.mem_setOf_eq] at hp ⊢
    rcases hp with ⟨hnpos, hkpos, hsum, hrecip⟩
    have hrecip_fin : ∑ i ∈ Finset.range n, (1 : ℝ) / (k i) = 1 := by
      rw [Finset.sum_subtype (s := Finset.range n) (f := fun i => (1 : ℝ) / (k i))]
      · exact hrecip
      · intro x
        simp
    have recip_bound : ∀ z : ℤ, 0 < z → (7 - (z : ℝ)) / 12 ≤ (1 : ℝ) / z := by
      intro z hz
      have hzR : (0 : ℝ) < z := by exact_mod_cast hz
      have hcases : z ≤ 3 ∨ 4 ≤ z := by omega
      rcases hcases with hle | hge
      · interval_cases z <;> norm_num
      · have hpoly : (0 : ℝ) ≤ ((z : ℝ) - 3) * ((z : ℝ) - 4) := by
          have hz4 : (4 : ℝ) ≤ z := by exact_mod_cast hge
          nlinarith
        field_simp [ne_of_gt hzR]
        nlinarith
    have hnle4 : n ≤ 4 := by
      have hineq : ∑ i ∈ Finset.range n, (7 - (k i : ℝ)) / 12 ≤ 1 := by
        calc
          ∑ i ∈ Finset.range n, (7 - (k i : ℝ)) / 12
              ≤ ∑ i ∈ Finset.range n, (1 : ℝ) / (k i) := by
                exact Finset.sum_le_sum fun i hi => recip_bound (k i) (hkpos i hi)
          _ = 1 := hrecip_fin
      have hsumR : ∑ i ∈ Finset.range n, (k i : ℝ) = 5 * (n : ℝ) - 4 := by
        exact_mod_cast hsum
      have hcalc : ((n : ℝ) + 2) / 6 ≤ 1 := by
        have hrewrite :
            ∑ i ∈ Finset.range n, (7 - (k i : ℝ)) / 12 = ((n : ℝ) + 2) / 6 := by
          simp_rw [div_eq_mul_inv, sub_mul]
          rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_mul, hsumR]
          simp [Finset.card_range]
          ring
        rw [← hrewrite]
        exact hineq
      by_contra hnot
      have hn5 : 5 ≤ n := by omega
      have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn5
      nlinarith
    interval_cases n
    · left
      refine ⟨rfl, ?_⟩
      norm_num [Finset.sum_range_succ] at hsum
      simp [hsum]
    · exfalso
      have hrecip2 : (↑(k 0) : ℝ)⁻¹ + (↑(k 1) : ℝ)⁻¹ = 1 := by
        norm_num [Finset.sum_range_succ] at hrecip_fin
        simpa [one_div] using hrecip_fin
      have h0pos : 0 < k 0 := hkpos 0 (by norm_num)
      have h1pos : 0 < k 1 := hkpos 1 (by norm_num)
      have hsum' : k 0 + k 1 = 6 := by
        norm_num [Finset.sum_range_succ] at hsum
        exact hsum
      have hprodR : (k 0 : ℝ) + (k 1 : ℝ) = (k 0 : ℝ) * (k 1 : ℝ) := by
        have h0R : (k 0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h0pos)
        have h1R : (k 1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h1pos)
        field_simp [h0R, h1R] at hrecip2
        nlinarith
      have hprod : k 0 * k 1 = 6 := by
        have hprodZ : k 0 + k 1 = k 0 * k 1 := by exact_mod_cast hprodR
        omega
      have h0le : k 0 ≤ 5 := by omega
      interval_cases (k 0)
      all_goals omega
    · right
      left
      refine ⟨rfl, ?_⟩
      have hrecip3 :
          (↑(k 0) : ℝ)⁻¹ + (↑(k 1) : ℝ)⁻¹ + (↑(k 2) : ℝ)⁻¹ = 1 := by
        norm_num [Finset.sum_range_succ] at hrecip_fin
        simpa [one_div] using hrecip_fin
      have h0pos : 0 < k 0 := hkpos 0 (by norm_num)
      have h1pos : 0 < k 1 := hkpos 1 (by norm_num)
      have h2pos : 0 < k 2 := hkpos 2 (by norm_num)
      have hsum' : k 0 + k 1 + k 2 = 11 := by
        norm_num [Finset.sum_range_succ] at hsum
        exact hsum
      have hprodR :
          (k 0 : ℝ) * (k 1 : ℝ) + (k 0 : ℝ) * (k 2 : ℝ) +
            (k 1 : ℝ) * (k 2 : ℝ) =
          (k 0 : ℝ) * (k 1 : ℝ) * (k 2 : ℝ) := by
        have h0R : (k 0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h0pos)
        have h1R : (k 1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h1pos)
        have h2R : (k 2 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h2pos)
        field_simp [h0R, h1R, h2R] at hrecip3
        nlinarith
      have hprod : k 0 * k 1 + k 0 * k 2 + k 1 * k 2 = k 0 * k 1 * k 2 := by
        exact_mod_cast hprodR
      have h0div : k 0 - 1 ∣ (10 : ℤ) := by
        have hA : (k 0 - 1) * (k 1 * k 2) = k 0 * (11 - k 0) := by
          have hbc : k 1 + k 2 = 11 - k 0 := by omega
          calc
            (k 0 - 1) * (k 1 * k 2) = k 0 * k 1 * k 2 - k 1 * k 2 := by ring
            _ = k 0 * k 1 + k 0 * k 2 := by nlinarith [hprod]
            _ = k 0 * (k 1 + k 2) := by ring
            _ = k 0 * (11 - k 0) := by rw [hbc]
        have hdvd : k 0 - 1 ∣ k 0 * (11 - k 0) := ⟨k 1 * k 2, hA.symm⟩
        have hdvd2 : k 0 - 1 ∣ (k 0 - 1) * (10 - k 0) := dvd_mul_right _ _
        have hdvd10 := dvd_sub hdvd hdvd2
        convert hdvd10 using 1
        ring
      have h1div : k 1 - 1 ∣ (10 : ℤ) := by
        have hA : (k 1 - 1) * (k 0 * k 2) = k 1 * (11 - k 1) := by
          have hbc : k 0 + k 2 = 11 - k 1 := by omega
          calc
            (k 1 - 1) * (k 0 * k 2) = k 1 * k 0 * k 2 - k 0 * k 2 := by ring
            _ = k 1 * k 0 + k 1 * k 2 := by nlinarith [hprod]
            _ = k 1 * (k 0 + k 2) := by ring
            _ = k 1 * (11 - k 1) := by rw [hbc]
        have hdvd : k 1 - 1 ∣ k 1 * (11 - k 1) := ⟨k 0 * k 2, hA.symm⟩
        have hdvd2 : k 1 - 1 ∣ (k 1 - 1) * (10 - k 1) := dvd_mul_right _ _
        have hdvd10 := dvd_sub hdvd hdvd2
        convert hdvd10 using 1
        ring
      have h2div : k 2 - 1 ∣ (10 : ℤ) := by
        have hA : (k 2 - 1) * (k 0 * k 1) = k 2 * (11 - k 2) := by
          have hbc : k 0 + k 1 = 11 - k 2 := by omega
          calc
            (k 2 - 1) * (k 0 * k 1) = k 2 * k 0 * k 1 - k 0 * k 1 := by ring
            _ = k 2 * k 0 + k 2 * k 1 := by nlinarith [hprod]
            _ = k 2 * (k 0 + k 1) := by ring
            _ = k 2 * (11 - k 2) := by rw [hbc]
        have hdvd : k 2 - 1 ∣ k 2 * (11 - k 2) := ⟨k 0 * k 1, hA.symm⟩
        have hdvd2 : k 2 - 1 ∣ (k 2 - 1) * (10 - k 2) := dvd_mul_right _ _
        have hdvd10 := dvd_sub hdvd hdvd2
        convert hdvd10 using 1
        ring
      have h0le : k 0 ≤ 9 := by omega
      have h1le : k 1 ≤ 9 := by omega
      have h2le : k 2 ≤ 9 := by omega
      have h0set : k 0 = 2 ∨ k 0 = 3 ∨ k 0 = 6 := by
        interval_cases (k 0)
        all_goals norm_num at h0div
        all_goals omega
      have h1set : k 1 = 2 ∨ k 1 = 3 ∨ k 1 = 6 := by
        interval_cases (k 1)
        all_goals norm_num at h1div
        all_goals omega
      have h2set : k 2 = 2 ∨ k 2 = 3 ∨ k 2 = 6 := by
        interval_cases (k 2)
        all_goals norm_num at h2div
        all_goals omega
      rcases h0set with h0 | h0 | h0 <;>
        rcases h1set with h1 | h1 | h1 <;>
          rcases h2set with h2 | h2 | h2
      all_goals first
        | (exfalso; omega)
        | simp [h0, h1, h2]
    · right
      right
      have line4 : ∀ z : ℤ, 0 < z → (8 - (z : ℝ)) / 16 ≤ (1 : ℝ) / z := by
        intro z hz
        have hzR : (0 : ℝ) < z := by exact_mod_cast hz
        have hsquare : (0 : ℝ) ≤ ((z : ℝ) - 4)^2 := sq_nonneg _
        field_simp [ne_of_gt hzR]
        nlinarith
      have line4_eq :
          ∀ z : ℤ, 0 < z → ((1 : ℝ) / z = (8 - (z : ℝ)) / 16 ↔ z = 4) := by
        intro z hz
        have hzR : (0 : ℝ) < z := by exact_mod_cast hz
        constructor
        · intro h
          have hsquare : ((z : ℝ) - 4)^2 = 0 := by
            field_simp [ne_of_gt hzR] at h
            nlinarith
          have hz4R : (z : ℝ) = 4 := by nlinarith [sq_eq_zero_iff.mp hsquare]
          exact_mod_cast hz4R
        · intro h
          subst z
          norm_num
      have hsumR : ∑ i ∈ Finset.range 4, (k i : ℝ) = 16 := by
        norm_num [Finset.sum_range_succ] at hsum ⊢
        exact_mod_cast hsum
      have hlow : ∑ i ∈ Finset.range 4, (8 - (k i : ℝ)) / 16 = 1 := by
        simp_rw [div_eq_mul_inv, sub_mul]
        rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_mul, hsumR]
        simp [Finset.card_range]
        ring
      have herrsum :
          ∑ i ∈ Finset.range 4, ((1 : ℝ) / (k i) - (8 - (k i : ℝ)) / 16) = 0 := by
        rw [Finset.sum_sub_distrib, hrecip_fin, hlow]
        norm_num
      have herr_nonneg :
          ∀ i ∈ Finset.range 4, 0 ≤ ((1 : ℝ) / (k i) - (8 - (k i : ℝ)) / 16) := by
        intro i hi
        have := line4 (k i) (hkpos i hi)
        linarith
      have herr_zero :
          ∀ i ∈ Finset.range 4, ((1 : ℝ) / (k i) - (8 - (k i : ℝ)) / 16) = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg herr_nonneg).mp herrsum
      have h0eq : (1 : ℝ) / (k 0) = (8 - (k 0 : ℝ)) / 16 := by
        have := herr_zero 0 (by norm_num)
        linarith
      have h1eq : (1 : ℝ) / (k 1) = (8 - (k 1 : ℝ)) / 16 := by
        have := herr_zero 1 (by norm_num)
        linarith
      have h2eq : (1 : ℝ) / (k 2) = (8 - (k 2 : ℝ)) / 16 := by
        have := herr_zero 2 (by norm_num)
        linarith
      have h3eq : (1 : ℝ) / (k 3) = (8 - (k 3 : ℝ)) / 16 := by
        have := herr_zero 3 (by norm_num)
        linarith
      refine ⟨rfl, ?_⟩
      have h0 : k 0 = 4 := (line4_eq (k 0) (hkpos 0 (by norm_num))).mp h0eq
      have h1 : k 1 = 4 := (line4_eq (k 1) (hkpos 1 (by norm_num))).mp h1eq
      have h2 : k 2 = 4 := (line4_eq (k 2) (hkpos 2 (by norm_num))).mp h2eq
      have h3 : k 3 = 4 := (line4_eq (k 3) (hkpos 3 (by norm_num))).mp h3eq
      simp [h0, h1, h2, h3]
  · intro hp
    rcases p with ⟨n, k⟩
    simp only [Set.mem_setOf_eq] at hp ⊢
    rcases hp with h1 | hrest
    · rcases h1 with ⟨hn, hprefix⟩
      subst n
      have h0 : k 0 = 1 := by
        simpa using hprefix
      refine ⟨by norm_num, ?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_range] at hi
        interval_cases i
        norm_num [h0]
      · norm_num [Finset.sum_range_succ, h0]
      · rw [show (∑ i : Finset.range 1, (1 : ℝ) / (k i)) =
            ∑ i ∈ Finset.range 1, (1 : ℝ) / (k i) by
          symm
          rw [Finset.sum_subtype]
          intro x
          simp]
        norm_num [Finset.sum_range_succ, h0]
    · rcases hrest with h3 | h4
      · rcases h3 with ⟨hn, hprefix⟩
        subst n
        have hcases :
            (k 0 = 2 ∧ k 1 = 3 ∧ k 2 = 6) ∨
            (k 0 = 2 ∧ k 1 = 6 ∧ k 2 = 3) ∨
            (k 0 = 3 ∧ k 1 = 2 ∧ k 2 = 6) ∨
            (k 0 = 3 ∧ k 1 = 6 ∧ k 2 = 2) ∨
            (k 0 = 6 ∧ k 1 = 2 ∧ k 2 = 3) ∨
            (k 0 = 6 ∧ k 1 = 3 ∧ k 2 = 2) := by
          simpa using hprefix
        rcases hcases with hcase | hcase | hcase | hcase | hcase | hcase
        all_goals
          rcases hcase with ⟨h0, h1, h2⟩
          refine ⟨by norm_num, ?_, ?_, ?_⟩
          · intro i hi
            rw [Finset.mem_range] at hi
            interval_cases i <;> norm_num [h0, h1, h2]
          · norm_num [Finset.sum_range_succ, h0, h1, h2]
          · rw [show (∑ i : Finset.range 3, (1 : ℝ) / (k i)) =
                ∑ i ∈ Finset.range 3, (1 : ℝ) / (k i) by
              symm
              rw [Finset.sum_subtype]
              intro x
              simp]
            norm_num [Finset.sum_range_succ, h0, h1, h2]
      · rcases h4 with ⟨hn, hprefix⟩
        subst n
        have hvalues : k 0 = 4 ∧ k 1 = 4 ∧ k 2 = 4 ∧ k 3 = 4 := by
          simpa using hprefix
        rcases hvalues with ⟨h0, h1, h2, h3⟩
        refine ⟨by norm_num, ?_, ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_range] at hi
          interval_cases i <;> norm_num [h0, h1, h2, h3]
        · norm_num [Finset.sum_range_succ, h0, h1, h2, h3]
        · rw [show (∑ i : Finset.range 4, (1 : ℝ) / (k i)) =
              ∑ i ∈ Finset.range 4, (1 : ℝ) / (k i) by
            symm
            rw [Finset.sum_subtype]
            intro x
            simp]
          norm_num [Finset.sum_range_succ, h0, h1, h2, h3]
