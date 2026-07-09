import Mathlib

abbrev putnam_1993_b1_solution : ℕ := 3987

/--
Find the smallest positive integer $n$ such that for every integer $m$ with $0< m<1993$, there exists an integer $k$ for which $\frac{m}{1993}<\frac{k}{n}<\frac{m+1}{1994}$.
-/
theorem putnam_1993_b1 :
    IsLeast
    {n : ℕ | 0 < n ∧
      ∀ m ∈ Set.Ioo (0 : ℤ) (1993), ∃ k : ℤ,
      (m / 1993 < (k : ℝ) / n) ∧ ((k : ℝ) / n < (m + 1) / 1994) }
    putnam_1993_b1_solution :=
by
  constructor
  · constructor
    · norm_num [putnam_1993_b1_solution]
    · intro m hm
      use 2 * m + 1
      rcases hm with ⟨_hm0, hm1993⟩
      have hm1993R : (m : ℝ) < 1993 := by exact_mod_cast hm1993
      constructor
      · field_simp [putnam_1993_b1_solution]
        push_cast
        ring_nf
        linarith
      · field_simp [putnam_1993_b1_solution]
        push_cast
        ring_nf
        linarith
  · intro n hnset
    rcases hnset with ⟨hnpos, hprop⟩
    have hm : (1992 : ℤ) ∈ Set.Ioo (0 : ℤ) (1993) := by norm_num
    obtain ⟨k, hk1, hk2⟩ := hprop 1992 hm
    have hk1' : (1992 : ℝ) * (n : ℝ) < 1993 * (k : ℝ) := by
      field_simp [show (n : ℝ) ≠ 0 by positivity] at hk1
      norm_num at hk1 ⊢
      linarith
    have hk2' : 1994 * (k : ℝ) < 1993 * (n : ℝ) := by
      field_simp [show (n : ℝ) ≠ 0 by positivity] at hk2
      norm_num at hk2 ⊢
      linarith
    have hk1z : (1992 : ℤ) * (n : ℤ) < 1993 * k := by exact_mod_cast hk1'
    have hk2z : 1994 * k < 1993 * (n : ℤ) := by exact_mod_cast hk2'
    have : (3987 : ℤ) ≤ (n : ℤ) := by omega
    exact_mod_cast this
