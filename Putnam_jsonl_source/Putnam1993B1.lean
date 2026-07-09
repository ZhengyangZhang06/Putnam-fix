import Mathlib

-- 3987
/--
Find the smallest positive integer $n$ such that for every integer $m$ with $0< m<1993$, there exists an integer $k$ for which $\frac{m}{1993}<\frac{k}{n}<\frac{m+1}{1994}$.
-/
theorem putnam_1993_b1 :
    IsLeast
    {n : ℕ | 0 < n ∧
      ∀ m ∈ Set.Ioo (0 : ℤ) (1993), ∃ k : ℤ,
      (m / 1993 < (k : ℝ) / n) ∧ ((k : ℝ) / n < (m + 1) / 1994) }
    ((3987) : ℕ ) := by
  constructor
  · constructor
    · norm_num
    · intro m hm
      have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
      have hm1993R : (m : ℝ) < 1993 := by exact_mod_cast hm.2
      use 2 * m + 1
      constructor <;> norm_num <;> nlinarith
  · intro n hn
    rcases hn with ⟨hnpos, hforall⟩
    have hm1992 : (1992 : ℤ) ∈ Set.Ioo (0 : ℤ) (1993) := by norm_num
    rcases hforall (1992 : ℤ) hm1992 with ⟨k, hleft, hright⟩
    norm_num at hright
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hleftI : (1992 : ℤ) * (n : ℤ) < 1993 * k := by
      have hleft' : (1992 : ℝ) < ((k : ℝ) / n) * 1993 := by
        exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1993)).1 hleft
      have hleftR : (1992 : ℝ) * (n : ℝ) < 1993 * (k : ℝ) := by
        have hmul := mul_lt_mul_of_pos_right hleft' hnR
        field_simp [hnR.ne'] at hmul
        nlinarith
      exact_mod_cast hleftR
    have hrightI : (1994 : ℤ) * k < 1993 * (n : ℤ) := by
      have hright' : ((k : ℝ) / n) * 1994 < 1993 := by
        exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 1994)).1 hright
      have hrightR : 1994 * (k : ℝ) < 1993 * (n : ℝ) := by
        have hmul := mul_lt_mul_of_pos_right hright' hnR
        field_simp [hnR.ne'] at hmul
        nlinarith
      exact_mod_cast hrightR
    omega
