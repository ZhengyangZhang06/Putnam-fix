import Mathlib

open Function Set

abbrev putnam_2013_b1_solution : ℤ := -1

lemma putnam_2013_b1_sum_range_two_mul (N : ℕ) (f : ℕ → ℤ) :
    (∑ k ∈ Finset.range (2 * N), f k) =
      ∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ k ∈ Finset.range (2 * (N + 1)), f k)
            = (∑ k ∈ Finset.range (2 * N + 2), f k) := by
                rw [show 2 * (N + 1) = 2 * N + 2 by omega]
        _ = (∑ k ∈ Finset.range (2 * N), f k) + f (2 * N) + f (2 * N + 1) := by
              rw [show 2 * N + 2 = 2 * N + 1 + 1 by omega]
              rw [Finset.sum_range_succ]
              rw [Finset.sum_range_succ]
        _ = (∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1))) +
              (f (2 * N) + f (2 * N + 1)) := by
              rw [ih]
              abel
        _ = ∑ m ∈ Finset.range (N + 1), (f (2 * m) + f (2 * m + 1)) := by
              rw [Finset.sum_range_succ]

lemma putnam_2013_b1_pair_cancel
(c : ℕ → ℤ)
(hceven : ∀ n : ℕ, n > 0 → c (2 * n) = c n)
(hcodd : ∀ n : ℕ, n > 0 → c (2 * n + 1) = (-1) ^ n * c n)
(m : ℕ) :
    c (2 * m + 2) * c ((2 * m + 2) + 2) +
      c (2 * m + 3) * c ((2 * m + 3) + 2) = 0 := by
  have he1 : c (2 * m + 2) = c (m + 1) := by
    convert hceven (m + 1) (by omega) using 1
  have he2 : c (2 * m + 4) = c (m + 2) := by
    convert hceven (m + 2) (by omega) using 1
  have ho1 : c (2 * m + 3) = (-1 : ℤ) ^ (m + 1) * c (m + 1) := by
    convert hcodd (m + 1) (by omega) using 1
  have ho2 : c (2 * m + 5) = (-1 : ℤ) ^ (m + 2) * c (m + 2) := by
    convert hcodd (m + 2) (by omega) using 1
  have hpow : ((-1 : ℤ) ^ (m + 1)) * ((-1 : ℤ) ^ (m + 2)) = -1 := by
    have hsucc : ((-1 : ℤ) ^ (m + 2)) = ((-1 : ℤ) ^ (m + 1)) * (-1) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    rw [hsucc]
    have hsq : ((-1 : ℤ) ^ (m + 1)) * ((-1 : ℤ) ^ (m + 1)) = 1 := by
      rcases neg_one_pow_eq_or ℤ (m + 1) with h | h <;> simp [h]
    rw [← mul_assoc, hsq]
    norm_num
  calc
    c (2 * m + 2) * c ((2 * m + 2) + 2) +
      c (2 * m + 3) * c ((2 * m + 3) + 2)
        = c (m + 1) * c (m + 2) +
            (((-1 : ℤ) ^ (m + 1) * c (m + 1)) *
              (((-1 : ℤ) ^ (m + 2)) * c (m + 2))) := by
              rw [he1, show (2 * m + 2) + 2 = 2 * m + 4 by omega, he2,
                ho1, show (2 * m + 3) + 2 = 2 * m + 5 by omega, ho2]
    _ = c (m + 1) * c (m + 2) + -(c (m + 1) * c (m + 2)) := by
          rw [show (((-1 : ℤ) ^ (m + 1) * c (m + 1)) *
              (((-1 : ℤ) ^ (m + 2)) * c (m + 2))) =
              - (c (m + 1) * c (m + 2)) by
                calc
                  (((-1 : ℤ) ^ (m + 1) * c (m + 1)) *
                    (((-1 : ℤ) ^ (m + 2)) * c (m + 2)))
                      = (((-1 : ℤ) ^ (m + 1) * ((-1 : ℤ) ^ (m + 2)))*
                          (c (m + 1) * c (m + 2))) := by ring
                  _ = - (c (m + 1) * c (m + 2)) := by rw [hpow]; ring]
    _ = 0 := by ring

/--
For positive integers $n$, let the numbers $c(n)$ be determined by the rules $c(1)=1$, $c(2n)=c(n)$, and $c(2n+1)=(-1)^nc(n)$. Find the value of $\sum_{n=1}^{2013} c(n)c(n+2)$.
-/
theorem putnam_2013_b1
(c : ℕ → ℤ)
(hc1 : c 1 = 1)
(hceven : ∀ n : ℕ, n > 0 → c (2 * n) = c n)
(hcodd : ∀ n : ℕ, n > 0 → c (2 * n + 1) = (-1) ^ n * c n)
: (∑ n : Set.Icc 1 2013, c n * c (n.1 + 2)) = putnam_2013_b1_solution :=
by
  let f : ℕ → ℤ := fun n => c n * c (n + 2)
  have hsubtype :
      (∑ n : Set.Icc 1 2013, c n * c (n.1 + 2)) =
        ∑ n ∈ Finset.Icc 1 2013, f n := by
    change (∑ n : Set.Icc 1 2013, f n) = ∑ n ∈ Finset.Icc 1 2013, f n
    exact (Finset.sum_subtype (Finset.Icc 1 2013)
      (by intro x; simp [Set.mem_Icc, Finset.mem_Icc]) f).symm
  have hIcc : (∑ n ∈ Finset.Icc 1 2013, f n) = ∑ k ∈ Finset.range 2013, f (1 + k) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num
  have hf1 : f 1 = -1 := by
    have hc3 : c 3 = -1 := by
      have h := hcodd 1 (by norm_num)
      norm_num [hc1] at h
      simpa using h
    simp [f, hc1, hc3]
  have htail : (∑ k ∈ Finset.range 2012, f (1 + (k + 1))) = 0 := by
    rw [show 2012 = 2 * 1006 by norm_num]
    rw [putnam_2013_b1_sum_range_two_mul]
    exact Finset.sum_eq_zero fun m hm => by
      dsimp [f]
      convert putnam_2013_b1_pair_cancel c hceven hcodd m using 4 <;> omega
  calc
    (∑ n : Set.Icc 1 2013, c n * c (n.1 + 2))
        = ∑ n ∈ Finset.Icc 1 2013, f n := hsubtype
    _ = ∑ k ∈ Finset.range 2013, f (1 + k) := hIcc
    _ = (∑ k ∈ Finset.range 2012, f (1 + (k + 1))) + f (1 + 0) := by
          rw [show 2013 = 2012 + 1 by norm_num]
          rw [Finset.sum_range_succ']
    _ = putnam_2013_b1_solution := by
          rw [htail, hf1]
          norm_num [putnam_2013_b1_solution]
