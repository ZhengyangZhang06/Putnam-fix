import Mathlib

open Function Set

-- -1
/--
For positive integers $n$, let the numbers $c(n)$ be determined by the rules $c(1)=1$, $c(2n)=c(n)$, and $c(2n+1)=(-1)^nc(n)$. Find the value of $\sum_{n=1}^{2013} c(n)c(n+2)$.
-/
theorem putnam_2013_b1
(c : ℕ → ℤ)
(hc1 : c 1 = 1)
(hceven : ∀ n : ℕ, n > 0 → c (2 * n) = c n)
(hcodd : ∀ n : ℕ, n > 0 → c (2 * n + 1) = (-1) ^ n * c n)
: (∑ n : Set.Icc 1 2013, c n * c (n.1 + 2)) = ((-1) : ℤ ) := by
  let d : ℕ → ℤ := fun n => c n * c (n + 2)
  have hpair : ∀ m : ℕ, 0 < m → d (2 * m) + d (2 * m + 1) = 0 := by
    intro m hm
    have hm1 : 0 < m + 1 := Nat.succ_pos m
    have h_even_succ : c (2 * m + 2) = c (m + 1) := by
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hceven (m + 1) hm1
    have h_odd_succ : c ((2 * m + 1) + 2) = (-1 : ℤ) ^ (m + 1) * c (m + 1) := by
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hcodd (m + 1) hm1
    have heven_sign : (-1 : ℤ) ^ (m * 2) = 1 := by
      have h_even : Even (m * 2) := ⟨m, by omega⟩
      exact h_even.neg_one_pow (α := ℤ)
    dsimp [d]
    rw [hceven m hm, h_even_succ, hcodd m hm, h_odd_succ]
    ring_nf
    rw [heven_sign]
    ring
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 (2 * N + 1), d n) = d 1 := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        have htop : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
        have hpair' : d (2 * N + 2) + d (2 * N + 3) = 0 := by
          have hp := hpair (N + 1) (Nat.succ_pos N)
          convert hp using 1
        calc
          (∑ n ∈ Finset.Icc 1 (2 * (N + 1) + 1), d n)
              = (∑ n ∈ Finset.Icc 1 ((2 * N + 1) + 2), d n) := by rw [htop]
          _ = (∑ n ∈ Finset.Icc 1 (2 * N + 1), d n) + d (2 * N + 2) +
                d (2 * N + 3) := by
                rw [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top]
                all_goals omega
          _ = d 1 := by
                rw [ih]
                rw [add_assoc, hpair', add_zero]
  have hd1 : d 1 = (-1 : ℤ) := by
    dsimp [d]
    have hc3 : c 3 = (-1 : ℤ) := by
      have h := hcodd 1 (by norm_num)
      norm_num [hc1] at h
      exact h
    norm_num [hc1, hc3]
  rw [← Finset.sum_subtype (Finset.Icc 1 2013)
    (by intro x; simp [Finset.mem_Icc, Set.mem_Icc]) (fun n => c n * c (n + 2))]
  change (∑ n ∈ Finset.Icc 1 2013, d n) = ((-1) : ℤ)
  simpa [hd1] using hsum 1006
