import Mathlib

abbrev putnam_1979_a1_solution : Multiset ℕ :=
  (Multiset.replicate 330 3 + {2}) + Multiset.replicate 329 3

private theorem putnam_1979_a1_part_bound (n : ℕ) (hn : 0 < n) :
    ∃ c d : ℕ, 2 * c + 3 * d ≤ n ∧ n ≤ 2 ^ c * 3 ^ d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn4 : n ≤ 4
      · interval_cases n
        · exact ⟨0, 0, by norm_num, by norm_num⟩
        · exact ⟨1, 0, by norm_num, by norm_num⟩
        · exact ⟨0, 1, by norm_num, by norm_num⟩
        · exact ⟨2, 0, by norm_num, by norm_num⟩
      · have hn5 : 5 ≤ n := by omega
        obtain ⟨c, d, hwt, hprod⟩ := ih (n - 3) (by omega) (by omega)
        refine ⟨c, d + 1, ?_, ?_⟩
        · omega
        · calc
            n ≤ 3 * (n - 3) := by omega
            _ ≤ 3 * (2 ^ c * 3 ^ d) := Nat.mul_le_mul_left 3 hprod
            _ = 2 ^ c * 3 ^ (d + 1) := by
              rw [pow_succ]
              ring

private theorem putnam_1979_a1_multiset_bound (s : Multiset ℕ)
    (hpos : ∀ i ∈ s, i > 0) :
    ∃ c d : ℕ, 2 * c + 3 * d ≤ s.sum ∧ s.prod ≤ 2 ^ c * 3 ^ d := by
  induction s using Multiset.induction_on with
  | empty =>
      refine ⟨0, 0, ?_, ?_⟩ <;> norm_num
  | cons a s ih =>
      have ha : a > 0 := hpos a (by rw [Multiset.mem_cons]; exact Or.inl rfl)
      have hspos : ∀ i ∈ s, i > 0 := by
        intro i hi
        exact hpos i (by rw [Multiset.mem_cons]; exact Or.inr hi)
      obtain ⟨c₁, d₁, hwt₁, hprod₁⟩ := putnam_1979_a1_part_bound a ha
      obtain ⟨c₂, d₂, hwt₂, hprod₂⟩ := ih hspos
      refine ⟨c₁ + c₂, d₁ + d₂, ?_, ?_⟩
      · rw [Multiset.sum_cons]
        omega
      · calc
          (a ::ₘ s).prod = a * s.prod := by rw [Multiset.prod_cons]
          _ ≤ (2 ^ c₁ * 3 ^ d₁) * (2 ^ c₂ * 3 ^ d₂) :=
            Nat.mul_le_mul hprod₁ hprod₂
          _ = 2 ^ (c₁ + c₂) * 3 ^ (d₁ + d₂) := by
            rw [pow_add, pow_add]
            ring

private theorem putnam_1979_a1_two_three_bound : ∀ c d : ℕ,
    2 * c + 3 * d ≤ 1979 → 2 ^ c * 3 ^ d ≤ 2 * 3 ^ 659
  | 0, d, hwt => by
      have hd : d ≤ 659 := by omega
      rw [pow_zero, one_mul]
      have hpow : 3 ^ d ≤ 3 ^ 659 := Nat.pow_le_pow_right (by norm_num : 0 < 3) hd
      have htop : 3 ^ 659 ≤ 2 * 3 ^ 659 := by
        exact Nat.le_mul_of_pos_left (3 ^ 659) (by norm_num : 0 < 2)
      exact le_trans hpow htop
  | 1, d, hwt => by
      have hd : d ≤ 659 := by omega
      rw [pow_one]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num : 0 < 3) hd)
  | 2, d, hwt => by
      have hd : d ≤ 658 := by omega
      rw [show 2 ^ 2 = 4 by norm_num]
      have hpow : 4 * 3 ^ d ≤ 4 * 3 ^ 658 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num : 0 < 3) hd)
      have htop : 4 * 3 ^ 658 ≤ 2 * 3 ^ 659 := by
        have h46 : 4 * 3 ^ 658 ≤ 6 * 3 ^ 658 :=
          Nat.mul_le_mul_right (3 ^ 658) (by norm_num : 4 ≤ 6)
        have h6 : 6 * 3 ^ 658 = 2 * 3 ^ 659 := by
          conv_rhs => rw [show 659 = 658 + 1 by norm_num, pow_add, pow_one]
          rw [show 2 * (3 ^ 658 * 3) = 6 * 3 ^ 658 by
            rw [← mul_assoc, mul_comm 2 (3 ^ 658), mul_assoc]
            norm_num
            rw [mul_comm]]
        exact h46.trans (le_of_eq h6)
      exact le_trans hpow htop
  | c + 3, d, hwt => by
      have hwt' : 2 * c + 3 * (d + 2) ≤ 1979 := by omega
      have hrec := putnam_1979_a1_two_three_bound c (d + 2) hwt'
      have hstep : 2 ^ (c + 3) * 3 ^ d ≤ 2 ^ c * 3 ^ (d + 2) := by
        calc
          2 ^ (c + 3) * 3 ^ d = (2 ^ c * 8) * 3 ^ d := by
            conv_lhs => rw [pow_add]
            ring_nf
          _ ≤ (2 ^ c * 9) * 3 ^ d := by
            exact Nat.mul_le_mul_right (3 ^ d)
              (Nat.mul_le_mul_left (2 ^ c) (by norm_num))
          _ = 2 ^ c * 3 ^ (d + 2) := by
            conv_rhs => rw [pow_add]
            ring_nf
      exact hstep.trans hrec

/--
For which positive integers $n$ and $a_1, a_2, \dots, a_n$ with $\sum_{i = 1}^{n} a_i = 1979$ does $\prod_{i = 1}^{n} a_i$ attain the greatest value?
-/
theorem putnam_1979_a1
    (P : Multiset ℕ → Prop)
    (hP : ∀ a, P a ↔ Multiset.card a > 0 ∧ (∀ i ∈ a, i > 0) ∧ a.sum = 1979) :
    P putnam_1979_a1_solution ∧ ∀ a : Multiset ℕ, P a → putnam_1979_a1_solution.prod ≥ a.prod :=
  by
  have hsolprod : putnam_1979_a1_solution.prod = 2 * 3 ^ 659 := by
    rw [putnam_1979_a1_solution, Multiset.prod_add, Multiset.prod_add]
    repeat rw [Multiset.prod_replicate]
    simp only [Multiset.prod_singleton]
    conv_rhs => rw [show 659 = 330 + 329 by norm_num, pow_add]
    ring
  constructor
  · rw [hP]
    refine ⟨?_, ?_, ?_⟩
    · rw [putnam_1979_a1_solution, Multiset.card_add, Multiset.card_add]
      repeat rw [Multiset.card_replicate]
      norm_num
    · intro i hi
      rw [putnam_1979_a1_solution, Multiset.mem_add] at hi
      rcases hi with hi | hi
      · rw [Multiset.mem_add] at hi
        rcases hi with hi | hi
        · have hi3 : i = 3 := Multiset.eq_of_mem_replicate hi
          omega
        · simp at hi
          omega
      · have hi3 : i = 3 := Multiset.eq_of_mem_replicate hi
        omega
    · rw [putnam_1979_a1_solution, Multiset.sum_add, Multiset.sum_add]
      repeat rw [Multiset.sum_replicate]
      norm_num
  · intro a ha
    have hdata := (hP a).mp ha
    obtain ⟨_, hpos, hsum⟩ := hdata
    obtain ⟨c, d, hwt, hprod⟩ := putnam_1979_a1_multiset_bound a hpos
    have hwt1979 : 2 * c + 3 * d ≤ 1979 := by omega
    exact hprod.trans
      (by simpa [hsolprod] using putnam_1979_a1_two_three_bound c d hwt1979)
