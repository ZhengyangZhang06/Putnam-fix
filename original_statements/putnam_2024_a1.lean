import Mathlib

noncomputable abbrev putnam_2024_a1_solution : Set ℕ := sorry
--{1}
/--
Determine all positive integers $n$ for which there exist positive integers $a$, $b$ and $c$ satisfying $2a^n + 3b^n = 4c^n$.
-/
theorem putnam_2024_a1 :
    {n : ℕ | 0 < n ∧ ∃ (a b c : ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 2*a^n + 3*b^n = 4*c^n}
      = putnam_2024_a1_solution :=
  sorry
