import Mathlib

open Nat Set

-- Note: There might be multiple possible correct answers.
-- (MvPolynomial.X 1 - 2 * MvPolynomial.X 0) * (MvPolynomial.X 1 - 2 * MvPolynomial.X 0 - 1)
/--
Find a nonzero polynomial $P(x,y)$ such that $P(\lfloor a \rfloor,\lfloor 2a \rfloor)=0$ for all real numbers $a$. (Note: $\lfloor \nu \rfloor$ is the greatest integer less than or equal to $\nu$.)
-/
theorem putnam_2005_b1
: ((MvPolynomial.X 1 - 2 * MvPolynomial.X 0) * (MvPolynomial.X 1 - 2 * MvPolynomial.X 0 - 1) : MvPolynomial (Fin 2) ℝ ) ≠ 0 ∧ ∀ a : ℝ, MvPolynomial.eval (fun n : Fin 2 => if (n = 0) then (Int.floor a : ℝ) else (Int.floor (2 * a))) ((MvPolynomial.X 1 - 2 * MvPolynomial.X 0) * (MvPolynomial.X 1 - 2 * MvPolynomial.X 0 - 1) : MvPolynomial (Fin 2) ℝ ) = 0 := by
  constructor
  · intro h
    have he := congrArg (MvPolynomial.eval (fun n : Fin 2 => if n = 0 then (0 : ℝ) else 2)) h
    norm_num [MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X] at he
  · intro a
    have hz_cases :
        Int.floor (2 * a) - 2 * Int.floor a = 0 ∨
          Int.floor (2 * a) - 2 * Int.floor a = 1 := by
      have hz_nonneg : 0 ≤ Int.floor (2 * a) - 2 * Int.floor a := by
        have hle_floor : 2 * Int.floor a ≤ Int.floor (2 * a) := by
          rw [Int.le_floor]
          have h : ((Int.floor a : ℤ) : ℝ) ≤ a := Int.floor_le a
          norm_num [Int.cast_mul]
          nlinarith
        omega
      have hz_lt : Int.floor (2 * a) - 2 * Int.floor a < 2 := by
        have hlt_floor : Int.floor (2 * a) < 2 * Int.floor a + 2 := by
          rw [Int.floor_lt]
          have h : a < ((Int.floor a : ℤ) : ℝ) + 1 := Int.lt_floor_add_one a
          norm_num [Int.cast_mul, Int.cast_add]
          nlinarith
        omega
      omega
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X]
    rcases hz_cases with h | h
    · left
      have h' : ((Int.floor (2 * a) - 2 * Int.floor a : ℤ) : ℝ) = 0 := by
        exact_mod_cast h
      norm_num [Int.cast_sub, Int.cast_mul] at h'
      simpa using h'
    · right
      have h' : ((Int.floor (2 * a) - 2 * Int.floor a : ℤ) : ℝ) = 1 := by
        exact_mod_cast h
      norm_num [Int.cast_sub, Int.cast_mul] at h'
      nlinarith
