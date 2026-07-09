import Mathlib

open Nat Set

noncomputable abbrev putnam_2005_b1_solution : MvPolynomial (Fin 2) ℝ :=
  (MvPolynomial.X 1 - 2 * MvPolynomial.X 0) ^ 2
    - MvPolynomial.X 1
    + 2 * MvPolynomial.X 0

/--
Find a nonzero polynomial $P(x,y)$ such that $P(\lfloor a \rfloor,\lfloor 2a \rfloor)=0$ for all real numbers $a$. (Note: $\lfloor \nu \rfloor$ is the greatest integer less than or equal to $\nu$.)
-/
theorem putnam_2005_b1
: putnam_2005_b1_solution ≠ 0 ∧ ∀ a : ℝ, MvPolynomial.eval (fun n : Fin 2 => if (n = 0) then (Int.floor a : ℝ) else (Int.floor (2 * a))) putnam_2005_b1_solution = 0 :=
by
  constructor
  · intro h
    have h' : (2 : ℝ) = 0 := by
      calc
        (2 : ℝ) =
            MvPolynomial.eval (fun n : Fin 2 => if n = 0 then (0 : ℝ) else 2)
              putnam_2005_b1_solution := by
          norm_num [putnam_2005_b1_solution]
        _ = MvPolynomial.eval (fun n : Fin 2 => if n = 0 then (0 : ℝ) else 2) 0 := by
          rw [h]
        _ = 0 := by
          simp
    norm_num at h'
  · intro a
    have hlow : 2 * Int.floor a ≤ Int.floor (2 * a) := by
      rw [Int.le_floor]
      push_cast
      have hfa : (Int.floor a : ℝ) ≤ a := Int.floor_le a
      nlinarith
    have hhigh : Int.floor (2 * a) < 2 * Int.floor a + 2 := by
      rw [Int.floor_lt]
      push_cast
      have hfa : a < (Int.floor a : ℝ) + 1 := Int.lt_floor_add_one a
      nlinarith
    have hm : Int.floor (2 * a) - 2 * Int.floor a = 0 ∨
        Int.floor (2 * a) - 2 * Int.floor a = 1 := by
      omega
    rcases hm with hm | hm
    · have hm' : (Int.floor (2 * a) : ℝ) - 2 * (Int.floor a : ℝ) = 0 := by
        exact_mod_cast hm
      simp [putnam_2005_b1_solution]
      nlinarith [hm']
    · have hm' : (Int.floor (2 * a) : ℝ) - 2 * (Int.floor a : ℝ) = 1 := by
        exact_mod_cast hm
      simp [putnam_2005_b1_solution]
      nlinarith [hm']
