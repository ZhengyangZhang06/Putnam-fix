import Mathlib

open Topology Filter Polynomial Set

abbrev putnam_2001_b2_solution : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 - p.2 = 1 ∧
    p.1 + p.2 = (3 : ℝ) ^ ((1 : ℝ) / 5)}

/--
Find all pairs of real numbers $(x,y)$ satisfying the system of equations
\begin{align*}
\frac{1}{x}+\frac{1}{2y}&=(x^2+3y^2)(3x^2+y^2) \\
\frac{1}{x}-\frac{1}{2y}&=2(y^4-x^4).
\end{align*}
-/
theorem putnam_2001_b2
    (x y : ℝ)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (eq1 eq2 : Prop)
    (heq1 : eq1 ↔ (1 / x + 1 / (2 * y) = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2)))
    (heq2 : eq2 ↔ (1 / x - 1 / (2 * y) = 2 * (y ^ 4 - x ^ 4))) :
    eq1 ∧ eq2 ↔ (x, y) ∈ putnam_2001_b2_solution :=
  by
  let z : ℝ := (3 : ℝ) ^ ((1 : ℝ) / 5)
  have hz5 : z ^ 5 = 3 := by
    dsimp [z]
    simpa using (Real.rpow_inv_natCast_pow (x := (3 : ℝ)) (n := 5) (by norm_num) (by norm_num))
  constructor
  · intro h
    have h1 : 1 / x + 1 / (2 * y) = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2) :=
      heq1.mp h.1
    have h2 : 1 / x - 1 / (2 * y) = 2 * (y ^ 4 - x ^ 4) :=
      heq2.mp h.2
    have h1' : 1 / x + 1 / (2 * y) = 3 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + 3 * y ^ 4 := by
      rw [h1]
      ring
    have h2' : 1 / x - 1 / (2 * y) = 2 * y ^ 4 - 2 * x ^ 4 := by
      rw [h2]
      ring
    have hsum : 2 / x = x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4 := by
      linear_combination h1' + h2'
    have hdiff : 1 / y = 5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4 := by
      linear_combination h1' - h2'
    have hA : x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) = 2 := by
      field_simp [hx] at hsum ⊢
      nlinarith
    have hB : y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) = 1 := by
      field_simp [hy] at hdiff ⊢
      nlinarith
    have hplus5 : (x + y) ^ 5 = 3 := by
      calc
        (x + y) ^ 5 = x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) +
            y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) := by ring
        _ = 3 := by rw [hA, hB]; norm_num
    have hminus5 : (x - y) ^ 5 = 1 := by
      calc
        (x - y) ^ 5 = x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) -
            y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) := by ring
        _ = 1 := by rw [hA, hB]; norm_num
    have hplus : x + y = z := by
      exact (show Odd (5 : ℕ) by norm_num).pow_injective (by simp [hplus5, hz5])
    have hminus : x - y = (1 : ℝ) := by
      exact (show Odd (5 : ℕ) by norm_num).pow_injective (by simpa using hminus5)
    simpa [putnam_2001_b2_solution, z] using And.intro hminus hplus
  · intro hmem
    have hsumdiff :
        x - y = 1 ∧ x + y = (3 : ℝ) ^ ((1 : ℝ) / 5) := by
      simpa [putnam_2001_b2_solution] using hmem
    have hminus : x - y = (1 : ℝ) := by
      simpa using hsumdiff.1
    have hplus : x + y = z := by
      simpa [z] using hsumdiff.2
    have hplus5 : (x + y) ^ 5 = 3 := by
      rw [hplus, hz5]
    have hminus5 : (x - y) ^ 5 = 1 := by
      rw [hminus]
      norm_num
    have hp' : x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) +
        y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) = 3 := by
      calc
        x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) +
            y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) = (x + y) ^ 5 := by ring
        _ = 3 := hplus5
    have hm' : x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) -
        y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) = 1 := by
      calc
        x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) -
            y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) = (x - y) ^ 5 := by ring
        _ = 1 := hminus5
    have hA : x * (x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) = 2 := by
      linear_combination (1 / 2) * hp' + (1 / 2) * hm'
    have hB : y * (5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4) = 1 := by
      linear_combination (1 / 2) * hp' - (1 / 2) * hm'
    have hsum : 2 / x = x ^ 4 + 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4 := by
      field_simp [hx]
      linarith
    have hdiff : 1 / y = 5 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + y ^ 4 := by
      field_simp [hy]
      linarith
    constructor
    · apply heq1.mpr
      have h1' : 1 / x + 1 / (2 * y) = 3 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + 3 * y ^ 4 := by
        linear_combination (1 / 2) * hsum + (1 / 2) * hdiff
      calc
        1 / x + 1 / (2 * y) = 3 * x ^ 4 + 10 * x ^ 2 * y ^ 2 + 3 * y ^ 4 := h1'
        _ = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2) := by ring
    · apply heq2.mpr
      have h2' : 1 / x - 1 / (2 * y) = 2 * y ^ 4 - 2 * x ^ 4 := by
        linear_combination (1 / 2) * hsum - (1 / 2) * hdiff
      calc
        1 / x - 1 / (2 * y) = 2 * y ^ 4 - 2 * x ^ 4 := h2'
        _ = 2 * (y ^ 4 - x ^ 4) := by ring
