import Mathlib

open Topology MvPolynomial Filter Set

abbrev putnam_2009_a3_solution : ℝ := 0

/--
Let $d_n$ be the determinant of the $n \times n$ matrix whose entries, from left to right and then from top to bottom, are $\cos 1, \cos 2, \dots, \cos n^2$. (For example,\[ d_3 = \left|\begin{matrix} \cos 1 & \cos 2 & \cos 3 \\ \cos 4 & \cos 5 & \cos 6 \\  \cos 7 & \cos 8 & \cos 9 \end{matrix} \right|. \]The argument of $\cos$ is always in radians, not degrees.) Evaluate $\lim_{n\to\infty} d_n$.
-/
theorem putnam_2009_a3
(cos_matrix : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
(hM : ∀ n : ℕ, ∀ i j : Fin n, (cos_matrix n) i j = Real.cos (1 + n * i + j))
: Tendsto (fun n => (cos_matrix n).det) atTop (𝓝 putnam_2009_a3_solution) :=
by
  refine tendsto_atTop_of_eventually_const (i₀ := 3) ?_
  intro n hn
  have hdet : (cos_matrix n).det = 0 := by
    classical
    let j0 : Fin n := ⟨0, by omega⟩
    let j1 : Fin n := ⟨1, by omega⟩
    let j2 : Fin n := ⟨2, by omega⟩
    have h01 : j0 ≠ j1 := by
      intro h
      have := congrArg Fin.val h
      simp [j0, j1] at this
    have h02 : j0 ≠ j2 := by
      intro h
      have := congrArg Fin.val h
      simp [j0, j2] at this
    have h12 : j1 ≠ j2 := by
      intro h
      have := congrArg Fin.val h
      simp [j1, j2] at this
    let coeff : Fin n → ℝ := fun j =>
      if j = j0 then Real.sin 1 else if j = j1 then - Real.sin 2 else if j = j2 then Real.sin 1 else 0
    have htrig : ∀ x : ℝ,
        Real.sin 1 * Real.cos x + (- Real.sin 2) * Real.cos (x + 1) +
          Real.sin 1 * Real.cos (x + 2) = 0 := by
      intro x
      rw [show (2 : ℝ) = 1 + 1 by norm_num]
      simp only [Real.sin_add, Real.cos_add]
      ring_nf
      calc
        Real.sin 1 * Real.cos x +
              (-(Real.sin 1 * Real.cos x * Real.cos 1 ^ 2) - Real.sin 1 ^ 3 * Real.cos x) =
            Real.sin 1 * Real.cos x * (1 - Real.cos 1 ^ 2 - Real.sin 1 ^ 2) := by ring
        _ = 0 := by
          have h : 1 - Real.cos 1 ^ 2 - Real.sin 1 ^ 2 = 0 := by
            nlinarith [Real.sin_sq_add_cos_sq 1]
          rw [h, mul_zero]
    have hsum : ({j0, j1, j2} : Finset (Fin n)).sum
        (fun j => coeff j • (cos_matrix n).transpose j) = 0 := by
      ext i
      simp [coeff, h01, h02, h12, hM n i j0, hM n i j1, hM n i j2,
        Matrix.transpose_apply, j0, j1, j2]
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc] using
        htrig (1 + (n : ℝ) * (i : ℝ))
    have hdep : ¬ LinearIndependent ℝ (fun j : Fin n => (cos_matrix n).transpose j) := by
      refine not_linearIndependent_iff.mpr ?_
      refine ⟨({j0, j1, j2} : Finset (Fin n)), coeff, ?_, ?_⟩
      · simpa using hsum
      · refine ⟨j0, ?_, ?_⟩
        · simp
        · have hsinpos : 0 < Real.sin (1 : ℝ) := by
            exact Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.one_le_pi_div_two])
          simp [coeff, hsinpos.ne']
    exact Matrix.det_eq_zero_of_not_linearIndependent_cols hdep
  simpa [putnam_2009_a3_solution] using hdet
