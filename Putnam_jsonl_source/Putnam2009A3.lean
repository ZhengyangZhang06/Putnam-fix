import Mathlib

open Topology MvPolynomial Filter Set

-- 0
/--
Let $d_n$ be the determinant of the $n \times n$ matrix whose entries, from left to right and then from top to bottom, are $\cos 1, \cos 2, \dots, \cos n^2$. (For example,\[ d_3 = \left|\begin{matrix} \cos 1 & \cos 2 & \cos 3 \\ \cos 4 & \cos 5 & \cos 6 \\  \cos 7 & \cos 8 & \cos 9 \end{matrix} \right|. \]The argument of $\cos$ is always in radians, not degrees.) Evaluate $\lim_{n\to\infty} d_n$.
-/
theorem putnam_2009_a3
(cos_matrix : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
(hM : ∀ n : ℕ, ∀ i j : Fin n, (cos_matrix n) i j = Real.cos (1 + n * i + j))
: Tendsto (fun n => (cos_matrix n).det) atTop (𝓝 ((0) : ℝ )) := by
  classical
  refine tendsto_atTop_of_eventually_const (i₀ := 3) ?_
  intro n hn
  have hrow_subset :
      Set.range (fun i : Fin n => (cos_matrix n) i) ⊆
        Submodule.span ℝ ({(fun j : Fin n => Real.cos (j : ℝ)),
          (fun j : Fin n => Real.sin (j : ℝ))} : Set (Fin n → ℝ)) := by
    rintro row ⟨i, rfl⟩
    change (cos_matrix n i) ∈ Submodule.span ℝ ({(fun j : Fin n => Real.cos (j : ℝ)),
      (fun j : Fin n => Real.sin (j : ℝ))} : Set (Fin n → ℝ))
    rw [Submodule.mem_span_pair]
    set a : ℝ := (1 : ℝ) + (n : ℝ) * (i : ℝ) with ha
    refine ⟨Real.cos a, -Real.sin a, ?_⟩
    ext j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hM n i j]
    rw [show ((1 : ℝ) + (n : ℝ) * (i : ℝ) + (j : ℝ)) = a + (j : ℝ) by rw [ha]]
    conv_rhs => rw [Real.cos_add]
    simp [smul_eq_mul]
    ring
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin n => (cos_matrix n) i) := by
    intro hli
    have hcard_le : Fintype.card (Fin n) ≤
        Set.finrank ℝ (Set.range (fun i : Fin n => (cos_matrix n) i)) :=
      (linearIndependent_iff_card_le_finrank_span (R := ℝ)
        (b := fun i : Fin n => (cos_matrix n) i)).mp hli
    have hspan_le : Set.finrank ℝ (Set.range (fun i : Fin n => (cos_matrix n) i)) ≤ 2 := by
      let c : Fin n → ℝ := fun j => Real.cos (j : ℝ)
      let s : Fin n → ℝ := fun j => Real.sin (j : ℝ)
      have hmono : Set.finrank ℝ (Set.range (fun i : Fin n => (cos_matrix n) i)) ≤
          Set.finrank ℝ ({c, s} : Set (Fin n → ℝ)) := by
        dsimp [Set.finrank]
        exact Submodule.finrank_mono (Submodule.span_le.mpr (by simpa [c, s] using hrow_subset))
      have htwo : Set.finrank ℝ ({c, s} : Set (Fin n → ℝ)) ≤ 2 := by
        have hseteq : ((({c, s} : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) =
            ({c, s} : Set (Fin n → ℝ)) := by
          ext x
          simp
        have hfin := finrank_span_finset_le_card (R := ℝ) ({c, s} : Finset (Fin n → ℝ))
        have hcard : ({c, s} : Finset (Fin n → ℝ)).card ≤ 2 := by
          simpa using (Finset.card_insert_le c ({s} : Finset (Fin n → ℝ)))
        rw [← hseteq]
        exact hfin.trans hcard
      exact hmono.trans htwo
    have hn_le_two : n ≤ 2 := by
      simpa using hcard_le.trans hspan_le
    omega
  have hdet : (cos_matrix n).det = 0 :=
    Matrix.det_eq_zero_of_not_linearIndependent_rows hdep
  simp [hdet]
