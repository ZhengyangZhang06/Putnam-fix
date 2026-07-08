import Mathlib

open RingHom Set Nat Filter Topology

noncomputable abbrev putnam_1977_b1_solution : ℝ := 2 / 3

private lemma putnam_1977_b1_prod_formula (N : ℤ) (hN : 2 ≤ N) :
    (∏ n ∈ Finset.Icc (2 : ℤ) N, ((n : ℝ) ^ 3 - 1) / (n ^ 3 + 1)) =
      (2 * ((N : ℝ) ^ 2 + (N : ℝ) + 1)) / (3 * (N : ℝ) * ((N : ℝ) + 1)) := by
  induction N, hN using Int.le_induction with
  | base =>
      norm_num
  | succ N hN ih =>
      have hnot : N + 1 ∉ Finset.Icc (2 : ℤ) N := by
        simp [Finset.mem_Icc]
      have hIcc :
          Finset.Icc (2 : ℤ) (N + 1) = insert (N + 1) (Finset.Icc (2 : ℤ) N) := by
        ext x
        simp [Finset.mem_Icc]
        omega
      have hNpos : (0 : ℝ) < N := by
        exact_mod_cast (by omega : (0 : ℤ) < N)
      have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
      have hN2pos : (0 : ℝ) < (N : ℝ) + 2 := by linarith
      have hcube : ((N : ℝ) + 1) ^ 3 + 1 ≠ 0 := by positivity
      rw [hIcc, Finset.prod_insert hnot, ih]
      field_simp [Int.cast_add, hNpos.ne', hN1pos.ne', hN2pos.ne', hcube]
      push_cast
      ring_nf

private lemma putnam_1977_b1_closed_form_tendsto :
    Tendsto
      (fun N : ℤ =>
        (2 * ((N : ℝ) ^ 2 + (N : ℝ) + 1)) / (3 * (N : ℝ) * ((N : ℝ) + 1)))
      atTop (𝓝 (2 / 3 : ℝ)) := by
  have hN : Tendsto (fun N : ℤ => (N : ℝ)) atTop atTop :=
    tendsto_intCast_atTop_atTop
  have hN1 : Tendsto (fun N : ℤ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hN
  have hden : Tendsto (fun N : ℤ => (3 : ℝ) * (N : ℝ) * ((N : ℝ) + 1)) atTop atTop := by
    exact ((hN.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).atTop_mul_atTop₀ hN1)
  have htail :
      Tendsto (fun N : ℤ => (2 : ℝ) / (3 * (N : ℝ) * ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (2 : ℝ))).mul hden.inv_tendsto_atTop
  have hsum :
      Tendsto (fun N : ℤ => (2 / 3 : ℝ) + 2 / (3 * (N : ℝ) * ((N : ℝ) + 1)))
        atTop (𝓝 (2 / 3)) := by
    simpa using (tendsto_const_nhds (x := (2 / 3 : ℝ))).add htail
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℤ)] with N hNge
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (by omega : (0 : ℤ) < N)
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  field_simp [hNpos.ne', hN1pos.ne']

/--
Find $\prod_{n=2}^{\infty} \frac{(n^3 - 1)}{(n^3 + 1)}$.
-/
theorem putnam_1977_b1
: Tendsto (fun N ↦ ∏ n ∈ Finset.Icc (2 : ℤ) N, ((n : ℝ) ^ 3 - 1) / (n ^ 3 + 1)) atTop (𝓝 putnam_1977_b1_solution) :=
by
  refine putnam_1977_b1_closed_form_tendsto.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℤ)] with N hN
  exact (putnam_1977_b1_prod_formula N hN).symm
