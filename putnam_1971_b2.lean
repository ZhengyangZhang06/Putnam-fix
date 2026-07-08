import Mathlib

open Set MvPolynomial

abbrev putnam_1971_b2_solution : Set (ℝ → ℝ) :=
  {fun x : ℝ => ((1 + x) - (1 + (x - 1) / x) + (1 - 1 / (x - 1))) / 2}

/--
Find all functions $F : \mathbb{R} \setminus \{0, 1\} \to \mathbb{R}$ that satisfy $F(x) + F\left(\frac{x - 1}{x}\right) = 1 + x$ for all $x \in \mathbb{R} \setminus \{0, 1\}$.
-/
theorem putnam_1971_b2
(S : Set ℝ)
(hS : S = univ \ {0, 1})
(P : (ℝ → ℝ) → Prop)
(hP : P = fun (F : ℝ → ℝ) => ∀ x ∈ S, F x + F ((x - 1)/x) = 1 + x)
: (∀ F ∈ putnam_1971_b2_solution, P F) ∧ ∀ f : ℝ → ℝ, P f → ∃ F ∈ putnam_1971_b2_solution, (∀ x ∈ S, f x = F x) :=
by
  subst P
  subst S
  have mem_ne_zero : ∀ {y : ℝ}, y ∈ (univ \ ({0, 1} : Set ℝ)) → y ≠ 0 := by
    intro y hy h
    exact hy.2 (by simp [h])
  have mem_ne_one : ∀ {y : ℝ}, y ∈ (univ \ ({0, 1} : Set ℝ)) → y ≠ 1 := by
    intro y hy h
    exact hy.2 (by simp [h])
  have step_mem : ∀ {y : ℝ}, y ∈ (univ \ ({0, 1} : Set ℝ)) → (y - 1) / y ∈ (univ \ ({0, 1} : Set ℝ)) := by
    intro y hy
    have hy0 : y ≠ 0 := mem_ne_zero hy
    have hy1 : y ≠ 1 := mem_ne_one hy
    have hstep0 : (y - 1) / y ≠ 0 := by
      exact div_ne_zero (sub_ne_zero.mpr hy1) hy0
    have hstep1 : (y - 1) / y ≠ 1 := by
      intro h
      field_simp [hy0] at h
      linarith
    constructor
    · simp
    · intro hmem
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h0 | h1
      · exact hstep0 h0
      · exact hstep1 h1
  constructor
  · intro F hF x hx
    rw [Set.mem_singleton_iff] at hF
    have hx0 : x ≠ 0 := mem_ne_zero hx
    have hx1 : x ≠ 1 := mem_ne_one hx
    have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hTx : (x - 1) / x ∈ (univ \ ({0, 1} : Set ℝ)) := step_mem hx
    have hTx0 : (x - 1) / x ≠ 0 := mem_ne_zero hTx
    have hTx1 : (x - 1) / x ≠ 1 := mem_ne_one hTx
    rw [hF]
    field_simp [hx0, hxsub, hTx0, sub_ne_zero.mpr hTx1]
    ring_nf
  · intro f hf
    refine ⟨(fun x : ℝ => ((1 + x) - (1 + (x - 1) / x) + (1 - 1 / (x - 1))) / 2), ?_, ?_⟩
    · rfl
    · intro x hx
      have hx0 : x ≠ 0 := mem_ne_zero hx
      have hx1 : x ≠ 1 := mem_ne_one hx
      have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      have honesubx : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
      have hTx : (x - 1) / x ∈ (univ \ ({0, 1} : Set ℝ)) := step_mem hx
      have hT2 : ((x - 1) / x - 1) / ((x - 1) / x) ∈ (univ \ ({0, 1} : Set ℝ)) := step_mem hTx
      have hTx0 : (x - 1) / x ≠ 0 := mem_ne_zero hTx
      have hTxsub : (x - 1) / x - 1 ≠ 0 := by
        intro h
        field_simp [hx0] at h
        linarith
      have hT2_0 : ((x - 1) / x - 1) / ((x - 1) / x) ≠ 0 := mem_ne_zero hT2
      have hcycle : (((x - 1) / x - 1) / ((x - 1) / x) - 1) / (((x - 1) / x - 1) / ((x - 1) / x)) = x := by
        field_simp [hx0, hx1, hxsub, hTx0, hTxsub, hT2_0]
        ring_nf
      have h1 : f x + f ((x - 1) / x) = 1 + x := hf x hx
      have h2 : f ((x - 1) / x) + f (((x - 1) / x - 1) / ((x - 1) / x)) = 1 + (x - 1) / x := hf ((x - 1) / x) hTx
      have h3 : f (((x - 1) / x - 1) / ((x - 1) / x)) + f x = 1 + ((x - 1) / x - 1) / ((x - 1) / x) := by
        simpa [hcycle] using hf (((x - 1) / x - 1) / ((x - 1) / x)) hT2
      have hlin : f x = ((1 + x) - (1 + (x - 1) / x) + (1 + ((x - 1) / x - 1) / ((x - 1) / x))) / 2 := by
        linarith
      rw [hlin]
      field_simp [hx0, hxsub, honesubx, hTx0, hTxsub]
      ring_nf
