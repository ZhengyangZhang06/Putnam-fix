import Mathlib

abbrev putnam_2025_a4_solution : ℕ := 3

open Matrix

private def putnamA4t (i : Fin 2025) : ℝ :=
  (i.val : ℝ)

private def putnamA4u (i : Fin 2025) : Fin 3 → ℝ :=
  ![1, putnamA4t i, (putnamA4t i) ^ 2]

private def putnamA4v (i : Fin 2025) : Fin 3 → ℝ :=
  let a := putnamA4t (i - 1)
  let b := putnamA4t (i + 1)
  ![a * b, -(a + b), 1]

private def putnamA4M (i : Fin 2025) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.vecMulVec (putnamA4u i) (putnamA4v i)

private lemma putnamA4_dot (i j : Fin 2025) :
    putnamA4v i ⬝ᵥ putnamA4u j =
      (putnamA4t j - putnamA4t (i - 1)) *
        (putnamA4t j - putnamA4t (i + 1)) := by
  simp [putnamA4v, putnamA4u, putnamA4t]
  ring

private lemma putnamA4_dot_eq_zero_iff (i j : Fin 2025) :
    putnamA4v i ⬝ᵥ putnamA4u j = 0 ↔ j = i - 1 ∨ j = i + 1 := by
  rw [putnamA4_dot]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · left
      apply Fin.ext
      have hr : (j.val : ℝ) = ((i - 1).val : ℝ) := sub_eq_zero.mp h
      exact_mod_cast hr
    · right
      apply Fin.ext
      have hr : (j.val : ℝ) = ((i + 1).val : ℝ) := sub_eq_zero.mp h
      exact_mod_cast hr
  · rintro (rfl | rfl) <;> simp

private lemma putnamA4_eq_of_comm_of_dot_ne {i j : Fin 2025}
    (h : putnamA4M i * putnamA4M j = putnamA4M j * putnamA4M i)
    (hs : putnamA4v i ⬝ᵥ putnamA4u j ≠ 0) : i = j := by
  have h02 : putnamA4v i ⬝ᵥ putnamA4u j = putnamA4v j ⬝ᵥ putnamA4u i := by
    have h' :
        Matrix.vecMulVec (putnamA4u i) (putnamA4v i) *
            Matrix.vecMulVec (putnamA4u j) (putnamA4v j) =
          Matrix.vecMulVec (putnamA4u j) (putnamA4v j) *
            Matrix.vecMulVec (putnamA4u i) (putnamA4v i) := by
      simpa [putnamA4M] using h
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec] at h'
    have h02raw := congr_fun (congr_fun h' (0 : Fin 3)) (2 : Fin 3)
    simpa [Matrix.vecMulVec_apply, putnamA4u, putnamA4v] using h02raw
  have h12 :
      putnamA4t i * (putnamA4v i ⬝ᵥ putnamA4u j) =
        putnamA4t j * (putnamA4v j ⬝ᵥ putnamA4u i) := by
    have h' :
        Matrix.vecMulVec (putnamA4u i) (putnamA4v i) *
            Matrix.vecMulVec (putnamA4u j) (putnamA4v j) =
          Matrix.vecMulVec (putnamA4u j) (putnamA4v j) *
            Matrix.vecMulVec (putnamA4u i) (putnamA4v i) := by
      simpa [putnamA4M] using h
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec] at h'
    have h12raw := congr_fun (congr_fun h' (1 : Fin 3)) (2 : Fin 3)
    simpa [Matrix.vecMulVec_apply, putnamA4u, putnamA4v, mul_assoc] using h12raw
  rw [← h02] at h12
  have ht : putnamA4t i = putnamA4t j := mul_right_cancel₀ hs h12
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at ht
  exact_mod_cast ht

private lemma putnamA4_comm_iff (i j : Fin 2025) :
    putnamA4M i * putnamA4M j = putnamA4M j * putnamA4M i ↔
      i = j ∨ j = i - 1 ∨ j = i + 1 := by
  constructor
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij
    · by_cases hprev : j = i - 1
      · exact Or.inr (Or.inl hprev)
      · by_cases hnext : j = i + 1
        · exact Or.inr (Or.inr hnext)
        · exfalso
          have hs : putnamA4v i ⬝ᵥ putnamA4u j ≠ 0 := by
            intro hz
            rcases (putnamA4_dot_eq_zero_iff i j).1 hz with hp | hn
            · exact hprev hp
            · exact hnext hn
          exact hij (putnamA4_eq_of_comm_of_dot_ne h hs)
  · rintro (rfl | hprev | hnext)
    · rfl
    · have hij : putnamA4v i ⬝ᵥ putnamA4u j = 0 :=
        (putnamA4_dot_eq_zero_iff i j).2 (Or.inl hprev)
      have hji : putnamA4v j ⬝ᵥ putnamA4u i = 0 := by
        apply (putnamA4_dot_eq_zero_iff j i).2
        right
        subst hprev
        simp
      dsimp [putnamA4M]
      rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
      simp [hij, hji]
    · have hij : putnamA4v i ⬝ᵥ putnamA4u j = 0 :=
        (putnamA4_dot_eq_zero_iff i j).2 (Or.inr hnext)
      have hji : putnamA4v j ⬝ᵥ putnamA4u i = 0 := by
        apply (putnamA4_dot_eq_zero_iff j i).2
        left
        subst hnext
        simp
      dsimp [putnamA4M]
      rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
      simp [hij, hji]

private lemma putnamA4_cycle_iff_diff_mem {i j : Fin 2025} (hij : i ≤ j) :
    (i = j ∨ j = i - 1 ∨ j = i + 1) ↔
      j.val - i.val ∈ ({0, 1, 2024} : Set ℕ) := by
  constructor
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h with rfl | hprev | hnext
    · left
      omega
    · right; right
      have hji : j.val = (i - 1 : Fin 2025).val := congrArg Fin.val hprev
      have hle : i.val ≤ j.val := hij
      have hi0 : i.val = 0 := by
        by_contra hi0
        have hprevval : (i - 1 : Fin 2025).val = i.val - 1 := by
          rw [Fin.val_sub]
          simp
          omega
        omega
      have hj2024 : j.val = 2024 := by
        rw [hji]
        simp [Fin.val_sub, hi0]
      omega
    · right; left
      have hji : j.val = (i + 1 : Fin 2025).val := congrArg Fin.val hnext
      have hle : i.val ≤ j.val := hij
      have hi_lt : i.val < 2024 := by
        by_contra hnot
        have hi_ge : 2024 ≤ i.val := Nat.le_of_not_gt hnot
        have hi_eq : i.val = 2024 := by omega
        have hj0 : j.val = 0 := by
          rw [hji]
          simp [Fin.val_add, hi_eq]
        omega
      have hnextval : (i + 1 : Fin 2025).val = i.val + 1 := by
        rw [Fin.val_add]
        simp
        omega
      omega
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h0 | h1 | h2024
    · left
      apply Fin.ext
      omega
    · right; right
      apply Fin.ext
      rw [Fin.val_add]
      simp
      omega
    · right; left
      apply Fin.ext
      rw [Fin.val_sub]
      simp
      omega

private def putnamA4IsScalar2 (Y : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 0 0 = Y 1 1

private lemma putnamA4_isScalar2_commute {Y M : Matrix (Fin 2) (Fin 2) ℝ}
    (hY : putnamA4IsScalar2 Y) : Y * M = M * Y := by
  rcases hY with ⟨h01, h10, hdiag⟩
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, h01, h10, hdiag] <;> ring

private lemma putnamA4_comm_eq00 {X Y : Matrix (Fin 2) (Fin 2) ℝ}
    (h : X * Y = Y * X) :
    X 0 1 * Y 1 0 = Y 0 1 * X 1 0 := by
  have h00 := congr_fun (congr_fun h (0 : Fin 2)) (0 : Fin 2)
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  ring_nf at h00 ⊢
  linarith

private lemma putnamA4_comm_eq01 {X Y : Matrix (Fin 2) (Fin 2) ℝ}
    (h : X * Y = Y * X) :
    Y 0 1 * (X 0 0 - X 1 1) = X 0 1 * (Y 0 0 - Y 1 1) := by
  have h01 := congr_fun (congr_fun h (0 : Fin 2)) (1 : Fin 2)
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  ring_nf at h01 ⊢
  linarith

private lemma putnamA4_comm_eq10 {X Y : Matrix (Fin 2) (Fin 2) ℝ}
    (h : X * Y = Y * X) :
    Y 1 0 * (X 0 0 - X 1 1) = X 1 0 * (Y 0 0 - Y 1 1) := by
  have h10 := congr_fun (congr_fun h (1 : Fin 2)) (0 : Fin 2)
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h10
  ring_nf at h10 ⊢
  linarith

private lemma putnamA4_exists_scalar_add_smul_of_comm_of₀₁_ne_zero
    {X Y : Matrix (Fin 2) (Fin 2) ℝ} (h : X * Y = Y * X) (hb : Y 0 1 ≠ 0) :
    ∃ a b : ℝ, X = Matrix.scalar (Fin 2) a + b • Y := by
  refine ⟨X 0 0 - (X 0 1 / Y 0 1) * Y 0 0, X 0 1 / Y 0 1, ?_⟩
  ext r c
  fin_cases r <;> fin_cases c
  · simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hb]
  · have h00 := putnamA4_comm_eq00 h
    simp [Matrix.scalar_apply]
    field_simp [hb]
    ring_nf at h00 ⊢
    linarith
  · have h01 := putnamA4_comm_eq01 h
    simp [Matrix.scalar_apply]
    field_simp [hb]
    ring_nf at h01 ⊢
    linarith

private lemma putnamA4_exists_scalar_add_smul_of_comm_of₁₀_ne_zero
    {X Y : Matrix (Fin 2) (Fin 2) ℝ} (h : X * Y = Y * X) (hc : Y 1 0 ≠ 0) :
    ∃ a b : ℝ, X = Matrix.scalar (Fin 2) a + b • Y := by
  refine ⟨X 0 0 - (X 1 0 / Y 1 0) * Y 0 0, X 1 0 / Y 1 0, ?_⟩
  ext r c
  fin_cases r <;> fin_cases c
  · simp [Matrix.scalar_apply]
  · have h00 := putnamA4_comm_eq00 h
    simp [Matrix.scalar_apply]
    field_simp [hc]
    ring_nf at h00 ⊢
    linarith
  · simp [Matrix.scalar_apply, hc]
  · have h10 := putnamA4_comm_eq10 h
    simp [Matrix.scalar_apply]
    field_simp [hc]
    ring_nf at h10 ⊢
    linarith

private lemma putnamA4_exists_scalar_add_smul_of_comm_of_diag_ne
    {X Y : Matrix (Fin 2) (Fin 2) ℝ} (h : X * Y = Y * X)
    (hb : Y 0 1 = 0) (hc : Y 1 0 = 0) (hd : Y 0 0 ≠ Y 1 1) :
    ∃ a b : ℝ, X = Matrix.scalar (Fin 2) a + b • Y := by
  have hden : Y 0 0 - Y 1 1 ≠ 0 := sub_ne_zero.mpr hd
  have hx01 : X 0 1 = 0 := by
    have h01 := putnamA4_comm_eq01 h
    rw [hb, zero_mul] at h01
    exact (mul_eq_zero.mp h01.symm).resolve_right hden
  have hx10 : X 1 0 = 0 := by
    have h10 := putnamA4_comm_eq10 h
    rw [hc, zero_mul] at h10
    exact (mul_eq_zero.mp h10.symm).resolve_right hden
  refine ⟨X 0 0 - ((X 0 0 - X 1 1) / (Y 0 0 - Y 1 1)) * Y 0 0,
    (X 0 0 - X 1 1) / (Y 0 0 - Y 1 1), ?_⟩
  ext r c
  fin_cases r <;> fin_cases c
  · simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hb, hx01]
  · simp [Matrix.scalar_apply, hc, hx10]
  · simp [Matrix.scalar_apply]
    field_simp [hden]
    ring

private lemma putnamA4_exists_scalar_add_smul_of_comm_of_not_scalar
    {X Y : Matrix (Fin 2) (Fin 2) ℝ} (h : X * Y = Y * X)
    (hY : ¬ putnamA4IsScalar2 Y) :
    ∃ a b : ℝ, X = Matrix.scalar (Fin 2) a + b • Y := by
  by_cases hb : Y 0 1 = 0
  · by_cases hc : Y 1 0 = 0
    · have hd : Y 0 0 ≠ Y 1 1 := by
        intro hd
        exact hY ⟨hb, hc, hd⟩
      exact putnamA4_exists_scalar_add_smul_of_comm_of_diag_ne h hb hc hd
    · exact putnamA4_exists_scalar_add_smul_of_comm_of₁₀_ne_zero h hc
  · exact putnamA4_exists_scalar_add_smul_of_comm_of₀₁_ne_zero h hb

private lemma putnamA4_centralizer_fin_two {X Y Z : Matrix (Fin 2) (Fin 2) ℝ}
    (hXY : X * Y = Y * X) (hYZ : Y * Z = Z * Y)
    (hY : ¬ putnamA4IsScalar2 Y) : X * Z = Z * X := by
  rcases putnamA4_exists_scalar_add_smul_of_comm_of_not_scalar hXY hY with ⟨a, b, rfl⟩
  rcases putnamA4_exists_scalar_add_smul_of_comm_of_not_scalar hYZ.symm hY with ⟨c, d, rfl⟩
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] <;> ring

private lemma putnamA4_matrix_fin_one_comm (X Y : Matrix (Fin 1) (Fin 1) ℝ) :
    X * Y = Y * X := by
  ext r s
  fin_cases r
  fin_cases s
  simp [Matrix.mul_apply, mul_comm]

private lemma putnamA4_not_good_zero :
    ¬ ∃ A : Fin 2025 → Matrix (Fin 0) (Fin 0) ℝ,
      ∀ i j : Fin 2025, i ≤ j →
        (A i * A j = A j * A i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ)) := by
  rintro ⟨A, hA⟩
  have hc : A 0 * A 2 = A 2 * A 0 := Subsingleton.elim _ _
  have hmem := (hA 0 2 (by decide)).mp hc
  norm_num at hmem

private lemma putnamA4_not_good_one :
    ¬ ∃ A : Fin 2025 → Matrix (Fin 1) (Fin 1) ℝ,
      ∀ i j : Fin 2025, i ≤ j →
        (A i * A j = A j * A i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ)) := by
  rintro ⟨A, hA⟩
  have hc : A 0 * A 2 = A 2 * A 0 := putnamA4_matrix_fin_one_comm _ _
  have hmem := (hA 0 2 (by decide)).mp hc
  norm_num at hmem

private lemma putnamA4_not_good_two :
    ¬ ∃ A : Fin 2025 → Matrix (Fin 2) (Fin 2) ℝ,
      ∀ i j : Fin 2025, i ≤ j →
        (A i * A j = A j * A i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ)) := by
  rintro ⟨A, hA⟩
  have h01 : A 0 * A 1 = A 1 * A 0 := (hA 0 1 (by decide)).mpr (by norm_num)
  have h12 : A 1 * A 2 = A 2 * A 1 := (hA 1 2 (by decide)).mpr (by norm_num)
  have h02not : A 0 * A 2 ≠ A 2 * A 0 := by
    intro hc
    have hmem := (hA 0 2 (by decide)).mp hc
    norm_num at hmem
  have h13not : A 1 * A 3 ≠ A 3 * A 1 := by
    intro hc
    have hmem := (hA 1 3 (by decide)).mp hc
    norm_num at hmem
  have hY : ¬ putnamA4IsScalar2 (A 1) := by
    intro hs
    exact h13not (putnamA4_isScalar2_commute hs)
  exact h02not (putnamA4_centralizer_fin_two h01 h12 hY)

/--
Find the minimal value of $k$ such that there exist $k$-by-$k$ real matrices
$A_1, \ldots, A_{2025}$ with the property that $A_i A_j = A_j A_i$ if and only if
$|i - j| \in \{0, 1, 2024\}$.
-/
theorem putnam_2025_a4 :
  IsLeast {k : ℕ | ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ,
    ∀ i j : Fin 2025, i ≤ j →
      (A i * A j = A j * A i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ))}
  putnam_2025_a4_solution :=
by
  change IsLeast {k : ℕ | ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ,
    ∀ i j : Fin 2025, i ≤ j →
      (A i * A j = A j * A i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ))} 3
  constructor
  · refine ⟨putnamA4M, ?_⟩
    intro i j hij
    rw [putnamA4_comm_iff, putnamA4_cycle_iff_diff_mem hij]
  · intro k hk
    by_contra hle
    have hklt : k < 3 := Nat.lt_of_not_ge hle
    interval_cases k
    · exact putnamA4_not_good_zero hk
    · exact putnamA4_not_good_one hk
    · exact putnamA4_not_good_two hk
