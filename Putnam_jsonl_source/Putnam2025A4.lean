import Mathlib

-- 3

/--
Find the minimal value of $k$ such that there exist $k$-by-$k$ real matrices
$A_1, \ldots, A_{2025}$ with the property that $A_i A_j = A_j A_i$ if and only if
$|i - j| \in \{0, 1, 2024\}$.
-/
theorem putnam_2025_a4 :
  IsLeast {k : ℕ | ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ,
    ∀ i j : Fin 2025, i ≤ j →
      (A i * A j = A j * A i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ))}
  ((3) : ℕ ) := by
  classical
  let theta : ℝ := 2 * Real.pi * ((1012 : ℝ) / 2025)
  let c : ℝ := Real.sqrt (Real.cos (Real.pi / 2025))
  let v : Fin 2025 → Fin 3 → ℝ :=
    fun i => ![Real.cos ((i.val : ℝ) * theta), Real.sin ((i.val : ℝ) * theta), c]
  let A3 : Fin 2025 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun i => Matrix.vecMulVec (v i) (v i)
  have rankOne_comm_iff_of_same_third :
      ∀ {c0 : ℝ} {u w : Fin 3 → ℝ}, c0 ≠ 0 → u 2 = c0 → w 2 = c0 →
        (Matrix.vecMulVec u u * Matrix.vecMulVec w w =
            Matrix.vecMulVec w w * Matrix.vecMulVec u u ↔ u ⬝ᵥ w = 0 ∨ u = w) := by
    intro c0 u w hc0 hu hw
    constructor
    · intro h
      rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec] at h
      rw [dotProduct_comm w u] at h
      by_cases hdot : u ⬝ᵥ w = 0
      · exact Or.inl hdot
      · right
        funext r
        have hentry := Matrix.ext_iff.mpr h r (2 : Fin 3)
        simpa [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hu, hw, hdot, hc0]
          using hentry
    · rintro (hdot | rfl)
      · rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
        rw [dotProduct_comm w u, hdot]
        simp
      · simp
  have c_pos : 0 < Real.cos (Real.pi / 2025) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have c_ne_zero : c ≠ 0 := by
    unfold c
    exact ne_of_gt (Real.sqrt_pos.2 c_pos)
  have c_sq : c * c = Real.cos (Real.pi / 2025) := by
    rw [← sq]
    unfold c
    rw [Real.sq_sqrt]
    exact c_pos.le
  have theta_cos : Real.cos theta = -Real.cos (Real.pi / 2025) := by
    rw [show theta = Real.pi - Real.pi / 2025 by
      unfold theta
      ring]
    rw [Real.cos_pi_sub]
  have v_third : ∀ i : Fin 2025, v i 2 = c := by
    intro i
    simp [v]
  have v_dot_general : ∀ i j : Fin 2025,
      v i ⬝ᵥ v j =
        Real.cos (((i.val : ℝ) - (j.val : ℝ)) * theta) + Real.cos (Real.pi / 2025) := by
    intro i j
    rw [show v i ⬝ᵥ v j =
        Real.cos ((i.val : ℝ) * theta) * Real.cos ((j.val : ℝ) * theta) +
          Real.sin ((i.val : ℝ) * theta) * Real.sin ((j.val : ℝ) * theta) + c * c by
      simp [v, dotProduct, Fin.sum_univ_three]]
    rw [c_sq]
    rw [← Real.cos_sub]
    congr 1
    ring_nf
  have v_dot_of_le : ∀ i j : Fin 2025, i ≤ j →
      v i ⬝ᵥ v j =
        Real.cos (((j.val - i.val : ℕ) : ℝ) * theta) + Real.cos (Real.pi / 2025) := by
    intro i j hij
    rw [v_dot_general]
    have hsub : ((i.val : ℝ) - (j.val : ℝ)) * theta =
        -(((j.val - i.val : ℕ) : ℝ) * theta) := by
      have hijv : i.val ≤ j.val := hij
      rw [show (i.val : ℝ) - (j.val : ℝ) = -(((j.val - i.val : ℕ) : ℝ)) by
        rw [Nat.cast_sub hijv]
        ring]
      ring
    rw [hsub, Real.cos_neg]
  have cos_dtheta_eq_cos_theta_of_d : ∀ d : ℕ, d = 1 ∨ d = 2024 →
      Real.cos ((d : ℝ) * theta) = Real.cos theta := by
    intro d hd
    rcases hd with rfl | rfl
    · simp
    · rw [Real.cos_eq_cos_iff]
      refine ⟨(1012 : ℤ), Or.inr ?_⟩
      unfold theta
      norm_num
      ring
  have d_eq_one_or_last_of_cos : ∀ d : ℕ, d < 2025 →
      Real.cos ((d : ℝ) * theta) = Real.cos theta → d = 1 ∨ d = 2024 := by
    intro d hdlt hcos
    rcases (Real.cos_eq_cos_iff.mp hcos) with ⟨k, hk | hk⟩
    · left
      have hreal : (1012 : ℝ) * (1 - d) = 2025 * (k : ℝ) := by
        have hdiv := congrArg (fun x : ℝ => x / (2 * Real.pi)) hk
        unfold theta at hdiv
        field_simp [Real.pi_ne_zero] at hdiv
        linarith
      have hint : (1012 : ℤ) * (1 - (d : ℤ)) = 2025 * k := by
        exact_mod_cast hreal
      omega
    · right
      have hreal : (1012 : ℝ) * (1 + d) = 2025 * (k : ℝ) := by
        have hdiv := congrArg (fun x : ℝ => x / (2 * Real.pi)) hk
        unfold theta at hdiv
        field_simp [Real.pi_ne_zero] at hdiv
        linarith
      have hint : (1012 : ℤ) * (1 + (d : ℤ)) = 2025 * k := by
        exact_mod_cast hreal
      omega
  have v_dot_zero_iff : ∀ i j : Fin 2025, i ≤ j →
      (v i ⬝ᵥ v j = 0 ↔ j.val - i.val = 1 ∨ j.val - i.val = 2024) := by
    intro i j hij
    let d : ℕ := j.val - i.val
    have hdlt : d < 2025 := by
      exact lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
    rw [v_dot_of_le i j hij]
    change Real.cos ((d : ℝ) * theta) + Real.cos (Real.pi / 2025) = 0 ↔
      d = 1 ∨ d = 2024
    constructor
    · intro h
      have hcos : Real.cos ((d : ℝ) * theta) = Real.cos theta := by
        linarith [theta_cos]
      exact d_eq_one_or_last_of_cos d hdlt hcos
    · intro hd
      rw [cos_dtheta_eq_cos_theta_of_d d hd, theta_cos]
      ring
  have d_eq_zero_of_cos_one : ∀ d : ℕ, d < 2025 →
      Real.cos ((d : ℝ) * theta) = 1 → d = 0 := by
    intro d hdlt hcos
    rcases (Real.cos_eq_one_iff ((d : ℝ) * theta)).mp hcos with ⟨k, hk⟩
    have hreal : 2025 * (k : ℝ) = 1012 * (d : ℝ) := by
      have hdiv := congrArg (fun x : ℝ => x / (2 * Real.pi)) hk
      unfold theta at hdiv
      field_simp [Real.pi_ne_zero] at hdiv
      linarith
    have hint : 2025 * k = 1012 * (d : ℤ) := by
      exact_mod_cast hreal
    omega
  have v_eq_iff_of_le : ∀ i j : Fin 2025, i ≤ j → (v i = v j ↔ j.val - i.val = 0) := by
    intro i j hij
    constructor
    · intro hv
      let d : ℕ := j.val - i.val
      have hdlt : d < 2025 := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
      have h0 := congr_fun hv (0 : Fin 3)
      have h1 := congr_fun hv (1 : Fin 3)
      simp [v] at h0 h1
      have hcos_sub : Real.cos (((i.val : ℝ) - (j.val : ℝ)) * theta) = 1 := by
        rw [show ((i.val : ℝ) - (j.val : ℝ)) * theta =
            (i.val : ℝ) * theta - (j.val : ℝ) * theta by ring]
        rw [Real.cos_sub]
        rw [h0, h1]
        nlinarith [Real.cos_sq_add_sin_sq ((j.val : ℝ) * theta)]
      have hcosd : Real.cos ((d : ℝ) * theta) = 1 := by
        have hsub : ((i.val : ℝ) - (j.val : ℝ)) * theta = -((d : ℝ) * theta) := by
          have hijv : i.val ≤ j.val := hij
          rw [show (i.val : ℝ) - (j.val : ℝ) = -(((j.val - i.val : ℕ) : ℝ)) by
            rw [Nat.cast_sub hijv]
            ring]
          simp [d]
        rw [← Real.cos_neg ((d : ℝ) * theta), ← hsub]
        exact hcos_sub
      exact d_eq_zero_of_cos_one d hdlt hcosd
    · intro hd
      have hijv : i.val = j.val := by omega
      have : i = j := Fin.ext hijv
      subst j
      rfl
  have comm_iff : ∀ i j : Fin 2025, i ≤ j →
      (A3 i * A3 j = A3 j * A3 i ↔
        j.val - i.val ∈ ({0, 1, 2024} : Set ℕ)) := by
    intro i j hij
    change Matrix.vecMulVec (v i) (v i) * Matrix.vecMulVec (v j) (v j) =
        Matrix.vecMulVec (v j) (v j) * Matrix.vecMulVec (v i) (v i) ↔
        j.val - i.val ∈ ({0, 1, 2024} : Set ℕ)
    rw [rankOne_comm_iff_of_same_third c_ne_zero (v_third i) (v_third j)]
    constructor
    · rintro (hdot | heq)
      · have hd := (v_dot_zero_iff i j hij).mp hdot
        rcases hd with hd | hd <;> simp [hd]
      · have hd := (v_eq_iff_of_le i j hij).mp heq
        simp [hd]
    · intro hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h0 | h1 | h2024
      · exact Or.inr ((v_eq_iff_of_le i j hij).mpr h0)
      · exact Or.inl ((v_dot_zero_iff i j hij).mpr (Or.inl h1))
      · exact Or.inl ((v_dot_zero_iff i j hij).mpr (Or.inr h2024))
  have matrix_fin_two_centralizer_comm :
      ∀ {M B C : Matrix (Fin 2) (Fin 2) ℝ},
        B * M = M * B → C * M = M * C →
        M 0 1 ≠ 0 ∨ M 1 0 ≠ 0 ∨ M 0 0 ≠ M 1 1 → B * C = C * B := by
    intro M B C hB hC hM
    by_cases hb : M 0 1 ≠ 0
    · have hBr : B 1 0 = B 0 1 * M 1 0 / M 0 1 := by
        have h := Matrix.ext_iff.mpr hB (0 : Fin 2) (0 : Fin 2)
        simp [Matrix.mul_apply, Fin.sum_univ_two] at h
        field_simp [hb]
        linarith
      have hCr : C 1 0 = C 0 1 * M 1 0 / M 0 1 := by
        have h := Matrix.ext_iff.mpr hC (0 : Fin 2) (0 : Fin 2)
        simp [Matrix.mul_apply, Fin.sum_univ_two] at h
        field_simp [hb]
        linarith
      have hBp : B 0 0 = B 1 1 + (M 0 0 - M 1 1) * B 0 1 / M 0 1 := by
        have h := Matrix.ext_iff.mpr hB (0 : Fin 2) (1 : Fin 2)
        simp [Matrix.mul_apply, Fin.sum_univ_two] at h
        field_simp [hb]
        linarith
      have hCp : C 0 0 = C 1 1 + (M 0 0 - M 1 1) * C 0 1 / M 0 1 := by
        have h := Matrix.ext_iff.mpr hC (0 : Fin 2) (1 : Fin 2)
        simp [Matrix.mul_apply, Fin.sum_univ_two] at h
        field_simp [hb]
        linarith
      ext x y
      fin_cases x <;> fin_cases y <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hBr, hCr, hBp, hCp] <;>
        field_simp [hb] <;> ring
    · by_cases hc : M 1 0 ≠ 0
      · have hBq : B 0 1 = B 1 0 * M 0 1 / M 1 0 := by
          have h := Matrix.ext_iff.mpr hB (0 : Fin 2) (0 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two] at h
          field_simp [hc]
          linarith
        have hCq : C 0 1 = C 1 0 * M 0 1 / M 1 0 := by
          have h := Matrix.ext_iff.mpr hC (0 : Fin 2) (0 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two] at h
          field_simp [hc]
          linarith
        have hBs : B 1 1 = B 0 0 + (M 1 1 - M 0 0) * B 1 0 / M 1 0 := by
          have h := Matrix.ext_iff.mpr hB (1 : Fin 2) (0 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two] at h
          field_simp [hc]
          linarith
        have hCs : C 1 1 = C 0 0 + (M 1 1 - M 0 0) * C 1 0 / M 1 0 := by
          have h := Matrix.ext_iff.mpr hC (1 : Fin 2) (0 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two] at h
          field_simp [hc]
          linarith
        ext x y
        fin_cases x <;> fin_cases y <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, hBq, hCq, hBs, hCs] <;>
          field_simp [hc] <;> ring
      · push_neg at hb hc
        have hdiag : M 0 0 ≠ M 1 1 := by
          rcases hM with h | h | h
          · exact (h hb).elim
          · exact (h hc).elim
          · exact h
        have hdiff01 : M 1 1 - M 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hdiag)
        have hdiff10 : M 0 0 - M 1 1 ≠ 0 := sub_ne_zero.mpr hdiag
        have hBq : B 0 1 = 0 := by
          have h := Matrix.ext_iff.mpr hB (0 : Fin 2) (1 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two, hb] at h
          have hmul : B 0 1 * (M 1 1 - M 0 0) = 0 := by nlinarith
          exact (mul_eq_zero.mp hmul).resolve_right hdiff01
        have hBr : B 1 0 = 0 := by
          have h := Matrix.ext_iff.mpr hB (1 : Fin 2) (0 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two, hc] at h
          have hmul : B 1 0 * (M 0 0 - M 1 1) = 0 := by nlinarith
          exact (mul_eq_zero.mp hmul).resolve_right hdiff10
        have hCq : C 0 1 = 0 := by
          have h := Matrix.ext_iff.mpr hC (0 : Fin 2) (1 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two, hb] at h
          have hmul : C 0 1 * (M 1 1 - M 0 0) = 0 := by nlinarith
          exact (mul_eq_zero.mp hmul).resolve_right hdiff01
        have hCr : C 1 0 = 0 := by
          have h := Matrix.ext_iff.mpr hC (1 : Fin 2) (0 : Fin 2)
          simp [Matrix.mul_apply, Fin.sum_univ_two, hc] at h
          have hmul : C 1 0 * (M 0 0 - M 1 1) = 0 := by nlinarith
          exact (mul_eq_zero.mp hmul).resolve_right hdiff10
        ext x y
        fin_cases x <;> fin_cases y <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, hBq, hBr, hCq, hCr] <;> ring
  refine ⟨?_, ?_⟩
  · exact ⟨A3, comm_iff⟩
  · intro k hk
    rcases hk with ⟨A, hA⟩
    by_contra hk3
    have hklt : k < 3 := by omega
    interval_cases k
    · have hcomm : A 0 * A 2 = A 2 * A 0 := by
        exact Subsingleton.elim _ _
      have hbad := (hA 0 2 (by decide)).mp hcomm
      norm_num at hbad
    · have hcomm : A 0 * A 2 = A 2 * A 0 := by
        ext x y
        fin_cases x
        fin_cases y
        simp [Matrix.mul_apply, mul_comm]
      have hbad := (hA 0 2 (by decide)).mp hcomm
      norm_num at hbad
    · have h01 : A 0 * A 1 = A 1 * A 0 := by
        exact (hA 0 1 (by decide)).mpr (by norm_num)
      have h12 : A 1 * A 2 = A 2 * A 1 := by
        exact (hA 1 2 (by decide)).mpr (by norm_num)
      have h02not : A 0 * A 2 ≠ A 2 * A 0 := by
        intro hcomm
        have hbad := (hA 0 2 (by decide)).mp hcomm
        norm_num at hbad
      have hscalar : ¬ (A 1 0 1 ≠ 0 ∨ A 1 1 0 ≠ 0 ∨ A 1 0 0 ≠ A 1 1 1) := by
        intro hnonscalar
        exact h02not
          (matrix_fin_two_centralizer_comm (M := A 1) (B := A 0) (C := A 2)
            h01 h12.symm hnonscalar)
      push_neg at hscalar
      rcases hscalar with ⟨h01z, h10z, hdiag⟩
      have h13comm : A 1 * A 3 = A 3 * A 1 := by
        ext x y
        fin_cases x <;> fin_cases y <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, h01z, h10z, hdiag] <;> ring
      have hbad := (hA 1 3 (by decide)).mp h13comm
      norm_num at hbad
