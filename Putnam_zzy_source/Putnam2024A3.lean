import Mathlib

private abbrev putnam_2024_a3_tableaux : Set (ℕ × ℕ → ℕ) :=
  {T | Set.BijOn T (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024) (Finset.Icc 1 6072) ∧
    (∀ j ∈ Finset.Icc 1 2024, StrictMonoOn (fun i => T (i, j)) (Set.Icc 1 3)) ∧
    (∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024)) ∧
    (∀ x, x ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 → T x = 0)}

noncomputable abbrev putnam_2024_a3_solution : Prop := True

private theorem putnam_2024_a3_reviewed_rational_bound :
    (2025 / 6071 : ℚ) ∈ Set.Icc (1 / 3) (2 / 3) := by
  norm_num [Set.mem_Icc]

private theorem putnam_2024_a3_le_bottom_right
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_tableaux) {i j : ℕ}
    (hi : i ∈ Finset.Icc 1 3) (hj : j ∈ Finset.Icc 1 2024) :
    T (i, j) ≤ T (3, 2024) := by
  rcases hT with ⟨_, hcols, hrows, _⟩
  have hiS : i ∈ Set.Icc 1 3 := by simpa using hi
  have h3S : (3 : ℕ) ∈ Set.Icc 1 3 := by norm_num
  have hjS : j ∈ Set.Icc 1 2024 := by simpa using hj
  have h2024S : (2024 : ℕ) ∈ Set.Icc 1 2024 := by norm_num
  calc
    T (i, j) ≤ T (3, j) := by
      exact (hcols j hj).monotoneOn hiS h3S (Finset.mem_Icc.mp hi).2
    _ ≤ T (3, 2024) := by
      exact (hrows 3 (by norm_num)).monotoneOn hjS h2024S (Finset.mem_Icc.mp hj).2

private theorem putnam_2024_a3_bottom_right_eq_max
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_tableaux) :
    T (3, 2024) = 6072 := by
  rcases hT with ⟨hbij, hcols, hrows, hzero⟩
  have h6072 : (6072 : ℕ) ∈ (Finset.Icc 1 6072 : Finset ℕ) := by norm_num
  rcases hbij.surjOn h6072 with ⟨x, hxdom, hx⟩
  rcases x with ⟨i, j⟩
  have hi : i ∈ Finset.Icc 1 3 := by simpa using hxdom.1
  have hj : j ∈ Finset.Icc 1 2024 := by simpa using hxdom.2
  have hle :=
    putnam_2024_a3_le_bottom_right (T := T) ⟨hbij, hcols, hrows, hzero⟩ hi hj
  rw [hx] at hle
  have hbrdom :
      (3, 2024) ∈ (↑(Finset.Icc 1 3) ×ˢ ↑(Finset.Icc 1 2024) : Set (ℕ × ℕ)) := by
    exact ⟨by norm_num, by norm_num⟩
  have hbr_mem : 1 ≤ T (3, 2024) ∧ T (3, 2024) ≤ 6072 := by
    simpa [Finset.mem_Icc] using hbij.mapsTo hbrdom
  omega

private theorem putnam_2024_a3_le_two_2024
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_tableaux) {i j : ℕ}
    (hi : i ∈ Finset.Icc 1 2) (hj : j ∈ Finset.Icc 1 2024) :
    T (i, j) ≤ T (2, 2024) := by
  rcases hT with ⟨_, hcols, hrows, _⟩
  have hiS : i ∈ Set.Icc 1 3 := by
    have h := Finset.mem_Icc.mp hi
    exact ⟨h.1, by omega⟩
  have h2S : (2 : ℕ) ∈ Set.Icc 1 3 := by norm_num
  have hjS : j ∈ Set.Icc 1 2024 := by simpa using hj
  have h2024S : (2024 : ℕ) ∈ Set.Icc 1 2024 := by norm_num
  calc
    T (i, j) ≤ T (2, j) := by
      exact (hcols j hj).monotoneOn hiS h2S (Finset.mem_Icc.mp hi).2
    _ ≤ T (2, 2024) := by
      exact (hrows 2 (by norm_num)).monotoneOn hjS h2024S (Finset.mem_Icc.mp hj).2

private theorem putnam_2024_a3_second_max_of_event
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_tableaux)
    (he : T (3, 2023) < T (2, 2024)) :
    T (2, 2024) = 6071 := by
  rcases hT with ⟨hbij, hcols, hrows, hzero⟩
  have hT' : T ∈ putnam_2024_a3_tableaux := ⟨hbij, hcols, hrows, hzero⟩
  have h6071 : (6071 : ℕ) ∈ (Finset.Icc 1 6072 : Finset ℕ) := by norm_num
  rcases hbij.surjOn h6071 with ⟨x, hxdom, hx⟩
  rcases x with ⟨i, j⟩
  have hi13 : i ∈ Finset.Icc 1 3 := by simpa using hxdom.1
  have hj : j ∈ Finset.Icc 1 2024 := by simpa using hxdom.2
  have hle : T (i, j) ≤ T (2, 2024) := by
    have hi_bounds := Finset.mem_Icc.mp hi13
    by_cases hi2 : i ≤ 2
    · exact putnam_2024_a3_le_two_2024 hT' (Finset.mem_Icc.mpr ⟨hi_bounds.1, hi2⟩) hj
    · have hi_eq3 : i = 3 := by omega
      subst i
      have hj_bounds := Finset.mem_Icc.mp hj
      by_cases hj2023 : j ≤ 2023
      · have hjS : j ∈ Set.Icc 1 2024 := by simpa using hj
        have h2023S : (2023 : ℕ) ∈ Set.Icc 1 2024 := by norm_num
        have hrow : T (3, j) ≤ T (3, 2023) := by
          exact (hrows 3 (by norm_num)).monotoneOn hjS h2023S hj2023
        exact le_trans hrow he.le
      · have hj_eq : j = 2024 := by omega
        subst j
        have hmax := putnam_2024_a3_bottom_right_eq_max hT'
        rw [hmax] at hx
        omega
  rw [hx] at hle
  have hcell :
      (2, 2024) ∈ (↑(Finset.Icc 1 3) ×ˢ ↑(Finset.Icc 1 2024) : Set (ℕ × ℕ)) := by
    exact ⟨by norm_num, by norm_num⟩
  have hmem : 1 ≤ T (2, 2024) ∧ T (2, 2024) ≤ 6072 := by
    simpa [Finset.mem_Icc] using hbij.mapsTo hcell
  have hne_max : T (2, 2024) ≠ 6072 := by
    intro h
    have hbr :
        (3, 2024) ∈ (↑(Finset.Icc 1 3) ×ˢ ↑(Finset.Icc 1 2024) : Set (ℕ × ℕ)) := by
      exact ⟨by norm_num, by norm_num⟩
    have hcell_ne : (2, 2024) ≠ (3, 2024) := by norm_num
    have hinj := hbij.injOn hcell hbr
    have hbmax := putnam_2024_a3_bottom_right_eq_max hT'
    exact hcell_ne (hinj (by rw [h, hbmax]))
  omega

private theorem putnam_2024_a3_event_of_second_max
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_tableaux)
    (hsecond : T (2, 2024) = 6071) :
    T (3, 2023) < T (2, 2024) := by
  rcases hT with ⟨hbij, hcols, hrows, hzero⟩
  have hT' : T ∈ putnam_2024_a3_tableaux := ⟨hbij, hcols, hrows, hzero⟩
  have hcell :
      (3, 2023) ∈ (↑(Finset.Icc 1 3) ×ˢ ↑(Finset.Icc 1 2024) : Set (ℕ × ℕ)) := by
    exact ⟨by norm_num, by norm_num⟩
  have hmem : 1 ≤ T (3, 2023) ∧ T (3, 2023) ≤ 6072 := by
    simpa [Finset.mem_Icc] using hbij.mapsTo hcell
  have hne6072 : T (3, 2023) ≠ 6072 := by
    intro h
    have hbr :
        (3, 2024) ∈ (↑(Finset.Icc 1 3) ×ˢ ↑(Finset.Icc 1 2024) : Set (ℕ × ℕ)) := by
      exact ⟨by norm_num, by norm_num⟩
    have hcell_ne : (3, 2023) ≠ (3, 2024) := by norm_num
    have hinj := hbij.injOn hcell hbr
    have hbmax := putnam_2024_a3_bottom_right_eq_max hT'
    exact hcell_ne (hinj (by rw [h, hbmax]))
  have hne6071 : T (3, 2023) ≠ 6071 := by
    intro h
    have hcell2 :
        (2, 2024) ∈ (↑(Finset.Icc 1 3) ×ˢ ↑(Finset.Icc 1 2024) : Set (ℕ × ℕ)) := by
      exact ⟨by norm_num, by norm_num⟩
    have hcell_ne : (3, 2023) ≠ (2, 2024) := by norm_num
    have hinj := hbij.injOn hcell hcell2
    exact hcell_ne (hinj (by rw [h, hsecond]))
  omega

private theorem putnam_2024_a3_second_max_event_iff
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_tableaux) :
    T (3, 2023) < T (2, 2024) ↔ T (2, 2024) = 6071 :=
  ⟨putnam_2024_a3_second_max_of_event hT, putnam_2024_a3_event_of_second_max hT⟩

private noncomputable def putnam_2024_a3_hookCountQ (a b c : ℕ) : ℚ :=
  ((Nat.factorial (a + b + c) : ℚ) * (a - b + 1) * (a - c + 2) * (b - c + 1)) /
    ((Nat.factorial (a + 2) : ℚ) * Nat.factorial (b + 1) * Nat.factorial c)

private theorem putnam_2024_a3_hookCountQ_ratio :
    putnam_2024_a3_hookCountQ 2024 2023 2023 /
        putnam_2024_a3_hookCountQ 2024 2024 2024 = (2025 / 6071 : ℚ) := by
  norm_num [putnam_2024_a3_hookCountQ]

private theorem putnam_2024_a3_hookCountQ_recurrence_interior
    (a b c : ℕ) (hba : b < a) (hcb : c < b) (hc0 : 0 < c) :
    putnam_2024_a3_hookCountQ a b c =
      putnam_2024_a3_hookCountQ (a - 1) b c +
        putnam_2024_a3_hookCountQ a (b - 1) c +
          putnam_2024_a3_hookCountQ a b (c - 1) := by
  unfold putnam_2024_a3_hookCountQ
  rw [show a - 1 + b + c = a + b + c - 1 by omega]
  rw [show a + (b - 1) + c = a + b + c - 1 by omega]
  rw [show a + b + (c - 1) = a + b + c - 1 by omega]
  rw [show (a - 1) + 2 = a + 1 by omega]
  rw [show (b - 1) + 1 = b by omega]
  have hfacS : Nat.factorial (a + b + c) =
      (a + b + c) * Nat.factorial (a + b + c - 1) := by
    conv_lhs => rw [show a + b + c = (a + b + c - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a + b + c - 1) + 1 = a + b + c by omega]
  have hfacA : Nat.factorial (a + 2) = (a + 2) * Nat.factorial (a + 1) := by
    conv_lhs => rw [show a + 2 = (a + 1) + 1 by omega, Nat.factorial_succ]
  have hfacB : Nat.factorial (b + 1) = (b + 1) * Nat.factorial b := by
    rw [Nat.factorial_succ]
  have hfacC : Nat.factorial c = c * Nat.factorial (c - 1) := by
    conv_lhs => rw [show c = (c - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (c - 1) + 1 = c by omega]
  rw [hfacS, hfacA, hfacB, hfacC]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + b + c - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (c - 1))]
  rw [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_sub (show 1 ≤ b by omega),
    Nat.cast_sub (show 1 ≤ c by omega)]
  ring_nf

private def putnam_2024_a3_rowLen (a b c i : ℕ) : ℕ :=
  if i = 1 then a else if i = 2 then b else if i = 3 then c else 0

private def putnam_2024_a3_shape (a b c : ℕ) : Set (ℕ × ℕ) :=
  {x | 1 ≤ x.1 ∧ x.1 ≤ 3 ∧ 1 ≤ x.2 ∧ x.2 ≤ putnam_2024_a3_rowLen a b c x.1}

private def putnam_2024_a3_labels (a b c : ℕ) : Set ℕ :=
  Finset.Icc 1 (a + b + c)

private def putnam_2024_a3_cellLt (x y : ℕ × ℕ) : Prop :=
  (x.1 = y.1 ∧ x.2 < y.2) ∨ (x.2 = y.2 ∧ x.1 < y.1)

private def putnam_2024_a3_shapeStrict (a b c : ℕ) (T : ℕ × ℕ → ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ putnam_2024_a3_shape a b c →
    ∀ ⦃y⦄, y ∈ putnam_2024_a3_shape a b c →
      putnam_2024_a3_cellLt x y → T x < T y

private def putnam_2024_a3_partialTableaux (a b c : ℕ) : Set (ℕ × ℕ → ℕ) :=
  {T | Set.BijOn T (putnam_2024_a3_shape a b c) (putnam_2024_a3_labels a b c) ∧
    putnam_2024_a3_shapeStrict a b c T ∧
    (∀ x, x ∉ putnam_2024_a3_shape a b c → T x = 0)}

private theorem putnam_2024_a3_shape_finite (a b c : ℕ) :
    (putnam_2024_a3_shape a b c).Finite := by
  refine Set.Finite.subset
    (Finset.finite_toSet (Finset.Icc 1 3 ×ˢ Finset.Icc 1 (max a (max b c)))) ?_
  intro x hx
  rcases x with ⟨i, j⟩
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
  simp only [putnam_2024_a3_shape, Set.mem_setOf_eq] at hx
  rcases hx with ⟨hi1, hi3, hj1, hjle⟩
  refine ⟨⟨hi1, hi3⟩, hj1, ?_⟩
  have hrow : putnam_2024_a3_rowLen a b c i ≤ max a (max b c) := by
    unfold putnam_2024_a3_rowLen
    split_ifs <;> omega
  exact le_trans hjle hrow

private theorem putnam_2024_a3_partialTableaux_finite (a b c : ℕ) :
    (putnam_2024_a3_partialTableaux a b c).Finite := by
  classical
  haveI : Finite (putnam_2024_a3_shape a b c) :=
    (putnam_2024_a3_shape_finite a b c).to_subtype
  let f : putnam_2024_a3_partialTableaux a b c →
      (putnam_2024_a3_shape a b c → Fin (a + b + c + 1)) := fun T x =>
    ⟨T.1 x.1, by
      have hmaps := T.2.1.1 x.2
      simp only [putnam_2024_a3_labels, Finset.mem_coe, Finset.mem_Icc] at hmaps
      omega⟩
  have hf : Function.Injective f := by
    intro T U h
    ext x
    by_cases hx : x ∈ putnam_2024_a3_shape a b c
    · exact Fin.ext_iff.mp (congr_fun h ⟨x, hx⟩)
    · rw [T.2.2.2 x hx, U.2.2.2 x hx]
  exact Finite.of_injective f hf

private theorem putnam_2024_a3_cellLt_irrefl (x : ℕ × ℕ) :
    ¬ putnam_2024_a3_cellLt x x := by
  rcases x with ⟨i, j⟩
  simp [putnam_2024_a3_cellLt]

private theorem putnam_2024_a3_shape_top_insert {a b c : ℕ} (hba : b < a) :
    putnam_2024_a3_shape a b c =
      insert (1, a) (putnam_2024_a3_shape (a - 1) b c) := by
  ext x
  rcases x with ⟨i, j⟩
  simp only [putnam_2024_a3_shape, Set.mem_setOf_eq, Set.mem_insert_iff, Prod.mk.injEq]
  unfold putnam_2024_a3_rowLen
  by_cases hi1 : i = 1
  · subst i
    simp
    omega
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1]
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2]
      · simp [hi1, hi2, hi3]

private theorem putnam_2024_a3_shape_mid_insert {a b c : ℕ} (hcb : c < b) :
    putnam_2024_a3_shape a b c =
      insert (2, b) (putnam_2024_a3_shape a (b - 1) c) := by
  ext x
  rcases x with ⟨i, j⟩
  simp only [putnam_2024_a3_shape, Set.mem_setOf_eq, Set.mem_insert_iff, Prod.mk.injEq]
  unfold putnam_2024_a3_rowLen
  by_cases hi1 : i = 1
  · subst i
    simp
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1]
      omega
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2]
      · simp [hi1, hi2, hi3]

private theorem putnam_2024_a3_shape_bot_insert {a b c : ℕ} (hc0 : 0 < c) :
    putnam_2024_a3_shape a b c =
      insert (3, c) (putnam_2024_a3_shape a b (c - 1)) := by
  ext x
  rcases x with ⟨i, j⟩
  simp only [putnam_2024_a3_shape, Set.mem_setOf_eq, Set.mem_insert_iff, Prod.mk.injEq]
  unfold putnam_2024_a3_rowLen
  by_cases hi1 : i = 1
  · subst i
    simp
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1]
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2]
        omega
      · simp [hi1, hi2, hi3]

private theorem putnam_2024_a3_label_top_insert {a b c : ℕ} (hba : b < a) :
    putnam_2024_a3_labels a b c =
      insert (a + b + c) (putnam_2024_a3_labels (a - 1) b c) := by
  ext n
  simp only [putnam_2024_a3_labels, Finset.mem_coe, Finset.mem_Icc, Set.mem_insert_iff]
  omega

private theorem putnam_2024_a3_label_mid_insert {a b c : ℕ} (hcb : c < b) :
    putnam_2024_a3_labels a b c =
      insert (a + b + c) (putnam_2024_a3_labels a (b - 1) c) := by
  ext n
  simp only [putnam_2024_a3_labels, Finset.mem_coe, Finset.mem_Icc, Set.mem_insert_iff]
  omega

private theorem putnam_2024_a3_label_bot_insert {a b c : ℕ} (hc0 : 0 < c) :
    putnam_2024_a3_labels a b c =
      insert (a + b + c) (putnam_2024_a3_labels a b (c - 1)) := by
  ext n
  simp only [putnam_2024_a3_labels, Finset.mem_coe, Finset.mem_Icc, Set.mem_insert_iff]
  omega

private theorem putnam_2024_a3_top_not_small {a b c : ℕ} (hba : b < a) :
    (1, a) ∉ putnam_2024_a3_shape (a - 1) b c := by
  simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
  omega

private theorem putnam_2024_a3_mid_not_small {a b c : ℕ} (hcb : c < b) :
    (2, b) ∉ putnam_2024_a3_shape a (b - 1) c := by
  simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
  omega

private theorem putnam_2024_a3_bot_not_small {a b c : ℕ} (hc0 : 0 < c) :
    (3, c) ∉ putnam_2024_a3_shape a b (c - 1) := by
  simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
  omega

private theorem putnam_2024_a3_top_maximal {a b c : ℕ} (hab : b ≤ a) (hbc : c ≤ b)
    (hba : b < a) {y : ℕ × ℕ} (hy : y ∈ putnam_2024_a3_shape a b c) :
    ¬ putnam_2024_a3_cellLt (1, a) y := by
  rcases y with ⟨i, j⟩
  unfold putnam_2024_a3_shape putnam_2024_a3_rowLen at hy
  unfold putnam_2024_a3_cellLt
  by_cases hi1 : i = 1
  · subst i
    simp at hy ⊢ <;> omega
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1] at hy ⊢ <;> omega
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2] at hy ⊢ <;> omega
      · simp [hi1, hi2, hi3] at hy
        omega

private theorem putnam_2024_a3_mid_maximal {a b c : ℕ} (hab : b ≤ a) (hbc : c ≤ b)
    (hcb : c < b) {y : ℕ × ℕ} (hy : y ∈ putnam_2024_a3_shape a b c) :
    ¬ putnam_2024_a3_cellLt (2, b) y := by
  rcases y with ⟨i, j⟩
  unfold putnam_2024_a3_shape putnam_2024_a3_rowLen at hy
  unfold putnam_2024_a3_cellLt
  by_cases hi1 : i = 1
  · subst i
    simp at hy ⊢ <;> omega
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1] at hy ⊢ <;> omega
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2] at hy ⊢ <;> omega
      · simp [hi1, hi2, hi3] at hy
        omega

private theorem putnam_2024_a3_bot_maximal {a b c : ℕ} (hab : b ≤ a) (hbc : c ≤ b)
    (hc0 : 0 < c) {y : ℕ × ℕ} (hy : y ∈ putnam_2024_a3_shape a b c) :
    ¬ putnam_2024_a3_cellLt (3, c) y := by
  rcases y with ⟨i, j⟩
  unfold putnam_2024_a3_shape putnam_2024_a3_rowLen at hy
  unfold putnam_2024_a3_cellLt
  by_cases hi1 : i = 1
  · subst i
    simp at hy ⊢ <;> omega
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1] at hy ⊢ <;> omega
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2] at hy ⊢ <;> omega
      · simp [hi1, hi2, hi3] at hy
        omega

private theorem putnam_2024_a3_label_top_lt {a b c n : ℕ} (hba : b < a)
    (hn : n ∈ putnam_2024_a3_labels (a - 1) b c) : n < a + b + c := by
  simp [putnam_2024_a3_labels] at hn
  omega

private theorem putnam_2024_a3_label_mid_lt {a b c n : ℕ} (hcb : c < b)
    (hn : n ∈ putnam_2024_a3_labels a (b - 1) c) : n < a + b + c := by
  simp [putnam_2024_a3_labels] at hn
  omega

private theorem putnam_2024_a3_label_bot_lt {a b c n : ℕ} (hc0 : 0 < c)
    (hn : n ∈ putnam_2024_a3_labels a b (c - 1)) : n < a + b + c := by
  simp [putnam_2024_a3_labels] at hn
  omega

private theorem putnam_2024_a3_corner_insert_mem {a b c a' b' c' N : ℕ} {p : ℕ × ℕ}
    (hshape : putnam_2024_a3_shape a b c = insert p (putnam_2024_a3_shape a' b' c'))
    (hlabel : putnam_2024_a3_labels a b c = insert N (putnam_2024_a3_labels a' b' c'))
    (hpnot : p ∉ putnam_2024_a3_shape a' b' c')
    (hNnot : N ∉ putnam_2024_a3_labels a' b' c')
    (hmax : ∀ {y}, y ∈ putnam_2024_a3_shape a b c → ¬ putnam_2024_a3_cellLt p y)
    (hlabel_lt : ∀ {n}, n ∈ putnam_2024_a3_labels a' b' c' → n < N)
    {U : ℕ × ℕ → ℕ} (hU : U ∈ putnam_2024_a3_partialTableaux a' b' c') :
    Function.update U p N ∈ putnam_2024_a3_partialTableaux a b c := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape, hlabel]
    have hbijSmall : Set.BijOn (Function.update U p N)
        (putnam_2024_a3_shape a' b' c') (putnam_2024_a3_labels a' b' c') := by
      exact hU.1.congr (fun x hx => by
        rw [Function.update_of_ne (fun h => hpnot (by simpa [h] using hx))])
    have hNnot' : Function.update U p N p ∉ putnam_2024_a3_labels a' b' c' := by
      simpa [Function.update_self] using hNnot
    simpa [Function.update_self] using hbijSmall.insert hNnot'
  · intro x hx y hy hxy
    have hyBig : y ∈ putnam_2024_a3_shape a b c := hy
    rw [hshape] at hx hy
    by_cases hyp : y = p
    · subst y
      have hxsmall : x ∈ putnam_2024_a3_shape a' b' c' := by
        rcases hx with hxeq | hxsmall
        · exact False.elim (putnam_2024_a3_cellLt_irrefl p (by simpa [hxeq] using hxy))
        · exact hxsmall
      have hxp : x ≠ p := fun h => hpnot (by simpa [h] using hxsmall)
      have hUx := hU.1.1 hxsmall
      rw [Function.update_of_ne hxp, Function.update_self]
      exact hlabel_lt hUx
    · have hysmall : y ∈ putnam_2024_a3_shape a' b' c' := by
        rcases hy with hyeq | hysmall
        · exact False.elim (hyp hyeq)
        · exact hysmall
      have hxsmall : x ∈ putnam_2024_a3_shape a' b' c' := by
        rcases hx with hxeq | hxsmall
        · exact False.elim ((hmax hyBig) (by simpa [hxeq] using hxy))
        · exact hxsmall
      have hxp : x ≠ p := fun h => hpnot (by simpa [h] using hxsmall)
      rw [Function.update_of_ne hxp, Function.update_of_ne hyp]
      exact hU.2.1 hxsmall hysmall hxy
  · intro x hxnot
    by_cases hxp : x = p
    · subst x
      exfalso
      apply hxnot
      rw [hshape]
      simp
    · rw [Function.update_of_ne hxp]
      exact hU.2.2 x (by
        intro hxsmall
        apply hxnot
        rw [hshape]
        exact Or.inr hxsmall)

private theorem putnam_2024_a3_corner_delete_mem {a b c a' b' c' N : ℕ} {p : ℕ × ℕ}
    (hshape : putnam_2024_a3_shape a b c = insert p (putnam_2024_a3_shape a' b' c'))
    (hlabel : putnam_2024_a3_labels a b c = insert N (putnam_2024_a3_labels a' b' c'))
    (hpnot : p ∉ putnam_2024_a3_shape a' b' c')
    (hNnot : N ∉ putnam_2024_a3_labels a' b' c')
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_partialTableaux a b c) (hTp : T p = N) :
    Function.update T p 0 ∈ putnam_2024_a3_partialTableaux a' b' c' := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have hbijBig := hT.1
    rw [hshape, hlabel] at hbijBig
    have hTpnot : T p ∉ putnam_2024_a3_labels a' b' c' := by simpa [hTp] using hNnot
    have hbijBig' : Set.BijOn T (insert p (putnam_2024_a3_shape a' b' c'))
        (insert (T p) (putnam_2024_a3_labels a' b' c')) := by
      simpa [hTp] using hbijBig
    have hbijTsmall : Set.BijOn T (putnam_2024_a3_shape a' b' c')
        (putnam_2024_a3_labels a' b' c') :=
      (Set.BijOn.insert_iff hpnot hTpnot).mp hbijBig'
    exact hbijTsmall.congr (fun x hx => by
      rw [Function.update_of_ne (fun h => hpnot (by simpa [h] using hx))])
  · intro x hx y hy hxy
    have hxp : x ≠ p := fun h => hpnot (by simpa [h] using hx)
    have hyp : y ≠ p := fun h => hpnot (by simpa [h] using hy)
    rw [Function.update_of_ne hxp, Function.update_of_ne hyp]
    exact hT.2.1 (by rw [hshape]; exact Or.inr hx) (by rw [hshape]; exact Or.inr hy) hxy
  · intro x hxnot
    by_cases hxp : x = p
    · subst x
      rw [Function.update_self]
    · rw [Function.update_of_ne hxp]
      exact hT.2.2 x (by
        intro hxbig
        rw [hshape] at hxbig
        rcases hxbig with hxeq | hxsmall
        · exact hxp hxeq
        · exact hxnot hxsmall)

private def putnam_2024_a3_cornerTableaux (a b c N : ℕ) (p : ℕ × ℕ) :
    Set (ℕ × ℕ → ℕ) :=
  {T | T ∈ putnam_2024_a3_partialTableaux a b c ∧ T p = N}

private theorem putnam_2024_a3_corner_ncard_eq {a b c a' b' c' N : ℕ} {p : ℕ × ℕ}
    (hshape : putnam_2024_a3_shape a b c = insert p (putnam_2024_a3_shape a' b' c'))
    (hlabel : putnam_2024_a3_labels a b c = insert N (putnam_2024_a3_labels a' b' c'))
    (hpnot : p ∉ putnam_2024_a3_shape a' b' c')
    (hNnot : N ∉ putnam_2024_a3_labels a' b' c')
    (hmax : ∀ {y}, y ∈ putnam_2024_a3_shape a b c → ¬ putnam_2024_a3_cellLt p y)
    (hlabel_lt : ∀ {n}, n ∈ putnam_2024_a3_labels a' b' c' → n < N) :
    (putnam_2024_a3_cornerTableaux a b c N p).ncard =
      (putnam_2024_a3_partialTableaux a' b' c').ncard := by
  classical
  refine Set.ncard_congr' ?_
  refine
    { toFun := fun T => ⟨Function.update T.1 p 0,
        putnam_2024_a3_corner_delete_mem hshape hlabel hpnot hNnot T.2.1 T.2.2⟩
      invFun := fun U => ⟨Function.update U.1 p N,
        ⟨putnam_2024_a3_corner_insert_mem hshape hlabel hpnot hNnot hmax hlabel_lt U.2,
          by rw [Function.update_self]⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    apply Subtype.ext
    change Function.update (Function.update (T : ℕ × ℕ → ℕ) p 0) p N =
      (T : ℕ × ℕ → ℕ)
    funext x
    by_cases hx : x = p
    · subst x
      simp [Function.update_self, T.2.2]
    · simp [Function.update_of_ne hx]
  · intro U
    apply Subtype.ext
    change Function.update (Function.update (U : ℕ × ℕ → ℕ) p N) p 0 =
      (U : ℕ × ℕ → ℕ)
    funext x
    by_cases hx : x = p
    · subst x
      simp [Function.update_self, U.2.2.2 p hpnot]
    · simp [Function.update_of_ne hx]

private def putnam_2024_a3_validTop (a b c : ℕ) : Set (ℕ × ℕ → ℕ) :=
  {T | T ∈ putnam_2024_a3_partialTableaux a b c ∧ b < a ∧ T (1, a) = a + b + c}

private def putnam_2024_a3_validMid (a b c : ℕ) : Set (ℕ × ℕ → ℕ) :=
  {T | T ∈ putnam_2024_a3_partialTableaux a b c ∧ c < b ∧ T (2, b) = a + b + c}

private def putnam_2024_a3_validBot (a b c : ℕ) : Set (ℕ × ℕ → ℕ) :=
  {T | T ∈ putnam_2024_a3_partialTableaux a b c ∧ 0 < c ∧ T (3, c) = a + b + c}

private theorem putnam_2024_a3_validTop_ncard (a b c : ℕ) (hab : b ≤ a) (hbc : c ≤ b) :
    (putnam_2024_a3_validTop a b c).ncard =
      if b < a then (putnam_2024_a3_partialTableaux (a - 1) b c).ncard else 0 := by
  classical
  by_cases hba : b < a
  · have hset :
        putnam_2024_a3_validTop a b c =
          putnam_2024_a3_cornerTableaux a b c (a + b + c) (1, a) := by
      ext T
      simp [putnam_2024_a3_validTop, putnam_2024_a3_cornerTableaux, hba, and_assoc]
    have hNnot : a + b + c ∉ putnam_2024_a3_labels (a - 1) b c := by
      simp [putnam_2024_a3_labels]
      omega
    rw [hset, if_pos hba]
    exact putnam_2024_a3_corner_ncard_eq
      (putnam_2024_a3_shape_top_insert hba)
      (putnam_2024_a3_label_top_insert hba)
      (putnam_2024_a3_top_not_small hba)
      hNnot
      (fun {y} hy => putnam_2024_a3_top_maximal hab hbc hba hy)
      (fun {n} hn => putnam_2024_a3_label_top_lt hba hn)
  · have hset : putnam_2024_a3_validTop a b c = ∅ := by
      ext T
      simp [putnam_2024_a3_validTop, hba]
    rw [hset, if_neg hba, Set.ncard_empty]

private theorem putnam_2024_a3_validMid_ncard (a b c : ℕ) (hab : b ≤ a) (hbc : c ≤ b) :
    (putnam_2024_a3_validMid a b c).ncard =
      if c < b then (putnam_2024_a3_partialTableaux a (b - 1) c).ncard else 0 := by
  classical
  by_cases hcb : c < b
  · have hset :
        putnam_2024_a3_validMid a b c =
          putnam_2024_a3_cornerTableaux a b c (a + b + c) (2, b) := by
      ext T
      simp [putnam_2024_a3_validMid, putnam_2024_a3_cornerTableaux, hcb, and_assoc]
    have hNnot : a + b + c ∉ putnam_2024_a3_labels a (b - 1) c := by
      simp [putnam_2024_a3_labels]
      omega
    rw [hset, if_pos hcb]
    exact putnam_2024_a3_corner_ncard_eq
      (putnam_2024_a3_shape_mid_insert hcb)
      (putnam_2024_a3_label_mid_insert hcb)
      (putnam_2024_a3_mid_not_small hcb)
      hNnot
      (fun {y} hy => putnam_2024_a3_mid_maximal hab hbc hcb hy)
      (fun {n} hn => putnam_2024_a3_label_mid_lt hcb hn)
  · have hset : putnam_2024_a3_validMid a b c = ∅ := by
      ext T
      simp [putnam_2024_a3_validMid, hcb]
    rw [hset, if_neg hcb, Set.ncard_empty]

private theorem putnam_2024_a3_validBot_ncard (a b c : ℕ) (hab : b ≤ a) (hbc : c ≤ b) :
    (putnam_2024_a3_validBot a b c).ncard =
      if 0 < c then (putnam_2024_a3_partialTableaux a b (c - 1)).ncard else 0 := by
  classical
  by_cases hc0 : 0 < c
  · have hset :
        putnam_2024_a3_validBot a b c =
          putnam_2024_a3_cornerTableaux a b c (a + b + c) (3, c) := by
      ext T
      simp [putnam_2024_a3_validBot, putnam_2024_a3_cornerTableaux, hc0, and_assoc]
    have hNnot : a + b + c ∉ putnam_2024_a3_labels a b (c - 1) := by
      simp [putnam_2024_a3_labels]
      omega
    rw [hset, if_pos hc0]
    exact putnam_2024_a3_corner_ncard_eq
      (putnam_2024_a3_shape_bot_insert hc0)
      (putnam_2024_a3_label_bot_insert hc0)
      (putnam_2024_a3_bot_not_small hc0)
      hNnot
      (fun {y} hy => putnam_2024_a3_bot_maximal hab hbc hc0 hy)
      (fun {n} hn => putnam_2024_a3_label_bot_lt hc0 hn)
  · have hset : putnam_2024_a3_validBot a b c = ∅ := by
      ext T
      simp [putnam_2024_a3_validBot, hc0]
    rw [hset, if_neg hc0, Set.ncard_empty]

private theorem putnam_2024_a3_max_corner_of_partial {a b c : ℕ}
    (hab : b ≤ a) (hbc : c ≤ b) (hpos : 0 < a + b + c)
    {T : ℕ × ℕ → ℕ} (hT : T ∈ putnam_2024_a3_partialTableaux a b c) :
    (b < a ∧ T (1, a) = a + b + c) ∨
      (c < b ∧ T (2, b) = a + b + c) ∨
        (0 < c ∧ T (3, c) = a + b + c) := by
  let N := a + b + c
  have hNmem : N ∈ putnam_2024_a3_labels a b c := by
    simp [N, putnam_2024_a3_labels]
    omega
  rcases hT.1.surjOn hNmem with ⟨x, hxshape, hxT⟩
  rcases x with ⟨i, j⟩
  have hxbounds := hxshape
  unfold putnam_2024_a3_shape putnam_2024_a3_rowLen at hxbounds
  by_cases hi1 : i = 1
  · subst i
    simp at hxbounds
    have hj_eq : j = a := by
      by_contra hne
      have hjlt : j < a := by omega
      have hy : (1, j + 1) ∈ putnam_2024_a3_shape a b c := by
        simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
        omega
      have hlt := hT.2.1 hxshape hy (by simp [putnam_2024_a3_cellLt])
      have hyval := hT.1.mapsTo hy
      simp [putnam_2024_a3_labels] at hyval
      rw [hxT] at hlt
      omega
    subst j
    have hba : b < a := by
      by_contra hnot
      have hbaeq : b = a := by omega
      have hy : (2, a) ∈ putnam_2024_a3_shape a b c := by
        simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen, hbaeq]
        omega
      have hlt := hT.2.1 hxshape hy (by simp [putnam_2024_a3_cellLt])
      have hyval := hT.1.mapsTo hy
      simp [putnam_2024_a3_labels] at hyval
      rw [hxT] at hlt
      omega
    exact Or.inl ⟨hba, by simpa [N] using hxT⟩
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1] at hxbounds
      have hj_eq : j = b := by
        by_contra hne
        have hjlt : j < b := by omega
        have hy : (2, j + 1) ∈ putnam_2024_a3_shape a b c := by
          simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
          omega
        have hlt := hT.2.1 hxshape hy (by simp [putnam_2024_a3_cellLt])
        have hyval := hT.1.mapsTo hy
        simp [putnam_2024_a3_labels] at hyval
        rw [hxT] at hlt
        omega
      subst j
      have hcb : c < b := by
        by_contra hnot
        have hcbeq : c = b := by omega
        have hy : (3, b) ∈ putnam_2024_a3_shape a b c := by
          simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen, hcbeq]
          omega
        have hlt := hT.2.1 hxshape hy (by simp [putnam_2024_a3_cellLt])
        have hyval := hT.1.mapsTo hy
        simp [putnam_2024_a3_labels] at hyval
        rw [hxT] at hlt
        omega
      exact Or.inr (Or.inl ⟨hcb, by simpa [N] using hxT⟩)
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2] at hxbounds
        have hj_eq : j = c := by
          by_contra hne
          have hjlt : j < c := by omega
          have hy : (3, j + 1) ∈ putnam_2024_a3_shape a b c := by
            simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
            omega
          have hlt := hT.2.1 hxshape hy (by simp [putnam_2024_a3_cellLt])
          have hyval := hT.1.mapsTo hy
          simp [putnam_2024_a3_labels] at hyval
          rw [hxT] at hlt
          omega
        subst j
        have hc0 : 0 < c := by omega
        exact Or.inr (Or.inr ⟨hc0, by simpa [N] using hxT⟩)
      · simp [hi1, hi2, hi3] at hxbounds
        omega

private theorem putnam_2024_a3_validCorner_union {a b c : ℕ}
    (hab : b ≤ a) (hbc : c ≤ b) (hpos : 0 < a + b + c) :
    putnam_2024_a3_partialTableaux a b c =
      putnam_2024_a3_validTop a b c ∪
        (putnam_2024_a3_validMid a b c ∪ putnam_2024_a3_validBot a b c) := by
  ext T
  constructor
  · intro hT
    rcases putnam_2024_a3_max_corner_of_partial hab hbc hpos hT with
      ⟨hba, hval⟩ | ⟨hcb, hval⟩ | ⟨hc0, hval⟩
    · exact Or.inl ⟨hT, hba, hval⟩
    · exact Or.inr (Or.inl ⟨hT, hcb, hval⟩)
    · exact Or.inr (Or.inr ⟨hT, hc0, hval⟩)
  · intro h
    rcases h with htop | hrest
    · exact htop.1
    · rcases hrest with hmid | hbot
      · exact hmid.1
      · exact hbot.1

private theorem putnam_2024_a3_validTopMid_disjoint (a b c : ℕ) (hab : b ≤ a) :
    Disjoint (putnam_2024_a3_validTop a b c) (putnam_2024_a3_validMid a b c) := by
  rw [Set.disjoint_left]
  intro T htop hmid
  rcases htop with ⟨hT, hba, hTtop⟩
  rcases hmid with ⟨_, hcb, hTmid⟩
  have hp1 : (1, a) ∈ putnam_2024_a3_shape a b c := by
    simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
    omega
  have hp2 : (2, b) ∈ putnam_2024_a3_shape a b c := by
    simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
    omega
  have hcells : (1, a) ≠ (2, b) := by simp
  exact hcells (hT.1.injOn hp1 hp2 (by rw [hTtop, hTmid]))

private theorem putnam_2024_a3_validTopBot_disjoint (a b c : ℕ) :
    Disjoint (putnam_2024_a3_validTop a b c) (putnam_2024_a3_validBot a b c) := by
  rw [Set.disjoint_left]
  intro T htop hbot
  rcases htop with ⟨hT, hba, hTtop⟩
  rcases hbot with ⟨_, hc0, hTbot⟩
  have hp1 : (1, a) ∈ putnam_2024_a3_shape a b c := by
    simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
    omega
  have hp2 : (3, c) ∈ putnam_2024_a3_shape a b c := by
    simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
    omega
  have hcells : (1, a) ≠ (3, c) := by simp
  exact hcells (hT.1.injOn hp1 hp2 (by rw [hTtop, hTbot]))

private theorem putnam_2024_a3_validMidBot_disjoint (a b c : ℕ) (hab : b ≤ a) :
    Disjoint (putnam_2024_a3_validMid a b c) (putnam_2024_a3_validBot a b c) := by
  rw [Set.disjoint_left]
  intro T hmid hbot
  rcases hmid with ⟨hT, hcb, hTmid⟩
  rcases hbot with ⟨_, hc0, hTbot⟩
  have hp1 : (2, b) ∈ putnam_2024_a3_shape a b c := by
    simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
    omega
  have hp2 : (3, c) ∈ putnam_2024_a3_shape a b c := by
    simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
    omega
  have hcells : (2, b) ≠ (3, c) := by simp
  exact hcells (hT.1.injOn hp1 hp2 (by rw [hTmid, hTbot]))

private theorem putnam_2024_a3_validTop_disjoint_mid_union_bot (a b c : ℕ) (hab : b ≤ a) :
    Disjoint (putnam_2024_a3_validTop a b c)
      (putnam_2024_a3_validMid a b c ∪ putnam_2024_a3_validBot a b c) := by
  rw [Set.disjoint_left]
  intro T htop hrest
  rcases hrest with hmid | hbot
  · exact (Set.disjoint_left.mp (putnam_2024_a3_validTopMid_disjoint a b c hab)) htop hmid
  · exact (Set.disjoint_left.mp (putnam_2024_a3_validTopBot_disjoint a b c)) htop hbot

private theorem putnam_2024_a3_partial_ncard_recurrence {a b c : ℕ}
    (hab : b ≤ a) (hbc : c ≤ b) (hpos : 0 < a + b + c) :
    (putnam_2024_a3_partialTableaux a b c).ncard =
      (if b < a then (putnam_2024_a3_partialTableaux (a - 1) b c).ncard else 0) +
        ((if c < b then (putnam_2024_a3_partialTableaux a (b - 1) c).ncard else 0) +
          (if 0 < c then (putnam_2024_a3_partialTableaux a b (c - 1)).ncard else 0)) := by
  classical
  have hfinTop : (putnam_2024_a3_validTop a b c).Finite :=
    (putnam_2024_a3_partialTableaux_finite a b c).subset (by
      intro T hT
      exact hT.1)
  have hfinMid : (putnam_2024_a3_validMid a b c).Finite :=
    (putnam_2024_a3_partialTableaux_finite a b c).subset (by
      intro T hT
      exact hT.1)
  have hfinBot : (putnam_2024_a3_validBot a b c).Finite :=
    (putnam_2024_a3_partialTableaux_finite a b c).subset (by
      intro T hT
      exact hT.1)
  rw [putnam_2024_a3_validCorner_union hab hbc hpos]
  rw [Set.ncard_union_eq (putnam_2024_a3_validTop_disjoint_mid_union_bot a b c hab)
      hfinTop (hfinMid.union hfinBot)]
  rw [Set.ncard_union_eq (putnam_2024_a3_validMidBot_disjoint a b c hab) hfinMid hfinBot]
  rw [putnam_2024_a3_validTop_ncard a b c hab hbc,
    putnam_2024_a3_validMid_ncard a b c hab hbc,
    putnam_2024_a3_validBot_ncard a b c hab hbc]

private theorem putnam_2024_a3_hookCountQ_recurrence_c_zero
    (a b : ℕ) (hba : b < a) (hb0 : 0 < b) :
    putnam_2024_a3_hookCountQ a b 0 =
      putnam_2024_a3_hookCountQ (a - 1) b 0 +
        putnam_2024_a3_hookCountQ a (b - 1) 0 := by
  unfold putnam_2024_a3_hookCountQ
  rw [show a - 1 + b + 0 = a + b - 1 by omega]
  rw [show a + (b - 1) + 0 = a + b - 1 by omega]
  rw [show (a - 1) + 2 = a + 1 by omega]
  rw [show (b - 1) + 1 = b by omega]
  have hfacS : Nat.factorial (a + b + 0) = (a + b) * Nat.factorial (a + b - 1) := by
    conv_lhs => rw [show a + b + 0 = (a + b - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a + b - 1) + 1 = a + b by omega]
  have hfacA : Nat.factorial (a + 2) = (a + 2) * Nat.factorial (a + 1) := by
    conv_lhs => rw [show a + 2 = (a + 1) + 1 by omega, Nat.factorial_succ]
  have hfacB : Nat.factorial (b + 1) = (b + 1) * Nat.factorial b := by
    rw [Nat.factorial_succ]
  rw [hfacS, hfacA, hfacB]
  simp only [Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + b - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)]
  rw [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_sub (show 1 ≤ b by omega)]
  ring_nf

private theorem putnam_2024_a3_hookCountQ_recurrence_one_row
    (a : ℕ) (ha0 : 0 < a) :
    putnam_2024_a3_hookCountQ a 0 0 =
      putnam_2024_a3_hookCountQ (a - 1) 0 0 := by
  unfold putnam_2024_a3_hookCountQ
  rw [show a - 1 + 0 + 0 = a - 1 by omega]
  rw [show (a - 1) + 2 = a + 1 by omega]
  have hfacS : Nat.factorial (a + 0 + 0) = a * Nat.factorial (a - 1) := by
    conv_lhs => rw [show a + 0 + 0 = (a - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a - 1) + 1 = a by omega]
  have hfacA2 :
      Nat.factorial (a + 2) = (a + 2) * (a + 1) * a * Nat.factorial (a - 1) := by
    conv_lhs => rw [show a + 2 = (a + 1) + 1 by omega, Nat.factorial_succ]
    rw [Nat.factorial_succ]
    conv_lhs => rw [show a = (a - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a - 1) + 1 = a by omega]
    ring
  have hfacA1 : Nat.factorial (a + 1) = (a + 1) * a * Nat.factorial (a - 1) := by
    rw [Nat.factorial_succ]
    conv_lhs => rw [show a = (a - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a - 1) + 1 = a by omega]
    ring
  rw [hfacS, hfacA2, hfacA1]
  simp only [Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a - 1))]
  rw [Nat.cast_sub (show 1 ≤ a by omega)]
  ring_nf

private theorem putnam_2024_a3_hookCountQ_recurrence_c_eq_b
    (a b : ℕ) (hba : b < a) (hb0 : 0 < b) :
    putnam_2024_a3_hookCountQ a b b =
      putnam_2024_a3_hookCountQ (a - 1) b b +
        putnam_2024_a3_hookCountQ a b (b - 1) := by
  unfold putnam_2024_a3_hookCountQ
  rw [show a - 1 + b + b = a + b + b - 1 by omega]
  rw [show a + b + (b - 1) = a + b + b - 1 by omega]
  rw [show (a - 1) + 2 = a + 1 by omega]
  have hfacS : Nat.factorial (a + b + b) =
      (a + b + b) * Nat.factorial (a + b + b - 1) := by
    conv_lhs => rw [show a + b + b = (a + b + b - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a + b + b - 1) + 1 = a + b + b by omega]
  have hfacA : Nat.factorial (a + 2) = (a + 2) * Nat.factorial (a + 1) := by
    conv_lhs => rw [show a + 2 = (a + 1) + 1 by omega, Nat.factorial_succ]
  have hfacC : Nat.factorial b = b * Nat.factorial (b - 1) := by
    conv_lhs => rw [show b = (b - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (b - 1) + 1 = b by omega]
  rw [hfacS, hfacA, hfacC]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + b + b - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (b + 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (b - 1))]
  rw [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_sub (show 1 ≤ b by omega)]
  ring_nf

private theorem putnam_2024_a3_hookCountQ_recurrence_a_eq_b
    (a c : ℕ) (hca : c < a) (hc0 : 0 < c) :
    putnam_2024_a3_hookCountQ a a c =
      putnam_2024_a3_hookCountQ a (a - 1) c +
        putnam_2024_a3_hookCountQ a a (c - 1) := by
  unfold putnam_2024_a3_hookCountQ
  rw [show a + (a - 1) + c = a + a + c - 1 by omega]
  rw [show a + a + (c - 1) = a + a + c - 1 by omega]
  rw [show (a - 1) + 1 = a by omega]
  have hfacS : Nat.factorial (a + a + c) =
      (a + a + c) * Nat.factorial (a + a + c - 1) := by
    conv_lhs => rw [show a + a + c = (a + a + c - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a + a + c - 1) + 1 = a + a + c by omega]
  have hfacB : Nat.factorial (a + 1) = (a + 1) * Nat.factorial a := by
    rw [Nat.factorial_succ]
  have hfacC : Nat.factorial c = c * Nat.factorial (c - 1) := by
    conv_lhs => rw [show c = (c - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (c - 1) + 1 = c by omega]
  rw [hfacS, hfacB, hfacC]
  simp only [Nat.cast_mul, Nat.cast_add]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + a + c - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 2)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (c - 1))]
  rw [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_sub (show 1 ≤ c by omega)]
  ring_nf

private theorem putnam_2024_a3_hookCountQ_recurrence_a_eq_b_c_zero
    (a : ℕ) (ha0 : 0 < a) :
    putnam_2024_a3_hookCountQ a a 0 =
      putnam_2024_a3_hookCountQ a (a - 1) 0 := by
  unfold putnam_2024_a3_hookCountQ
  rw [show a + (a - 1) + 0 = a + a - 1 by omega]
  rw [show (a - 1) + 1 = a by omega]
  have hfacS : Nat.factorial (a + a + 0) = (a + a) * Nat.factorial (a + a - 1) := by
    conv_lhs => rw [show a + a + 0 = (a + a - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a + a - 1) + 1 = a + a by omega]
  have hfacB : Nat.factorial (a + 1) = (a + 1) * Nat.factorial a := by
    rw [Nat.factorial_succ]
  rw [hfacS, hfacB]
  simp only [Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + a - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 2)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)]
  rw [Nat.cast_sub (show 1 ≤ a by omega)]
  ring_nf

private theorem putnam_2024_a3_hookCountQ_recurrence_rectangle
    (a : ℕ) (ha0 : 0 < a) :
    putnam_2024_a3_hookCountQ a a a =
      putnam_2024_a3_hookCountQ a a (a - 1) := by
  unfold putnam_2024_a3_hookCountQ
  rw [show a + a + (a - 1) = a + a + a - 1 by omega]
  have hfacS : Nat.factorial (a + a + a) =
      (a + a + a) * Nat.factorial (a + a + a - 1) := by
    conv_lhs => rw [show a + a + a = (a + a + a - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a + a + a - 1) + 1 = a + a + a by omega]
  have hfacC : Nat.factorial a = a * Nat.factorial (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, Nat.factorial_succ]
    rw [show (a - 1) + 1 = a by omega]
  rw [hfacS, hfacC]
  simp only [Nat.cast_mul, Nat.cast_add]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + a + a - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 2)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a - 1))]
  rw [Nat.cast_sub (show 1 ≤ a by omega)]
  norm_num

private theorem putnam_2024_a3_hookCountQ_recurrence
    (a b c : ℕ) (hab : b ≤ a) (hbc : c ≤ b) (hpos : 0 < a + b + c) :
    putnam_2024_a3_hookCountQ a b c =
      (if b < a then putnam_2024_a3_hookCountQ (a - 1) b c else 0) +
        ((if c < b then putnam_2024_a3_hookCountQ a (b - 1) c else 0) +
          (if 0 < c then putnam_2024_a3_hookCountQ a b (c - 1) else 0)) := by
  by_cases hba : b < a
  · by_cases hcb : c < b
    · by_cases hc0 : 0 < c
      · rw [if_pos hba, if_pos hcb, if_pos hc0]
        rw [putnam_2024_a3_hookCountQ_recurrence_interior a b c hba hcb hc0]
        ring
      · have hc : c = 0 := by omega
        subst c
        have hb0 : 0 < b := by omega
        simp [hba, hcb, putnam_2024_a3_hookCountQ_recurrence_c_zero a b hba hb0]
    · have hceq : c = b := by omega
      subst c
      by_cases hb0 : 0 < b
      · rw [if_pos hba, if_neg (by omega : ¬b < b), if_pos hb0]
        simp [putnam_2024_a3_hookCountQ_recurrence_c_eq_b a b hba hb0]
      · have hb : b = 0 := by omega
        subst b
        have ha0 : 0 < a := by omega
        simp [hba, putnam_2024_a3_hookCountQ_recurrence_one_row a ha0]
  · have hbeq : b = a := by omega
    subst b
    by_cases hcb : c < a
    · by_cases hc0 : 0 < c
      · rw [if_neg (by omega : ¬a < a), if_pos hcb, if_pos hc0]
        simp [putnam_2024_a3_hookCountQ_recurrence_a_eq_b a c hcb hc0]
      · have hc : c = 0 := by omega
        subst c
        have ha0 : 0 < a := by omega
        simp [hcb, putnam_2024_a3_hookCountQ_recurrence_a_eq_b_c_zero a ha0]
    · have hceq : c = a := by omega
      subst c
      have ha0 : 0 < a := by omega
      rw [if_neg (by omega : ¬a < a), if_neg (by omega : ¬a < a), if_pos ha0]
      simp [putnam_2024_a3_hookCountQ_recurrence_rectangle a ha0]

private theorem putnam_2024_a3_shape_empty : putnam_2024_a3_shape 0 0 0 = ∅ := by
  ext x
  rcases x with ⟨i, j⟩
  simp [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
  omega

private theorem putnam_2024_a3_label_empty : putnam_2024_a3_labels 0 0 0 = ∅ := by
  ext n
  simp [putnam_2024_a3_labels]

private theorem putnam_2024_a3_partial_empty_eq_singleton :
    putnam_2024_a3_partialTableaux 0 0 0 = {fun _ : ℕ × ℕ => 0} := by
  ext T
  constructor
  · intro hT
    rw [Set.mem_singleton_iff]
    funext x
    exact hT.2.2 x (by rw [putnam_2024_a3_shape_empty]; simp)
  · intro hT
    rw [Set.mem_singleton_iff] at hT
    subst T
    refine ⟨?_, ?_, ?_⟩
    · rw [putnam_2024_a3_shape_empty, putnam_2024_a3_label_empty]
      simp [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn]
    · intro x hx
      rw [putnam_2024_a3_shape_empty] at hx
      simp at hx
    · intro x hx
      rfl

private theorem putnam_2024_a3_partial_empty_ncard :
    (putnam_2024_a3_partialTableaux 0 0 0).ncard = 1 := by
  rw [putnam_2024_a3_partial_empty_eq_singleton, Set.ncard_singleton]

private theorem putnam_2024_a3_partial_ncard_eq_hookCountQ
    {a b c : ℕ} (hab : b ≤ a) (hbc : c ≤ b) :
    ((putnam_2024_a3_partialTableaux a b c).ncard : ℚ) =
      putnam_2024_a3_hookCountQ a b c := by
  have hmain :
      ∀ n a b c, a + b + c = n → b ≤ a → c ≤ b →
        ((putnam_2024_a3_partialTableaux a b c).ncard : ℚ) =
          putnam_2024_a3_hookCountQ a b c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b c hsum hab hbc
      by_cases hpos : 0 < a + b + c
      · have hrec := putnam_2024_a3_partial_ncard_recurrence hab hbc hpos
        have hrecQ :
            ((putnam_2024_a3_partialTableaux a b c).ncard : ℚ) =
              (if b < a then ((putnam_2024_a3_partialTableaux (a - 1) b c).ncard : ℚ) else 0) +
                ((if c < b then ((putnam_2024_a3_partialTableaux a (b - 1) c).ncard : ℚ) else 0) +
                  (if 0 < c then ((putnam_2024_a3_partialTableaux a b (c - 1)).ncard : ℚ) else 0)) := by
          rw [hrec]
          simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_zero]
        have hhook := putnam_2024_a3_hookCountQ_recurrence a b c hab hbc hpos
        rw [hrecQ, hhook]
        by_cases hba : b < a
        · have ihTop :
              ((putnam_2024_a3_partialTableaux (a - 1) b c).ncard : ℚ) =
                putnam_2024_a3_hookCountQ (a - 1) b c :=
            ih ((a - 1) + b + c) (by omega) (a - 1) b c rfl (by omega) hbc
          by_cases hcb : c < b
          · have ihMid :
                ((putnam_2024_a3_partialTableaux a (b - 1) c).ncard : ℚ) =
                  putnam_2024_a3_hookCountQ a (b - 1) c :=
              ih (a + (b - 1) + c) (by omega) a (b - 1) c rfl (by omega) (by omega)
            by_cases hc0 : 0 < c
            · have ihBot :
                  ((putnam_2024_a3_partialTableaux a b (c - 1)).ncard : ℚ) =
                    putnam_2024_a3_hookCountQ a b (c - 1) :=
                ih (a + b + (c - 1)) (by omega) a b (c - 1) rfl hab (by omega)
              simp [hba, hcb, hc0, ihTop, ihMid, ihBot]
            · simp [hba, hcb, hc0, ihTop, ihMid]
          · by_cases hc0 : 0 < c
            · have ihBot :
                  ((putnam_2024_a3_partialTableaux a b (c - 1)).ncard : ℚ) =
                    putnam_2024_a3_hookCountQ a b (c - 1) :=
                ih (a + b + (c - 1)) (by omega) a b (c - 1) rfl hab (by omega)
              simp [hba, hcb, hc0, ihTop, ihBot]
            · simp [hba, hcb, hc0, ihTop]
        · by_cases hcb : c < b
          · have ihMid :
                ((putnam_2024_a3_partialTableaux a (b - 1) c).ncard : ℚ) =
                  putnam_2024_a3_hookCountQ a (b - 1) c :=
              ih (a + (b - 1) + c) (by omega) a (b - 1) c rfl (by omega) (by omega)
            by_cases hc0 : 0 < c
            · have ihBot :
                  ((putnam_2024_a3_partialTableaux a b (c - 1)).ncard : ℚ) =
                    putnam_2024_a3_hookCountQ a b (c - 1) :=
                ih (a + b + (c - 1)) (by omega) a b (c - 1) rfl hab (by omega)
              simp [hba, hcb, hc0, ihMid, ihBot]
            · simp [hba, hcb, hc0, ihMid]
          · by_cases hc0 : 0 < c
            · have ihBot :
                  ((putnam_2024_a3_partialTableaux a b (c - 1)).ncard : ℚ) =
                    putnam_2024_a3_hookCountQ a b (c - 1) :=
                ih (a + b + (c - 1)) (by omega) a b (c - 1) rfl hab (by omega)
              simp [hba, hcb, hc0, ihBot]
            · simp [hba, hcb, hc0]
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        have hc : c = 0 := by omega
        subst a
        subst b
        subst c
        norm_num [putnam_2024_a3_partial_empty_ncard, putnam_2024_a3_hookCountQ]
  exact hmain (a + b + c) a b c rfl hab hbc

private theorem putnam_2024_a3_rectangle_shape :
    putnam_2024_a3_shape 2024 2024 2024 =
      Set.Icc (1, 1) (3, 2024) := by
  ext x
  rcases x with ⟨i, j⟩
  unfold putnam_2024_a3_shape putnam_2024_a3_rowLen
  by_cases hi1 : i = 1
  · subst i
    simp
  · by_cases hi2 : i = 2
    · subst i
      simp [hi1]
    · by_cases hi3 : i = 3
      · subst i
        simp [hi1, hi2]
      · simp [hi1, hi2, hi3]
        omega

private theorem putnam_2024_a3_rectangle_labels :
    putnam_2024_a3_labels 2024 2024 2024 = (Finset.Icc 1 6072 : Set ℕ) := by
  ext n
  simp [putnam_2024_a3_labels]

private theorem putnam_2024_a3_tableaux_eq_partial :
    putnam_2024_a3_tableaux = putnam_2024_a3_partialTableaux 2024 2024 2024 := by
  ext T
  constructor
  · intro hT
    rcases hT with ⟨hbij, hcols, hrows, hzero⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [putnam_2024_a3_rectangle_shape, putnam_2024_a3_rectangle_labels] using hbij
    · intro x hx y hy hlt
      rcases x with ⟨i, j⟩
      rcases y with ⟨k, l⟩
      rw [putnam_2024_a3_rectangle_shape] at hx hy
      have hi : i ∈ Finset.Icc 1 3 := by
        exact Finset.mem_Icc.mpr ⟨hx.1.1, hx.2.1⟩
      have hj : j ∈ Finset.Icc 1 2024 := by
        exact Finset.mem_Icc.mpr ⟨hx.1.2, hx.2.2⟩
      have hk : k ∈ Finset.Icc 1 3 := by
        exact Finset.mem_Icc.mpr ⟨hy.1.1, hy.2.1⟩
      have hl : l ∈ Finset.Icc 1 2024 := by
        exact Finset.mem_Icc.mpr ⟨hy.1.2, hy.2.2⟩
      rcases hlt with hrow | hcol
      · rcases hrow with ⟨hik, hjl⟩
        have hik' : i = k := by simpa using hik
        subst k
        exact (hrows i hi) (by simpa using hj) (by simpa using hl) (by simpa using hjl)
      · rcases hcol with ⟨hjl, hik⟩
        have hjl' : j = l := by simpa using hjl
        subst l
        exact (hcols j hj) (by simpa using hi) (by simpa using hk) (by simpa using hik)
    · intro x hx
      exact hzero x (by
        intro hprod
        have hprod' :
            x.1 ∈ Finset.Icc 1 3 ∧ x.2 ∈ Finset.Icc 1 2024 := by
          simpa [Finset.mem_product] using hprod
        have hx1 := Finset.mem_Icc.mp hprod'.1
        have hx2 := Finset.mem_Icc.mp hprod'.2
        have hxrow : x.2 ≤ putnam_2024_a3_rowLen 2024 2024 2024 x.1 := by
          unfold putnam_2024_a3_rowLen
          split_ifs <;> omega
        apply hx
        exact ⟨hx1.1, hx1.2, hx2.1, hxrow⟩)
  · intro hT
    rcases hT with ⟨hbij, hstrict, hzero⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [putnam_2024_a3_rectangle_shape, putnam_2024_a3_rectangle_labels] using hbij
    · intro j hj
      intro i hi k hk hik
      apply hstrict
      · rw [putnam_2024_a3_rectangle_shape]
        have hj' := (Finset.mem_Icc.mp hj)
        exact ⟨⟨hi.1, hj'.1⟩, ⟨hi.2, hj'.2⟩⟩
      · rw [putnam_2024_a3_rectangle_shape]
        have hj' := (Finset.mem_Icc.mp hj)
        exact ⟨⟨hk.1, hj'.1⟩, ⟨hk.2, hj'.2⟩⟩
      · exact Or.inr ⟨rfl, hik⟩
    · intro i hi
      intro j hj k hk hjk
      apply hstrict
      · rw [putnam_2024_a3_rectangle_shape]
        have hi' := (Finset.mem_Icc.mp hi)
        exact ⟨⟨hi'.1, hj.1⟩, ⟨hi'.2, hj.2⟩⟩
      · rw [putnam_2024_a3_rectangle_shape]
        have hi' := (Finset.mem_Icc.mp hi)
        exact ⟨⟨hi'.1, hk.1⟩, ⟨hi'.2, hk.2⟩⟩
      · exact Or.inl ⟨rfl, hjk⟩
    · intro x hx
      exact hzero x (by
          intro hshape
          apply hx
          have hx1 : x.1 ∈ Finset.Icc 1 3 :=
            Finset.mem_Icc.mpr ⟨hshape.1, hshape.2.1⟩
          have hx2le : x.2 ≤ 2024 := by
            have hrow := hshape.2.2.2
            unfold putnam_2024_a3_rowLen at hrow
            split_ifs at hrow <;> omega
          have hx2 : x.2 ∈ Finset.Icc 1 2024 :=
            Finset.mem_Icc.mpr ⟨hshape.2.2.1, hx2le⟩
          simpa [Finset.mem_product] using And.intro hx1 hx2)

private theorem putnam_2024_a3_tableaux_ncard :
    ((putnam_2024_a3_tableaux.ncard : ℚ) =
      putnam_2024_a3_hookCountQ 2024 2024 2024) := by
  rw [putnam_2024_a3_tableaux_eq_partial]
  exact putnam_2024_a3_partial_ncard_eq_hookCountQ (by norm_num) (by norm_num)

private theorem putnam_2024_a3_event_ncard :
    ((({T | T ∈ putnam_2024_a3_tableaux ∧ T (3, 2023) < T (2, 2024)}).ncard : ℚ) =
      putnam_2024_a3_hookCountQ 2024 2023 2023) := by
  classical
  have hncard :
      ({T | T ∈ putnam_2024_a3_tableaux ∧ T (3, 2023) < T (2, 2024)}).ncard =
        (putnam_2024_a3_partialTableaux 2024 2023 2023).ncard := by
    refine Set.ncard_congr' ?_
    refine
      { toFun := fun T =>
          ⟨Function.update (Function.update T.1 (3, 2024) 0) (2, 2024) 0, by
            have hTab : T.1 ∈ putnam_2024_a3_tableaux := T.2.1
            have hpartialFull :
                T.1 ∈ putnam_2024_a3_partialTableaux 2024 2024 2024 := by
              simpa [putnam_2024_a3_tableaux_eq_partial] using hTab
            have hbot : T.1 (3, 2024) = 6072 :=
              putnam_2024_a3_bottom_right_eq_max hTab
            have hmid : T.1 (2, 2024) = 6071 :=
              (putnam_2024_a3_second_max_event_iff hTab).1 T.2.2
            have hbotDel :
                Function.update T.1 (3, 2024) 0 ∈
                  putnam_2024_a3_partialTableaux 2024 2024 2023 := by
              exact putnam_2024_a3_corner_delete_mem
                (putnam_2024_a3_shape_bot_insert (a := 2024) (b := 2024) (c := 2024) (by norm_num))
                (by simpa using
                  putnam_2024_a3_label_bot_insert (a := 2024) (b := 2024) (c := 2024) (by norm_num))
                (putnam_2024_a3_bot_not_small (a := 2024) (b := 2024) (c := 2024) (by norm_num))
                (by norm_num [putnam_2024_a3_labels])
                hpartialFull hbot
            have hmidAfter :
                (Function.update T.1 (3, 2024) 0) (2, 2024) = 6071 := by
              rw [Function.update_of_ne (by norm_num : (2, 2024) ≠ (3, 2024)), hmid]
            exact putnam_2024_a3_corner_delete_mem
              (putnam_2024_a3_shape_mid_insert (a := 2024) (b := 2024) (c := 2023) (by norm_num))
              (by simpa using
                putnam_2024_a3_label_mid_insert (a := 2024) (b := 2024) (c := 2023) (by norm_num))
              (putnam_2024_a3_mid_not_small (a := 2024) (b := 2024) (c := 2023) (by norm_num))
              (by norm_num [putnam_2024_a3_labels])
              hbotDel hmidAfter⟩
        invFun := fun U =>
          ⟨Function.update (Function.update U.1 (2, 2024) 6071) (3, 2024) 6072, by
            have hmidIns :
                Function.update U.1 (2, 2024) 6071 ∈
                  putnam_2024_a3_partialTableaux 2024 2024 2023 := by
              exact putnam_2024_a3_corner_insert_mem
                (putnam_2024_a3_shape_mid_insert (a := 2024) (b := 2024) (c := 2023) (by norm_num))
                (by simpa using
                  putnam_2024_a3_label_mid_insert (a := 2024) (b := 2024) (c := 2023) (by norm_num))
                (putnam_2024_a3_mid_not_small (a := 2024) (b := 2024) (c := 2023) (by norm_num))
                (by norm_num [putnam_2024_a3_labels])
                (fun {y} hy => putnam_2024_a3_mid_maximal
                  (a := 2024) (b := 2024) (c := 2023)
                  (by norm_num) (by norm_num) (by norm_num) hy)
                (fun {n} hn => putnam_2024_a3_label_mid_lt
                  (a := 2024) (b := 2024) (c := 2023) (by norm_num) hn)
                U.2
            have hbotIns :
                Function.update (Function.update U.1 (2, 2024) 6071) (3, 2024) 6072 ∈
                  putnam_2024_a3_partialTableaux 2024 2024 2024 := by
              exact putnam_2024_a3_corner_insert_mem
                (putnam_2024_a3_shape_bot_insert (a := 2024) (b := 2024) (c := 2024) (by norm_num))
                (by simpa using
                  putnam_2024_a3_label_bot_insert (a := 2024) (b := 2024) (c := 2024) (by norm_num))
                (putnam_2024_a3_bot_not_small (a := 2024) (b := 2024) (c := 2024) (by norm_num))
                (by norm_num [putnam_2024_a3_labels])
                (fun {y} hy => putnam_2024_a3_bot_maximal
                  (a := 2024) (b := 2024) (c := 2024)
                  (by norm_num) (by norm_num) (by norm_num) hy)
                (fun {n} hn => putnam_2024_a3_label_bot_lt
                  (a := 2024) (b := 2024) (c := 2024) (by norm_num) hn)
                hmidIns
            have hTab :
                Function.update (Function.update U.1 (2, 2024) 6071) (3, 2024) 6072 ∈
                  putnam_2024_a3_tableaux := by
              simpa [putnam_2024_a3_tableaux_eq_partial] using hbotIns
            refine ⟨hTab, ?_⟩
            have hsecond :
                (Function.update (Function.update U.1 (2, 2024) 6071) (3, 2024) 6072)
                    (2, 2024) = 6071 := by
              rw [Function.update_of_ne (by norm_num : (2, 2024) ≠ (3, 2024)),
                Function.update_self]
            exact putnam_2024_a3_event_of_second_max hTab hsecond⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro T
      apply Subtype.ext
      funext x
      have hTab : T.1 ∈ putnam_2024_a3_tableaux := T.2.1
      have hbot : T.1 (3, 2024) = 6072 :=
        putnam_2024_a3_bottom_right_eq_max hTab
      have hmid : T.1 (2, 2024) = 6071 :=
        (putnam_2024_a3_second_max_event_iff hTab).1 T.2.2
      by_cases hxbot : x = (3, 2024)
      · subst x
        simp [Function.update_self, hbot]
      · by_cases hxmid : x = (2, 2024)
        · subst x
          simp [Function.update_self, Function.update_of_ne, hmid]
        · simp [Function.update_of_ne hxbot, Function.update_of_ne hxmid]
    · intro U
      apply Subtype.ext
      funext x
      have hbotnot : (3, 2024) ∉ putnam_2024_a3_shape 2024 2023 2023 := by
        norm_num [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
      have hmidnot : (2, 2024) ∉ putnam_2024_a3_shape 2024 2023 2023 := by
        norm_num [putnam_2024_a3_shape, putnam_2024_a3_rowLen]
      have hUbot : U.1 (3, 2024) = 0 := U.2.2.2 (3, 2024) hbotnot
      have hUmid : U.1 (2, 2024) = 0 := U.2.2.2 (2, 2024) hmidnot
      by_cases hxbot : x = (3, 2024)
      · subst x
        simp [Function.update_self, Function.update_of_ne, hUbot]
      · by_cases hxmid : x = (2, 2024)
        · subst x
          simp [Function.update_self, Function.update_of_ne, hUmid]
        · simp [Function.update_of_ne hxbot, Function.update_of_ne hxmid]
  rw [hncard]
  exact putnam_2024_a3_partial_ncard_eq_hookCountQ (by norm_num) (by norm_num)

private theorem putnam_2024_a3_event_quotient :
    (({T | T ∈ putnam_2024_a3_tableaux ∧ T (3, 2023) < T (2, 2024)}).ncard /
        putnam_2024_a3_tableaux.ncard : ℚ) = 2025 / 6071 := by
  rw [putnam_2024_a3_event_ncard, putnam_2024_a3_tableaux_ncard]
  exact putnam_2024_a3_hookCountQ_ratio

/--
Let $S$ be the set of bijections $$T : \{1, 2, 3\} \times \{1, 2, ..., 2024\} \to \{1, 2, ..., 6072\}$$
such that $T(1, j) < T(2, j) < T(3, j)$ for all $j \in \{1, 2, ..., 2024\}$ and
$T(i, j) < T(i, j + 1)$ for all $i \in \{1, 2, 3\}$ and $j \in \{1, 2, ..., 2023\}$.
Do there exist $a, c$ in $\{1, 2, 3\}$ and $b$ and $d$ in $\{1, 2, ..., 2024\}$ such that
the fraction of elements $T$ in $S$ for which $T(a, b) < T(c, d)$ is at least $1/3$ and at most $2/3$?
-/
theorem putnam_2024_a3
    (S : Set (ℕ × ℕ → ℕ))
    (hS : S = {T | Set.BijOn T (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024) (Finset.Icc 1 6072) ∧
      (∀ j ∈ Finset.Icc 1 2024, StrictMonoOn (fun i => T (i, j)) (Set.Icc 1 3)) ∧
      (∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024)) ∧
      (∀ x, x ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 → T x = 0)}) :
    (∃ a ∈ Finset.Icc 1 3, ∃ b ∈ Finset.Icc 1 2024, ∃ c ∈ Finset.Icc 1 3, ∃ d ∈ Finset.Icc 1 2024,
      ({T | T ∈ S ∧ T (a, b) < T (c, d)}.ncard  / S.ncard : ℚ) ∈ Set.Icc (1/3) (2/3))
    ↔ putnam_2024_a3_solution :=
  by
  constructor
  · intro _
    trivial
  · intro _
    subst S
    refine ⟨3, by norm_num, 2023, by norm_num, 2, by norm_num, 2024, by norm_num, ?_⟩
    change
      (({T | T ∈ putnam_2024_a3_tableaux ∧ T (3, 2023) < T (2, 2024)}).ncard /
        putnam_2024_a3_tableaux.ncard : ℚ) ∈ Set.Icc (1 / 3) (2 / 3)
    rw [putnam_2024_a3_event_quotient]
    exact putnam_2024_a3_reviewed_rational_bound
