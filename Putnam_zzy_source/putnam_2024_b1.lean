import Mathlib

noncomputable abbrev putnam_2024_b1_solution : Set (ℕ × ℕ) :=
  { p | ∃ m : ℕ, 0 < m ∧ p = (2 * m - 1, m) }

/--
Let $n$ and $k$ be positive integers. The square in the $i$th row and
$j$th column of an $n$-by-$n$ grid contains the number $i + j - k$.
For which $n$ and $k$ is it possible to select $n$ squares from the
grid, no two in the same row or column, such that the numbers
contained in the selected squares are exactly $1, ..., n$?
-/
theorem putnam_2024_b1
    (grid : (n : ℕ) → ℕ → Fin n → Fin n → ℤ)
    (grid_def : ∀ n k i j, grid n k i j = i.succ + j.succ - k)
    (valid : ℕ → ℕ → Prop)
    (valid_def : ∀ n k, valid n k ↔ 0 < n ∧ 0 < k ∧
      ∃ (f : Fin n → Fin n), f.Injective ∧
        Set.range (fun i => grid n k i (f i)) = Set.Icc (1 : ℤ) n) :
    { (n, k) | valid n k } = putnam_2024_b1_solution :=
  by
  have interval_sum :
      ∀ n : ℕ, (∑ z ∈ Finset.Icc (1 : ℤ) (n : ℤ), z) =
        ∑ i : Fin n, ((i : ℤ) + 1) := by
    intro n
    have himage :
        Finset.image (fun i : Fin n => ((i : ℤ) + 1)) Finset.univ =
          Finset.Icc (1 : ℤ) (n : ℤ) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
      constructor
      · rintro ⟨i, rfl⟩
        constructor
        · omega
        · have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
          omega
      · intro hz
        rcases hz with ⟨hz1, hzn⟩
        refine ⟨⟨(z - 1).toNat, ?_⟩, ?_⟩
        · have hnonneg : 0 ≤ z - 1 := by omega
          have hcast : (((z - 1).toNat : ℕ) : ℤ) = z - 1 :=
            Int.toNat_of_nonneg hnonneg
          omega
        · change (((z - 1).toNat : ℤ) + 1 = z)
          have hnonneg : 0 ≤ z - 1 := by omega
          have hcast : (((z - 1).toNat : ℕ) : ℤ) = z - 1 :=
            Int.toNat_of_nonneg hnonneg
          omega
    have hinj :
        Set.InjOn (fun i : Fin n => ((i : ℤ) + 1))
          (Finset.univ : Finset (Fin n)) := by
      intro a ha b hb h
      apply Fin.ext
      have hvalZ : ((a.val : ℤ) + 1 = (b.val : ℤ) + 1) := by
        simpa using h
      have hvalZ' : (a.val : ℤ) = (b.val : ℤ) := by omega
      exact_mod_cast hvalZ'
    have hsum := Finset.sum_image (s := Finset.univ) (f := fun z : ℤ => z) hinj
    simpa [himage] using hsum
  have coord_sum_twice :
      ∀ n : ℕ, (∑ i : Fin n, ((i : ℤ) + 1)) * 2 =
        (n : ℤ) * ((n : ℤ) + 1) := by
    intro n
    have hnat : (∑ i ∈ Finset.range n, (i + 1)) * 2 = n * (n + 1) := by
      have h := Finset.sum_range_id_mul_two (n + 1)
      rw [Finset.sum_range_succ' (fun i : ℕ => i) n] at h
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i : ℤ) + 1)) n]
    exact_mod_cast hnat
  ext p
  rcases p with ⟨n, k⟩
  change valid n k ↔ ∃ m : ℕ, 0 < m ∧ (n, k) = (2 * m - 1, m)
  constructor
  · intro hvalid
    rw [valid_def] at hvalid
    rcases hvalid with ⟨hnpos, hkpos, f, hf, hrange⟩
    let g : Fin n → ℤ := fun i => grid n k i (f i)
    have himage : Finset.image g Finset.univ = Finset.Icc (1 : ℤ) (n : ℤ) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
      have hz : (∃ x, g x = z) ↔ z ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
        rw [← hrange]
        rfl
      simpa [g, Set.mem_Icc] using hz
    have hcard :
        (Finset.image g Finset.univ).card = (Finset.univ : Finset (Fin n)).card := by
      rw [himage]
      simp [Int.card_Icc]
    have hg_injOn : Set.InjOn g (Finset.univ : Finset (Fin n)) :=
      (Finset.card_image_iff.mp hcard)
    have hsum_range :
        (∑ i : Fin n, g i) = ∑ z ∈ Finset.Icc (1 : ℤ) (n : ℤ), z := by
      have hsum := Finset.sum_image (s := Finset.univ) (f := fun z : ℤ => z) hg_injOn
      simpa [himage] using hsum.symm
    have hgrid_sum :
        (∑ i : Fin n, g i) =
          2 * (∑ i : Fin n, ((i : ℤ) + 1)) - (n : ℤ) * (k : ℤ) := by
      have hsurj : Function.Surjective f := (Finite.injective_iff_surjective).mp hf
      have hsum_f : (∑ i : Fin n, ((f i : ℤ) + 1)) =
          ∑ i : Fin n, ((i : ℤ) + 1) := by
        exact Fintype.sum_bijective f ⟨hf, hsurj⟩
          (fun i : Fin n => ((f i : ℤ) + 1))
          (fun i : Fin n => ((i : ℤ) + 1))
          (fun i => rfl)
      calc
        (∑ i : Fin n, g i)
            = ∑ i : Fin n, (((i : ℤ) + 1) + ((f i : ℤ) + 1) - (k : ℤ)) := by
                simp [g, grid_def, Fin.val_succ]
        _ = (∑ i : Fin n, ((i : ℤ) + 1)) +
              (∑ i : Fin n, ((f i : ℤ) + 1)) -
              (∑ i : Fin n, (k : ℤ)) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        _ = 2 * (∑ i : Fin n, ((i : ℤ) + 1)) - (n : ℤ) * (k : ℤ) := by
                simp [hsum_f, Finset.sum_const, two_mul]
    have hselected_sum :
        (∑ i : Fin n, g i) = ∑ i : Fin n, ((i : ℤ) + 1) :=
      hsum_range.trans (interval_sum n)
    rw [hgrid_sum] at hselected_sum
    have hk_int : (2 : ℤ) * (k : ℤ) = (n : ℤ) + 1 := by
      have hS : (∑ i : Fin n, ((i : ℤ) + 1)) = (n : ℤ) * (k : ℤ) := by
        linarith
      have hmul :
          (n : ℤ) * ((2 : ℤ) * (k : ℤ)) = (n : ℤ) * ((n : ℤ) + 1) := by
        nlinarith [coord_sum_twice n]
      have hnz : (n : ℤ) ≠ 0 := by omega
      exact mul_left_cancel₀ hnz hmul
    have hk_nat : 2 * k = n + 1 := by omega
    exact ⟨k, hkpos, by ext <;> omega⟩
  · intro hsol
    rcases hsol with ⟨k0, hk0pos, hp⟩
    have hparam : ∃ m, n = 2 * m + 1 ∧ k = m + 1 := by
      refine ⟨k0 - 1, ?_, ?_⟩
      · have hn : n = 2 * k0 - 1 := congrArg Prod.fst hp
        omega
      · have hk : k = k0 := congrArg Prod.snd hp
        omega
    rcases hparam with ⟨m, hn, hk⟩
    subst n
    rw [hk, valid_def]
    refine ⟨by omega, by omega, ?_⟩
    let f : Fin (2 * m + 1) → Fin (2 * m + 1) :=
      fun i => i + (⟨m, by omega⟩ : Fin (2 * m + 1))
    refine ⟨f, ?_, ?_⟩
    · intro a b h
      dsimp [f] at h
      exact add_right_cancel h
    · let g : Fin (2 * m + 1) → ℤ := fun i => grid (2 * m + 1) (m + 1) i (f i)
      have hval : ∀ i : Fin (2 * m + 1),
          g i = if i.val ≤ m then (2 * i.val + 1 : ℤ) else (2 * (i.val - m) : ℤ) := by
        intro i
        by_cases hi : i.val ≤ m
        · simp [g, f, grid_def, Fin.val_add_eq_ite, hi, Fin.val_succ]
          omega
        · have hle : 2 * m + 1 ≤ i.val + m := by omega
          simp [g, f, grid_def, Fin.val_add_eq_ite, hle, hi, Fin.val_succ]
          omega
      have hg_mem :
          ∀ i, g i ∈ Set.Icc (1 : ℤ) (((2 * m + 1 : ℕ) : ℤ)) := by
        intro i
        rw [hval i]
        by_cases hi : i.val ≤ m
        · simp only [hi, if_true, Set.mem_Icc]
          constructor <;> omega
        · simp only [hi, if_false, Set.mem_Icc]
          constructor <;> omega
      have hg_inj : Function.Injective g := by
        intro a b hab
        have ha_lt : a.val < 2 * m + 1 := a.isLt
        have hb_lt : b.val < 2 * m + 1 := b.isLt
        rw [hval a, hval b] at hab
        by_cases ha : a.val ≤ m <;> by_cases hb : b.val ≤ m
        · simp only [ha, hb, if_true] at hab
          apply Fin.ext
          omega
        · simp only [ha, hb, if_true, if_false] at hab
          omega
        · simp only [ha, hb, if_false, if_true] at hab
          omega
        · simp only [ha, hb, if_false] at hab
          apply Fin.ext
          omega
      have hsubset :
          Finset.image g Finset.univ ⊆
            Finset.Icc (1 : ℤ) (((2 * m + 1 : ℕ) : ℤ)) := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
        simpa [Finset.mem_Icc, Set.mem_Icc] using hg_mem i
      have hcard :
          (Finset.Icc (1 : ℤ) (((2 * m + 1 : ℕ) : ℤ))).card ≤
            (Finset.image g Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hg_inj]
        simp [Int.card_Icc]
      have himage :
          Finset.image g Finset.univ =
            Finset.Icc (1 : ℤ) (((2 * m + 1 : ℕ) : ℤ)) :=
        Finset.eq_of_subset_of_card_le hsubset hcard
      have hrange : Set.range g = Set.Icc (1 : ℤ) (((2 * m + 1 : ℕ) : ℤ)) := by
        ext z
        have hz := congrArg (fun s : Finset ℤ => z ∈ s) himage
        simpa [Finset.mem_image, Set.mem_range, Finset.mem_Icc, Set.mem_Icc] using hz
      simpa [g] using hrange
