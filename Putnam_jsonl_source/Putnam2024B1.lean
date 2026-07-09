import Mathlib

--{(2*l+1, l+1) | (l : ℕ)}
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
    { (n, k) | valid n k } = (({(2*l+1, l+1) | (l : ℕ)}) : Set (ℕ × ℕ) ) := by
  classical
  ext x
  rcases x with ⟨n, k⟩
  constructor
  · intro hx
    have hx_valid : valid n k := by
      simpa using hx
    rw [valid_def] at hx_valid
    rcases hx_valid with ⟨hn, hk, f, hfinj, hrange⟩
    let S : ℤ := ∑ i : Fin n, ((((i : ℕ) + 1 : ℕ) : ℤ))
    have hcardIcc : Fintype.card (Set.Icc (1 : ℤ) (n : ℤ)) = n := by
      rw [Fintype.card_Icc]
      have h : ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℤ) = (n : ℤ) := by
        rw [Int.card_Icc_of_le]
        · ring
        · omega
      exact Int.ofNat.inj h
    let gToIcc : Fin n → Set.Icc (1 : ℤ) (n : ℤ) := fun i =>
      ⟨grid n k i (f i), by
        rw [← hrange]
        exact Set.mem_range_self i⟩
    have hg_surj : Function.Surjective gToIcc := by
      intro y
      have hyRange : y.1 ∈ Set.range (fun i => grid n k i (f i)) := by
        rw [hrange]
        exact y.2
      rcases hyRange with ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
    have hg_bij : Function.Bijective gToIcc := by
      refine (Fintype.bijective_iff_surjective_and_card gToIcc).mpr ⟨hg_surj, ?_⟩
      rw [Fintype.card_fin, hcardIcc]
    let cToIcc : Fin n → Set.Icc (1 : ℤ) (n : ℤ) := fun i =>
      ⟨((((i : ℕ) + 1 : ℕ) : ℤ)), by
        constructor
        · exact_mod_cast (Nat.succ_pos (i : ℕ))
        · exact_mod_cast (Nat.succ_le_of_lt i.isLt)⟩
    have hc_inj : Function.Injective cToIcc := by
      intro a b h
      apply Fin.ext
      have hval : ((((a : ℕ) + 1 : ℕ) : ℤ) = (((b : ℕ) + 1 : ℕ) : ℤ)) := by
        exact congrArg Subtype.val h
      have hnat : (a : ℕ) + 1 = (b : ℕ) + 1 := Int.ofNat.inj hval
      omega
    have hc_bij : Function.Bijective cToIcc := by
      refine (Fintype.bijective_iff_injective_and_card cToIcc).mpr ⟨hc_inj, ?_⟩
      rw [Fintype.card_fin, hcardIcc]
    have hsum_range : (∑ i : Fin n, grid n k i (f i)) = S := by
      calc
        (∑ i : Fin n, grid n k i (f i))
            = ∑ i : Fin n, ((gToIcc i : Set.Icc (1 : ℤ) (n : ℤ)) : ℤ) := rfl
        _ = ∑ y : Set.Icc (1 : ℤ) (n : ℤ),
              ((y : Set.Icc (1 : ℤ) (n : ℤ)) : ℤ) :=
            hg_bij.sum_comp fun y : Set.Icc (1 : ℤ) (n : ℤ) =>
              ((y : Set.Icc (1 : ℤ) (n : ℤ)) : ℤ)
        _ = ∑ i : Fin n, ((cToIcc i : Set.Icc (1 : ℤ) (n : ℤ)) : ℤ) :=
            (hc_bij.sum_comp fun y : Set.Icc (1 : ℤ) (n : ℤ) =>
              ((y : Set.Icc (1 : ℤ) (n : ℤ)) : ℤ)).symm
        _ = S := rfl
    have hf_bij : Function.Bijective f := by
      refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, ?_⟩
      rfl
    have hsum_f_val :
        (∑ i : Fin n, (((f i : Fin n) : ℕ) : ℤ)) =
          ∑ i : Fin n, (((i : ℕ) : ℤ)) := by
      simpa using (hf_bij.sum_comp fun j : Fin n => (((j : ℕ) : ℤ)))
    have hsum_grid_formula :
        (∑ i : Fin n, grid n k i (f i)) = S + S - (n : ℤ) * (k : ℤ) := by
      dsimp [S]
      simp_rw [grid_def]
      simp [Fin.val_succ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum_f_val]
    have hS_twice : S * 2 = (n : ℤ) * (((n + 1 : ℕ) : ℤ)) := by
      dsimp [S]
      have hnat : ((∑ i : Fin n, ((i : ℕ) + 1)) * 2 = n * (n + 1)) := by
        rw [Fin.sum_univ_eq_sum_range (fun j => j + 1) n]
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul, mul_one]
        calc
          ((∑ x ∈ Finset.range n, x) + n) * 2
              = (∑ x ∈ Finset.range n, x) * 2 + n * 2 := by ring
          _ = n * (n - 1) + n * 2 := by rw [Finset.sum_range_id_mul_two]
          _ = n * (n + 1) := by
            cases n with
            | zero => norm_num
            | succ m =>
                simp only [Nat.succ_sub_one]
                ring
      exact_mod_cast hnat
    have hk_eq : 2 * k = n + 1 := by
      have hmain : (n : ℤ) * (k : ℤ) * 2 = (n : ℤ) * (((n + 1 : ℕ) : ℤ)) := by
        nlinarith [hsum_range, hsum_grid_formula, hS_twice]
      have hnz : (n : ℤ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hn)
      have hcancel : (k : ℤ) * 2 = (((n + 1 : ℕ) : ℤ)) := by
        exact mul_left_cancel₀ hnz (by simpa [mul_assoc] using hmain)
      have hcancel' : ((2 * k : ℕ) : ℤ) = (((n + 1 : ℕ) : ℤ)) := by
        rw [Nat.cast_mul]
        norm_num
        simpa [mul_comm] using hcancel
      exact Int.ofNat.inj hcancel'
    have hodd : ∃ l, n = 2 * l + 1 ∧ k = l + 1 := by
      refine ⟨k - 1, ?_, ?_⟩ <;> omega
    rcases hodd with ⟨l, hn_eq, hk_eq'⟩
    exact ⟨l, by ext <;> simp [hn_eq, hk_eq']⟩
  · intro hx
    rcases hx with ⟨l, hpair⟩
    have hn_eq : n = 2 * l + 1 := by
      simpa using congrArg Prod.fst hpair.symm
    have hk_eq : k = l + 1 := by
      simpa using congrArg Prod.snd hpair.symm
    subst n
    subst k
    let n' := 2 * l + 1
    change valid n' (l + 1)
    let f : Fin n' → Fin n' := fun i =>
      if h : (i : ℕ) ≤ l then
        ⟨(i : ℕ) + l, by omega⟩
      else
        ⟨(i : ℕ) - (l + 1), by omega⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      by_cases ha : (a : ℕ) ≤ l
      · by_cases hb : (b : ℕ) ≤ l
        · apply Fin.ext
          have hv : (a : ℕ) + l = (b : ℕ) + l := by
            have := congrArg Fin.val hab
            simpa [f, ha, hb] using this
          omega
        · apply Fin.ext
          have hv : (a : ℕ) + l = (b : ℕ) - (l + 1) := by
            have := congrArg Fin.val hab
            simpa [f, ha, hb] using this
          omega
      · by_cases hb : (b : ℕ) ≤ l
        · apply Fin.ext
          have hv : (a : ℕ) - (l + 1) = (b : ℕ) + l := by
            have := congrArg Fin.val hab
            simpa [f, ha, hb] using this
          omega
        · apply Fin.ext
          have hv : (a : ℕ) - (l + 1) = (b : ℕ) - (l + 1) := by
            have := congrArg Fin.val hab
            simpa [f, ha, hb] using this
          omega
    have hgrid_le (i : Fin n') (hi : (i : ℕ) ≤ l) :
        grid n' (l + 1) i (f i) = (2 * (i : ℕ) + 1 : ℤ) := by
      rw [grid_def]
      simp [f, hi, Fin.val_succ]
      omega
    have hgrid_gt (i : Fin n') (hi : ¬ (i : ℕ) ≤ l) :
        grid n' (l + 1) i (f i) = (2 * ((i : ℕ) - (l + 1) + 1) : ℤ) := by
      rw [grid_def]
      simp [f, hi, Fin.val_succ]
      omega
    let gToIcc : Fin n' → Set.Icc (1 : ℤ) (n' : ℤ) := fun i =>
      ⟨grid n' (l + 1) i (f i), by
        by_cases hi : (i : ℕ) ≤ l
        · rw [hgrid_le i hi]
          constructor <;> omega
        · rw [hgrid_gt i hi]
          constructor <;> omega⟩
    have hg_inj : Function.Injective gToIcc := by
      intro a b hab
      apply Fin.ext
      have hval : grid n' (l + 1) a (f a) = grid n' (l + 1) b (f b) :=
        congrArg Subtype.val hab
      by_cases ha : (a : ℕ) ≤ l
      · by_cases hb : (b : ℕ) ≤ l
        · rw [hgrid_le a ha, hgrid_le b hb] at hval
          omega
        · rw [hgrid_le a ha, hgrid_gt b hb] at hval
          omega
      · by_cases hb : (b : ℕ) ≤ l
        · rw [hgrid_gt a ha, hgrid_le b hb] at hval
          omega
        · rw [hgrid_gt a ha, hgrid_gt b hb] at hval
          omega
    have hcardIcc : Fintype.card (Set.Icc (1 : ℤ) (n' : ℤ)) = n' := by
      rw [Fintype.card_Icc]
      have h : ((Finset.Icc (1 : ℤ) (n' : ℤ)).card : ℤ) = (n' : ℤ) := by
        rw [Int.card_Icc_of_le]
        · ring
        · omega
      exact Int.ofNat.inj h
    have hg_bij : Function.Bijective gToIcc := by
      refine (Fintype.bijective_iff_injective_and_card gToIcc).mpr ⟨hg_inj, ?_⟩
      rw [Fintype.card_fin, hcardIcc]
    have hrange :
        Set.range (fun i : Fin n' => grid n' (l + 1) i (f i)) =
          Set.Icc (1 : ℤ) (n' : ℤ) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact (gToIcc i).2
      · intro hz
        rcases hg_bij.2 ⟨z, hz⟩ with ⟨i, hi⟩
        exact ⟨i, congrArg Subtype.val hi⟩
    rw [valid_def]
    refine ⟨by omega, by omega, f, hf_inj, ?_⟩
    simpa [n'] using hrange
