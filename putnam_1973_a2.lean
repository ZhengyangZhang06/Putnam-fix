import Mathlib

open Nat Set MeasureTheory Topology Filter

abbrev putnam_1973_a2_solution : Prop :=
  ∀ (L : List ℝ)
    (hL : L.length = 8 ∧ ∀ i : Fin L.length, List.get L i = 1 ∨ List.get L i = -1)
    (pluses : ℕ)
    (_hpluses : pluses = {i : Fin L.length | List.get L i = 1}.ncard)
    (S : ℕ → ℝ),
    S = (fun n : ℕ ↦ ∑ i ∈ Finset.Icc 1 n,
      List.get L ⟨i % 8, hL.1.symm ▸ Nat.mod_lt i (Nat.succ_pos 7)⟩ / i) →
      (pluses = 4 ↔ ∃ l : ℝ, Tendsto S atTop (𝓝 l))

private lemma putnam_1973_a2_list_length_eq_eight {α : Type*} (L : List α)
    (h : L.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 : α, L = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  cases L with
  | nil => simp at h
  | cons a0 L =>
    cases L with
    | nil => simp at h
    | cons a1 L =>
      cases L with
      | nil => simp at h
      | cons a2 L =>
        cases L with
        | nil => simp at h
        | cons a3 L =>
          cases L with
          | nil => simp at h
          | cons a4 L =>
            cases L with
            | nil => simp at h
            | cons a5 L =>
              cases L with
              | nil => simp at h
              | cons a6 L =>
                cases L with
                | nil => simp at h
                | cons a7 L =>
                  cases L with
                  | nil => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
                  | cons _ _ => simp at h

private def putnam_1973_a2_entry (L : List ℝ) (hLen : L.length = 8) (i : ℕ) : ℝ :=
  L.get ⟨i % 8, by
    rw [hLen]
    exact Nat.mod_lt i (by norm_num : 0 < 8)⟩

private lemma putnam_1973_a2_entry_periodic (L : List ℝ) (hLen : L.length = 8)
    (q r : ℕ) :
    putnam_1973_a2_entry L hLen (8 * q + r) = putnam_1973_a2_entry L hLen r := by
  unfold putnam_1973_a2_entry
  congr 1
  apply Fin.ext
  rw [Nat.add_comm]
  exact Nat.add_mul_mod_self_left r 8 q

private lemma putnam_1973_a2_sum_entries (L : List ℝ)
    (hpm : ∀ i : Fin L.length, L.get i = 1 ∨ L.get i = -1) :
    (∑ i : Fin L.length, L.get i) =
      2 * (({i : Fin L.length | L.get i = 1}.ncard : ℕ) : ℝ) - L.length := by
  classical
  have hcardn :
      {i : Fin L.length | L.get i = 1}.ncard =
        (Finset.univ.filter fun i : Fin L.length => L.get i = 1).card := by
    rw [Set.ncard_eq_toFinset_card]
    simp
  rw [hcardn]
  calc
    (∑ i : Fin L.length, L.get i)
        = ∑ i : Fin L.length, (if L.get i = 1 then 1 else -1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases h1 : L.get i = 1
          · rw [if_pos h1, h1]
          · rcases hpm i with h | h
            · contradiction
            · rw [if_neg h1, h]
    _ = ∑ i : Fin L.length,
          ((if L.get i = 1 then (1 : ℝ) else 0) -
            (if L.get i = 1 then (0 : ℝ) else 1)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases h1 : L.get i = 1
          · rw [if_pos h1, if_pos h1, if_pos h1]
            ring
          · rw [if_neg h1, if_neg h1, if_neg h1]
            ring
    _ = (∑ i : Fin L.length, (if L.get i = 1 then (1 : ℝ) else 0)) -
          ∑ i : Fin L.length, (if L.get i = 1 then (0 : ℝ) else 1) := by
          rw [Finset.sum_sub_distrib]
    _ = (Finset.univ.filter fun i : Fin L.length => L.get i = 1).card -
          (Finset.univ.filter fun i : Fin L.length => ¬ L.get i = 1).card := by
          simp [Finset.sum_ite]
    _ = 2 * (((Finset.univ.filter fun i : Fin L.length => L.get i = 1).card : ℕ) : ℝ) -
          L.length := by
          have hcard := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin L.length))) (p := fun i : Fin L.length => L.get i = 1)
          rw [Finset.card_univ, Fintype.card_fin] at hcard
          have hcardR :
              (((Finset.univ.filter fun i : Fin L.length => L.get i = 1).card : ℕ) : ℝ) +
                (((Finset.univ.filter fun i : Fin L.length => ¬ L.get i = 1).card : ℕ) : ℝ) =
                  (L.length : ℝ) := by
            exact_mod_cast hcard
          nlinarith

private lemma putnam_1973_a2_block_sum_eq_fin_sum (L : List ℝ) (hLen : L.length = 8) :
    (∑ i ∈ Finset.range 8, putnam_1973_a2_entry L hLen (i + 1)) =
      ∑ i : Fin L.length, L.get i := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ :=
    putnam_1973_a2_list_length_eq_eight L hLen
  simp [putnam_1973_a2_entry, Fin.sum_univ_eight, Finset.sum_range_succ, add_comm, add_left_comm]

private lemma putnam_1973_a2_coeff_norm_le_one (L : List ℝ) (hLen : L.length = 8)
    (hpm : ∀ i : Fin L.length, L.get i = 1 ∨ L.get i = -1) :
    ∀ i : ℕ, ‖putnam_1973_a2_entry L hLen (i + 1)‖ ≤ 1 := by
  intro i
  let j : Fin L.length := ⟨(i + 1) % 8, by
    rw [hLen]
    exact Nat.mod_lt (i + 1) (by norm_num : 0 < 8)⟩
  have hv := hpm j
  change ‖L.get j‖ ≤ 1
  rcases hv with hv | hv
  · rw [hv]
    norm_num
  · rw [hv]
    norm_num

private lemma putnam_1973_a2_sum_range_mul_eight_periodic_zero (u : ℕ → ℝ)
    (hper : ∀ q r : ℕ, u (8 * q + r) = u r)
    (hblock : ∑ i ∈ Finset.range 8, u i = 0) :
    ∀ q : ℕ, ∑ i ∈ Finset.range (8 * q), u i = 0 := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 8 * (q + 1) = 8 * q + 8 by ring, Finset.sum_range_add, ih]
      have hshift : (∑ x ∈ Finset.range 8, u (8 * q + x)) = ∑ x ∈ Finset.range 8, u x := by
        apply Finset.sum_congr rfl
        intro x _
        exact hper q x
      rw [hshift, hblock, zero_add]

private lemma putnam_1973_a2_periodic_partial_sum_bound (u : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hper : ∀ q r : ℕ, u (8 * q + r) = u r)
    (hblock : ∑ i ∈ Finset.range 8, u i = 0)
    (hnorm : ∀ i : ℕ, ‖u i‖ ≤ B) :
    ∀ n : ℕ, ‖∑ i ∈ Finset.range n, u i‖ ≤ 8 * B := by
  intro n
  have hdecomp : (∑ i ∈ Finset.range n, u i) = ∑ i ∈ Finset.range (n % 8), u i := by
    conv_lhs => rw [← Nat.div_add_mod n 8]
    rw [Finset.sum_range_add, putnam_1973_a2_sum_range_mul_eight_periodic_zero u hper hblock]
    have hshift :
        (∑ x ∈ Finset.range (n % 8), u (8 * (n / 8) + x)) =
          ∑ x ∈ Finset.range (n % 8), u x := by
      apply Finset.sum_congr rfl
      intro x _
      exact hper (n / 8) x
    rw [hshift, zero_add]
  rw [hdecomp]
  calc
    ‖∑ i ∈ Finset.range (n % 8), u i‖ ≤ ∑ i ∈ Finset.range (n % 8), ‖u i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n % 8), B := by
      apply Finset.sum_le_sum
      intro i _
      exact hnorm i
    _ = ((n % 8 : ℕ) : ℝ) * B := by simp [mul_comm]
    _ ≤ 8 * B := by
      gcongr
      exact_mod_cast (Nat.mod_lt n (by norm_num : 0 < 8)).le

private lemma putnam_1973_a2_antitone_inv_nat_succ :
    Antitone (fun n : ℕ => ((n + 1 : ℝ)⁻¹)) := by
  intro a b hab
  exact (inv_le_inv₀ (a := (b + 1 : ℝ)) (b := (a + 1 : ℝ))
    (by positivity) (by positivity)).2 (by exact_mod_cast Nat.succ_le_succ hab)

private lemma putnam_1973_a2_tendsto_inv_nat_succ_zero :
    Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
  simpa [one_div, Nat.cast_add] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma putnam_1973_a2_periodic_weighted_converges (u : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hper : ∀ q r : ℕ, u (8 * q + r) = u r)
    (hblock : ∑ i ∈ Finset.range 8, u i = 0)
    (hnorm : ∀ i : ℕ, ‖u i‖ ≤ B) :
    ∃ l : ℝ, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * u i) atTop (𝓝 l) := by
  have hbdd : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, u i‖ ≤ 8 * B :=
    putnam_1973_a2_periodic_partial_sum_bound u B hB hper hblock hnorm
  have hc : CauchySeq
      (fun n : ℕ => ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) • u i) :=
    putnam_1973_a2_antitone_inv_nat_succ.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      putnam_1973_a2_tendsto_inv_nat_succ_zero hbdd
  simpa [smul_eq_mul] using (cauchySeq_tendsto_of_complete hc)

private lemma putnam_1973_a2_sum_Icc_one_eq_range (L : List ℝ) (hLen : L.length = 8)
    (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_entry L hLen i / (i : ℝ)) =
      ∑ k ∈ Finset.range n, ((k + 1 : ℝ)⁻¹) * putnam_1973_a2_entry L hLen (k + 1) := by
  let g : ℕ → ℝ := fun i => putnam_1973_a2_entry L hLen i / (i : ℝ)
  have hshift : (∑ i ∈ Finset.Icc 1 n, g i) = ∑ k ∈ Finset.range n, g (k + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := n)]
    rw [← Nat.Ico_zero_eq_range]
    rw [← Finset.sum_Ico_add' (f := g) (a := 0) (b := n) (c := 1)]
  rw [show (∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_entry L hLen i / (i : ℝ)) =
      ∑ i ∈ Finset.Icc 1 n, g i by rfl]
  rw [hshift]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [g]
  rw [div_eq_inv_mul]
  rw [show ((k + 1 : ℕ) : ℝ) = (k + 1 : ℝ) by norm_num]

private lemma putnam_1973_a2_harmonic_range_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹)) = (harmonic n : ℝ) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private lemma putnam_1973_a2_tendsto_harmonic_atTop :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
    convert Real.tendsto_log_atTop.comp hnat using 1
    ext n
    norm_num [Nat.cast_add]
  exact tendsto_atTop_mono (fun n => log_add_one_le_harmonic n) hlog

private lemma putnam_1973_a2_harmonic_const_mul_not_tendsto_nhds {c l : ℝ}
    (hc : c ≠ 0) :
    ¬ Tendsto (fun n : ℕ => c * (harmonic n : ℝ)) atTop (𝓝 l) := by
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hbot : Tendsto (fun n : ℕ => c * (harmonic n : ℝ)) atTop atBot := by
      simpa [mul_comm] using
        (Filter.Tendsto.neg_mul_atTop (C := c) hcneg tendsto_const_nhds
          putnam_1973_a2_tendsto_harmonic_atTop)
    exact not_tendsto_nhds_of_tendsto_atBot hbot l
  · have htop : Tendsto (fun n : ℕ => c * (harmonic n : ℝ)) atTop atTop :=
      Filter.Tendsto.pos_mul_atTop (C := c) hcpos tendsto_const_nhds
        putnam_1973_a2_tendsto_harmonic_atTop
    exact not_tendsto_nhds_of_tendsto_atTop htop l

private lemma putnam_1973_a2_block_sum_eq_zero_of_convergent (L : List ℝ)
    (hLen : L.length = 8)
    (hpm : ∀ i : Fin L.length, L.get i = 1 ∨ L.get i = -1)
    (hconv : ∃ l : ℝ, Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * putnam_1973_a2_entry L hLen (i + 1))
        atTop (𝓝 l)) :
    (∑ i ∈ Finset.range 8, putnam_1973_a2_entry L hLen (i + 1)) = 0 := by
  let a : ℕ → ℝ := fun i => putnam_1973_a2_entry L hLen (i + 1)
  let A : ℝ := ∑ i ∈ Finset.range 8, a i
  let c : ℝ := A / 8
  let v : ℕ → ℝ := fun i => a i - c
  have hper_a : ∀ q r : ℕ, a (8 * q + r) = a r := by
    intro q r
    dsimp [a]
    rw [show 8 * q + r + 1 = 8 * q + (r + 1) by omega]
    exact putnam_1973_a2_entry_periodic L hLen q (r + 1)
  have hper_v : ∀ q r : ℕ, v (8 * q + r) = v r := by
    intro q r
    dsimp [v]
    rw [hper_a q r]
  have hblock_v : ∑ i ∈ Finset.range 8, v i = 0 := by
    dsimp [v, c, A]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  have hnorm_v : ∀ i : ℕ, ‖v i‖ ≤ 1 + |c| := by
    intro i
    dsimp [v]
    calc
      ‖a i - c‖ ≤ ‖a i‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ 1 + |c| := by
        have ha : ‖a i‖ ≤ 1 := by
          simpa [a] using putnam_1973_a2_coeff_norm_le_one L hLen hpm i
        rw [Real.norm_eq_abs (a i)] at ha
        rw [Real.norm_eq_abs (a i), Real.norm_eq_abs c]
        nlinarith [abs_nonneg c]
  obtain ⟨lR, hR⟩ := putnam_1973_a2_periodic_weighted_converges v (1 + |c|)
    (by positivity) hper_v hblock_v hnorm_v
  obtain ⟨lT, hT⟩ := hconv
  have hT' : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * a i) atTop (𝓝 lT) := by
    simpa [a] using hT
  have hscaled : Tendsto (fun n : ℕ => c * (harmonic n : ℝ)) atTop (𝓝 (lT - lR)) := by
    have hdiff := hT'.sub hR
    have hpoint :
        (fun n : ℕ =>
            (∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * a i) -
              ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * v i) =
          fun n : ℕ => c * (harmonic n : ℝ) := by
      ext n
      calc
        (∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * a i) -
            ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * v i
            = ∑ i ∈ Finset.range n,
                (((i + 1 : ℝ)⁻¹) * a i - ((i + 1 : ℝ)⁻¹) * v i) := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * c := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [v]
              ring
        _ = c * ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = c * (harmonic n : ℝ) := by
              rw [putnam_1973_a2_harmonic_range_sum]
    simpa [hpoint] using hdiff
  by_contra hA
  have hc : c ≠ 0 := by
    dsimp [c, A]
    exact div_ne_zero hA (by norm_num)
  exact putnam_1973_a2_harmonic_const_mul_not_tendsto_nhds hc hscaled

private lemma putnam_1973_a2_necessity
    (L : List ℝ)
    (hL : L.length = 8 ∧ ∀ i : Fin L.length, List.get L i = 1 ∨ List.get L i = -1)
    (pluses : ℕ)
    (hpluses : pluses = {i : Fin L.length | List.get L i = 1}.ncard)
    (S : ℕ → ℝ)
    (hS : S = fun n : ℕ ↦ ∑ i ∈ Finset.Icc 1 n,
      List.get L ⟨i % 8, hL.1.symm ▸ Nat.mod_lt i (Nat.succ_pos 7)⟩ / i) :
    (∃ l : ℝ, Tendsto S atTop (𝓝 l)) → pluses = 4 := by
  classical
  intro hconvS
  rcases hL with ⟨hLen, hpm_get⟩
  have hsum_pluses : (∑ i : Fin L.length, List.get L i) = 2 * (pluses : ℝ) - 8 := by
    calc
      (∑ i : Fin L.length, List.get L i)
          = 2 * (({i : Fin L.length | List.get L i = 1}.ncard : ℕ) : ℝ) - L.length :=
            putnam_1973_a2_sum_entries L hpm_get
      _ = 2 * (pluses : ℝ) - 8 := by
            rw [← hpluses, hLen]
            norm_num
  have hSrange :
      S = fun n : ℕ =>
        ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * putnam_1973_a2_entry L hLen (i + 1) := by
    funext n
    rw [hS]
    simpa [putnam_1973_a2_entry] using putnam_1973_a2_sum_Icc_one_eq_range L hLen n
  have hconvRange : ∃ l : ℝ, Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * putnam_1973_a2_entry L hLen (i + 1))
        atTop (𝓝 l) := by
    obtain ⟨l, hl⟩ := hconvS
    exact ⟨l, by simpa [hSrange] using hl⟩
  have hblock0 :=
    putnam_1973_a2_block_sum_eq_zero_of_convergent L hLen hpm_get hconvRange
  have hfin0 : (∑ i : Fin L.length, List.get L i) = 0 := by
    have hgetsum : (∑ i : Fin L.length, List.get L i) = 0 := by
      rw [← putnam_1973_a2_block_sum_eq_fin_sum L hLen]
      exact hblock0
    exact hgetsum
  have hpR : (pluses : ℝ) = 4 := by
    nlinarith [hsum_pluses, hfin0]
  exact_mod_cast hpR

private lemma putnam_1973_a2_sufficiency
    (L : List ℝ)
    (hL : L.length = 8 ∧ ∀ i : Fin L.length, List.get L i = 1 ∨ List.get L i = -1)
    (pluses : ℕ)
    (hpluses : pluses = {i : Fin L.length | List.get L i = 1}.ncard)
    (S : ℕ → ℝ)
    (hS : S = fun n : ℕ ↦ ∑ i ∈ Finset.Icc 1 n,
      List.get L ⟨i % 8, by
        rw [hL.1]
        exact Nat.mod_lt i (by norm_num : 0 < 8)⟩ / i) :
    pluses = 4 → ∃ l : ℝ, Tendsto S atTop (𝓝 l) := by
  classical
  intro hp4
  rcases hL with ⟨hLen, hpm_get⟩
  have hsum_pluses : (∑ i : Fin L.length, List.get L i) = 2 * (pluses : ℝ) - 8 := by
    calc
      (∑ i : Fin L.length, List.get L i)
          = 2 * (({i : Fin L.length | List.get L i = 1}.ncard : ℕ) : ℝ) - L.length :=
            putnam_1973_a2_sum_entries L hpm_get
      _ = 2 * (pluses : ℝ) - 8 := by
            rw [← hpluses, hLen]
            norm_num
  have hSrange :
      S = fun n : ℕ =>
        ∑ i ∈ Finset.range n, ((i + 1 : ℝ)⁻¹) * putnam_1973_a2_entry L hLen (i + 1) := by
    funext n
    rw [hS]
    simpa [putnam_1973_a2_entry] using putnam_1973_a2_sum_Icc_one_eq_range L hLen n
  have hfin0 : (∑ i : Fin L.length, List.get L i) = 0 := by
    rw [hsum_pluses, hp4]
    norm_num
  have hblock :
      (∑ i ∈ Finset.range 8, putnam_1973_a2_entry L hLen (i + 1)) = 0 := by
    rw [putnam_1973_a2_block_sum_eq_fin_sum L hLen]
    simpa using hfin0
  let u : ℕ → ℝ := fun i => putnam_1973_a2_entry L hLen (i + 1)
  have hper : ∀ q r : ℕ, u (8 * q + r) = u r := by
    intro q r
    dsimp [u]
    rw [show 8 * q + r + 1 = 8 * q + (r + 1) by omega]
    exact putnam_1973_a2_entry_periodic L hLen q (r + 1)
  have hnorm : ∀ i : ℕ, ‖u i‖ ≤ 1 := by
    intro i
    simpa [u] using putnam_1973_a2_coeff_norm_le_one L hLen hpm_get i
  obtain ⟨l, hl⟩ := putnam_1973_a2_periodic_weighted_converges u 1
    (by norm_num) hper (by simpa [u] using hblock) hnorm
  refine ⟨l, ?_⟩
  simpa [hSrange, u] using hl

/--
Consider an infinite series whose $n$th term is given by $\pm \frac{1}{n}$, where the actual values of the $\pm$ signs repeat in blocks of $8$ (so the $\frac{1}{9}$ term has the same sign as the $\frac{1}{1}$ term, and so on). Call such a sequence balanced if each block contains four $+$ and four $-$ signs. Prove that being balanced is a sufficient condition for the sequence to converge. Is being balanced also necessary for the sequence to converge?
-/
theorem putnam_1973_a2
(L : List ℝ)
(hL : L.length = 8 ∧ ∀ i : Fin L.length, L[i] = 1 ∨ L[i] = -1)
(pluses : ℕ)
(hpluses : pluses = {i : Fin L.length | L[i] = 1}.ncard)
(S : ℕ → ℝ)
(hS : S = fun n : ℕ ↦ ∑ i ∈ Finset.Icc 1 n, L[i % 8]/i)
: (pluses = 4 → ∃ l : ℝ, Tendsto S atTop (𝓝 l)) ∧ (putnam_1973_a2_solution ↔ ((∃ l : ℝ, Tendsto S atTop (𝓝 l)) → pluses = 4)) :=
by
  constructor
  · exact putnam_1973_a2_sufficiency L hL pluses hpluses S hS
  · constructor
    · intro hsolution hconvS
      exact (hsolution L hL pluses hpluses S hS).2 hconvS
    · intro _ L' hL' pluses' hpluses' S' hS'
      constructor
      · exact putnam_1973_a2_sufficiency L' hL' pluses' hpluses' S' hS'
      · exact putnam_1973_a2_necessity L' hL' pluses' hpluses' S' hS'
