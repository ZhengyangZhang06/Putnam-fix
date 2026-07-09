import Mathlib

open Polynomial Filter Topology

private abbrev putnamModSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, ((2 * n) / k) % 2

private abbrev putnamLower (J n : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 J, ((2 * n) / (2 * j + 1) - n / (j + 1))

private noncomputable abbrev putnamPartial (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J, ((2 : ℝ) / (2 * j + 1) - (1 : ℝ) / (j + 1))

private lemma sum_int_Icc_eq_sum_nat_Icc {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℤ → M) :
    (∑ z ∈ Finset.Icc (1 : ℤ) (n : ℤ), F z) =
      ∑ k ∈ Finset.Icc 1 n, F (k : ℤ) := by
  refine Finset.sum_bij (fun z _ => z.toNat) ?_ ?_ ?_ ?_
  · intro z hzmem
    rw [Finset.mem_Icc] at hzmem ⊢
    have hz0 : 0 ≤ z := by omega
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    constructor
    · have : (1 : ℤ) ≤ (z.toNat : ℤ) := by
        rw [hzcast]
        exact hzmem.1
      exact_mod_cast this
    · have : (z.toNat : ℤ) ≤ (n : ℤ) := by
        rw [hzcast]
        exact hzmem.2
      exact_mod_cast this
  · intro a hamem b hbmem h
    rw [Finset.mem_Icc] at hamem hbmem
    have ha0 : 0 ≤ a := by omega
    have hb0 : 0 ≤ b := by omega
    rw [← Int.toNat_of_nonneg ha0, ← Int.toNat_of_nonneg hb0]
    exact congrArg Int.ofNat h
  · intro k hkmem
    refine ⟨(k : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc] at hkmem ⊢
      constructor
      · exact_mod_cast hkmem.1
      · exact_mod_cast hkmem.2
    · simp
  · intro z hzmem
    congr 1
    rw [Finset.mem_Icc] at hzmem
    exact (Int.toNat_of_nonneg (by omega : 0 ≤ z)).symm

private lemma nat_two_mul_div_div_two (n k : ℕ) : (2 * n / k) / 2 = n / k := by
  rw [Nat.div_div_eq_div_mul]
  rw [show k * 2 = 2 * k by omega]
  rw [Nat.mul_div_mul_left n k (by norm_num : 0 < 2)]

private lemma nat_floor_diff_eq_mod_two (n k : ℕ) :
    ((2 * n / k : ℕ) : ℤ) - 2 * ((n / k : ℕ) : ℤ) =
      ((2 * n / k) % 2 : ℕ) := by
  have hdiv : (2 * n / k) / 2 = n / k := nat_two_mul_div_div_two n k
  have h := Nat.div_add_mod (2 * n / k) 2
  omega

private lemma original_sum_eq_mod_sum (n : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n,
      (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) =
    ∑ k ∈ Finset.Icc 1 n, ((((2 * n) / k) % 2 : ℕ) : ℤ) := by
  rw [sum_int_Icc_eq_sum_nat_Icc n (fun k : ℤ =>
      (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k)))]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  change ((2 * n / k : ℕ) : ℤ) - 2 * ((n / k : ℕ) : ℤ) =
    (((2 * n / k) % 2 : ℕ) : ℤ)
  exact nat_floor_diff_eq_mod_two n k

private lemma card_filter_div_eq (N m : ℕ) (hm : 0 < m) :
    ((Finset.Icc 1 N).filter (fun k => N / k = m)).card = N / m - N / (m + 1) := by
  have hset : (Finset.Icc 1 N).filter (fun k => N / k = m) =
      Finset.Icc (N / (m + 1) + 1) (N / m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, _hkN⟩, hdiv⟩
      constructor
      · rw [Nat.succ_le_iff]
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos m)]
        have hkpos : 0 < k := hk1
        have hlt : N / k < m + 1 := by
          rw [hdiv]
          exact Nat.lt_succ_self m
        have hNlt : N < (m + 1) * k := (Nat.div_lt_iff_lt_mul hkpos).mp hlt
        simpa [mul_comm] using hNlt
      · rw [Nat.le_div_iff_mul_le hm]
        have hle : m * k ≤ N := (Nat.div_eq_iff hk1).mp hdiv |>.1
        simpa [mul_comm] using hle
    · rintro ⟨hlow, hup⟩
      have hlt1 : N / (m + 1) < k := Nat.succ_le_iff.mp hlow
      have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hlt1
      have hk1 : 1 ≤ k := hkpos
      refine ⟨⟨hk1, ?_⟩, ?_⟩
      · exact le_trans hup (Nat.div_le_self N m)
      · apply Nat.div_eq_of_lt_le
        · have hle : k * m ≤ N := (Nat.le_div_iff_mul_le hm).mp hup
          simpa [mul_comm] using hle
        · have hlt2 : N < k * (m + 1) :=
            (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp hlt1
          simpa [mul_comm] using hlt2
  rw [hset, Nat.card_Icc]
  omega

private lemma card_filter_two_mul_div_eq (n m : ℕ) (hm : 2 ≤ m) :
    ((Finset.Icc 1 n).filter (fun k => (2 * n) / k = m)).card =
      (2 * n) / m - (2 * n) / (m + 1) := by
  have hset : (Finset.Icc 1 n).filter (fun k => (2 * n) / k = m) =
      (Finset.Icc 1 (2 * n)).filter (fun k => (2 * n) / k = m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, hdiv⟩
      exact ⟨⟨hk1, le_trans hkn (by omega : n ≤ 2 * n)⟩, hdiv⟩
    · rintro ⟨⟨hk1, _hk2n⟩, hdiv⟩
      have hmpos : 0 < m := lt_of_lt_of_le (by norm_num : 0 < 2) hm
      have hk_le_div : k ≤ (2 * n) / m := by
        rw [Nat.le_div_iff_mul_le hmpos]
        have hle : m * k ≤ 2 * n := (Nat.div_eq_iff hk1).mp hdiv |>.1
        simpa [mul_comm] using hle
      have hdiv_le : (2 * n) / m ≤ n := by
        apply Nat.div_le_of_le_mul
        exact Nat.mul_le_mul_right n hm
      exact ⟨⟨hk1, le_trans hk_le_div hdiv_le⟩, hdiv⟩
  rw [hset]
  exact card_filter_div_eq (2 * n) m (lt_of_lt_of_le (by norm_num : 0 < 2) hm)

private lemma card_odd_fiber (n j : ℕ) (hj : 1 ≤ j) :
    ((Finset.Icc 1 n).filter (fun k => (2 * n) / k = 2 * j + 1)).card =
      (2 * n) / (2 * j + 1) - n / (j + 1) := by
  rw [card_filter_two_mul_div_eq n (2 * j + 1) (by omega)]
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
  rw [Nat.mul_div_mul_left n (j + 1) (by norm_num : 0 < 2)]

private lemma lower_eq_card_filter (J n : ℕ) :
    putnamLower J n =
      ((Finset.Icc 1 n).filter
        (fun k => (2 * n) / k ∈ (Finset.Icc 1 J).image (fun j => 2 * j + 1))).card := by
  calc
    putnamLower J n
        = ∑ j ∈ Finset.Icc 1 J,
            ((Finset.Icc 1 n).filter (fun k => (2 * n) / k = 2 * j + 1)).card := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [card_odd_fiber n j]
          exact (Finset.mem_Icc.mp hj).1
    _ = ∑ q ∈ (Finset.Icc 1 J).image (fun j => 2 * j + 1),
            ((Finset.Icc 1 n).filter (fun k => (2 * n) / k = q)).card := by
          rw [Finset.sum_image]
          intro a _ha b _hb h
          have h2 : 2 * a = 2 * b := Nat.succ.inj h
          exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
    _ = ((Finset.Icc 1 n).filter
            (fun k => (2 * n) / k ∈ (Finset.Icc 1 J).image (fun j => 2 * j + 1))).card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter]

private lemma lower_le_mod_sum (J n : ℕ) :
    putnamLower J n ≤ putnamModSum n := by
  rw [putnamModSum, lower_eq_card_filter]
  rw [Finset.card_filter]
  refine Finset.sum_le_sum ?_
  intro k _hk
  by_cases hmem : (2 * n) / k ∈ (Finset.Icc 1 J).image (fun j => 2 * j + 1)
  · simp [hmem]
    rcases Finset.mem_image.mp hmem with ⟨j, _hj, hjq⟩
    omega
  · simp [hmem]

private lemma odd_small_mem_image {J q : ℕ} (hq2 : 2 ≤ q) (hqodd : q % 2 = 1)
    (hqle : q ≤ 2 * J + 1) :
    q ∈ (Finset.Icc 1 J).image (fun j => 2 * j + 1) := by
  refine Finset.mem_image.mpr ⟨q / 2, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    have h := Nat.div_add_mod q 2
    constructor <;> omega
  · have h := Nat.div_add_mod q 2
    omega

private lemma two_le_two_mul_div {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    2 ≤ (2 * n) / k := by
  rw [Nat.le_div_iff_mul_le hk1]
  nlinarith [Nat.mul_le_mul_left 2 hkn]

private lemma mod_sum_le_lower_add_tail (J n : ℕ) :
    putnamModSum n ≤ putnamLower J n + (2 * n) / (2 * J + 2) := by
  let img := (Finset.Icc 1 J).image (fun j => 2 * j + 1)
  let tail := (Finset.Icc 1 n).filter (fun k => 2 * J + 2 ≤ (2 * n) / k)
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
      ((2 * n) / k) % 2 ≤
        (if (2 * n) / k ∈ img then 1 else 0) +
          (if 2 * J + 2 ≤ (2 * n) / k then 1 else 0) := by
    rw [Finset.mem_Icc] at hk
    set q := (2 * n) / k
    rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
    · simp [hq0]
    · by_cases hmem : q ∈ img
      · simp [hq1, hmem]
      · have htail : 2 * J + 2 ≤ q := by
          by_contra hnot
          have hqle : q ≤ 2 * J + 1 := by omega
          have hq2 : 2 ≤ q := by
            dsimp [q]
            exact two_le_two_mul_div hk.1 hk.2
          exact hmem (odd_small_mem_image hq2 hq1 hqle)
        simp [hq1, hmem, htail]
  calc
    putnamModSum n
        ≤ ∑ k ∈ Finset.Icc 1 n,
            ((if (2 * n) / k ∈ img then 1 else 0) +
              (if 2 * J + 2 ≤ (2 * n) / k then 1 else 0)) := by
          exact Finset.sum_le_sum hpoint
    _ = (∑ k ∈ Finset.Icc 1 n, if (2 * n) / k ∈ img then 1 else 0) +
          ∑ k ∈ Finset.Icc 1 n, if 2 * J + 2 ≤ (2 * n) / k then 1 else 0 := by
          rw [Finset.sum_add_distrib]
    _ = ((Finset.Icc 1 n).filter (fun k => (2 * n) / k ∈ img)).card + tail.card := by
          rw [← Finset.card_filter, ← Finset.card_filter]
    _ = putnamLower J n + tail.card := by
          rw [lower_eq_card_filter]
    _ ≤ putnamLower J n + (2 * n) / (2 * J + 2) := by
          gcongr
          have hsubset : tail ⊆ Finset.Icc 1 ((2 * n) / (2 * J + 2)) := by
            intro k hk
            simp only [tail, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
            have hkpos : 0 < k := hk.1.1
            have hMpos : 0 < 2 * J + 2 := by omega
            have hMk : (2 * J + 2) * k ≤ 2 * n :=
              (Nat.le_div_iff_mul_le hkpos).mp hk.2
            constructor
            · exact hk.1.1
            · rw [Nat.le_div_iff_mul_le hMpos]
              simpa [mul_comm] using hMk
          have hcard := Finset.card_le_card hsubset
          simpa [tail, Nat.card_Icc] using hcard

private lemma nat_floor_const_div_mul (c m n : ℕ) (hm : 0 < m) :
    ⌊((c : ℝ) / (m : ℝ)) * (n : ℝ)⌋₊ = (c * n) / m := by
  rw [show ((c : ℝ) / (m : ℝ)) * (n : ℝ) = ((c * n : ℕ) : ℝ) / (m : ℝ) by
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hm)]
    norm_num [mul_comm, mul_left_comm, mul_assoc]]
  rw [Nat.floor_div_natCast]
  rw [Nat.floor_natCast]

private lemma tendsto_nat_const_mul_div (c m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => (((c * n) / m : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 ((c : ℝ) / m)) := by
  have hbase := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (c : ℝ) / m)
    (by positivity)).comp tendsto_natCast_atTop_atTop
  refine hbase.congr' ?_
  filter_upwards with n
  change ((⌊((c : ℝ) / (m : ℝ)) * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) =
    (((c * n) / m : ℕ) : ℝ) / (n : ℝ)
  rw [nat_floor_const_div_mul c m n hm]

private lemma div_le_odd (n j : ℕ) : n / (j + 1) ≤ (2 * n) / (2 * j + 1) := by
  rw [← Nat.mul_div_mul_left n (j + 1) (by norm_num : 0 < 2)]
  apply Nat.div_le_div_left
  · omega
  · omega

private lemma tendsto_lower_fixed (J : ℕ) :
    Tendsto (fun n : ℕ => ((putnamLower J n : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 (putnamPartial J)) := by
  rw [show (fun n : ℕ => ((putnamLower J n : ℕ) : ℝ) / (n : ℝ)) =
      (fun n : ℕ => ∑ j ∈ Finset.Icc 1 J,
        ((((2 * n) / (2 * j + 1) - n / (j + 1) : ℕ) : ℝ) / (n : ℝ))) by
    funext n
    rw [putnamLower, Nat.cast_sum, Finset.sum_div]]
  refine tendsto_finset_sum (Finset.Icc 1 J) ?_
  intro j _hj
  have h2 : Tendsto (fun n : ℕ => (((2 * n) / (2 * j + 1) : ℕ) : ℝ) /
      (n : ℝ)) atTop (𝓝 ((2 : ℝ) / (2 * j + 1))) := by
    simpa using tendsto_nat_const_mul_div 2 (2 * j + 1) (by omega)
  have h1 : Tendsto (fun n : ℕ => ((n / (j + 1) : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 ((1 : ℝ) / (j + 1))) := by
    simpa using tendsto_nat_const_mul_div 1 (j + 1) (by omega)
  have hsub := h2.sub h1
  refine hsub.congr' ?_
  filter_upwards with n
  rw [Nat.cast_sub (div_le_odd n j)]
  rw [sub_div]

private lemma partial_sum_eq_harmonic (J : ℕ) :
    putnamPartial J =
      2 * (harmonic (2 * J + 1) : ℝ) - (harmonic J : ℝ) -
        (harmonic (J + 1) : ℝ) - 1 := by
  induction J with
  | zero =>
      simp [putnamPartial, harmonic_zero, harmonic_succ]
      ring
  | succ J ih =>
      rw [putnamPartial, Finset.sum_Icc_succ_top]
      · rw [show (∑ j ∈ Finset.Icc 1 J,
              ((2 : ℝ) / (2 * j + 1) - (1 : ℝ) / (j + 1))) = putnamPartial J by
            rfl]
        rw [ih]
        rw [show 2 * (J + 1) + 1 = (2 * J + 1) + 2 by omega]
        rw [show J + 1 + 1 = J + 2 by omega]
        rw [show harmonic ((2 * J + 1) + 2) =
            harmonic (2 * J + 1) + ((2 * J + 2 : ℕ) : ℚ)⁻¹ +
              ((2 * J + 3 : ℕ) : ℚ)⁻¹ by
          rw [show (2 * J + 1) + 2 = (2 * J + 2) + 1 by omega]
          rw [harmonic_succ]
          rw [show 2 * J + 2 = (2 * J + 1) + 1 by omega]
          rw [harmonic_succ]]
        rw [show harmonic (J + 2) = harmonic (J + 1) + ((J + 2 : ℕ) : ℚ)⁻¹ by
          rw [show J + 2 = (J + 1) + 1 by omega]
          rw [harmonic_succ]]
        norm_num [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
        field_simp
        ring
      · omega

private lemma tendsto_ratio_one :
    Tendsto (fun J : ℕ => (2 * (J : ℝ) + 1) / (J : ℝ)) atTop (𝓝 (2 : ℝ)) := by
  have hbase : Tendsto (fun J : ℕ => (2 : ℝ) + (1 : ℝ) / (J : ℝ)) atTop
      (𝓝 (2 + 0 : ℝ)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1)
  have hbase' : Tendsto (fun J : ℕ => (2 : ℝ) + (1 : ℝ) / (J : ℝ)) atTop
      (𝓝 (2 : ℝ)) := by
    simpa using hbase
  refine hbase'.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with J hJ
  field_simp [Nat.cast_ne_zero.mpr hJ]

private lemma tendsto_ratio_two :
    Tendsto (fun J : ℕ => (2 * (J : ℝ) + 1) / ((J : ℝ) + 1)) atTop
      (𝓝 (2 : ℝ)) := by
  have hbase : Tendsto (fun J : ℕ => (2 : ℝ) - (1 : ℝ) / ((J : ℝ) + 1)) atTop
      (𝓝 (2 - 0 : ℝ)) := by
    exact tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbase' : Tendsto (fun J : ℕ => (2 : ℝ) - (1 : ℝ) / ((J : ℝ) + 1)) atTop
      (𝓝 (2 : ℝ)) := by
    simpa using hbase
  refine hbase'.congr' ?_
  filter_upwards with J
  have hden : (J : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]
  ring

private lemma tendsto_log_part :
    Tendsto (fun J : ℕ => 2 * Real.log (2 * (J : ℝ) + 1) - Real.log (J : ℝ) -
      Real.log ((J : ℝ) + 1)) atTop (𝓝 (Real.log 4)) := by
  have hlog1 : Tendsto (fun J : ℕ => Real.log ((2 * (J : ℝ) + 1) / (J : ℝ))) atTop
      (𝓝 (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp tendsto_ratio_one
  have hlog2 : Tendsto (fun J : ℕ => Real.log ((2 * (J : ℝ) + 1) / ((J : ℝ) + 1))) atTop
      (𝓝 (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp tendsto_ratio_two
  have hadd : Tendsto (fun J : ℕ => Real.log ((2 * (J : ℝ) + 1) / (J : ℝ)) +
      Real.log ((2 * (J : ℝ) + 1) / ((J : ℝ) + 1))) atTop (𝓝 (Real.log 4)) := by
    have hsum := hlog1.add hlog2
    have htarget : Real.log 2 + Real.log 2 = Real.log 4 := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    simpa [htarget] using hsum
  refine hadd.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with J hJ
  have hnum : 2 * (J : ℝ) + 1 ≠ 0 := by positivity
  have hJr : (J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hJ
  have hJ1 : (J : ℝ) + 1 ≠ 0 := by positivity
  rw [Real.log_div hnum hJr, Real.log_div hnum hJ1]
  ring

private lemma tendsto_partial_ideal :
    Tendsto putnamPartial atTop (𝓝 (Real.log 4 - 1)) := by
  have htop2 : Tendsto (fun J : ℕ => 2 * J + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun J => show J ≤ 2 * J + 1 by omega) tendsto_id
  have htop1 : Tendsto (fun J : ℕ => J + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun J => show J ≤ J + 1 by omega) tendsto_id
  have hγ2c := Real.tendsto_harmonic_sub_log.comp htop2
  have hγ2 : Tendsto (fun J : ℕ => (harmonic (2 * J + 1) : ℝ) -
      Real.log (2 * (J : ℝ) + 1)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine hγ2c.congr' ?_
    filter_upwards with J
    change (harmonic (2 * J + 1) : ℝ) - Real.log (((2 * J + 1 : ℕ) : ℝ)) =
      (harmonic (2 * J + 1) : ℝ) - Real.log (2 * (J : ℝ) + 1)
    norm_num
  have hγ0 : Tendsto (fun J : ℕ => (harmonic J : ℝ) - Real.log (J : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hγ1c := Real.tendsto_harmonic_sub_log.comp htop1
  have hγ1 : Tendsto (fun J : ℕ => (harmonic (J + 1) : ℝ) -
      Real.log ((J : ℝ) + 1)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine hγ1c.congr' ?_
    filter_upwards with J
    change (harmonic (J + 1) : ℝ) - Real.log (((J + 1 : ℕ) : ℝ)) =
      (harmonic (J + 1) : ℝ) - Real.log ((J : ℝ) + 1)
    norm_num
  have herr : Tendsto (fun J : ℕ =>
      2 * ((harmonic (2 * J + 1) : ℝ) - Real.log (2 * (J : ℝ) + 1)) -
        ((harmonic J : ℝ) - Real.log (J : ℝ)) -
        ((harmonic (J + 1) : ℝ) - Real.log ((J : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (hγ2.const_mul 2).sub hγ0 |>.sub hγ1
    convert h using 1
    ext J
    ring_nf
  have hmain := (herr.add tendsto_log_part).sub_const 1
  have hmain' : Tendsto (fun J : ℕ =>
      (2 * ((harmonic (2 * J + 1) : ℝ) - Real.log (2 * (J : ℝ) + 1)) -
        ((harmonic J : ℝ) - Real.log (J : ℝ)) -
        ((harmonic (J + 1) : ℝ) - Real.log ((J : ℝ) + 1)) +
        (2 * Real.log (2 * (J : ℝ) + 1) - Real.log (J : ℝ) -
          Real.log ((J : ℝ) + 1))) - 1) atTop (𝓝 (Real.log 4 - 1)) := by
    simpa using hmain
  refine hmain'.congr' ?_
  filter_upwards with J
  rw [partial_sum_eq_harmonic]
  ring

private lemma tendsto_tail_J : Tendsto (fun J : ℕ => (2 : ℝ) / (2 * J + 2)) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine h.congr' ?_
  filter_upwards with J
  have hden : (2 : ℝ) * J + 2 ≠ 0 := by positivity
  field_simp [hden]

private lemma tendsto_mod_average :
    Tendsto (fun n : ℕ => ((putnamModSum n : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 (Real.log 4 - 1)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hAevent : ∀ᶠ J : ℕ in atTop, a < putnamPartial J :=
      (tendsto_order.mp tendsto_partial_ideal).1 a ha
    rcases eventually_atTop.mp hAevent with ⟨J, hJ⟩
    have hAJ : a < putnamPartial J := hJ J le_rfl
    have hLevent : ∀ᶠ n : ℕ in atTop, a < ((putnamLower J n : ℕ) : ℝ) / (n : ℝ) :=
      (tendsto_order.mp (tendsto_lower_fixed J)).1 a hAJ
    filter_upwards [hLevent, eventually_gt_atTop (0 : ℕ)] with n han hnpos
    calc
      a < ((putnamLower J n : ℕ) : ℝ) / (n : ℝ) := han
      _ ≤ ((putnamModSum n : ℕ) : ℝ) / (n : ℝ) := by
        have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
        gcongr
        exact_mod_cast lower_le_mod_sum J n
  · intro b hb
    have hAupper : Tendsto (fun J : ℕ => putnamPartial J + (2 : ℝ) / (2 * J + 2))
        atTop (𝓝 (Real.log 4 - 1 + 0)) := tendsto_partial_ideal.add tendsto_tail_J
    have hAupper' : Tendsto (fun J : ℕ => putnamPartial J + (2 : ℝ) / (2 * J + 2))
        atTop (𝓝 (Real.log 4 - 1)) := by
      simpa using hAupper
    have hJevent : ∀ᶠ J : ℕ in atTop, putnamPartial J + (2 : ℝ) / (2 * J + 2) < b :=
      (tendsto_order.mp hAupper').2 b hb
    rcases eventually_atTop.mp hJevent with ⟨J, hJ⟩
    have hAJ : putnamPartial J + (2 : ℝ) / (2 * J + 2) < b := hJ J le_rfl
    have hU : Tendsto (fun n : ℕ => ((putnamLower J n : ℕ) : ℝ) / (n : ℝ) +
        ((((2 * n) / (2 * J + 2) : ℕ) : ℝ) / (n : ℝ))) atTop
        (𝓝 (putnamPartial J + (2 : ℝ) / (2 * J + 2))) :=
      (tendsto_lower_fixed J).add
        (by simpa using tendsto_nat_const_mul_div 2 (2 * J + 2) (by omega))
    have hUevent : ∀ᶠ n : ℕ in atTop,
        ((putnamLower J n : ℕ) : ℝ) / (n : ℝ) +
          ((((2 * n) / (2 * J + 2) : ℕ) : ℝ) / (n : ℝ)) < b :=
      (tendsto_order.mp hU).2 b hAJ
    filter_upwards [hUevent, eventually_gt_atTop (0 : ℕ)] with n hnb hnpos
    calc
      ((putnamModSum n : ℕ) : ℝ) / (n : ℝ) ≤
          ((putnamLower J n + (2 * n) / (2 * J + 2) : ℕ) : ℝ) / (n : ℝ) := by
        have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
        gcongr
        exact_mod_cast mod_sum_le_lower_add_tail J n
      _ = ((putnamLower J n : ℕ) : ℝ) / (n : ℝ) +
          ((((2 * n) / (2 * J + 2) : ℕ) : ℝ) / (n : ℝ)) := by
        rw [Nat.cast_add, add_div]
      _ < b := hnb

-- (4, 1)
/--
Find $$\lim_{n \to \infty} \frac{1}{n} \sum_{k=1}^{n}\left(\left\lfloor \frac{2n}{k} \right\rfloor - 2\left\lfloor \frac{n}{k} \right\rfloor\right).$$ Your answer should be in the form $\ln(a) - b$, where $a$ and $b$ are positive integers.
-/
theorem putnam_1976_b1
: Tendsto (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n, (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) atTop
(𝓝 (Real.log ((4, 1) : ℕ × ℕ ).1 - ((4, 1) : ℕ × ℕ ).2)) := by
  have htarget : Real.log ((4, 1) : ℕ × ℕ).1 - (((4, 1) : ℕ × ℕ).2 : ℝ) =
      Real.log 4 - 1 := by
    norm_num
  rw [htarget]
  refine tendsto_mod_average.congr' ?_
  filter_upwards with n
  rw [original_sum_eq_mod_sum n]
  rw [Int.cast_sum]
  simp only [Int.cast_natCast, Nat.cast_sum]
  rw [div_eq_mul_inv]
  ring
