import Mathlib

open Topology Filter Set Polynomial Function

noncomputable abbrev putnam_1981_a1_solution : ℝ := 1 / 8

private def putnamTerm (j n : ℕ) : ℕ :=
  5 ^ j * ∑ q ∈ Finset.Icc 1 (n / 5 ^ j), q

private noncomputable def putnamPartial (J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J, ((putnamTerm j n : ℕ) : ℝ) / (n : ℝ) ^ 2

private noncomputable def putnamFull (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ((putnamTerm j n : ℕ) : ℝ) / (n : ℝ) ^ 2

private lemma ratio_div_const (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => ((n / d : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  refine squeeze_zero' ?_ ?_ (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact Filter.Eventually.of_forall fun n => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with n hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hdposR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hle : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hlt : (n : ℝ) / (d : ℝ) - 1 < ((n / d : ℕ) : ℝ) := by
      simpa [Nat.floor_div_eq_div (K := ℝ) n d] using
        (Nat.sub_one_lt_floor ((n : ℝ) / (d : ℝ)))
    have hle_ratio : ((n / d : ℕ) : ℝ) / (n : ℝ) ≤ 1 / (d : ℝ) := by
      have := div_le_div_of_nonneg_right hle hnpos.le
      calc
        ((n / d : ℕ) : ℝ) / (n : ℝ) ≤ ((n : ℝ) / (d : ℝ)) / (n : ℝ) := this
        _ = 1 / (d : ℝ) := by field_simp [hnpos.ne', hdposR.ne']
    have hdiff_le : 1 / (d : ℝ) - ((n / d : ℕ) : ℝ) / (n : ℝ) ≤ (n : ℝ)⁻¹ := by
      have hlt' : (n : ℝ) / (d : ℝ) - ((n / d : ℕ) : ℝ) < 1 := by linarith
      have hlt'' :
          ((n : ℝ) / (d : ℝ) - ((n / d : ℕ) : ℝ)) / (n : ℝ) < 1 / (n : ℝ) := by
        exact div_lt_div_of_pos_right hlt' hnpos
      have heq :
          ((n : ℝ) / (d : ℝ) - ((n / d : ℕ) : ℝ)) / (n : ℝ)
            = 1 / (d : ℝ) - ((n / d : ℕ) : ℝ) / (n : ℝ) := by
        field_simp [hnpos.ne', hdposR.ne']
      exact le_of_lt (by simpa [heq] using hlt'')
    have habs :
        |((n / d : ℕ) : ℝ) / (n : ℝ) - 1 / (d : ℝ)|
          = 1 / (d : ℝ) - ((n / d : ℕ) : ℝ) / (n : ℝ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle_ratio)]
      ring
    rw [habs]
    simpa [one_div] using hdiff_le

private lemma sum_Icc_id_mul_two (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 N, q) * 2 = N * (N + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 N]
  have hset : Finset.Ico 1 (N + 1) = (Finset.range (N + 1)).erase 0 := by
    ext q
    simp [Finset.mem_Ico, Finset.mem_range]
    omega
  rw [hset]
  rw [Finset.sum_erase]
  · rw [Finset.sum_range_id_mul_two]
    simp [Nat.mul_comm]
  · simp

private lemma multiples_sum_eq (n j : ℕ) :
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => 5 ^ j ∣ m), m = putnamTerm j n := by
  let d := 5 ^ j
  have hdpos : 0 < d := pow_pos (by norm_num : 0 < 5) j
  have h : ∑ m ∈ (Finset.Icc 1 n).filter (fun m => d ∣ m), m
      = ∑ q ∈ Finset.Icc 1 (n / d), d * q := by
    refine Finset.sum_bij (fun m _ => m / d) ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Icc] at hm ⊢
      constructor
      · have hquot_ne : m / d ≠ 0 := by
          intro hzero
          have hm_eq : m = d * (m / d) := Nat.eq_mul_of_div_eq_right hm.2 rfl
          simp [hzero] at hm_eq
          omega
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hquot_ne)
      · exact Nat.div_le_div_right hm.1.2
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      have haeq : a = d * (a / d) := Nat.eq_mul_of_div_eq_right ha.2 rfl
      have hbeq : b = d * (b / d) := Nat.eq_mul_of_div_eq_right hb.2 rfl
      rw [haeq, hbeq, show a / d = b / d from hab]
    · intro q hq
      refine ⟨d * q, ?_, ?_⟩
      · rw [Finset.mem_filter]
        rw [Finset.mem_Icc] at hq ⊢
        constructor
        · constructor
          · exact Nat.succ_le_of_lt (Nat.mul_pos hdpos (lt_of_lt_of_le zero_lt_one hq.1))
          · have hmul : q * d ≤ n := (Nat.le_div_iff_mul_le hdpos).mp hq.2
            simpa [Nat.mul_comm] using hmul
        · exact ⟨q, by rw [Nat.mul_comm]⟩
      · exact Nat.mul_div_right q hdpos
    · intro m hm
      rw [Finset.mem_filter] at hm
      exact Nat.eq_mul_of_div_eq_right hm.2 rfl
  change ∑ m ∈ (Finset.Icc 1 n).filter (fun m => d ∣ m), m
      = d * ∑ q ∈ Finset.Icc 1 (n / d), q
  rw [h, Finset.mul_sum]

private lemma term_tendsto (j : ℕ) :
    Tendsto (fun n : ℕ => ((putnamTerm j n : ℕ) : ℝ) / (n : ℝ)^2)
      atTop (𝓝 (1 / (2 * (5 : ℝ)^j))) := by
  let d := 5 ^ j
  have hd : 0 < d := pow_pos (by norm_num : 0 < 5) j
  have hdR : (d : ℝ) = (5 : ℝ)^j := by simp [d]
  have hbase :
      Tendsto (fun n : ℕ => ((d * ∑ q ∈ Finset.Icc 1 (n / d), q : ℕ) : ℝ) / (n : ℝ)^2)
        atTop (𝓝 (1 / (2 * (d : ℝ)))) := by
    let r : ℕ → ℝ := fun n => ((n / d : ℕ) : ℝ) / (n : ℝ)
    have hr : Tendsto r atTop (𝓝 (1 / (d : ℝ))) := ratio_div_const d hd
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hr2 :
        Tendsto (fun n : ℕ => (((n / d : ℕ) + 1 : ℕ) : ℝ) / (n : ℝ))
          atTop (𝓝 (1 / (d : ℝ))) := by
      have hsum : Tendsto (fun n : ℕ => r n + (n : ℝ)⁻¹) atTop (𝓝 (1 / (d : ℝ) + 0)) :=
        hr.add hinv
      have hcongr : (fun n : ℕ => r n + (n : ℝ)⁻¹) =ᶠ[atTop]
          (fun n : ℕ => (((n / d : ℕ) + 1 : ℕ) : ℝ) / (n : ℝ)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simp [r, add_div]
      simpa using Filter.Tendsto.congr' hcongr hsum
    have hmain :
        Tendsto
          (fun n : ℕ =>
            ((d : ℝ) / 2) * (r n * ((((n / d : ℕ) + 1 : ℕ) : ℝ) / (n : ℝ))))
          atTop (𝓝 (((d : ℝ) / 2) * ((1 / (d : ℝ)) * (1 / (d : ℝ))))) := by
      exact (hr.mul hr2).const_mul ((d : ℝ) / 2)
    have hcongr :
        (fun n : ℕ => ((d * ∑ q ∈ Finset.Icc 1 (n / d), q : ℕ) : ℝ) / (n : ℝ)^2) =ᶠ[atTop]
          (fun n : ℕ =>
            ((d : ℝ) / 2) * (r n * ((((n / d : ℕ) + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      let N := n / d
      let S := ∑ q ∈ Finset.Icc 1 N, q
      have htri2_nat : S * 2 = N * (N + 1) := sum_Icc_id_mul_two N
      have htri2 : (S : ℝ) * 2 = (N : ℝ) * ((N + 1 : ℕ) : ℝ) := by exact_mod_cast htri2_nat
      have htri : (S : ℝ) = (N : ℝ) * ((N + 1 : ℕ) : ℝ) / 2 := by linarith
      simp only [r]
      change ((d * S : ℕ) : ℝ) / (n : ℝ)^2 =
        ((d : ℝ) / 2) * ((((N : ℕ) : ℝ) / (n : ℝ)) *
          ((((N + 1 : ℕ) : ℝ) / (n : ℝ))))
      rw [Nat.cast_mul, htri]
      field_simp [hnpos.ne']
    refine Filter.Tendsto.congr' hcongr.symm ?_
    convert hmain using 1
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hd)]
  have hbase' :
      Tendsto (fun n : ℕ => ((putnamTerm j n : ℕ) : ℝ) / (n : ℝ)^2)
        atTop (𝓝 (1 / (2 * (d : ℝ)))) := by
    refine Filter.Tendsto.congr ?_ hbase
    intro n
    simp [putnamTerm, d]
  simpa [hdR] using hbase'

private lemma term_bound (j n : ℕ) (hn : 1 ≤ n) :
    ((putnamTerm j n : ℕ) : ℝ) / (n : ℝ)^2 ≤ 1 / ((5 : ℝ)^j) := by
  let d := 5 ^ j
  let N := n / d
  let S := ∑ q ∈ Finset.Icc 1 N, q
  have hdpos : 0 < d := pow_pos (by norm_num : 0 < 5) j
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hS_le : S ≤ N * N := by
    calc
      S ≤ (Finset.Icc 1 N).card • N := by
        exact Finset.sum_le_card_nsmul (Finset.Icc 1 N) (fun q => q) N
          (by intro q hq; exact (Finset.mem_Icc.mp hq).2)
      _ = N * N := by
        rw [Nat.card_Icc]
        simp
  have hdN_le : d * N ≤ n := by
    simpa [N, d, Nat.mul_comm] using Nat.div_mul_le_self n d
  have hterm_le_nat : d * S ≤ n * N := by
    calc
      d * S ≤ d * (N * N) := Nat.mul_le_mul_left d hS_le
      _ = (d * N) * N := by ring
      _ ≤ n * N := Nat.mul_le_mul_right N hdN_le
  have hle_real : ((d * S : ℕ) : ℝ) / (n : ℝ)^2 ≤ ((n * N : ℕ) : ℝ) / (n : ℝ)^2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hterm_le_nat) (sq_nonneg (n : ℝ))
  have hratio : ((N : ℕ) : ℝ) / (n : ℝ) ≤ 1 / (d : ℝ) := by
    have hle : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
    have := div_le_div_of_nonneg_right hle hnpos.le
    calc
      ((N : ℕ) : ℝ) / (n : ℝ) = ((n / d : ℕ) : ℝ) / (n : ℝ) := rfl
      _ ≤ ((n : ℝ) / (d : ℝ)) / (n : ℝ) := this
      _ = 1 / (d : ℝ) := by
        have hdposR : 0 < (d : ℝ) := by exact_mod_cast hdpos
        field_simp [hnpos.ne', hdposR.ne']
  calc
    ((putnamTerm j n : ℕ) : ℝ) / (n : ℝ)^2
        = ((d * S : ℕ) : ℝ) / (n : ℝ)^2 := by simp [putnamTerm, d, N, S]
    _ ≤ ((n * N : ℕ) : ℝ) / (n : ℝ)^2 := hle_real
    _ = ((N : ℕ) : ℝ) / (n : ℝ) := by
      rw [Nat.cast_mul]
      field_simp [hnpos.ne']
    _ ≤ 1 / (d : ℝ) := hratio
    _ = 1 / ((5 : ℝ)^j) := by simp [d]

private lemma partial_tendsto (J : ℕ) :
    Tendsto (fun n : ℕ => putnamPartial J n)
      atTop (𝓝 (∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (2 * (5 : ℝ)^j))) := by
  exact tendsto_finset_sum (Finset.Icc 1 J)
    (fun j hj => term_tendsto j)

private lemma partial_sum_formula (J : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (2 * (5 : ℝ)^j)) =
      (1 / 8 : ℝ) * (1 - (1 / 5 : ℝ)^J) := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 J]
  calc
    (∑ j ∈ Finset.Ico 1 (J + 1), (1 : ℝ) / (2 * (5 : ℝ)^j))
        = (1 / 2 : ℝ) * ∑ j ∈ Finset.Ico 1 (J + 1), (1 / 5 : ℝ)^j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [div_pow]
          simp [one_div]
          ring
    _ = (1 / 2 : ℝ) * (((1 / 5 : ℝ)^1 - (1 / 5 : ℝ)^(J + 1)) / (1 - (1 / 5 : ℝ))) := by
          rw [geom_sum_Ico'] <;> norm_num
    _ = (1 / 8 : ℝ) * (1 - (1 / 5 : ℝ)^J) := by
          field_simp
          ring

private lemma partial_le_full (J n : ℕ) (hJn : J ≤ n) :
    putnamPartial J n ≤ putnamFull n := by
  unfold putnamPartial putnamFull
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hJn) ?_
  intro j hj hnot
  positivity

private lemma tail_geom_bound (J n : ℕ) :
    (∑ j ∈ Finset.Ico (J + 1) (n + 1), (1 : ℝ) / ((5 : ℝ)^j))
      ≤ ((1 / 5 : ℝ)^(J + 1)) / (1 - (1 / 5 : ℝ)) := by
  calc
    (∑ j ∈ Finset.Ico (J + 1) (n + 1), (1 : ℝ) / ((5 : ℝ)^j))
        = ∑ j ∈ Finset.Ico (J + 1) (n + 1), (1 / 5 : ℝ)^j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [div_pow]
          simp [one_div]
    _ ≤ ((1 / 5 : ℝ)^(J + 1)) / (1 - (1 / 5 : ℝ)) := by
          exact geom_sum_Ico_le_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 5)
            (by norm_num : (1 / 5 : ℝ) < 1)

private lemma full_le_partial_add_tail (J n : ℕ) (hn : 1 ≤ n) (hJn : J ≤ n) :
    putnamFull n ≤ putnamPartial J n + ((1 / 5 : ℝ)^(J + 1)) / (1 - (1 / 5 : ℝ)) := by
  let f : ℕ → ℝ := fun j => ((putnamTerm j n : ℕ) : ℝ) / (n : ℝ)^2
  let g : ℕ → ℝ := fun j => (1 : ℝ) / ((5 : ℝ)^j)
  have hsub : Finset.Icc 1 J ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc_right hJn
  have hsdiff_sub : Finset.Icc 1 n \ Finset.Icc 1 J ⊆ Finset.Ico (J + 1) (n + 1) := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hj
    rw [Finset.mem_Ico]
    have hJlt : J < j := by
      by_contra hnot
      exact hj.2 (Finset.mem_Icc.mpr ⟨hj.1.1, le_of_not_gt hnot⟩)
    constructor
    · omega
    · omega
  have hsdiff_le :
      ∑ j ∈ Finset.Icc 1 n \ Finset.Icc 1 J, f j
        ≤ ∑ j ∈ Finset.Ico (J + 1) (n + 1), g j := by
    calc
      ∑ j ∈ Finset.Icc 1 n \ Finset.Icc 1 J, f j
          ≤ ∑ j ∈ Finset.Icc 1 n \ Finset.Icc 1 J, g j := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact term_bound j n hn
      _ ≤ ∑ j ∈ Finset.Ico (J + 1) (n + 1), g j := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsdiff_sub ?_
            intro j hj hnot
            positivity
  have hsplit := Finset.sum_sdiff hsub (f := f)
  have hfull_eq : putnamFull n = putnamPartial J n + ∑ j ∈ Finset.Icc 1 n \ Finset.Icc 1 J, f j := by
    unfold putnamFull putnamPartial
    change (∑ j ∈ Finset.Icc 1 n, f j) =
      (∑ j ∈ Finset.Icc 1 J, f j) + ∑ j ∈ Finset.Icc 1 n \ Finset.Icc 1 J, f j
    linarith
  calc
    putnamFull n = putnamPartial J n + ∑ j ∈ Finset.Icc 1 n \ Finset.Icc 1 J, f j := hfull_eq
    _ ≤ putnamPartial J n + ∑ j ∈ Finset.Ico (J + 1) (n + 1), g j := by
          exact add_le_add (le_refl _) hsdiff_le
    _ ≤ putnamPartial J n + ((1 / 5 : ℝ)^(J + 1)) / (1 - (1 / 5 : ℝ)) := by
          exact add_le_add (le_refl _) (tail_geom_bound J n)

private lemma product_factorization_eq_terms (n : ℕ) :
    (∏ m ∈ Finset.Icc 1 n, m^m).factorization 5 =
      ∑ j ∈ Finset.Icc 1 n, putnamTerm j n := by
  have hcard : ∀ m ∈ Finset.Icc 1 n,
      ((Finset.Icc 1 n).filter (fun j => 5 ^ j ∣ m)).card = m.factorization 5 := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
    have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hm1)
    have hfact_le_m : m.factorization 5 ≤ m := by
      exact Nat.factorization_le_of_le_pow (n := m) (p := 5) (b := m)
        (le_of_lt (Nat.lt_pow_self (by norm_num : 1 < 5) (n := m)))
    have hfact_le_n : m.factorization 5 ≤ n := hfact_le_m.trans hmn
    have hset :
        (Finset.Icc 1 n).filter (fun j => 5 ^ j ∣ m) =
          Finset.Icc 1 (m.factorization 5) := by
      ext j
      constructor
      · intro hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_Icc]
        exact ⟨(Finset.mem_Icc.mp hj.1).1,
          (Nat.prime_five.pow_dvd_iff_le_factorization hm0).mp hj.2⟩
      · intro hj
        rw [Finset.mem_filter]
        rw [Finset.mem_Icc] at hj
        exact ⟨Finset.mem_Icc.mpr ⟨hj.1, hj.2.trans hfact_le_n⟩,
          (Nat.prime_five.pow_dvd_iff_le_factorization hm0).mpr hj.2⟩
    rw [hset, Nat.card_Icc]
    omega
  rw [Nat.factorization_prod_apply]
  · calc
      ∑ m ∈ Finset.Icc 1 n, (m ^ m).factorization 5
          = ∑ m ∈ Finset.Icc 1 n, m * m.factorization 5 := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Nat.factorization_pow]
              simp [Finsupp.smul_apply]
      _ = ∑ m ∈ Finset.Icc 1 n,
            ∑ j ∈ (Finset.Icc 1 n).filter (fun j => 5 ^ j ∣ m), m := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.sum_const, hcard m hm]
              simp [Nat.mul_comm]
      _ = ∑ j ∈ Finset.Icc 1 n,
            ∑ m ∈ (Finset.Icc 1 n).filter (fun m => 5 ^ j ∣ m), m := by
              simp_rw [Finset.sum_filter]
              rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.Icc 1 n, putnamTerm j n := by
              apply Finset.sum_congr rfl
              intro j hj
              exact multiples_sum_eq n j
  · intro m hm
    exact pow_ne_zero m (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)

private lemma putnamFull_tendsto :
    Tendsto (fun n : ℕ => putnamFull n) atTop (𝓝 (1 / 8 : ℝ)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    let δ : ℝ := 1 - 8 * a
    have hδ : 0 < δ := by
      dsimp [δ]
      nlinarith
    have hpow :
        Tendsto (fun J : ℕ => (1 / 5 : ℝ)^J) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num : (1 / 5 : ℝ) < 1)
    have hevent : ∀ᶠ J in atTop, (1 / 5 : ℝ)^J < δ :=
      hpow.eventually (eventually_lt_nhds hδ)
    rcases Filter.eventually_atTop.mp hevent with ⟨J, hJ⟩
    have hJsmall : (1 / 5 : ℝ)^J < δ := hJ J le_rfl
    have hlim_gt :
        a < ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (2 * (5 : ℝ)^j) := by
      rw [partial_sum_formula]
      dsimp [δ] at hJsmall
      nlinarith
    have hpart_event : ∀ᶠ n in atTop, a < putnamPartial J n :=
      (partial_tendsto J).eventually (eventually_gt_nhds hlim_gt)
    have hle_event : ∀ᶠ n in atTop, putnamPartial J n ≤ putnamFull n := by
      filter_upwards [eventually_ge_atTop J] with n hn
      exact partial_le_full J n hn
    filter_upwards [hpart_event, hle_event] with n hpart hle
    exact lt_of_lt_of_le hpart hle
  · intro b hb
    let δ : ℝ := b - 1 / 8
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hpow :
        Tendsto (fun J : ℕ => (1 / 5 : ℝ)^J) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num : (1 / 5 : ℝ) < 1)
    have hevent : ∀ᶠ J in atTop, (1 / 5 : ℝ)^J < δ :=
      hpow.eventually (eventually_lt_nhds hδ)
    rcases Filter.eventually_atTop.mp hevent with ⟨J, hJ⟩
    have hJsmall : (1 / 5 : ℝ)^J < δ := hJ J le_rfl
    let tail : ℝ := ((1 / 5 : ℝ)^(J + 1)) / (1 - (1 / 5 : ℝ))
    have htail : tail = (1 / 4 : ℝ) * (1 / 5 : ℝ)^J := by
      dsimp [tail]
      rw [pow_succ']
      field_simp
      ring
    have hlim_lt :
        (∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (2 * (5 : ℝ)^j)) + tail < b := by
      rw [partial_sum_formula, htail]
      dsimp [δ] at hJsmall
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 5) J]
    have hupper_event : ∀ᶠ n in atTop, putnamPartial J n + tail < b := by
      have htend :
          Tendsto (fun n : ℕ => putnamPartial J n + tail) atTop
            (𝓝 ((∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (2 * (5 : ℝ)^j)) + tail)) :=
        (partial_tendsto J).add tendsto_const_nhds
      exact htend.eventually (eventually_lt_nhds hlim_lt)
    have hle_event : ∀ᶠ n in atTop, putnamFull n ≤ putnamPartial J n + tail := by
      filter_upwards [eventually_ge_atTop (max 1 J)] with n hn
      have hn1 : 1 ≤ n := (le_max_left 1 J).trans hn
      have hJn : J ≤ n := (le_max_right 1 J).trans hn
      simpa [tail] using full_le_partial_add_tail J n hn1 hJn
    filter_upwards [hupper_event, hle_event] with n hupper hle
    exact lt_of_le_of_lt hle hupper

/--
Let $E(n)$ be the greatest integer $k$ such that $5^k$ divides $1^1 2^2 3^3 \cdots n^n$. Find $\lim_{n \rightarrow \infty} \frac{E(n)}{n^2}$.
-/
theorem putnam_1981_a1
    (P : ℕ → ℕ → Prop)
    (hP : ∀ n k, P n k ↔ 5^k ∣ ∏ m ∈ Finset.Icc 1 n, (m^m : ℤ))
    (E : ℕ → ℕ)
    (hE : ∀ n ∈ Ici 1, P n (E n) ∧ ∀ k : ℕ, P n k → k ≤ E n) :
    Tendsto (fun n : ℕ => ((E n) : ℝ)/n^2) atTop (𝓝 putnam_1981_a1_solution) :=
by
  have h_event :
      (fun n : ℕ => ((E n) : ℝ) / n^2) =ᶠ[atTop] (fun n : ℕ => putnamFull n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let A : ℕ := ∏ m ∈ Finset.Icc 1 n, m^m
    let Z : ℤ := ∏ m ∈ Finset.Icc 1 n, (m^m : ℤ)
    have hZabs : Z.natAbs = A := by
      change Int.natAbsHom (∏ m ∈ Finset.Icc 1 n, (m^m : ℤ)) =
        ∏ m ∈ Finset.Icc 1 n, m^m
      rw [map_prod]
      simp [Int.natAbs_pow]
    have hA0 : A ≠ 0 := by
      dsimp [A]
      apply Finset.prod_ne_zero_iff.mpr
      intro m hm
      exact pow_ne_zero m (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
    have hPiff : ∀ k : ℕ, P n k ↔ k ≤ A.factorization 5 := by
      intro k
      rw [hP n k]
      constructor
      · intro hdivZ
        have hdivNat : 5 ^ k ∣ A := by
          rw [← hZabs]
          exact Int.natCast_dvd.mp hdivZ
        exact (Nat.prime_five.pow_dvd_iff_le_factorization hA0).mp hdivNat
      · intro hk
        have hdivNat : 5 ^ k ∣ A :=
          (Nat.prime_five.pow_dvd_iff_le_factorization hA0).mpr hk
        apply Int.natCast_dvd.mpr
        rwa [hZabs]
    have hEeqFactor : E n = A.factorization 5 := by
      have hEn := hE n hn
      exact le_antisymm ((hPiff (E n)).mp hEn.1) (hEn.2 (A.factorization 5) ((hPiff _).mpr le_rfl))
    have hEeq :
        E n = ∑ j ∈ Finset.Icc 1 n, putnamTerm j n := by
      calc
        E n = A.factorization 5 := hEeqFactor
        _ = (∏ m ∈ Finset.Icc 1 n, m^m).factorization 5 := rfl
        _ = ∑ j ∈ Finset.Icc 1 n, putnamTerm j n := product_factorization_eq_terms n
    unfold putnamFull
    rw [hEeq, Nat.cast_sum, Finset.sum_div]
  exact Filter.Tendsto.congr' h_event.symm (by
    simpa [putnam_1981_a1_solution] using putnamFull_tendsto)
