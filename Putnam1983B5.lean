import Mathlib

open Nat Filter Topology Real MeasureTheory

noncomputable abbrev putnam_1983_b5_solution : ℝ := Real.log (4 / Real.pi)

private lemma putnam_1983_b5_dist_left (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1 / 2)) :
    min (Int.fract x) ((⌈x⌉ : ℤ) - x) = x - k := by
  have hxlt : x < (k : ℝ) + 1 := by linarith [hx.2]
  have hfloor : ⌊x⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hxlt
  by_cases hxk : x = (k : ℝ)
  · subst x
    simp [Int.fract]
  · have hkltx : (k : ℝ) < x := lt_of_le_of_ne hx.1 (Ne.symm hxk)
    have hxle : x ≤ ((k : ℤ) + 1 : ℤ) := by
      norm_num
      linarith [hx.2]
    have hceil : ⌈x⌉ = ((k : ℤ) + 1) := by
      rw [Int.ceil_eq_iff]
      constructor
      · norm_num
        exact hkltx
      · exact hxle
    rw [Int.fract, hfloor, hceil]
    norm_num
    nlinarith [hx.2]

private lemma putnam_1983_b5_dist_right (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) + 1 / 2) ((k : ℝ) + 1)) :
    min (Int.fract x) ((⌈x⌉ : ℤ) - x) = (k : ℝ) + 1 - x := by
  have hkltx : (k : ℝ) < x := by linarith [hx.1]
  have hceil : ⌈x⌉ = ((k : ℤ) + 1) := by
    rw [Int.ceil_eq_iff]
    constructor
    · norm_num
      exact hkltx
    · exact_mod_cast hx.2
  by_cases hxright : x = (k : ℝ) + 1
  · subst x
    simp [Int.fract]
  · have hxlt : x < (k : ℝ) + 1 := lt_of_le_of_ne hx.2 hxright
    have hfloor : ⌊x⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast (le_of_lt hkltx)
      · exact_mod_cast hxlt
    rw [Int.fract, hfloor, hceil]
    norm_num
    nlinarith [hx.1]

private lemma putnam_1983_b5_pos_of_mem_uIcc {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Set.uIcc a b) : 0 < x := by
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨hx1, _⟩ | ⟨hx1, _⟩
  · exact lt_of_lt_of_le ha hx1
  · exact lt_of_lt_of_le hb hx1

private lemma putnam_1983_b5_intervalIntegrable_x_sub_const_div_sq
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => (x - c) / x ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine (continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2) ?_
  intro x hx
  exact pow_ne_zero 2 (putnam_1983_b5_pos_of_mem_uIcc ha hb hx).ne'

private lemma putnam_1983_b5_integral_x_sub_const_div_sq
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, (x - c) / x ^ 2 = Real.log b + c / b - (Real.log a + c / a) := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => Real.log y + c / y)
      ((x - c) / x ^ 2) x := by
    intro x hx
    have hxpos : 0 < x := putnam_1983_b5_pos_of_mem_uIcc ha hb hx
    have hxne : x ≠ 0 := hxpos.ne'
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hxne
    have hdiv : HasDerivAt (fun y : ℝ => c / y) (-c / x ^ 2) x := by
      simpa using ((hasDerivAt_const (x := x) (c := c)).div (hasDerivAt_id x) hxne)
    convert hlog.add hdiv using 1
    field_simp [hxne]
    ring
  simpa [sub_eq_add_neg, add_assoc] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (putnam_1983_b5_intervalIntegrable_x_sub_const_div_sq ha hb)

private lemma putnam_1983_b5_intervalIntegrable_const_sub_x_div_sq
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => (c - x) / x ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine (continuousOn_const.sub continuousOn_id).div (continuousOn_id.pow 2) ?_
  intro x hx
  exact pow_ne_zero 2 (putnam_1983_b5_pos_of_mem_uIcc ha hb hx).ne'

private lemma putnam_1983_b5_integral_const_sub_x_div_sq
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, (c - x) / x ^ 2 = -(Real.log b + c / b - (Real.log a + c / a)) := by
  calc
    ∫ x in a..b, (c - x) / x ^ 2 = ∫ x in a..b, -((x - c) / x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      field_simp [(putnam_1983_b5_pos_of_mem_uIcc ha hb hx).ne']
      ring_nf
    _ = -(∫ x in a..b, (x - c) / x ^ 2) := by rw [intervalIntegral.integral_neg]
    _ = -(Real.log b + c / b - (Real.log a + c / a)) := by
      rw [putnam_1983_b5_integral_x_sub_const_div_sq ha hb]

private lemma putnam_1983_b5_intervalIntegrable_dist_piece (k : ℕ) (hk : 1 ≤ k) :
    IntervalIntegrable
      (fun x : ℝ => min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2)
      volume (k : ℝ) ((k : ℝ) + 1) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hmpos : 0 < (k : ℝ) + 1 / 2 := by positivity
  have hk1pos : 0 < (k : ℝ) + 1 := by positivity
  have hkmid : (k : ℝ) ≤ (k : ℝ) + 1 / 2 := by norm_num
  have hmidk1 : (k : ℝ) + 1 / 2 ≤ (k : ℝ) + 1 := by norm_num
  have hleft :
      IntervalIntegrable
        (fun x : ℝ => min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2)
        volume (k : ℝ) ((k : ℝ) + 1 / 2) := by
    refine (putnam_1983_b5_intervalIntegrable_x_sub_const_div_sq
      (a := (k : ℝ)) (b := (k : ℝ) + 1 / 2) (c := (k : ℝ)) hkpos hmpos).congr ?_
    intro x hx
    have hxIcc : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1 / 2) := by
      have hx' := Set.uIoc_subset_uIcc hx
      rwa [Set.uIcc_of_le hkmid] at hx'
    dsimp
    have hdist : min (Int.fract x) ((⌈x⌉ : ℤ) - x) = x - (k : ℝ) :=
      putnam_1983_b5_dist_left k hxIcc
    rw [hdist]
  have hright :
      IntervalIntegrable
        (fun x : ℝ => min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2)
        volume ((k : ℝ) + 1 / 2) ((k : ℝ) + 1) := by
    refine (putnam_1983_b5_intervalIntegrable_const_sub_x_div_sq
      (a := (k : ℝ) + 1 / 2) (b := (k : ℝ) + 1) (c := (k : ℝ) + 1) hmpos hk1pos).congr ?_
    intro x hx
    have hxIcc : x ∈ Set.Icc ((k : ℝ) + 1 / 2) ((k : ℝ) + 1) := by
      have hx' := Set.uIoc_subset_uIcc hx
      rwa [Set.uIcc_of_le hmidk1] at hx'
    dsimp
    have hdist : min (Int.fract x) ((⌈x⌉ : ℤ) - x) = (k : ℝ) + 1 - x :=
      putnam_1983_b5_dist_right k hxIcc
    rw [hdist]
  exact hleft.trans hright

private lemma putnam_1983_b5_integral_piece (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in (k : ℝ)..((k : ℝ) + 1),
        min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2 =
      Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hmpos : 0 < (k : ℝ) + 1 / 2 := by positivity
  have hk1pos : 0 < (k : ℝ) + 1 := by positivity
  have hkmid : (k : ℝ) ≤ (k : ℝ) + 1 / 2 := by norm_num
  have hmidk1 : (k : ℝ) + 1 / 2 ≤ (k : ℝ) + 1 := by norm_num
  have hleft_int :
      IntervalIntegrable
        (fun x : ℝ => min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2)
        volume (k : ℝ) ((k : ℝ) + 1 / 2) := by
    exact (putnam_1983_b5_intervalIntegrable_dist_piece k hk).mono_set
      (by
        intro x hx
        rw [Set.uIcc_of_le hkmid] at hx
        rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)]
        exact ⟨hx.1, le_trans hx.2 hmidk1⟩)
  have hright_int :
      IntervalIntegrable
        (fun x : ℝ => min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2)
        volume ((k : ℝ) + 1 / 2) ((k : ℝ) + 1) := by
    exact (putnam_1983_b5_intervalIntegrable_dist_piece k hk).mono_set
      (by
        intro x hx
        rw [Set.uIcc_of_le hmidk1] at hx
        rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)]
        exact ⟨le_trans hkmid hx.1, hx.2⟩)
  have hleft_eq :
      ∫ x in (k : ℝ)..((k : ℝ) + 1 / 2),
          min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2 =
        ∫ x in (k : ℝ)..((k : ℝ) + 1 / 2), (x - (k : ℝ)) / x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1 / 2) := by
      simpa [Set.uIcc_of_le hkmid] using hx
    dsimp
    have hdist : min (Int.fract x) ((⌈x⌉ : ℤ) - x) = x - (k : ℝ) :=
      putnam_1983_b5_dist_left k hxIcc
    rw [hdist]
  have hright_eq :
      ∫ x in ((k : ℝ) + 1 / 2)..((k : ℝ) + 1),
          min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2 =
        ∫ x in ((k : ℝ) + 1 / 2)..((k : ℝ) + 1), ((k : ℝ) + 1 - x) / x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc ((k : ℝ) + 1 / 2) ((k : ℝ) + 1) := by
      have hx' := hx
      rwa [Set.uIcc_of_le hmidk1] at hx'
    dsimp
    have hdist : min (Int.fract x) ((⌈x⌉ : ℤ) - x) = (k : ℝ) + 1 - x :=
      putnam_1983_b5_dist_right k hxIcc
    rw [hdist]
  have harg : (((k : ℝ) + 1 / 2) ^ 2) / ((k : ℝ) * ((k : ℝ) + 1)) =
      (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) := by
    field_simp [hkpos.ne', hk1pos.ne']
    ring
  have hlog : Real.log ((((k : ℝ) + 1 / 2) ^ 2) / ((k : ℝ) * ((k : ℝ) + 1))) =
      2 * Real.log ((k : ℝ) + 1 / 2) -
        (Real.log (k : ℝ) + Real.log ((k : ℝ) + 1)) := by
    rw [Real.log_div (pow_ne_zero 2 hmpos.ne') (mul_ne_zero hkpos.ne' hk1pos.ne')]
    rw [Real.log_pow, Real.log_mul hkpos.ne' hk1pos.ne']
    ring
  calc
    ∫ x in (k : ℝ)..((k : ℝ) + 1),
        min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2
        = (∫ x in (k : ℝ)..((k : ℝ) + 1 / 2),
            min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2)
          + (∫ x in ((k : ℝ) + 1 / 2)..((k : ℝ) + 1),
            min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2) := by
          simpa using (intervalIntegral.integral_add_adjacent_intervals hleft_int hright_int).symm
    _ = (∫ x in (k : ℝ)..((k : ℝ) + 1 / 2), (x - (k : ℝ)) / x ^ 2) +
        (∫ x in ((k : ℝ) + 1 / 2)..((k : ℝ) + 1), ((k : ℝ) + 1 - x) / x ^ 2) := by
          simpa using congrArg₂ (fun a b : ℝ => a + b) hleft_eq hright_eq
    _ = (Real.log ((k : ℝ) + 1 / 2) + (k : ℝ) / ((k : ℝ) + 1 / 2) -
          (Real.log (k : ℝ) + (k : ℝ) / (k : ℝ))) +
        (-(Real.log ((k : ℝ) + 1) + ((k : ℝ) + 1) / ((k : ℝ) + 1) -
            (Real.log ((k : ℝ) + 1 / 2) + ((k : ℝ) + 1) / ((k : ℝ) + 1 / 2)))) := by
          rw [putnam_1983_b5_integral_x_sub_const_div_sq hkpos hmpos]
          rw [putnam_1983_b5_integral_const_sub_x_div_sq hmpos hk1pos]
    _ = Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) := by
          rw [← harg, hlog]
          field_simp [hkpos.ne', hmpos.ne', hk1pos.ne']
          ring

private lemma putnam_1983_b5_integral_sum (N : ℕ) :
    ∫ x in (1 : ℝ)..((N : ℝ) + 1),
        min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2 =
      ∑ k ∈ Finset.Icc 1 N,
        Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) := by
  have hsum :=
    intervalIntegral.sum_integral_adjacent_intervals_Ico
      (f := fun x : ℝ => min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2)
      (μ := volume) (a := fun k : ℕ => (k : ℝ)) (m := 1) (n := N + 1)
      (Nat.succ_le_succ (Nat.zero_le N))
      (by
        intro k hk
        have hk1 : 1 ≤ k := hk.1
        simpa [Nat.cast_add, Nat.cast_one] using putnam_1983_b5_intervalIntegrable_dist_piece k hk1)
  calc
    ∫ x in (1 : ℝ)..((N : ℝ) + 1),
        min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2
        = ∑ k ∈ Finset.Ico 1 (N + 1),
            ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ),
              min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2 := by
          simpa [Nat.cast_add, Nat.cast_one] using hsum.symm
    _ = ∑ k ∈ Finset.Ico 1 (N + 1),
        Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkFin : k ∈ Finset.Ico 1 (N + 1) := by simpa using hk
          have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hkFin).1
          simpa [Nat.cast_add, Nat.cast_one] using putnam_1983_b5_integral_piece k hk1
    _ = ∑ k ∈ Finset.Icc 1 N,
        Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) := by
          rw [show Finset.Ico 1 (N + 1) = Finset.Icc 1 N by
            simpa using (Finset.Ico_succ_right_eq_Icc (a := 1) (b := N))]

private lemma putnam_1983_b5_div_image_Ioc (n : ℕ) (hn : 1 ≤ n) :
    (fun x : ℝ => (n : ℝ) / x) '' Set.Ioc (1 : ℝ) (n : ℝ) =
      Set.Ico (1 : ℝ) (n : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxpos : 0 < x := by linarith [hx.1]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
    constructor
    · exact (one_le_div hxpos).2 hx.2
    · exact (div_lt_self hnpos hx.1)
  · intro hy
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
    refine ⟨(n : ℝ) / y, ?_, ?_⟩
    · constructor
      · exact (one_lt_div hypos).2 hy.2
      · exact div_le_self hnpos.le hy.1
    · field_simp [hypos.ne']

private lemma putnam_1983_b5_change_var (dist_fun : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * ∫ x in (1 : ℝ)..(n : ℝ), dist_fun ((n : ℝ) / x) =
      ∫ x in (1 : ℝ)..(n : ℝ), dist_fun x / x ^ 2 := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  let f : ℝ → ℝ := fun x => (n : ℝ) / x
  let g : ℝ → ℝ := fun x => dist_fun x / x ^ 2
  have hderiv : ∀ x ∈ Set.Ioc (1 : ℝ) (n : ℝ),
      HasDerivWithinAt f (-(n : ℝ) / x ^ 2) (Set.Ioc (1 : ℝ) (n : ℝ)) x := by
    intro x hx
    have hxne : x ≠ 0 := by linarith [hx.1]
    have hderiv_at : HasDerivAt f (-(n : ℝ) / x ^ 2) x := by
      simpa [f] using ((hasDerivAt_const (x := x) (c := (n : ℝ))).div (hasDerivAt_id x) hxne)
    exact hderiv_at.hasDerivWithinAt
  have hanti : AntitoneOn f (Set.Ioc (1 : ℝ) (n : ℝ)) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := by linarith [hx.1]
    exact div_le_div_of_nonneg_left (by positivity : 0 ≤ (n : ℝ)) hxpos hxy
  have hsubst :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_antitone
      (s := Set.Ioc (1 : ℝ) (n : ℝ)) (f := f) (f' := fun x => -(n : ℝ) / x ^ 2)
      (g := g) measurableSet_Ioc hderiv hanti
  have himage : f '' Set.Ioc (1 : ℝ) (n : ℝ) = Set.Ico (1 : ℝ) (n : ℝ) := by
    simpa [f] using putnam_1983_b5_div_image_Ioc n hn
  have hset :
      ∫ x in Set.Ioc (1 : ℝ) (n : ℝ), dist_fun x / x ^ 2 =
        ∫ x in Set.Ioc (1 : ℝ) (n : ℝ),
          (1 / (n : ℝ)) * dist_fun ((n : ℝ) / x) := by
    calc
      ∫ x in Set.Ioc (1 : ℝ) (n : ℝ), dist_fun x / x ^ 2
          = ∫ x in Set.Ico (1 : ℝ) (n : ℝ), g x := by
              rw [setIntegral_congr_set (MeasureTheory.Ico_ae_eq_Ioc (μ := volume)).symm]
      _ = ∫ x in f '' Set.Ioc (1 : ℝ) (n : ℝ), g x := by rw [himage]
      _ = ∫ x in Set.Ioc (1 : ℝ) (n : ℝ), (-(fun x => -(n : ℝ) / x ^ 2) x) • g (f x) := by
              simpa using hsubst
      _ = ∫ x in Set.Ioc (1 : ℝ) (n : ℝ),
          (1 / (n : ℝ)) * dist_fun ((n : ℝ) / x) := by
              apply setIntegral_congr_fun measurableSet_Ioc
              intro x hx
              have hxne : x ≠ 0 := by linarith [hx.1]
              dsimp [f, g]
              field_simp [hxne, hnpos.ne']
  rw [intervalIntegral.integral_of_le hnreal, intervalIntegral.integral_of_le hnreal, hset]
  rw [← integral_const_mul]

private lemma putnam_1983_b5_prod_mul_identity (N : ℕ) :
    (∏ k ∈ Finset.Icc 1 N,
      ((((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) *
        ((2 * (k : ℝ) / (2 * (k : ℝ) - 1)) *
          (2 * (k : ℝ) / (2 * (k : ℝ) + 1))))) =
      (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) := by
  induction N with
  | zero =>
      norm_num
  | succ N ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [ih]
      have hN1pos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
      have hN2pos : 0 < ((N + 2 : ℕ) : ℝ) := by positivity
      have hN1ge : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
      have hdenpos : 0 < 2 * ((N + 1 : ℕ) : ℝ) - 1 := by nlinarith
      have hden : 2 * ((N + 1 : ℕ) : ℝ) - 1 ≠ 0 := hdenpos.ne'
      field_simp [hN1pos.ne', hN2pos.ne', hden]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf

private lemma putnam_1983_b5_prod_relation (N : ℕ) :
    (∏ k ∈ Finset.Icc 1 N,
      (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1)))) =
      ((2 * (N : ℝ) + 1) / ((N : ℝ) + 1)) /
        (∏ k ∈ Finset.Icc 1 N,
          ((2 * (k : ℝ) / (2 * (k : ℝ) - 1)) *
            (2 * (k : ℝ) / (2 * (k : ℝ) + 1)))) := by
  have hmul :
      (∏ k ∈ Finset.Icc 1 N,
        (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1)))) *
        (∏ k ∈ Finset.Icc 1 N,
          ((2 * (k : ℝ) / (2 * (k : ℝ) - 1)) *
            (2 * (k : ℝ) / (2 * (k : ℝ) + 1)))) =
        (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) := by
    rw [← Finset.prod_mul_distrib]
    exact putnam_1983_b5_prod_mul_identity N
  have hWne :
      (∏ k ∈ Finset.Icc 1 N,
          ((2 * (k : ℝ) / (2 * (k : ℝ) - 1)) *
            (2 * (k : ℝ) / (2 * (k : ℝ) + 1)))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 ?_
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk1)
    have hkge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hden1 : 0 < 2 * (k : ℝ) - 1 := by nlinarith
    have hden2 : 0 < 2 * (k : ℝ) + 1 := by nlinarith
    have hleft : 0 < (2 * (k : ℝ) / (2 * (k : ℝ) - 1) : ℝ) := by
      exact div_pos (by positivity) hden1
    have hright : 0 < (2 * (k : ℝ) / (2 * (k : ℝ) + 1) : ℝ) := by
      exact div_pos (by positivity) hden2
    exact (mul_pos hleft hright).ne'
  exact (eq_div_iff_mul_eq hWne).2 hmul

private lemma putnam_1983_b5_sum_log_eq (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
      Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1)))) =
      Real.log (((2 * (N : ℝ) + 1) / ((N : ℝ) + 1)) /
        (∏ k ∈ Finset.Icc 1 N,
          ((2 * (k : ℝ) / (2 * (k : ℝ) - 1)) *
            (2 * (k : ℝ) / (2 * (k : ℝ) + 1))))) := by
  have hne :
      ∀ k ∈ Finset.Icc 1 N,
        (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) ≠ 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk1)
    have hk1pos : 0 < (k : ℝ) + 1 := by positivity
    have hnum : 0 < (2 * (k : ℝ) + 1) ^ 2 := sq_pos_of_ne_zero (by positivity)
    have hden : 0 < 4 * (k : ℝ) * ((k : ℝ) + 1) := by positivity
    exact (div_pos hnum hden).ne'
  rw [← Real.log_prod hne, putnam_1983_b5_prod_relation N]

private lemma putnam_1983_b5_ratio_tendsto :
    Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1) / ((N : ℝ) + 1)) atTop (𝓝 2) := by
  have h :
      (fun N : ℕ => (2 * (N : ℝ) + 1) / ((N : ℝ) + 1)) =
        fun N : ℕ => 2 - 1 / ((N : ℝ) + 1) := by
    funext N
    have hden : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [h]
  simpa using
    ((tendsto_const_nhds (x := (2 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

private lemma putnam_1983_b5_sum_tendsto
    (fact : Tendsto (fun N ↦ ∏ n ∈ Finset.Icc 1 N,
      (2 * n / (2 * n - 1)) * (2 * n / (2 * n + 1)) : ℕ → ℝ)
      atTop (𝓝 (Real.pi / 2))) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))))
      atTop (𝓝 putnam_1983_b5_solution) := by
  have hquot :
      Tendsto (fun N : ℕ =>
        ((2 * (N : ℝ) + 1) / ((N : ℝ) + 1)) /
          (∏ n ∈ Finset.Icc 1 N,
            (2 * n / (2 * n - 1)) * (2 * n / (2 * n + 1)) : ℝ))
        atTop (𝓝 (4 / Real.pi)) := by
    have hdiv := putnam_1983_b5_ratio_tendsto.div fact (by positivity : Real.pi / 2 ≠ 0)
    have htarget : 2 / (Real.pi / 2) = 4 / Real.pi := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simpa [htarget] using hdiv
  have hlog :
      Tendsto (fun N : ℕ => Real.log
        (((2 * (N : ℝ) + 1) / ((N : ℝ) + 1)) /
          (∏ n ∈ Finset.Icc 1 N,
            (2 * n / (2 * n - 1)) * (2 * n / (2 * n + 1)) : ℝ)))
        atTop (𝓝 putnam_1983_b5_solution) := by
    simpa [putnam_1983_b5_solution] using
      (Real.continuousAt_log (by positivity : (4 / Real.pi : ℝ) ≠ 0)).tendsto.comp hquot
  refine hlog.congr' ?_
  filter_upwards [] with N
  exact (putnam_1983_b5_sum_log_eq N).symm

/--
Define $\left\lVert x \right\rVert$ as the distance from $x$ to the nearest integer. Find $\lim_{n \to \infty} \frac{1}{n} \int_{1}^{n} \left\lVert \frac{n}{x} \right\rVert \, dx$. You may assume that $\prod_{n=1}^{\infty} \frac{2n}{(2n-1)} \cdot \frac{2n}{(2n+1)} = \frac{\pi}{2}$.
-/
theorem putnam_1983_b5
(dist_fun : ℝ → ℝ)
(hdist_fun : dist_fun = fun (x : ℝ) ↦ min (x - ⌊x⌋) (⌈x⌉ - x))
(fact : Tendsto (fun N ↦ ∏ n ∈ Finset.Icc 1 N, (2 * n / (2 * n - 1)) * (2 * n / (2 * n + 1)) : ℕ → ℝ) atTop (𝓝 (Real.pi / 2)))
: (Tendsto (fun n ↦ (1 / n) * ∫ x in (1)..n, dist_fun (n / x) : ℕ → ℝ) atTop (𝓝 putnam_1983_b5_solution)) :=
by
  let a : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) * ∫ x in (1 : ℝ)..(n : ℝ), dist_fun ((n : ℝ) / x)
  have hshift :
      Tendsto (fun N : ℕ => a (N + 1)) atTop (𝓝 putnam_1983_b5_solution) := by
    refine (putnam_1983_b5_sum_tendsto fact).congr' ?_
    filter_upwards [] with N
    have hchange := putnam_1983_b5_change_var dist_fun (N + 1) (Nat.succ_pos N)
    symm
    calc
      a (N + 1)
          = ∫ x in (1 : ℝ)..((N + 1 : ℕ) : ℝ), dist_fun x / x ^ 2 := hchange
      _ = ∫ x in (1 : ℝ)..((N : ℝ) + 1),
          min (x - (⌊x⌋ : ℤ)) ((⌈x⌉ : ℤ) - x) / x ^ 2 := by
            rw [hdist_fun]
            simp [Nat.cast_add, Nat.cast_one]
      _ = ∑ k ∈ Finset.Icc 1 N,
          Real.log (((2 * (k : ℝ) + 1) ^ 2) / (4 * (k : ℝ) * ((k : ℝ) + 1))) := by
            simpa [Nat.cast_add, Nat.cast_one] using putnam_1983_b5_integral_sum N
  have hmain : Tendsto a atTop (𝓝 putnam_1983_b5_solution) :=
    (tendsto_add_atTop_iff_nat (f := a) 1).mp hshift
  simpa [a] using hmain
