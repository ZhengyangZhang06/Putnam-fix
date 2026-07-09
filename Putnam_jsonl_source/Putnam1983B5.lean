import Mathlib

open Nat Filter Topology Real

noncomputable def putnam_1983_b5_dist (x : ℝ) : ℝ :=
  min (x - ⌊x⌋) (⌈x⌉ - x)

lemma putnam_1983_b5_dist_eq_min_fract (x : ℝ) :
    putnam_1983_b5_dist x = min (Int.fract x) (1 - Int.fract x) := by
  unfold putnam_1983_b5_dist
  by_cases hx : Int.fract x = 0
  · have hxmem : x ∈ Set.range (Int.cast : ℤ → ℝ) := Int.fract_eq_zero_iff.mp hx
    have hceil : (⌈x⌉ : ℝ) = x := (Int.ceil_eq_self_iff_mem x).mpr hxmem
    simp [Int.self_sub_floor, hx, hceil]
  · rw [Int.self_sub_floor, Int.ceil_sub_self_eq hx]

lemma putnam_1983_b5_dist_continuous : Continuous putnam_1983_b5_dist := by
  have hcont : Continuous (fun x : ℝ => min (Int.fract x) (1 - Int.fract x)) := by
    have hbase : ContinuousOn (fun t : ℝ => min t (1 - t)) (Set.Icc 0 1) :=
      (continuous_id.min (continuous_const.sub continuous_id)).continuousOn
    have hend : (fun t : ℝ => min t (1 - t)) 0 = (fun t : ℝ => min t (1 - t)) 1 := by
      norm_num
    simpa [Function.comp_def] using hbase.comp_fract'' hend
  exact hcont.congr fun x => (putnam_1983_b5_dist_eq_min_fract x).symm

lemma putnam_1983_b5_dist_first_half (m : ℕ) {x : ℝ}
    (hx₁ : (m : ℝ) < x) (hx₂ : x ≤ (m : ℝ) + 1 / 2) :
    putnam_1983_b5_dist x = x - m := by
  have hlt : x < (m : ℝ) + 1 := by linarith
  have hfloor : (⌊x⌋ : ℝ) = (m : ℝ) := by
    have hfloor' : ⌊x⌋ = (m : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hx₁.le
      · exact_mod_cast hlt
    exact_mod_cast hfloor'
  have hfract : Int.fract x = x - (m : ℝ) := by
    rw [← Int.self_sub_floor x, hfloor]
  rw [putnam_1983_b5_dist_eq_min_fract, hfract, min_eq_left]
  linarith

lemma putnam_1983_b5_dist_second_half (m : ℕ) {x : ℝ}
    (hx₁ : (m : ℝ) + 1 / 2 < x) (hx₂ : x ≤ (m : ℝ) + 1) :
    putnam_1983_b5_dist x = (m : ℝ) + 1 - x := by
  by_cases hxend : x = (m : ℝ) + 1
  · subst x
    simp [putnam_1983_b5_dist, Int.floor_natCast, Int.ceil_natCast]
  · have hlt : x < (m : ℝ) + 1 := lt_of_le_of_ne hx₂ hxend
    have hfloor : (⌊x⌋ : ℝ) = (m : ℝ) := by
      have hfloor' : ⌊x⌋ = (m : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor
        · exact_mod_cast (by linarith : (m : ℝ) ≤ x)
        · exact_mod_cast hlt
      exact_mod_cast hfloor'
    have hfract : Int.fract x = x - (m : ℝ) := by
      rw [← Int.self_sub_floor x, hfloor]
    rw [putnam_1983_b5_dist_eq_min_fract, hfract, min_eq_right]
    · ring
    · linarith

lemma putnam_1983_b5_integral_first_linear (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (m : ℝ)..(m : ℝ) + 1 / 2, (x - m) / x ^ 2)
      = log (((m : ℝ) + 1 / 2) / (m : ℝ))
          + (m : ℝ) / ((m : ℝ) + 1 / 2) - 1 := by
  let a : ℝ := m
  let b : ℝ := (m : ℝ) + 1 / 2
  have hle : a ≤ b := by dsimp [a, b]; norm_num
  have hapos : 0 < a := by
    dsimp [a]
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hpos : ∀ x ∈ Set.Icc a b, 0 < x := fun x hx => hapos.trans_le hx.1
  have hcont : ContinuousOn (fun y : ℝ => log y + (m : ℝ) / y) (Set.Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    exact ((continuousAt_log hx0).add (continuousAt_const.div continuousAt_id hx0)).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y : ℝ => log y + (m : ℝ) / y) ((x - m) / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x (Set.Ioo_subset_Icc_self hx)).ne'
    convert (Real.hasDerivAt_log hx0).add
      ((hasDerivAt_const x (m : ℝ)).div (hasDerivAt_id x) hx0) using 1
    field_simp [hx0]
    simp only [id_eq]
    ring_nf
  have hint : IntervalIntegrable (fun y : ℝ => (y - m) / y ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    exact ((continuousAt_id.sub continuousAt_const).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0)).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint
  dsimp [a, b] at hFTC
  rw [hFTC]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hmb0 : (m : ℝ) + 1 / 2 ≠ 0 := by positivity
  rw [log_div hmb0 hm0]
  field_simp [hm0, hmb0]
  ring

lemma putnam_1983_b5_integral_second_linear (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (m : ℝ) + 1 / 2..(m : ℝ) + 1, ((m : ℝ) + 1 - x) / x ^ 2)
      = log (((m : ℝ) + 1 / 2) / ((m : ℝ) + 1))
          + ((m : ℝ) + 1) / ((m : ℝ) + 1 / 2) - 1 := by
  let a : ℝ := (m : ℝ) + 1 / 2
  let b : ℝ := (m : ℝ) + 1
  let c : ℝ := (m : ℝ) + 1
  have hle : a ≤ b := by dsimp [a, b]; norm_num
  have hapos : 0 < a := by dsimp [a]; positivity
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hpos : ∀ x ∈ Set.Icc a b, 0 < x := fun x hx => hapos.trans_le hx.1
  have hcont : ContinuousOn (fun y : ℝ => -log y - c / y) (Set.Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    exact ((continuousAt_log hx0).neg.sub
      (continuousAt_const.div continuousAt_id hx0)).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y : ℝ => -log y - c / y) ((c - x) / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos x (Set.Ioo_subset_Icc_self hx)).ne'
    convert (Real.hasDerivAt_log hx0).neg.sub
      ((hasDerivAt_const x c).div (hasDerivAt_id x) hx0) using 1
    field_simp [hx0]
    simp only [id_eq]
    ring_nf
  have hint : IntervalIntegrable (fun y : ℝ => (c - y) / y ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle
    intro x hx
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    exact ((continuousAt_const.sub continuousAt_id).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0)).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint
  dsimp [a, b, c] at hFTC
  rw [hFTC]
  have hma0 : (m : ℝ) + 1 / 2 ≠ 0 := by positivity
  have hmb0 : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [log_div hma0 hmb0]
  field_simp [hma0, hmb0]
  ring

lemma putnam_1983_b5_unit_integral (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (m : ℝ)..(m : ℝ) + 1, putnam_1983_b5_dist x / x ^ 2)
      = Real.log (((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1))) := by
  let mid : ℝ := (m : ℝ) + 1 / 2
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm0 : (m : ℝ) ≠ 0 := hmpos.ne'
  have hmidpos : 0 < mid := by dsimp [mid]; positivity
  have hmid0 : mid ≠ 0 := hmidpos.ne'
  have hm1pos : 0 < (m : ℝ) + 1 := by positivity
  have hm10 : (m : ℝ) + 1 ≠ 0 := hm1pos.ne'
  have hle₁ : (m : ℝ) ≤ mid := by dsimp [mid]; norm_num
  have hle₂ : mid ≤ (m : ℝ) + 1 := by dsimp [mid]; norm_num
  have hEq₁ : Set.EqOn
      (fun x : ℝ => putnam_1983_b5_dist x / x ^ 2)
      (fun x : ℝ => (x - (m : ℝ)) / x ^ 2)
      (Set.uIcc (m : ℝ) mid) := by
    intro x hx
    rw [Set.uIcc_of_le hle₁] at hx
    by_cases hxm : x = (m : ℝ)
    · subst x
      simp [putnam_1983_b5_dist]
    · have hxgt : (m : ℝ) < x := lt_of_le_of_ne hx.1 (Ne.symm hxm)
      change putnam_1983_b5_dist x / x ^ 2 = (x - (m : ℝ)) / x ^ 2
      rw [putnam_1983_b5_dist_first_half m hxgt hx.2]
  have hEq₂ : Set.EqOn
      (fun x : ℝ => putnam_1983_b5_dist x / x ^ 2)
      (fun x : ℝ => ((m : ℝ) + 1 - x) / x ^ 2)
      (Set.uIcc mid ((m : ℝ) + 1)) := by
    intro x hx
    rw [Set.uIcc_of_le hle₂] at hx
    by_cases hxmid : x = mid
    · subst x
      have hdist : putnam_1983_b5_dist mid = mid - (m : ℝ) := by
        apply putnam_1983_b5_dist_first_half
        · dsimp [mid]; norm_num
        · exact le_rfl
      change putnam_1983_b5_dist mid / mid ^ 2 = ((m : ℝ) + 1 - mid) / mid ^ 2
      rw [hdist]
      dsimp [mid]
      ring
    · have hxgt : mid < x := lt_of_le_of_ne hx.1 (Ne.symm hxmid)
      dsimp [mid] at hxgt
      change putnam_1983_b5_dist x / x ^ 2 = ((m : ℝ) + 1 - x) / x ^ 2
      rw [putnam_1983_b5_dist_second_half m hxgt hx.2]
  have hsimple₁ : IntervalIntegrable
      (fun x : ℝ => (x - (m : ℝ)) / x ^ 2) MeasureTheory.volume (m : ℝ) mid := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle₁
    intro x hx
    have hx0 : x ≠ 0 := (hmpos.trans_le hx.1).ne'
    exact ((continuousAt_id.sub continuousAt_const).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0)).continuousWithinAt
  have hsimple₂ : IntervalIntegrable
      (fun x : ℝ => ((m : ℝ) + 1 - x) / x ^ 2) MeasureTheory.volume mid ((m : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle₂
    intro x hx
    have hx0 : x ≠ 0 := (hmidpos.trans_le hx.1).ne'
    exact ((continuousAt_const.sub continuousAt_id).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0)).continuousWithinAt
  have hint₁ : IntervalIntegrable
      (fun x : ℝ => putnam_1983_b5_dist x / x ^ 2) MeasureTheory.volume (m : ℝ) mid :=
    hsimple₁.congr (hEq₁.symm.mono Set.uIoc_subset_uIcc)
  have hint₂ : IntervalIntegrable
      (fun x : ℝ => putnam_1983_b5_dist x / x ^ 2) MeasureTheory.volume mid ((m : ℝ) + 1) :=
    hsimple₂.congr (hEq₂.symm.mono Set.uIoc_subset_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
  rw [intervalIntegral.integral_congr hEq₁, intervalIntegral.integral_congr hEq₂]
  rw [putnam_1983_b5_integral_first_linear m hm,
    putnam_1983_b5_integral_second_linear m hm]
  calc
    Real.log (((m : ℝ) + 1 / 2) / (m : ℝ)) + (m : ℝ) / ((m : ℝ) + 1 / 2) - 1
        + (Real.log (((m : ℝ) + 1 / 2) / ((m : ℝ) + 1))
          + ((m : ℝ) + 1) / ((m : ℝ) + 1 / 2) - 1)
        = Real.log (((m : ℝ) + 1 / 2) / (m : ℝ))
          + Real.log (((m : ℝ) + 1 / 2) / ((m : ℝ) + 1)) := by
          field_simp [hmid0]
          ring
    _ = Real.log ((((m : ℝ) + 1 / 2) / (m : ℝ))
          * (((m : ℝ) + 1 / 2) / ((m : ℝ) + 1))) := by
          have hq₁ : ((m : ℝ) + 1 / 2) / (m : ℝ) ≠ 0 := by positivity
          have hq₂ : ((m : ℝ) + 1 / 2) / ((m : ℝ) + 1) ≠ 0 := by positivity
          rw [Real.log_mul hq₁ hq₂]
    _ = Real.log (((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1))) := by
          congr 1
          field_simp [hm0, hmid0, hm10]
          ring_nf

lemma putnam_1983_b5_unit_intervalIntegrable (m : ℕ) (hm : 1 ≤ m) :
    IntervalIntegrable (fun x : ℝ => putnam_1983_b5_dist x / x ^ 2)
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) := by
  let mid : ℝ := (m : ℝ) + 1 / 2
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmidpos : 0 < mid := by dsimp [mid]; positivity
  have hle₁ : (m : ℝ) ≤ mid := by dsimp [mid]; norm_num
  have hle₂ : mid ≤ (m : ℝ) + 1 := by dsimp [mid]; norm_num
  have hEq₁ : Set.EqOn
      (fun x : ℝ => putnam_1983_b5_dist x / x ^ 2)
      (fun x : ℝ => (x - (m : ℝ)) / x ^ 2)
      (Set.uIcc (m : ℝ) mid) := by
    intro x hx
    rw [Set.uIcc_of_le hle₁] at hx
    by_cases hxm : x = (m : ℝ)
    · subst x
      simp [putnam_1983_b5_dist]
    · have hxgt : (m : ℝ) < x := lt_of_le_of_ne hx.1 (Ne.symm hxm)
      change putnam_1983_b5_dist x / x ^ 2 = (x - (m : ℝ)) / x ^ 2
      rw [putnam_1983_b5_dist_first_half m hxgt hx.2]
  have hEq₂ : Set.EqOn
      (fun x : ℝ => putnam_1983_b5_dist x / x ^ 2)
      (fun x : ℝ => ((m : ℝ) + 1 - x) / x ^ 2)
      (Set.uIcc mid ((m : ℝ) + 1)) := by
    intro x hx
    rw [Set.uIcc_of_le hle₂] at hx
    by_cases hxmid : x = mid
    · subst x
      have hdist : putnam_1983_b5_dist mid = mid - (m : ℝ) := by
        apply putnam_1983_b5_dist_first_half
        · dsimp [mid]; norm_num
        · exact le_rfl
      change putnam_1983_b5_dist mid / mid ^ 2 = ((m : ℝ) + 1 - mid) / mid ^ 2
      rw [hdist]
      dsimp [mid]
      ring
    · have hxgt : mid < x := lt_of_le_of_ne hx.1 (Ne.symm hxmid)
      dsimp [mid] at hxgt
      change putnam_1983_b5_dist x / x ^ 2 = ((m : ℝ) + 1 - x) / x ^ 2
      rw [putnam_1983_b5_dist_second_half m hxgt hx.2]
  have hsimple₁ : IntervalIntegrable
      (fun x : ℝ => (x - (m : ℝ)) / x ^ 2) MeasureTheory.volume (m : ℝ) mid := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle₁
    intro x hx
    have hx0 : x ≠ 0 := (hmpos.trans_le hx.1).ne'
    exact ((continuousAt_id.sub continuousAt_const).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0)).continuousWithinAt
  have hsimple₂ : IntervalIntegrable
      (fun x : ℝ => ((m : ℝ) + 1 - x) / x ^ 2) MeasureTheory.volume mid ((m : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hle₂
    intro x hx
    have hx0 : x ≠ 0 := (hmidpos.trans_le hx.1).ne'
    exact ((continuousAt_const.sub continuousAt_id).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx0)).continuousWithinAt
  exact (hsimple₁.congr (hEq₁.symm.mono Set.uIoc_subset_uIcc)).trans
    (hsimple₂.congr (hEq₂.symm.mono Set.uIoc_subset_uIcc))

lemma putnam_1983_b5_integral_sum (N : ℕ) :
    (∫ x in (1 : ℝ)..((N + 1 : ℕ) : ℝ), putnam_1983_b5_dist x / x ^ 2)
      = ∑ m ∈ Finset.Icc 1 N,
          Real.log (((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1))) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := fun x : ℝ => putnam_1983_b5_dist x / x ^ 2)
    (a := fun k : ℕ => (k : ℝ)) (m := 1) (n := N + 1)
    (by omega)
    (fun k hk => by
      simpa [Nat.cast_add, Nat.cast_one] using
        putnam_1983_b5_unit_intervalIntegrable k hk.1)
  calc
    (∫ x in (1 : ℝ)..((N + 1 : ℕ) : ℝ), putnam_1983_b5_dist x / x ^ 2)
        = ∑ k ∈ Finset.Ico 1 (N + 1),
            ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), putnam_1983_b5_dist x / x ^ 2 := by
          simpa using hsum.symm
    _ = ∑ m ∈ Finset.Icc 1 N,
          Real.log (((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1))) := by
          rw [Finset.Ico_add_one_right_eq_Icc]
          refine Finset.sum_congr rfl ?_
          intro m hm
          simpa [Nat.cast_add, Nat.cast_one] using
            putnam_1983_b5_unit_integral m (Finset.mem_Icc.mp hm).1

lemma putnam_1983_b5_scaled_integral (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist ((n : ℝ) / x)
      = ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist x / x ^ 2 := by
  let f : ℝ → ℝ := fun x => (n : ℝ) / x
  let f' : ℝ → ℝ := fun x => -((n : ℝ) / x ^ 2)
  let g : ℝ → ℝ := fun x => putnam_1983_b5_dist x / x ^ 2
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) (n : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    dsimp [f, f']
    convert ((hasDerivAt_const x (n : ℝ)).div (hasDerivAt_id x) hx0) using 1
    field_simp [hx0]
    simp only [id_eq]
    ring
  have hderiv_cont : ContinuousOn f' (Set.uIcc (1 : ℝ) (n : ℝ)) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hcont : ContinuousAt (fun y : ℝ => -((n : ℝ)) / y ^ 2) x :=
      (continuousAt_const (x := x) (y := -((n : ℝ)))).div
        (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)
    simpa [f', neg_div] using hcont.continuousWithinAt
  have hg_cont : ContinuousOn g (f '' Set.uIcc (1 : ℝ) (n : ℝ)) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hle] at hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hy0 : (n : ℝ) / x ≠ 0 := by positivity
    dsimp [g]
    exact (putnam_1983_b5_dist_continuous.continuousAt.div
      (continuousAt_id.pow 2) (pow_ne_zero 2 hy0)).continuousWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := (1 : ℝ)) (b := (n : ℝ)) (f := f) (f' := f') (g := g)
    hderiv hderiv_cont hg_cont
  have hf_one : f 1 = (n : ℝ) := by
    dsimp [f]
    ring
  have hf_n : f (n : ℝ) = 1 := by
    dsimp [f]
    field_simp [hnpos.ne']
  have hleft :
      (∫ x in (1 : ℝ)..(n : ℝ), (g ∘ f) x * f' x)
        = -((1 / (n : ℝ)) *
            ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist ((n : ℝ) / x)) := by
    calc
      (∫ x in (1 : ℝ)..(n : ℝ), (g ∘ f) x * f' x)
          = ∫ x in (1 : ℝ)..(n : ℝ),
              -(1 / (n : ℝ) * putnam_1983_b5_dist ((n : ℝ) / x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le hle] at hx
            have hx0 : x ≠ 0 := by linarith [hx.1]
            dsimp [g, f, f']
            field_simp [hx0, hnpos.ne']
      _ = -∫ x in (1 : ℝ)..(n : ℝ),
              1 / (n : ℝ) * putnam_1983_b5_dist ((n : ℝ) / x) := by
            rw [intervalIntegral.integral_neg]
      _ = -((1 / (n : ℝ)) *
              ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist ((n : ℝ) / x)) := by
            rw [intervalIntegral.integral_const_mul]
  have hright :
      (∫ x in f (1 : ℝ)..f (n : ℝ), g x)
        = -∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist x / x ^ 2 := by
    rw [hf_one, hf_n, intervalIntegral.integral_symm]
  have hneg :
      -((1 / (n : ℝ)) *
          ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist ((n : ℝ) / x))
        = -∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist x / x ^ 2 := by
    rw [← hleft, hsubst, hright]
  exact neg_injective hneg

lemma putnam_1983_b5_product_identity (N : ℕ) :
    ((∏ n ∈ Finset.Icc 1 N,
        (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1))) *
      (∏ n ∈ Finset.Icc 1 N,
        ((2 * (n : ℝ) + 1) ^ 2) / (4 * (n : ℝ) * ((n : ℝ) + 1))))
      = (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) := by
  induction N with
  | zero =>
      norm_num
  | succ N ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1),
        Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1)]
      calc
        ((∏ n ∈ Finset.Icc 1 N,
            (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1))) *
          ((2 * ((N + 1 : ℕ) : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) - 1)) *
            (2 * ((N + 1 : ℕ) : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) + 1)))) *
          ((∏ n ∈ Finset.Icc 1 N,
            ((2 * (n : ℝ) + 1) ^ 2) / (4 * (n : ℝ) * ((n : ℝ) + 1))) *
            (((2 * ((N + 1 : ℕ) : ℝ) + 1) ^ 2) /
              (4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 1))))
            =
          (((∏ n ∈ Finset.Icc 1 N,
              (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1))) *
            (∏ n ∈ Finset.Icc 1 N,
              ((2 * (n : ℝ) + 1) ^ 2) / (4 * (n : ℝ) * ((n : ℝ) + 1)))) *
            (((2 * ((N + 1 : ℕ) : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) - 1)) *
              (2 * ((N + 1 : ℕ) : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) + 1))) *
              (((2 * ((N + 1 : ℕ) : ℝ) + 1) ^ 2) /
                (4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 1))))) := by
              ring
        _ = ((2 * (N : ℝ) + 1) / ((N : ℝ) + 1)) *
            (((2 * ((N + 1 : ℕ) : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) - 1)) *
              (2 * ((N + 1 : ℕ) : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) + 1))) *
              (((2 * ((N + 1 : ℕ) : ℝ) + 1) ^ 2) /
                (4 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 1)))) := by
              rw [ih]
        _ = (2 * ((N + 1 : ℕ) : ℝ) + 1) / (((N + 1 : ℕ) : ℝ) + 1) := by
              have hN0 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
              have hNm1 : 2 * ((N + 1 : ℕ) : ℝ) - 1 ≠ 0 := by
                have hge : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
                  exact_mod_cast Nat.succ_pos N
                nlinarith
              have hNp1 : 2 * ((N + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
              have hNs1 : ((N + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
              have hNold : (N : ℝ) + 1 ≠ 0 := by positivity
              field_simp [hN0, hNm1, hNp1, hNs1, hNold]
              norm_num [Nat.cast_add, Nat.cast_one]
              ring

lemma putnam_1983_b5_product_limit
    (fact : Tendsto (fun N ↦ ∏ n ∈ Finset.Icc 1 N,
      (2 * n / (2 * n - 1)) * (2 * n / (2 * n + 1)) : ℕ → ℝ)
      atTop (𝓝 (Real.pi / 2))) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
      ((2 * (n : ℝ) + 1) ^ 2) / (4 * (n : ℝ) * ((n : ℝ) + 1)))
      atTop (𝓝 (4 / Real.pi)) := by
  have hfact : Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
      (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1)))
      atTop (𝓝 (Real.pi / 2)) := by
    simpa using fact
  have hratio : Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1) / ((N : ℝ) + 1))
      atTop (𝓝 2) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) (1 : ℝ) (1 : ℝ) (2 : ℝ) (d := 1) one_ne_zero
    convert h using 1
    · ext N
      ring
    · norm_num
  have hPne : ∀ N : ℕ,
      (∏ n ∈ Finset.Icc 1 N,
        (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1))) ≠ 0 := by
    intro N
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hnge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hden₁ : 2 * (n : ℝ) - 1 ≠ 0 := by nlinarith
    have hden₂ : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    exact mul_ne_zero
      (div_ne_zero (by positivity) hden₁)
      (div_ne_zero (by positivity) hden₂)
  have hquot_eq : (fun N : ℕ => (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) /
        (∏ n ∈ Finset.Icc 1 N,
          (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1))))
      =ᶠ[atTop]
      (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
        ((2 * (n : ℝ) + 1) ^ 2) / (4 * (n : ℝ) * ((n : ℝ) + 1))) := by
    refine Eventually.of_forall ?_
    intro N
    have hid := putnam_1983_b5_product_identity N
    change ((2 * (N : ℝ) + 1) / ((N : ℝ) + 1) /
        (∏ n ∈ Finset.Icc 1 N,
          (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1))))
      = (∏ n ∈ Finset.Icc 1 N,
        ((2 * (n : ℝ) + 1) ^ 2) / (4 * (n : ℝ) * ((n : ℝ) + 1)))
    rw [← hid]
    exact mul_div_cancel_left₀ _ (hPne N)
  have hpi2 : Real.pi / 2 ≠ 0 := by positivity
  have hquot := hratio.div hfact hpi2
  have hlim : Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
        ((2 * (n : ℝ) + 1) ^ 2) / (4 * (n : ℝ) * ((n : ℝ) + 1)))
      atTop (𝓝 (2 / (Real.pi / 2))) :=
    hquot.congr' hquot_eq
  convert hlim using 1
  field_simp [Real.pi_pos.ne']
  ring_nf

lemma putnam_1983_b5_log_sum_limit
    (fact : Tendsto (fun N ↦ ∏ n ∈ Finset.Icc 1 N,
      (2 * n / (2 * n - 1)) * (2 * n / (2 * n + 1)) : ℕ → ℝ)
      atTop (𝓝 (Real.pi / 2))) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
      Real.log (((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1))))
      atTop (𝓝 (Real.log (4 / Real.pi))) := by
  have hprod := putnam_1983_b5_product_limit fact
  have hlog : Tendsto (fun N : ℕ => Real.log (∏ m ∈ Finset.Icc 1 N,
        ((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1))))
      atTop (𝓝 (Real.log (4 / Real.pi))) := by
    exact (Real.continuousAt_log (by positivity : 4 / Real.pi ≠ 0)).tendsto.comp hprod
  refine hlog.congr' (Eventually.of_forall ?_)
  intro N
  have hne : ∀ m ∈ Finset.Icc 1 N,
      ((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1)) ≠ 0 := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm1)
    positivity
  exact Real.log_prod hne

-- log (4 / Real.pi)
/--
Define $\left\lVert x \right\rVert$ as the distance from $x$ to the nearest integer. Find $\lim_{n \to \infty} \frac{1}{n} \int_{1}^{n} \left\lVert \frac{n}{x} \right\rVert \, dx$. You may assume that $\prod_{n=1}^{\infty} \frac{2n}{(2n-1)} \cdot \frac{2n}{(2n+1)} = \frac{\pi}{2}$.
-/
theorem putnam_1983_b5
(dist_fun : ℝ → ℝ)
(hdist_fun : dist_fun = fun (x : ℝ) ↦ min (x - ⌊x⌋) (⌈x⌉ - x))
(fact : Tendsto (fun N ↦ ∏ n ∈ Finset.Icc 1 N, (2 * n / (2 * n - 1)) * (2 * n / (2 * n + 1)) : ℕ → ℝ) atTop (𝓝 (Real.pi / 2)))
: (Tendsto (fun n ↦ (1 / n) * ∫ x in (1)..n, dist_fun (n / x) : ℕ → ℝ) atTop (𝓝 ((log (4 / Real.pi)) : ℝ ))) := by
  subst dist_fun
  change Tendsto
    (fun n : ℕ => (1 / (n : ℝ)) *
      ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist ((n : ℝ) / x))
    atTop (𝓝 (Real.log (4 / Real.pi)))
  have hlog := putnam_1983_b5_log_sum_limit fact
  have hcomp := hlog.comp (tendsto_sub_atTop_nat 1)
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  symm
  calc
    (1 / (n : ℝ)) * ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist ((n : ℝ) / x)
        = ∫ x in (1 : ℝ)..(n : ℝ), putnam_1983_b5_dist x / x ^ 2 := by
          exact putnam_1983_b5_scaled_integral n hn
    _ = ∑ m ∈ Finset.Icc 1 (n - 1),
          Real.log (((2 * (m : ℝ) + 1) ^ 2) / (4 * (m : ℝ) * ((m : ℝ) + 1))) := by
          have hsum := putnam_1983_b5_integral_sum (n - 1)
          simpa [Nat.sub_add_cancel hn] using hsum
