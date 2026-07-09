import Mathlib

open Polynomial Filter Topology

abbrev putnam_1976_b1_solution : ℕ × ℕ := (4, 1)

namespace Putnam1976B1

open Finset

private lemma summable_main_series :
    Summable (fun m : ℕ => if m = 0 then 0 else
      (1 : ℝ) / ((m + 1 : ℕ) * (2 * m + 1 : ℕ))) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((summable_nat_add_iff 1 (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2)).mpr
      (by simp))
  · split_ifs <;> positivity
  · by_cases hm : m = 0
    · simp [hm]
    · have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hden : ((m + 1 : ℕ) : ℝ) ^ 2 ≤
          ((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℝ) := by
        norm_num
        nlinarith [sq_nonneg (m : ℝ), hmpos]
      have hle : (1 : ℝ) / ((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℝ) ≤
          1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        gcongr
      simpa [hm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, pow_two] using hle

private lemma main_series_partial (M : ℕ) :
    ∑ m ∈ range (M + 1), (if m = 0 then 0 else
      (1 : ℝ) / ((m + 1 : ℕ) * (2 * m + 1 : ℕ))) =
      2 * ((harmonic (2 * M + 2) : ℝ) - (harmonic (M + 1) : ℝ)) - 1 := by
  induction M with
  | zero =>
      simp [harmonic_succ, harmonic_zero]
  | succ M ih =>
      rw [sum_range_succ, ih]
      rw [show 2 * (M + 1) + 2 = (2 * M + 2) + 1 + 1 by omega]
      rw [harmonic_succ ((2 * M + 2) + 1), harmonic_succ (2 * M + 2)]
      rw [show M + 1 + 1 = (M + 1) + 1 by rfl]
      rw [harmonic_succ (M + 1)]
      simp
      field_simp
      ring

private lemma main_series_partial_tendsto :
    Tendsto (fun M : ℕ =>
      2 * ((harmonic (2 * M + 2) : ℝ) - (harmonic (M + 1) : ℝ)) - 1)
      atTop (𝓝 (Real.log 4 - 1)) := by
  have h2M : Tendsto (fun M : ℕ => 2 * M + 2) atTop atTop := by
    exact tendsto_atTop_mono (fun M : ℕ => (show M ≤ 2 * M + 2 by omega)) tendsto_id
  have hM : Tendsto (fun M : ℕ => M + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun M : ℕ => (show M ≤ M + 1 by omega)) tendsto_id
  have hA : Tendsto
      (fun M : ℕ => (harmonic (2 * M + 2) : ℝ) - Real.log (2 * M + 2))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul]
      using Real.tendsto_harmonic_sub_log.comp h2M
  have hB : Tendsto
      (fun M : ℕ => (harmonic (M + 1) : ℝ) - Real.log (M + 1))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul]
      using Real.tendsto_harmonic_sub_log.comp hM
  have hdiff : Tendsto (fun M : ℕ =>
      ((harmonic (2 * M + 2) : ℝ) - Real.log (2 * M + 2)) -
        ((harmonic (M + 1) : ℝ) - Real.log (M + 1))) atTop (𝓝 0) := by
    simpa using hA.sub hB
  have hlog (M : ℕ) :
      Real.log (2 * M + 2 : ℝ) - Real.log (M + 1 : ℝ) = Real.log 2 := by
    have hpos : (M + 1 : ℝ) ≠ 0 := by positivity
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    rw [show (2 * M + 2 : ℝ) = 2 * (M + 1 : ℝ) by ring]
    rw [Real.log_mul htwo hpos]
    ring
  have hconv : Tendsto (fun M : ℕ =>
      2 * ((((harmonic (2 * M + 2) : ℝ) - Real.log (2 * M + 2)) -
        ((harmonic (M + 1) : ℝ) - Real.log (M + 1))) + Real.log 2) - 1)
      atTop (𝓝 (2 * Real.log 2 - 1)) := by
    simpa using ((hdiff.add tendsto_const_nhds).const_mul 2).sub tendsto_const_nhds
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4]
  refine hconv.congr' ?_
  filter_upwards with M
  rw [← hlog M]
  ring

private lemma main_series_hasSum :
    HasSum (fun m : ℕ => if m = 0 then 0 else
      (1 : ℝ) / ((m + 1 : ℕ) * (2 * m + 1 : ℕ)))
      (Real.log 4 - 1) := by
  rw [summable_main_series.hasSum_iff_tendsto_nat]
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  refine main_series_partial_tendsto.congr' ?_
  filter_upwards with M
  exact (main_series_partial M).symm

private lemma nat_floor_diff_indicator (n k : ℕ) (hk : 0 < k) :
    (2 * n) / k - 2 * (n / k) = if k ≤ 2 * (n % k) then 1 else 0 := by
  have hdecomp : (2 * n) / k = 2 * (n / k) + (2 * (n % k)) / k := by
    calc
      (2 * n) / k = (2 * (k * (n / k) + n % k)) / k := by
        rw [Nat.div_add_mod]
      _ = (2 * (n % k) + k * (2 * (n / k))) / k := by ring_nf
      _ = (2 * (n % k)) / k + 2 * (n / k) := by
        rw [Nat.add_mul_div_left _ _ hk]
      _ = 2 * (n / k) + (2 * (n % k)) / k := by omega
  rw [hdecomp]
  have hmod : n % k < k := Nat.mod_lt n hk
  by_cases h : k ≤ 2 * (n % k)
  · have hlo : 1 * k ≤ 2 * (n % k) := by simpa using h
    have hlt : 2 * (n % k) < (1 + 1) * k := by omega
    have hdiv : (2 * (n % k)) / k = 1 := Nat.div_eq_of_lt_le hlo hlt
    simp [h, hdiv]
  · have hlt : 2 * (n % k) < k := by omega
    have hdiv : (2 * (n % k)) / k = 0 := Nat.div_eq_of_lt hlt
    simp [h, hdiv]

private lemma quotient_hit_iff (n m k : ℕ) (hk : 0 < k) (hm : 0 < m) :
    n / k = m ∧ k ≤ 2 * (n % k) ↔
      n / (m + 1) < k ∧ k ≤ (2 * n) / (2 * m + 1) := by
  constructor
  · rintro ⟨hq, hc⟩
    have hlt_div : n / k < m + 1 := by omega
    have hlt : n < (m + 1) * k := (Nat.div_lt_iff_lt_mul hk).mp hlt_div
    have hlower : n / (m + 1) < k := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos m)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
    have hdecomp : k * (n / k) + n % k = n := Nat.div_add_mod n k
    have hupper_mul : (2 * m + 1) * k ≤ 2 * n := by
      rw [← hq]
      nlinarith
    have hupper : k ≤ (2 * n) / (2 * m + 1) := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * m + 1)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hupper_mul
    exact ⟨hlower, hupper⟩
  · rintro ⟨hlower, hupper⟩
    have hlt : n < (m + 1) * k := by
      have := (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp hlower
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hupper_mul : (2 * m + 1) * k ≤ 2 * n := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * m + 1)).mp hupper
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hlo : m * k ≤ n := by nlinarith
    have hq : n / k = m := Nat.div_eq_of_lt_le hlo hlt
    have hdecomp : k * (n / k) + n % k = n := Nat.div_add_mod n k
    have hc : k ≤ 2 * (n % k) := by
      rw [hq] at hdecomp
      nlinarith
    exact ⟨hq, hc⟩

private lemma quotient_hit_card (n m : ℕ) (hm : 0 < m) :
    ((Finset.Icc 1 n).filter (fun k => n / k = m ∧ k ≤ 2 * (n % k))).card =
      (2 * n) / (2 * m + 1) - n / (m + 1) := by
  have hset : (Finset.Icc 1 n).filter (fun k => n / k = m ∧ k ≤ 2 * (n % k)) =
      Finset.Ioc (n / (m + 1)) ((2 * n) / (2 * m + 1)) := by
    ext k
    constructor
    · intro hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      rw [Finset.mem_Ioc]
      exact (quotient_hit_iff n m k (by omega) hm).mp hk.2
    · intro hk
      rw [Finset.mem_Ioc] at hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hkpos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) hk.1
      have hkle : k ≤ n := by
        exact hk.2.trans
          (Nat.div_le_of_le_mul (by nlinarith : 2 * n ≤ (2 * m + 1) * n))
      exact ⟨⟨Nat.succ_le_of_lt hkpos, hkle⟩,
        (quotient_hit_iff n m k hkpos hm).mpr hk⟩
  rw [hset, Nat.card_Ioc]

private lemma nat_sum_eq_indicator_card (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ((2 * n) / k - 2 * (n / k))) =
      ((Finset.Icc 1 n).filter (fun k => k ≤ 2 * (n % k))).card := by
  calc
    (∑ k ∈ Finset.Icc 1 n, ((2 * n) / k - 2 * (n / k)))
        = ∑ k ∈ Finset.Icc 1 n, (if k ≤ 2 * (n % k) then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [Finset.mem_Icc] at hk
            exact nat_floor_diff_indicator n k (by omega)
    _ = ((Finset.Icc 1 n).filter (fun k => k ≤ 2 * (n % k))).card := by
            rw [Finset.card_eq_sum_ones]
            simp

private lemma nat_sum_eq_quotient_counts (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ((2 * n) / k - 2 * (n / k))) =
      ∑ m ∈ Finset.Icc 1 n, ((2 * n) / (2 * m + 1) - n / (m + 1)) := by
  rw [nat_sum_eq_indicator_card]
  let s := (Finset.Icc 1 n).filter (fun k => k ≤ 2 * (n % k))
  have hmap : (s : Set ℕ).MapsTo (fun k => n / k) (Finset.Icc 1 n : Set ℕ) := by
    intro k hk
    have hkI : k ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hk).1
    rw [Finset.mem_Icc] at hkI
    have hkpos : 0 < k := by omega
    simpa [Finset.mem_Icc] using
      ⟨(Nat.one_le_div_iff hkpos).mpr hkI.2, Nat.div_le_self n k⟩
  have hpart := Finset.card_eq_sum_card_fiberwise
    (f := fun k => n / k) (s := s) (t := Finset.Icc 1 n) hmap
  rw [hpart]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_Icc] at hm
  have hmpos : 0 < m := by omega
  have hfilter : {a ∈ s | (fun k => n / k) a = m} =
      (Finset.Icc 1 n).filter (fun k => n / k = m ∧ k ≤ 2 * (n % k)) := by
    ext k
    simp [s]
    aesop
  rw [hfilter, quotient_hit_card n m hmpos]

private lemma int_floor_diff_eq_nat (n j : ℕ) (hj : 0 < j) :
    (Int.floor (((2 * n : ℕ) : ℤ) / (j : ℤ)) -
        2 * Int.floor (((n : ℕ) : ℤ) / (j : ℤ))) =
      (((2 * n) / j - 2 * (n / j) : ℕ) : ℤ) := by
  have hdecomp : (2 * n) / j = 2 * (n / j) + (2 * (n % j)) / j := by
    calc
      (2 * n) / j = (2 * (j * (n / j) + n % j)) / j := by
        rw [Nat.div_add_mod]
      _ = (2 * (n % j) + j * (2 * (n / j))) / j := by ring_nf
      _ = (2 * (n % j)) / j + 2 * (n / j) := by
        rw [Nat.add_mul_div_left _ _ hj]
      _ = 2 * (n / j) + (2 * (n % j)) / j := by omega
  have hle : 2 * (n / j) ≤ (2 * n) / j := by
    rw [hdecomp]
    exact Nat.le_add_right _ _
  rw [Nat.cast_sub hle]
  simp

private lemma int_sum_eq_nat_sum (n : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ),
      (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) =
    ∑ k ∈ Finset.Icc 1 n, (((2 * n) / k - 2 * (n / k) : ℕ) : ℤ) := by
  refine Finset.sum_nbij (fun z : ℤ => z.toNat) ?hi ?hinj ?hsurj ?hterm
  · intro z hz
    change z.toNat ∈ Finset.Icc 1 n
    have hzI : (1 : ℤ) ≤ z ∧ z ≤ (n : ℤ) := by simpa [Finset.mem_Icc] using hz
    have hz0 : 0 ≤ z := by omega
    have hzt : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have h1z : (1 : ℤ) ≤ (z.toNat : ℤ) := by simpa [hzt] using hzI.1
    have hzn : (z.toNat : ℤ) ≤ (n : ℤ) := by simpa [hzt] using hzI.2
    rw [Finset.mem_Icc]
    exact ⟨by exact_mod_cast h1z, by exact_mod_cast hzn⟩
  · intro z1 hz1 z2 hz2 h
    have hz1I : (1 : ℤ) ≤ z1 ∧ z1 ≤ (n : ℤ) := by
      simpa [Finset.mem_Icc] using hz1
    have hz2I : (1 : ℤ) ≤ z2 ∧ z2 ≤ (n : ℤ) := by
      simpa [Finset.mem_Icc] using hz2
    have hz10 : 0 ≤ z1 := by omega
    have hz20 : 0 ≤ z2 := by omega
    rw [← Int.toNat_of_nonneg hz10, ← Int.toNat_of_nonneg hz20]
    exact_mod_cast h
  · intro j hj
    have hjI : 1 ≤ j ∧ j ≤ n := by simpa [Finset.mem_Icc] using hj
    refine ⟨(j : ℤ), ?_, ?_⟩
    · have h1 : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hjI.1
      have h2 : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hjI.2
      change (j : ℤ) ∈ Finset.Icc (1 : ℤ) (n : ℤ)
      rw [Finset.mem_Icc]
      exact ⟨h1, h2⟩
    · simp
  · intro z hz
    have hzI : (1 : ℤ) ≤ z ∧ z ≤ (n : ℤ) := by simpa [Finset.mem_Icc] using hz
    have hz0 : 0 ≤ z := by omega
    have hzt : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hj : 0 < z.toNat := by
      have hzpos : (0 : ℤ) < (z.toNat : ℤ) := by
        simpa [hzt] using (by omega : (0 : ℤ) < z)
      exact_mod_cast hzpos
    simpa [hzt] using int_floor_diff_eq_nat n z.toNat hj

private lemma int_sum_eq_quotient_counts (n : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ),
      (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) =
    (∑ m ∈ Finset.Icc 1 n,
      ((2 * n) / (2 * m + 1) - n / (m + 1)) : ℕ) := by
  rw [int_sum_eq_nat_sum]
  exact_mod_cast nat_sum_eq_quotient_counts n

private lemma quotient_count_tail_le (n M : ℕ) :
    ∑ m ∈ Finset.Icc (M + 1) n,
      ((2 * n) / (2 * m + 1) - n / (m + 1)) ≤ n / (M + 1) := by
  let s := (Finset.Icc 1 n).filter (fun k => k ≤ 2 * (n % k))
  have hsumfib : ∑ m ∈ Finset.Icc (M + 1) n, #{k ∈ s | n / k = m} =
      #{k ∈ s | n / k ∈ Finset.Icc (M + 1) n} := by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter
      (s := s) (t := Finset.Icc (M + 1) n) (g := fun k => n / k))
  calc
    ∑ m ∈ Finset.Icc (M + 1) n,
        ((2 * n) / (2 * m + 1) - n / (m + 1))
        = ∑ m ∈ Finset.Icc (M + 1) n, #{k ∈ s | n / k = m} := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [Finset.mem_Icc] at hm
            have hmpos : 0 < m := by omega
            have hfilter : {k ∈ s | n / k = m} =
                (Finset.Icc 1 n).filter (fun k => n / k = m ∧ k ≤ 2 * (n % k)) := by
              ext k
              simp [s]
              aesop
            rw [hfilter, quotient_hit_card n m hmpos]
    _ = #{k ∈ s | n / k ∈ Finset.Icc (M + 1) n} := hsumfib
    _ ≤ #((Finset.Icc 1 n).filter (fun k => M + 1 ≤ n / k)) := by
          apply Finset.card_le_card
          intro k hk
          rw [Finset.mem_filter] at hk ⊢
          rcases hk with ⟨hks, hkq⟩
          have hkI : k ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hks).1
          rw [Finset.mem_Icc] at hkq
          exact ⟨hkI, hkq.1⟩
    _ ≤ #(Finset.Icc 1 (n / (M + 1))) := by
          apply Finset.card_le_card
          intro k hk
          rw [Finset.mem_filter, Finset.mem_Icc] at hk
          rw [Finset.mem_Icc]
          have hkpos : 0 < k := by omega
          have hmul : (M + 1) * k ≤ n :=
            (Nat.le_div_iff_mul_le hkpos).mp hk.2
          have hle : k ≤ n / (M + 1) := by
            rw [Nat.le_div_iff_mul_le (Nat.succ_pos M)]
            simpa [mul_comm] using hmul
          exact ⟨hk.1.1, hle⟩
    _ = n / (M + 1) := by
          rw [Nat.card_Icc]
          simp

private lemma quotient_count_le (n m : ℕ) :
    n / (m + 1) ≤ (2 * n) / (2 * m + 1) := by
  rw [← Nat.mul_div_mul_left n (m + 1) (by decide : 0 < 2)]
  exact Nat.div_le_div_left
    (by omega : 2 * m + 1 ≤ 2 * (m + 1)) (by omega : 0 < 2 * m + 1)

private lemma tendsto_nat_div_linear (a d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => (((a * n) / d : ℕ) : ℝ) / n)
      atTop (𝓝 ((a : ℝ) / d)) := by
  have hbase : Tendsto (fun x : ℝ => (⌊((a : ℝ) / d) * x⌋₊ : ℝ) / x)
      atTop (𝓝 ((a : ℝ) / d)) := by
    exact tendsto_nat_floor_mul_div_atTop (a := (a : ℝ) / d) (by positivity)
  have hcomp := hbase.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine hcomp.congr' ?_
  filter_upwards with n
  change (↑⌊((a : ℝ) / d) * (n : ℝ)⌋₊ : ℝ) / (n : ℝ) =
    (((a * n) / d : ℕ) : ℝ) / (n : ℝ)
  have harg : ((a : ℝ) / d) * (n : ℝ) = ((a * n : ℕ) : ℝ) / (d : ℝ) := by
    field_simp [show (d : ℝ) ≠ 0 by positivity]
    norm_num [Nat.cast_mul]
  rw [harg, Nat.floor_div_eq_div]

private lemma tendsto_count_fixed (m : ℕ) :
    Tendsto (fun n : ℕ =>
      ((((2 * n) / (2 * m + 1) - n / (m + 1) : ℕ) : ℝ) / n))
      atTop (𝓝 ((1 : ℝ) / (((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℕ) : ℝ))) := by
  have h1 : Tendsto (fun n : ℕ => (((2 * n) / (2 * m + 1) : ℕ) : ℝ) / n)
      atTop (𝓝 ((2 : ℝ) / (2 * m + 1 : ℕ))) := by
    simpa using tendsto_nat_div_linear 2 (2 * m + 1) (by omega)
  have h2 : Tendsto (fun n : ℕ => ((n / (m + 1) : ℕ) : ℝ) / n)
      atTop (𝓝 ((1 : ℝ) / (m + 1 : ℕ))) := by
    simpa using tendsto_nat_div_linear 1 (m + 1) (by omega)
  have hsub := h1.sub h2
  have hlim : (2 : ℝ) / (2 * m + 1 : ℕ) - (1 : ℝ) / (m + 1 : ℕ) =
      (1 : ℝ) / (((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℕ) : ℝ) := by
    field_simp [show ((m + 1 : ℕ) : ℝ) ≠ 0 by positivity,
      show ((2 * m + 1 : ℕ) : ℝ) ≠ 0 by positivity]
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  rw [← hlim]
  refine hsub.congr' ?_
  filter_upwards with n
  rw [Nat.cast_sub (quotient_count_le n m)]
  ring

private lemma partial_quotient_counts_tendsto (M : ℕ) :
    Tendsto (fun n : ℕ => ((1 : ℝ) / n) *
      ((∑ m ∈ Finset.Icc 1 M,
        ((2 * n) / (2 * m + 1) - n / (m + 1)) : ℕ) : ℝ))
      atTop
      (𝓝 (∑ m ∈ Finset.Icc 1 M,
        (1 : ℝ) / (((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℕ) : ℝ))) := by
  have hsum : Tendsto (fun n : ℕ =>
      ∑ m ∈ Finset.Icc 1 M,
        ((((2 * n) / (2 * m + 1) - n / (m + 1) : ℕ) : ℝ) / n))
      atTop
      (𝓝 (∑ m ∈ Finset.Icc 1 M,
        (1 : ℝ) / (((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℕ) : ℝ))) := by
    refine tendsto_finset_sum _ ?_
    intro m hm
    exact tendsto_count_fixed m
  refine hsum.congr' ?_
  filter_upwards with n
  rw [← Finset.sum_div, Nat.cast_sum]
  ring

private lemma sum_range_if_zero_eq_Icc (M : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (M + 1), (if i = 0 then 0 else f i)) =
      ∑ i ∈ Finset.Icc 1 M, f i := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      simp

private lemma series_Icc_tendsto :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
      (1 : ℝ) / (((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℕ) : ℝ))
      atTop (𝓝 (Real.log 4 - 1)) := by
  have hM : Tendsto (fun M : ℕ => M + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun M : ℕ => (show M ≤ M + 1 by omega)) tendsto_id
  have h := main_series_hasSum.tendsto_sum_nat.comp hM
  refine h.congr' ?_
  filter_upwards with M
  simpa [Nat.cast_mul] using sum_range_if_zero_eq_Icc M
    (fun m => (1 : ℝ) / (((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℕ) : ℝ))

private lemma quotient_counts_tendsto :
    Tendsto (fun n : ℕ => ((1 : ℝ) / n) *
      ((∑ m ∈ Finset.Icc 1 n,
        ((2 * n) / (2 * m + 1) - n / (m + 1)) : ℕ) : ℝ))
      atTop (𝓝 (Real.log 4 - 1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hseries_event := (Metric.tendsto_nhds.mp series_Icc_tendsto) (ε / 3) hε3
  have hMtop : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun M : ℕ => (show M ≤ M + 1 by omega)) tendsto_id)
  have hinv : Tendsto (fun M : ℕ => (1 : ℝ) / (M + 1 : ℕ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hMtop
  have htail_event := (Metric.tendsto_nhds.mp hinv) (ε / 3) hε3
  rcases (hseries_event.and htail_event).exists with ⟨M, hMseries, hMtail⟩
  have hMtail' : (1 : ℝ) / (M + 1 : ℕ) < ε / 3 := by
    have hposM : 0 < (M : ℝ) + 1 := by positivity
    simpa [Real.dist_eq, one_div, abs_inv, abs_of_pos hposM]
      using hMtail
  have hpartial := (Metric.tendsto_nhds.mp (partial_quotient_counts_tendsto M)) (ε / 3) hε3
  filter_upwards [hpartial, eventually_ge_atTop (M + 1)] with n hnclose hnlarge
  let q : ℕ → ℕ → ℕ := fun n m => (2 * n) / (2 * m + 1) - n / (m + 1)
  let part : ℝ := ((1 : ℝ) / n) * ((∑ m ∈ Finset.Icc 1 M, q n m) : ℝ)
  let tail : ℝ := ((1 : ℝ) / n) * ((∑ m ∈ Finset.Icc (M + 1) n, q n m) : ℝ)
  let sM : ℝ := ∑ m ∈ Finset.Icc 1 M,
    (1 : ℝ) / (((m + 1 : ℕ) * (2 * m + 1 : ℕ) : ℕ) : ℝ)
  have hnpos : 0 < n := by omega
  have hsplitNat : (∑ m ∈ Finset.Icc 1 n, q n m) =
      (∑ m ∈ Finset.Icc 1 M, q n m) + ∑ m ∈ Finset.Icc (M + 1) n, q n m := by
    have hUnion : Finset.Icc 1 n = Finset.Icc 1 M ∪ Finset.Icc (M + 1) n := by
      ext m
      simp [Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) n) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      rw [Finset.mem_Icc] at hm1 hm2
      omega
    rw [hUnion, Finset.sum_union hdisj]
  have hfull : ((1 : ℝ) / n) *
        ((∑ m ∈ Finset.Icc 1 n, q n m) : ℝ) = part + tail := by
    have hsplitReal : (∑ m ∈ Finset.Icc 1 n, (q n m : ℝ)) =
        (∑ m ∈ Finset.Icc 1 M, (q n m : ℝ)) +
          ∑ m ∈ Finset.Icc (M + 1) n, (q n m : ℝ) := by
      exact_mod_cast hsplitNat
    simp only [part, tail]
    rw [hsplitReal]
    ring
  have htail_nonneg : 0 ≤ tail := by
    exact mul_nonneg (by positivity) (by positivity)
  have htail_bound : tail ≤ (1 : ℝ) / (M + 1 : ℕ) := by
    have htail_nat : (∑ m ∈ Finset.Icc (M + 1) n, q n m) ≤ n / (M + 1) :=
      quotient_count_tail_le n M
    have htail_cast : (∑ m ∈ Finset.Icc (M + 1) n, (q n m : ℝ)) ≤
        ((n / (M + 1) : ℕ) : ℝ) := by exact_mod_cast htail_nat
    have hfloor : (((n / (M + 1) : ℕ) : ℝ) / n) ≤ (1 : ℝ) / (M + 1 : ℕ) := by
      have hmul : ((n / (M + 1)) * (M + 1) : ℕ) ≤ n :=
        Nat.div_mul_le_self n (M + 1)
      have hmulR : (((n / (M + 1) : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) ≤
          (n : ℝ)) := by exact_mod_cast hmul
      field_simp [show (n : ℝ) ≠ 0 by positivity,
        show (((M + 1 : ℕ) : ℝ)) ≠ 0 by positivity]
      nlinarith
    have htail_div : tail ≤ (((n / (M + 1) : ℕ) : ℝ) / n) := by
      simp only [tail]
      change (1 : ℝ) / n * ((∑ m ∈ Finset.Icc (M + 1) n, q n m) : ℝ) ≤
        (((n / (M + 1) : ℕ) : ℝ) / n)
      rw [one_div, mul_comm]
      exact div_le_div_of_nonneg_right htail_cast (by positivity)
    exact htail_div.trans hfloor
  have htail_lt : tail < ε / 3 := htail_bound.trans_lt hMtail'
  have htri₁ : dist (part + tail) (Real.log 4 - 1) ≤
      dist (part + tail) (sM + tail) + dist (sM + tail) (Real.log 4 - 1) :=
    dist_triangle _ _ _
  have htri₂ : dist (sM + tail) (Real.log 4 - 1) ≤
      dist (sM + tail) sM + dist sM (Real.log 4 - 1) :=
    dist_triangle _ _ _
  have hnclose' : dist part sM < ε / 3 := by
    simpa [part, sM] using hnclose
  have hMseries' : dist sM (Real.log 4 - 1) < ε / 3 := by
    simpa [sM] using hMseries
  rw [Nat.cast_sum]
  change dist (((1 : ℝ) / n) * (∑ m ∈ Finset.Icc 1 n, (q n m : ℝ)))
    (Real.log 4 - 1) < ε
  calc
    dist (((1 : ℝ) / n) * (∑ m ∈ Finset.Icc 1 n, (q n m : ℝ)))
        (Real.log 4 - 1)
        = dist (part + tail) (Real.log 4 - 1) := by rw [hfull]
    _ ≤ dist (part + tail) (sM + tail) + dist (sM + tail) sM +
        dist sM (Real.log 4 - 1) := by linarith
    _ = dist part sM + tail + dist sM (Real.log 4 - 1) := by
        simp [Real.dist_eq, abs_of_nonneg htail_nonneg]
    _ < ε := by
        calc
          dist part sM + tail + dist sM (Real.log 4 - 1)
              < ε / 3 + ε / 3 + ε / 3 := by
                gcongr
          _ = ε := by ring

end Putnam1976B1

/--
Find $$\lim_{n \to \infty} \frac{1}{n} \sum_{k=1}^{n}\left(\left\lfloor \frac{2n}{k} \right\rfloor - 2\left\lfloor \frac{n}{k} \right\rfloor\right).$$ Your answer should be in the form $\ln(a) - b$, where $a$ and $b$ are positive integers.
-/
theorem putnam_1976_b1
: Tendsto (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n, (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) atTop
(𝓝 (Real.log putnam_1976_b1_solution.1 - putnam_1976_b1_solution.2)) :=
by
  have hbase := Putnam1976B1.quotient_counts_tendsto
  have htarget :
      Tendsto (fun n : ℕ => ((1 : ℝ) / n) *
        ∑ k ∈ Finset.Icc (1 : ℤ) n,
          (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k)))
        atTop (𝓝 (Real.log 4 - 1)) := by
    refine hbase.congr' ?_
    filter_upwards with n
    rw [Putnam1976B1.int_sum_eq_quotient_counts n]
    norm_num
  simpa [putnam_1976_b1_solution] using htarget
