import Mathlib

open Filter Topology

theorem putnam_2015_b6_neg_one_rpow_nat {k : ℕ} (hk : 1 ≤ k) :
    (-1 : ℝ) ^ ((k : ℝ) - 1) = (-1 : ℝ) ^ (k - 1) := by
  rw [Real.rpow_def_of_neg (by norm_num : (-1 : ℝ) < 0)]
  have hcast : (↑k - 1 : ℝ) = (↑(k - 1) : ℝ) := by
    norm_num [Nat.cast_sub hk]
  rw [hcast]
  simp [Real.log_neg_eq_log, Real.cos_nat_mul_pi]

theorem putnam_2015_b6_sqrt_iff {j m : ℕ} (hj : 0 < j) :
    ((j : ℝ) < Real.sqrt (2 * (j * m))) ↔ j < 2 * m := by
  rw [Real.lt_sqrt (Nat.cast_nonneg j)]
  constructor
  · intro h
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj
    norm_num [Nat.cast_mul, pow_two] at h
    have : (j : ℝ) < 2 * (m : ℝ) := by nlinarith
    exact_mod_cast this
  · intro h
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj
    have h' : (j : ℝ) < 2 * (m : ℝ) := by exact_mod_cast h
    norm_num [Nat.cast_mul, pow_two]
    nlinarith

theorem putnam_2015_b6_neg_one_pow_mul_sub_one {j m : ℕ} (hj : Odd j) (hm : 0 < m) :
    (-1 : ℝ) ^ (j * m - 1) = (-1 : ℝ) ^ (m - 1) := by
  apply neg_one_pow_congr
  have hle1 : 1 ≤ j * m := by
    have hjpos : 0 < j := Odd.pos hj
    exact Nat.succ_le_of_lt (Nat.mul_pos hjpos hm)
  have hle2 : 1 ≤ m := hm
  rw [Nat.even_sub' hle1, Nat.even_sub' hle2]
  simp [Nat.odd_mul, hj]

theorem putnam_2015_b6_card
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    {k : ℕ} (hk : 0 < k) :
    A k = ((Nat.divisors k).filter
      (fun j : ℕ => Odd j ∧ (j : ℝ) < Real.sqrt (2 * k))).card := by
  classical
  let s : Set ℕ := {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}
  have hfin : s.Finite := by
    refine (Nat.divisors k).finite_toSet.subset ?_
    intro j hj
    simp only [s, Set.mem_setOf_eq] at hj
    exact Nat.mem_divisors.mpr ⟨hj.2.1, ne_of_gt hk⟩
  have hcard : A k = hfin.toFinset.card := by
    apply ENat.coe_inj.mp
    rw [hA k hk]
    exact hfin.encard_eq_coe_toFinset_card
  rw [hcard]
  congr 1
  ext j
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · intro hj
    exact ⟨⟨hj.2.1, ne_of_gt hk⟩, hj.1, hj.2.2⟩
  · intro hj
    exact ⟨hj.2.1, hj.1.1, hj.2.2⟩

noncomputable def putnam_2015_b6_oddH (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range n, (1 : ℝ) / (2 * r + 1)

noncomputable def putnam_2015_b6_b (n : ℕ) : ℝ :=
  putnam_2015_b6_oddH (n + 1) / (n + 1)

noncomputable def putnam_2015_b6_c (K n : ℕ) : ℝ :=
  if n < K then
    (∑ r ∈ Finset.range (n + 1),
      if (2 * r + 1) * (n + 1) ≤ K then (1 : ℝ) / (2 * r + 1) else 0) / (n + 1)
  else 0

theorem putnam_2015_b6_b_nonneg (n : ℕ) : 0 ≤ putnam_2015_b6_b n := by
  unfold putnam_2015_b6_b putnam_2015_b6_oddH
  positivity

theorem putnam_2015_b6_c_nonneg (K n : ℕ) : 0 ≤ putnam_2015_b6_c K n := by
  unfold putnam_2015_b6_c
  split_ifs <;> positivity

theorem putnam_2015_b6_c_le_b (K n : ℕ) :
    putnam_2015_b6_c K n ≤ putnam_2015_b6_b n := by
  unfold putnam_2015_b6_c putnam_2015_b6_b putnam_2015_b6_oddH
  split_ifs
  · gcongr with r hr
    by_cases h : (2 * r + 1) * (n + 1) ≤ K
    · simp [h]
    · simp [h]
      positivity
  · positivity

theorem putnam_2015_b6_oddH_le_harmonic (n : ℕ) :
    putnam_2015_b6_oddH n ≤ (harmonic n : ℝ) := by
  unfold putnam_2015_b6_oddH harmonic
  simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  gcongr with r hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le r
  have hden : (r : ℝ) + 1 ≤ (2 : ℝ) * (r : ℝ) + 1 := by nlinarith
  simpa [Nat.cast_add, Nat.cast_one] using
    (one_div_le_one_div_of_le (show (0 : ℝ) < (r : ℝ) + 1 by positivity) hden)

theorem putnam_2015_b6_b_antitone : Antitone putnam_2015_b6_b := by
  refine antitone_nat_of_succ_le ?_
  intro n
  unfold putnam_2015_b6_b putnam_2015_b6_oddH
  rw [Finset.sum_range_succ]
  let H : ℝ := ∑ r ∈ Finset.range (n + 1), (1 : ℝ) / (2 * r + 1)
  have hH : 1 ≤ H := by
    dsimp [H]
    have hnonneg :
        ∀ r ∈ Finset.range (n + 1), (0 : ℝ) ≤ (1 : ℝ) / (2 * r + 1) := by
      intro r hr
      positivity
    simpa using (Finset.single_le_sum hnonneg (by simp : 0 ∈ Finset.range (n + 1)))
  have hpos3 : (0 : ℝ) < 2 * (n : ℝ) + 3 := by positivity
  have hkey : ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) ≤ H := by
    have : ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) ≤ 1 := by
      rw [div_le_one hpos3]
      nlinarith
    exact this.trans hH
  change (H + 1 / (2 * ↑(n + 1) + 1)) / (↑(n + 1) + 1) ≤ H / (↑n + 1)
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [div_le_div_iff₀]
  · field_simp [hpos3.ne']
    nlinarith
  · positivity
  · positivity

theorem putnam_2015_b6_b_tendsto_zero :
    Tendsto putnam_2015_b6_b atTop (𝓝 0) := by
  have hlim :
      Tendsto (fun n : ℕ => (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop hn
    have hlog :
        Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
          atTop (𝓝 0) := by
      have hreal : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
        simpa [one_mul, pow_one] using
          Real.tendsto_pow_log_div_mul_add_atTop (a := 1) (b := 0) (n := 1) one_ne_zero
      exact hreal.comp hn
    have hsum := h1.add hlog
    convert hsum using 1
    · ext n
      ring
    · simp
  apply squeeze_zero
  · exact putnam_2015_b6_b_nonneg
  · intro n
    unfold putnam_2015_b6_b
    have hodd := putnam_2015_b6_oddH_le_harmonic (n + 1)
    have hharm : ((harmonic (n + 1) : ℚ) : ℝ) ≤ 1 + Real.log ((n : ℝ) + 1) := by
      simpa [Nat.cast_add, Nat.cast_one] using (harmonic_le_one_add_log (n + 1))
    have hnum : putnam_2015_b6_oddH (n + 1) ≤ 1 + Real.log ((n : ℝ) + 1) :=
      hodd.trans hharm
    exact div_le_div_of_nonneg_right hnum (by positivity)
  · exact hlim

theorem putnam_2015_b6_c_antitone (K : ℕ) : Antitone (putnam_2015_b6_c K) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  by_cases hnext : n + 1 < K
  · have hn : n < K := Nat.lt_trans (Nat.lt_succ_self n) hnext
    unfold putnam_2015_b6_c
    simp [hnext, hn]
    let S : ℝ := ∑ r ∈ Finset.range (n + 1),
      if (2 * r + 1) * (n + 1) ≤ K then (2 * (r : ℝ) + 1)⁻¹ else 0
    let T : ℝ := ∑ r ∈ Finset.range (n + 1 + 1),
      if (2 * r + 1) * (n + 1 + 1) ≤ K then (2 * (r : ℝ) + 1)⁻¹ else 0
    change T / (↑n + 1 + 1) ≤ S / (↑n + 1)
    have hSge : 1 ≤ S := by
      dsimp [S]
      have hnonneg : ∀ r ∈ Finset.range (n + 1),
          (0 : ℝ) ≤ if (2 * r + 1) * (n + 1) ≤ K
            then (2 * (r : ℝ) + 1)⁻¹ else 0 := by
        intro r hr
        split_ifs <;> positivity
      simpa [hn] using (Finset.single_le_sum hnonneg (by simp : 0 ∈ Finset.range (n + 1)))
    have hTle : T ≤ S + 1 / (2 * (n : ℝ) + 3) := by
      dsimp [T, S]
      rw [Finset.sum_range_succ]
      have hsum : (∑ r ∈ Finset.range (n + 1),
          if (2 * r + 1) * (n + 1 + 1) ≤ K then (2 * (r : ℝ) + 1)⁻¹ else 0) ≤
          ∑ r ∈ Finset.range (n + 1),
          if (2 * r + 1) * (n + 1) ≤ K then (2 * (r : ℝ) + 1)⁻¹ else 0 := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases h : (2 * r + 1) * (n + 1 + 1) ≤ K
        · have h' : (2 * r + 1) * (n + 1) ≤ K := by
            have hle : n + 1 ≤ n + 1 + 1 := by omega
            exact (Nat.mul_le_mul_left (2 * r + 1) hle).trans h
          simp [h, h']
        · simp [h]
          split_ifs <;> positivity
      have hlast : (if (2 * (n + 1) + 1) * (n + 1 + 1) ≤ K
            then (2 * (↑(n + 1) : ℝ) + 1)⁻¹ else 0)
          ≤ 1 / (2 * (n : ℝ) + 3) := by
        by_cases h : (2 * (n + 1) + 1) * (n + 1 + 1) ≤ K
        · simp [h]
          ring_nf
          exact le_rfl
        · simp [h]
          positivity
      linarith
    have hkey : ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) ≤ S := by
      have hpos3 : (0 : ℝ) < 2 * (n : ℝ) + 3 := by positivity
      have : ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) ≤ 1 := by
        rw [div_le_one hpos3]
        nlinarith
      exact this.trans hSge
    calc
      T / (↑n + 1 + 1) ≤ (S + 1 / (2 * (n : ℝ) + 3)) / (↑n + 1 + 1) := by
        exact div_le_div_of_nonneg_right hTle (by positivity)
      _ ≤ S / (↑n + 1) := by
        rw [div_le_div_iff₀]
        · field_simp [show (2 * (n : ℝ) + 3) ≠ 0 by positivity]
          nlinarith
        · positivity
        · positivity
  · have hzero : putnam_2015_b6_c K (n + 1) = 0 := by
      unfold putnam_2015_b6_c
      simp [hnext]
    rw [hzero]
    exact putnam_2015_b6_c_nonneg K n

theorem putnam_2015_b6_c_tendsto_b (n : ℕ) :
    Tendsto (fun K : ℕ => putnam_2015_b6_c K n) atTop (𝓝 (putnam_2015_b6_b n)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ((2 * n + 1) * (n + 1))] with K hK
  unfold putnam_2015_b6_c putnam_2015_b6_b putnam_2015_b6_oddH
  have hnK : n < K := by
    have hprod : n + 1 ≤ (2 * n + 1) * (n + 1) := by
      have hpos : 1 ≤ 2 * n + 1 := by omega
      exact Nat.le_mul_of_pos_left (n + 1) hpos
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (hprod.trans hK)
  simp [hnK]
  have hsum : (∑ r ∈ Finset.range (n + 1),
      if (2 * r + 1) * (n + 1) ≤ K then (2 * (r : ℝ) + 1)⁻¹ else 0) =
      ∑ r ∈ Finset.range (n + 1), (2 * (r : ℝ) + 1)⁻¹ := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrle : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hoddle : 2 * r + 1 ≤ 2 * n + 1 := by omega
    have hcond : (2 * r + 1) * (n + 1) ≤ K := by
      exact (Nat.mul_le_mul_right (n + 1) hoddle).trans hK
    simp [hcond]
  rw [hsum]

theorem putnam_2015_b6_alternating_error_bound {f : ℕ → ℝ} {l : ℝ}
    (hfa : Antitone f) (hf0 : ∀ n, 0 ≤ f n)
    (hfl : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 l))
    (n : ℕ) :
    |l - (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)| ≤ f n := by
  have upper := hfa.alternating_series_le_tendsto hfl
  have lower := hfa.tendsto_le_alternating_series hfl
  obtain (h | h) := n.even_or_odd
  · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper n
    specialize lower n
    simp only [Finset.sum_range_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul]
      at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (hf0 (2 * n)))
  · obtain ⟨n, rfl⟩ := odd_iff_exists_bit1.mp h
    specialize upper (n + 1)
    specialize lower n
    rw [Nat.mul_add, Finset.sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (hf0 (2 * n + 1)))
    · simpa [Finset.sum_range_succ, add_comm, pow_add] using upper

theorem putnam_2015_b6_c_eq_zero_of_le {K n : ℕ} (h : K ≤ n) :
    putnam_2015_b6_c K n = 0 := by
  unfold putnam_2015_b6_c
  simp [not_lt.mpr h]

theorem putnam_2015_b6_c_summable (K : ℕ) :
    Summable (fun n : ℕ => putnam_2015_b6_c K n) := by
  refine summable_of_ne_finset_zero (s := Finset.range K) ?_
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  exact putnam_2015_b6_c_eq_zero_of_le hn

theorem putnam_2015_b6_c_tail_bound (K N : ℕ) :
    |(∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n) -
      (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * putnam_2015_b6_c K n)| ≤
      putnam_2015_b6_c K N := by
  have htsum : (∑' n : ℕ, (-1 : ℝ) ^ n * putnam_2015_b6_c K n) =
      ∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n := by
    rw [tsum_eq_sum]
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [putnam_2015_b6_c_eq_zero_of_le hn, mul_zero]
  have herr := alternating_series_error_bound (fun n : ℕ => putnam_2015_b6_c K n)
    (putnam_2015_b6_c_antitone K) (putnam_2015_b6_c_summable K) N
  rw [htsum] at herr
  simpa [abs_sub_comm] using herr

theorem putnam_2015_b6_c_sum_tendsto {l : ℝ}
    (hrow : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * putnam_2015_b6_b n)
      atTop (𝓝 l)) :
    Tendsto
      (fun K : ℕ => ∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n)
      atTop (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hb_event := (Metric.tendsto_nhds.mp putnam_2015_b6_b_tendsto_zero) (ε / 3) hε3
  rcases eventually_atTop.1 hb_event with ⟨N, hN⟩
  have hbNdist : dist (putnam_2015_b6_b N) 0 < ε / 3 := hN N le_rfl
  have hbN : putnam_2015_b6_b N < ε / 3 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (putnam_2015_b6_b_nonneg N)] at hbNdist
    exact hbNdist
  have hfinite :
      Tendsto
        (fun K : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * putnam_2015_b6_c K n)
        atTop
        (𝓝 (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * putnam_2015_b6_b n)) := by
    refine tendsto_finset_sum (Finset.range N) ?_
    intro n hn
    exact tendsto_const_nhds.mul (putnam_2015_b6_c_tendsto_b n)
  have hfinite_event := (Metric.tendsto_nhds.mp hfinite) (ε / 3) hε3
  filter_upwards [hfinite_event] with K hK
  let S : ℝ := ∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n
  let C : ℝ := ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * putnam_2015_b6_c K n
  let B : ℝ := ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * putnam_2015_b6_b n
  change dist S l < ε
  rw [Real.dist_eq]
  have hKabs : |C - B| < ε / 3 := by
    simpa [Real.dist_eq, C, B] using hK
  have htailc : |S - C| ≤ putnam_2015_b6_b N := by
    exact (putnam_2015_b6_c_tail_bound K N).trans (putnam_2015_b6_c_le_b K N)
  have htailb : |B - l| ≤ putnam_2015_b6_b N := by
    have h := putnam_2015_b6_alternating_error_bound putnam_2015_b6_b_antitone
      putnam_2015_b6_b_nonneg hrow N
    simpa [abs_sub_comm, B] using h
  have htri : |S - l| ≤ |S - C| + |C - B| + |B - l| := by
    calc
      |S - l| = |(S - C) + (C - B) + (B - l)| := by ring_nf
      _ ≤ |(S - C) + (C - B)| + |B - l| := by
        exact abs_add_le _ _
      _ ≤ (|S - C| + |C - B|) + |B - l| := by
        gcongr
        exact abs_add_le _ _
      _ = |S - C| + |C - B| + |B - l| := by ring
  calc
    |S - l| ≤ |S - C| + |C - B| + |B - l| := htri
    _ < putnam_2015_b6_b N + ε / 3 + putnam_2015_b6_b N := by nlinarith
    _ < ε := by nlinarith

theorem putnam_2015_b6_arctan_summable_norm {x : ℝ} (hx : ‖x‖ < 1) :
    Summable fun n : ℕ => ‖((-1 : ℝ) ^ n * x ^ (2 * n) / (2 * n + 1) : ℝ)‖ := by
  have hxabs : |x| < 1 := by simpa [Real.norm_eq_abs] using hx
  have hsq : |x| ^ 2 < 1 := by
    nlinarith [abs_nonneg x, hxabs]
  have hgeom : Summable fun n : ℕ => (|x| ^ 2) ^ n :=
    summable_geometric_of_lt_one (sq_nonneg |x|) hsq
  refine hgeom.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hden : 1 ≤ |(2 * (n : ℝ) + 1)| := by
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  calc
    |x ^ (2 * n)| / |(2 * (n : ℝ) + 1)| ≤ |x ^ (2 * n)| / 1 := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hden
    _ = (|x| ^ 2) ^ n := by
      rw [abs_pow, pow_mul]
      ring

theorem putnam_2015_b6_arctan_hasSum_div {x : ℝ} (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * x ^ (2 * n) / (2 * n + 1))
      (Real.arctan x / x) := by
  have har := Real.hasSum_arctan hx
  have hdiv := har.div_const x
  convert hdiv using 1
  ext n
  field_simp [hx0]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

theorem putnam_2015_b6_diag_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (1 : ℝ) / ((2 * k + 1) * (2 * (n - k) + 1))) = putnam_2015_b6_b n := by
  unfold putnam_2015_b6_b putnam_2015_b6_oddH
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (1 : ℝ) / ((2 * k + 1) * (2 * (n - k) + 1)) =
        (1 / (2 * ((n + 1 : ℕ) : ℝ))) *
          ((1 : ℝ) / (2 * k + 1) + (1 : ℝ) / (2 * (n - k) + 1)) := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnonneg : (0 : ℝ) ≤ (n : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hk_le)
    have hpos1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have hpos2 : (0 : ℝ) < 2 * ((n : ℝ) - k) + 1 := by positivity
    have hpos3 : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
    field_simp [hpos1.ne', hpos2.ne', hpos3.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  have hreflect : (∑ x ∈ Finset.range (n + 1), (1 : ℝ) / (2 * ((n : ℝ) - x) + 1)) =
      ∑ x ∈ Finset.range (n + 1), (1 : ℝ) / (2 * x + 1) := by
    convert (Finset.sum_range_reflect (fun x : ℕ => (1 : ℝ) / (2 * x + 1)) (n + 1)) using 1
    apply Finset.sum_congr rfl
    intro x hx
    have hx_le : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
    have hidx : n + 1 - 1 - x = n - x := by omega
    rw [hidx, Nat.cast_sub hx_le]
  rw [hreflect]
  field_simp [show (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0 by positivity]
  norm_num [Nat.cast_add, Nat.cast_one]

theorem putnam_2015_b6_cauchy_coeff (x : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ k * x ^ (2 * k) / (2 * k + 1)) *
        ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k)) / (2 * (n - k) + 1))) =
    ((-1 : ℝ) ^ n * putnam_2015_b6_b n) * (x ^ 2) ^ n := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ k * x ^ (2 * k) / (2 * k + 1)) *
        ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k)) / (2 * (n - k) + 1)) =
      ((-1 : ℝ) ^ n * (x ^ 2) ^ n) *
        ((1 : ℝ) / ((2 * k + 1) * (2 * (n - k) + 1))) := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkn : k + (n - k) = n := Nat.add_sub_of_le hk_le
    have hexp : 2 * k + 2 * (n - k) = 2 * n := by omega
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ n := by
      rw [← pow_add, hkn]
    have hxpow : x ^ (2 * k) * x ^ (2 * (n - k)) = (x ^ 2) ^ n := by
      rw [← pow_add, hexp, pow_mul]
    field_simp
    rw [← hsign, ← hxpow]
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum]
  rw [putnam_2015_b6_diag_sum n]
  ring

theorem putnam_2015_b6_power_identity {x : ℝ} (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    (∑' n : ℕ, ((-1 : ℝ) ^ n * putnam_2015_b6_b n) * (x ^ 2) ^ n) =
      (Real.arctan x / x) ^ 2 := by
  let f : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * x ^ (2 * n) / (2 * n + 1)
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm (R := ℝ)
    (f := f) (g := f) (putnam_2015_b6_arctan_summable_norm hx)
    (putnam_2015_b6_arctan_summable_norm hx)
  have hsum : (∑' n : ℕ, f n) = Real.arctan x / x :=
    (putnam_2015_b6_arctan_hasSum_div hx hx0).tsum_eq
  rw [hsum] at hprod
  have hcoeff : (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), f k * f (n - k)) =
      fun n : ℕ => ((-1 : ℝ) ^ n * putnam_2015_b6_b n) * (x ^ 2) ^ n := by
    funext n
    dsimp [f]
    convert putnam_2015_b6_cauchy_coeff x n using 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.cast_sub hk_le]
  rw [show (∑' n : ℕ, ((-1 : ℝ) ^ n * putnam_2015_b6_b n) * (x ^ 2) ^ n) =
      ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * f (n - k) by rw [hcoeff]]
  rw [← hprod]
  ring

theorem putnam_2015_b6_row_tendsto :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * putnam_2015_b6_b n)
      atTop (𝓝 (Real.pi ^ 2 / 16)) := by
  obtain ⟨l, hrow⟩ :=
    putnam_2015_b6_b_antitone.tendsto_alternating_series_of_tendsto_zero
      putnam_2015_b6_b_tendsto_zero
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hrow
  have q : Tendsto (fun x : ℝ => x ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · nth_rw 3 [← one_pow 2]
      exact (tendsto_id.mono_left nhdsWithin_le_nhds).pow 2
    · rw [eventually_iff_exists_mem]
      use Set.Ioo (-1 : ℝ) 1
      exact ⟨Ioo_mem_nhdsLT <| by simp,
        fun y hy1 ↦ by
          rw [Set.mem_Iio]
          rw [Set.mem_Ioo] at hy1
          rw [sq_lt_one_iff_abs_lt_one, abs_lt]
          exact ⟨hy1.1, hy1.2⟩⟩
  have habel_sq :
      Tendsto
        (fun x : ℝ => ∑' n : ℕ,
          ((-1 : ℝ) ^ n * putnam_2015_b6_b n) * (x ^ 2) ^ n)
        (𝓝[<] 1) (𝓝 l) := by
    simpa [Function.comp_def] using habel.comp q
  have heq :
      (fun x : ℝ => ∑' n : ℕ,
          ((-1 : ℝ) ^ n * putnam_2015_b6_b n) * (x ^ 2) ^ n)
        =ᶠ[𝓝[<] 1] fun x : ℝ => (Real.arctan x / x) ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hxnorm : ‖x‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hx.1]
      exact hx.2
    exact putnam_2015_b6_power_identity hxnorm hx0
  have habel_arctan :
      Tendsto (fun x : ℝ => (Real.arctan x / x) ^ 2) (𝓝[<] 1) (𝓝 l) :=
    habel_sq.congr' heq
  have harctan_lim :
      Tendsto (fun x : ℝ => (Real.arctan x / x) ^ 2) (𝓝[<] 1)
        (𝓝 ((Real.pi ^ 2 / 16) : ℝ)) := by
    have hdiv :
        Tendsto (fun x : ℝ => Real.arctan x / x) (𝓝[<] 1) (𝓝 (Real.pi / 4)) := by
      have h :
          Tendsto (fun x : ℝ => Real.arctan x / x) (𝓝 1)
            (𝓝 (Real.arctan 1 / 1)) :=
        (Real.continuous_arctan.tendsto 1).div tendsto_id one_ne_zero
      have hm := h.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
      simpa [Real.arctan_one] using hm
    have hpow := hdiv.pow 2
    convert hpow using 1
    ring_nf
  have hl : l = Real.pi ^ 2 / 16 := tendsto_nhds_unique habel_arctan harctan_lim
  simpa [hl] using hrow

noncomputable def putnam_2015_b6_pairTerm (p : ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ (p.2 - 1) * (((1 : ℝ) / (p.1 : ℝ)) / (p.2 : ℝ))

def putnam_2015_b6_pairFinset (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc 0 K) ×ˢ (Finset.Ioc 0 K)).filter
    (fun p : ℕ × ℕ => Odd p.1 ∧ p.1 < 2 * p.2 ∧ p.1 * p.2 ≤ K)

noncomputable def putnam_2015_b6_mrTerm (q : ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ (q.1 - 1) * (((1 : ℝ) / (2 * q.2 + 1 : ℕ)) / (q.1 : ℝ))

def putnam_2015_b6_mrFinset (K : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Ioc 0 K) ×ˢ (Finset.range K)).filter
    (fun q : ℕ × ℕ => q.2 < q.1 ∧ (2 * q.2 + 1) * q.1 ≤ K))

theorem putnam_2015_b6_term_eq_antidiagonal
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    {k : ℕ} (hk : 1 ≤ k) :
    (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ)) =
      ∑ p ∈ k.divisorsAntidiagonal,
        if Odd p.1 ∧ p.1 < 2 * p.2 then putnam_2015_b6_pairTerm p else 0 := by
  classical
  have hkpos : 0 < k := hk
  rw [putnam_2015_b6_card A hA hkpos]
  rw [Finset.card_eq_sum_ones]
  rw [Nat.cast_sum]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  rw [show (∑ p ∈ k.divisorsAntidiagonal,
        if Odd p.1 ∧ p.1 < 2 * p.2 then putnam_2015_b6_pairTerm p else 0) =
      ∑ p ∈ k.divisorsAntidiagonal,
        (fun a b => if Odd a ∧ a < 2 * b then putnam_2015_b6_pairTerm (a, b) else 0)
          p.1 p.2 by rfl]
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => if Odd a ∧ a < 2 * b then putnam_2015_b6_pairTerm (a, b) else (0 : ℝ))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjdvd : j ∣ k := Nat.dvd_of_mem_divisors hj
  have hjpos : 0 < j := Nat.pos_of_mem_divisors hj
  have hjle : j ≤ k := Nat.le_of_dvd hkpos hjdvd
  have hmpos : 0 < k / j := Nat.div_pos hjle hjpos
  have hmul : j * (k / j) = k := Nat.mul_div_cancel' hjdvd
  by_cases hodd : Odd j
  · have hsqrt : ((j : ℝ) < Real.sqrt (2 * k)) ↔ j < 2 * (k / j) := by
      have hsqrt0 := putnam_2015_b6_sqrt_iff (j := j) (m := k / j) hjpos
      have hmulr : (j : ℝ) * ((k / j : ℕ) : ℝ) = (k : ℝ) := by
        exact_mod_cast hmul
      convert hsqrt0 using 2
      · rw [hmulr]
    by_cases hlt : j < 2 * (k / j)
    · rw [if_pos ⟨hodd, hsqrt.mpr hlt⟩, if_pos ⟨hodd, hlt⟩]
      rw [putnam_2015_b6_neg_one_rpow_nat hk]
      have hsign : (-1 : ℝ) ^ (k - 1) = (-1 : ℝ) ^ (k / j - 1) := by
        nth_rw 1 [← hmul]
        exact putnam_2015_b6_neg_one_pow_mul_sub_one hodd hmpos
      rw [hsign]
      have hkreal : (k : ℝ) = (j : ℝ) * (((k / j : ℕ) : ℝ)) := by
        exact_mod_cast hmul.symm
      rw [hkreal]
      unfold putnam_2015_b6_pairTerm
      field_simp [show (j : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hjpos,
        show (((k / j : ℕ) : ℝ)) ≠ 0 by exact_mod_cast ne_of_gt hmpos]
      ring
    · have hsqrtnot : ¬(j : ℝ) < Real.sqrt (2 * k) := by
        intro hjs
        exact hlt (hsqrt.mp hjs)
      rw [if_neg (by intro hcond; exact hsqrtnot hcond.2),
        if_neg (by intro hcond; exact hlt hcond.2)]
  · rw [if_neg (by intro hcond; exact hodd hcond.1),
      if_neg (by intro hcond; exact hodd hcond.1)]

theorem putnam_2015_b6_original_eq_pair
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ))) =
      ∑ p ∈ putnam_2015_b6_pairFinset K, putnam_2015_b6_pairTerm p := by
  classical
  rw [show (∑ k ∈ Finset.Icc 1 K,
      (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ))) =
      ∑ k ∈ Finset.Icc 1 K,
        ∑ p ∈ k.divisorsAntidiagonal,
          if Odd p.1 ∧ p.1 < 2 * p.2 then putnam_2015_b6_pairTerm p else 0 by
    apply Finset.sum_congr rfl
    intro k hk
    exact putnam_2015_b6_term_eq_antidiagonal A hA (Finset.mem_Icc.mp hk).1]
  have hrewrite : (∑ k ∈ Finset.Icc 1 K,
        ∑ p ∈ k.divisorsAntidiagonal,
          if Odd p.1 ∧ p.1 < 2 * p.2 then putnam_2015_b6_pairTerm p else 0) =
      ∑ k ∈ Finset.Icc 1 K,
        ∑ p ∈ (((Finset.Ioc 0 K) ×ˢ (Finset.Ioc 0 K)).filter
            (fun p : ℕ × ℕ => p.1 * p.2 = k)),
          if Odd p.1 ∧ p.1 < 2 * p.2 then putnam_2015_b6_pairTerm p else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkne : k ≠ 0 := by omega
    have hkle : k ≤ K := hk.2
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hkne hkle]
  rw [hrewrite]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr ?_ ?_
  · ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc,
      putnam_2015_b6_pairFinset]
    constructor
    · intro h
      rcases h with ⟨⟨hpbox, hprodIcc⟩, hodd, hlt⟩
      exact ⟨hpbox, hodd, hlt, hprodIcc.2⟩
    · intro h
      rcases h with ⟨hpbox, hodd, hlt, hle⟩
      have hprodpos : 1 ≤ p.1 * p.2 := by
        have hp1 : 0 < p.1 := hpbox.1.1
        have hp2 : 0 < p.2 := hpbox.2.1
        exact Nat.succ_le_of_lt (Nat.mul_pos hp1 hp2)
      exact ⟨⟨hpbox, hprodpos, hle⟩, hodd, hlt⟩
  · intro p hp
    rfl

theorem putnam_2015_b6_triangular_eq_mr (K : ℕ) :
    (∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n) =
      ∑ q ∈ putnam_2015_b6_mrFinset K, putnam_2015_b6_mrTerm q := by
  classical
  have hreindex : (∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n) =
      ∑ m ∈ Finset.Ioc 0 K,
        (-1 : ℝ) ^ (m - 1) *
          ((∑ r ∈ Finset.range m,
            if (2 * r + 1) * m ≤ K then (1 : ℝ) / (2 * r + 1) else 0) / (m : ℝ)) := by
    refine Finset.sum_bij (s := Finset.range K) (t := Finset.Ioc 0 K)
      (f := fun n => (-1 : ℝ) ^ n * putnam_2015_b6_c K n)
      (g := fun m => (-1 : ℝ) ^ (m - 1) *
          ((∑ r ∈ Finset.range m,
            if (2 * r + 1) * m ≤ K then (1 : ℝ) / (2 * r + 1) else 0) / (m : ℝ)))
      (fun n hn => n + 1) ?_ ?_ ?_ ?_
    · intro n hn
      dsimp
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Ioc]
      exact ⟨by omega, by omega⟩
    · intro a ha b hb h
      dsimp at h
      omega
    · intro m hm
      rw [Finset.mem_Ioc] at hm
      refine ⟨m - 1, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · dsimp
        omega
    · intro n hn
      dsimp
      rw [Finset.mem_range] at hn
      unfold putnam_2015_b6_c
      rw [if_pos hn]
      simp
  rw [hreindex]
  have hexpand : (∑ m ∈ Finset.Ioc 0 K,
        (-1 : ℝ) ^ (m - 1) *
          ((∑ r ∈ Finset.range m,
            if (2 * r + 1) * m ≤ K then (1 : ℝ) / (2 * r + 1) else 0) / (m : ℝ))) =
      ∑ m ∈ Finset.Ioc 0 K,
        ∑ r ∈ Finset.range m,
          if (2 * r + 1) * m ≤ K then
            (-1 : ℝ) ^ (m - 1) * (((1 : ℝ) / (2 * r + 1 : ℕ)) / (m : ℝ))
          else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hcond : (2 * r + 1) * m ≤ K
    · simp [hcond]
    · simp [hcond]
  rw [hexpand]
  rw [← Finset.sum_finset_product' (r := ((Finset.Ioc 0 K) ×ˢ (Finset.range K)).filter
      (fun q : ℕ × ℕ => q.2 < q.1)) (s := Finset.Ioc 0 K) (t := fun m => Finset.range m)
      (f := fun m r => if (2 * r + 1) * m ≤ K then
            (-1 : ℝ) ^ (m - 1) * (((1 : ℝ) / (2 * r + 1 : ℕ)) / (m : ℝ))
          else 0) ?_]
  · rw [← Finset.sum_filter]
    apply Finset.sum_congr ?_ ?_
    · ext q
      simp only [putnam_2015_b6_mrFinset, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Ioc, Finset.mem_range]
      tauto
    · intro q hq
      rfl
  · intro q
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      rcases h with ⟨hm, hr⟩
      exact ⟨⟨hm, by omega⟩, hr⟩

theorem putnam_2015_b6_mr_eq_pair (K : ℕ) :
    (∑ q ∈ putnam_2015_b6_mrFinset K, putnam_2015_b6_mrTerm q) =
      ∑ p ∈ putnam_2015_b6_pairFinset K, putnam_2015_b6_pairTerm p := by
  classical
  refine Finset.sum_bij (s := putnam_2015_b6_mrFinset K) (t := putnam_2015_b6_pairFinset K)
    (f := putnam_2015_b6_mrTerm) (g := putnam_2015_b6_pairTerm)
    (fun q hq => (2 * q.2 + 1, q.1)) ?_ ?_ ?_ ?_
  · intro q hq
    rcases q with ⟨m, r⟩
    simp only [putnam_2015_b6_mrFinset, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ioc, Finset.mem_range] at hq
    simp only [putnam_2015_b6_pairFinset, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ioc]
    rcases hq with ⟨⟨⟨hmpos, hmle⟩, hrK⟩, hrm, hprod⟩
    have hjpos : 0 < 2 * r + 1 := by omega
    have hjleprod : 2 * r + 1 ≤ (2 * r + 1) * m :=
      Nat.le_mul_of_pos_right (2 * r + 1) hmpos
    exact ⟨⟨⟨hjpos, hjleprod.trans hprod⟩, hmpos, hmle⟩,
      odd_two_mul_add_one r, by omega, hprod⟩
  · intro q₁ hq₁ q₂ hq₂ h
    rcases q₁ with ⟨m₁, r₁⟩
    rcases q₂ with ⟨m₂, r₂⟩
    simp only [Prod.mk.injEq] at h ⊢
    omega
  · intro p hp
    refine ⟨(p.2, p.1 / 2), ?_, ?_⟩
    · rcases p with ⟨j, m⟩
      simp only [putnam_2015_b6_pairFinset, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Ioc] at hp
      simp only [putnam_2015_b6_mrFinset, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Ioc, Finset.mem_range]
      rcases hp with ⟨⟨⟨hjpos, hjleK⟩, hmpos, hmleK⟩, hodd, hlt, hprod⟩
      have hjrepr : 2 * (j / 2) + 1 = j := Nat.two_mul_div_two_add_one_of_odd hodd
      have hrK : j / 2 < K := by
        exact (Nat.div_lt_self hjpos (by norm_num : 1 < 2)).trans_le hjleK
      have hrm : j / 2 < m := by omega
      exact ⟨⟨⟨hmpos, hmleK⟩, hrK⟩, hrm, by simpa [hjrepr] using hprod⟩
    · rcases p with ⟨j, m⟩
      simp only [putnam_2015_b6_pairFinset, Finset.mem_filter] at hp
      simp only [Prod.mk.injEq]
      have hodd : Odd j := hp.2.1
      exact ⟨Nat.two_mul_div_two_add_one_of_odd hodd, trivial⟩
  · intro q hq
    rcases q with ⟨m, r⟩
    rfl

theorem putnam_2015_b6_triangular_eq_pair (K : ℕ) :
    (∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n) =
      ∑ p ∈ putnam_2015_b6_pairFinset K, putnam_2015_b6_pairTerm p := by
  exact (putnam_2015_b6_triangular_eq_mr K).trans (putnam_2015_b6_mr_eq_pair K)

theorem putnam_2015_b6_original_eq_triangular
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ))) =
      ∑ n ∈ Finset.range K, (-1 : ℝ) ^ n * putnam_2015_b6_c K n := by
  exact (putnam_2015_b6_original_eq_pair A hA K).trans
    (putnam_2015_b6_triangular_eq_pair K).symm

-- Real.pi ^ 2 / 16
/--
For each positive integer $k$, let $A(k)$ be the number of odd divisors of $k$ in the interval $[1,\sqrt{2k})$. Evaluate $\sum_{k=1}^\infty (-1)^{k-1}\frac{A(k)}{k}$.
-/
theorem putnam_2015_b6
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard) :
    Tendsto (fun K : ℕ ↦ ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ)))
      atTop (𝓝 ((Real.pi ^ 2 / 16) : ℝ )) := by
  exact (putnam_2015_b6_c_sum_tendsto putnam_2015_b6_row_tendsto).congr'
    (Filter.Eventually.of_forall fun K => (putnam_2015_b6_original_eq_triangular A hA K).symm)
