import Mathlib

open Filter Topology

private noncomputable def putnam_2015_b6_row (n N : ℕ) : ℝ :=
  ∑ r ∈ Finset.range N,
    (-1 : ℝ) ^ ((((2 * n + 1) * (n + r + 1) : ℕ) : ℝ) - 1) /
      (((2 * n + 1 : ℕ) : ℝ) * ((n + r + 1 : ℕ) : ℝ))

noncomputable abbrev putnam_2015_b6_solution : ℝ :=
  ∑' n : ℕ, limUnder atTop (putnam_2015_b6_row n)

private noncomputable def putnam_2015_b6_bound (n : ℕ) : ℝ :=
  1 / (((2 * n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))

private noncomputable def putnam_2015_b6_pairDomain (K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 K ×ˢ Finset.Ioc 0 K).filter fun p : ℕ × ℕ ↦
    p.1 * p.2 ≤ K ∧ Odd p.1 ∧
      (p.1 : ℝ) < Real.sqrt (2 * (((p.1 * p.2 : ℕ) : ℝ)))

private noncomputable def putnam_2015_b6_pairTerm (p : ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ ((((p.1 * p.2 : ℕ) : ℝ) - 1)) / (((p.1 * p.2 : ℕ) : ℝ))

private def putnam_2015_b6_rowSigmaDomain (K : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (K + 1)).sigma fun n : ℕ ↦ Finset.range (K / (2 * n + 1) - n)

private noncomputable def putnam_2015_b6_rowSigmaTerm (q : Σ _ : ℕ, ℕ) : ℝ :=
  (-1 : ℝ) ^ ((((2 * q.1 + 1) * (q.1 + q.2 + 1) : ℕ) : ℝ) - 1) /
    (((2 * q.1 + 1 : ℕ) : ℝ) * ((q.1 + q.2 + 1 : ℕ) : ℝ))

private lemma putnam_2015_b6_sign_eq (n r : ℕ) :
    (-1 : ℝ) ^ ((((2 * n + 1) * (n + r + 1) : ℕ) : ℝ) - 1) =
      (-1 : ℝ) ^ (n + r) := by
  have hposA : 0 < 2 * n + 1 := by omega
  have hposB : 0 < n + r + 1 := by omega
  have hpos : 1 ≤ (2 * n + 1) * (n + r + 1) :=
    Nat.succ_le_iff.mpr (Nat.mul_pos hposA hposB)
  have hcast : (((2 * n + 1) * (n + r + 1) - 1 : ℕ) : ℝ) =
      (((2 * n + 1) * (n + r + 1) : ℕ) : ℝ) - 1 := by
    simp [Nat.cast_sub (R := ℝ) hpos]
  rw [← hcast, Real.rpow_natCast]
  have hmul : (2 * n + 1) * (n + r + 1) =
      2 * (n * (n + r + 1)) + (n + r) + 1 := by
    ring
  have hnat : (2 * n + 1) * (n + r + 1) - 1 =
      2 * (n * (n + r + 1)) + (n + r) := by
    rw [hmul, Nat.add_sub_cancel]
  rw [hnat, pow_add, pow_mul]
  norm_num

private lemma putnam_2015_b6_row_as_alt (n N : ℕ) :
    putnam_2015_b6_row n N =
      (-1 : ℝ) ^ n * ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r *
        ((((2 * n + 1 : ℕ) : ℝ) * ((n + r + 1 : ℕ) : ℝ))⁻¹) := by
  simp only [putnam_2015_b6_row]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [putnam_2015_b6_sign_eq n r, pow_add]
  ring_nf

private lemma putnam_2015_b6_row_tendsto (n : ℕ) :
    Tendsto (putnam_2015_b6_row n) atTop
      (𝓝 (limUnder atTop (putnam_2015_b6_row n))) := by
  apply tendsto_nhds_limUnder
  let f : ℕ → ℝ := fun r ↦
    ((((2 * n + 1 : ℕ) : ℝ) * ((n + r + 1 : ℕ) : ℝ))⁻¹)
  have hanti : Antitone f := by
    intro a b hab
    dsimp [f]
    gcongr
  have hnr : Tendsto (fun r : ℕ ↦ (((n + r + 1 : ℕ) : ℝ))) atTop atTop := by
    have hbase : Tendsto (fun r : ℕ ↦ (((r + (n + 1) : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (n + 1))
    convert hbase using 1
    ext r
    congr 1
    omega
  have hden : Tendsto
      (fun r : ℕ ↦ (((2 * n + 1 : ℕ) : ℝ) * ((n + r + 1 : ℕ) : ℝ)))
      atTop atTop := by
    exact hnr.const_mul_atTop (by positivity)
  have hf0 : Tendsto f atTop (𝓝 0) := by
    exact hden.inv_tendsto_atTop
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hf0
  refine ⟨(-1 : ℝ) ^ n * l, ?_⟩
  have hfun :
      putnam_2015_b6_row n =
        fun N ↦ (-1 : ℝ) ^ n * ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * f r := by
    funext N
    simpa [f] using putnam_2015_b6_row_as_alt n N
  rw [hfun]
  exact tendsto_const_nhds.mul hl

private lemma putnam_2015_b6_norm_alternating_sum_range_le_first
    (f : ℕ → ℝ) (hanti : Antitone f) (hnonneg : ∀ i, 0 ≤ f i) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * f i‖ ≤ f 0 := by
  by_cases hN : N = 0
  · simp [hN, hnonneg 0]
  let G : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i
  have hG (n : ℕ) : ‖G n‖ ≤ (1 : ℝ) := by
    simpa [G] using norm_sum_neg_one_pow_le n
  have hby := Finset.sum_range_by_parts (fun i ↦ f i) (fun i ↦ ((-1 : ℝ) ^ i)) N
  have hsum_eq : (∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * f i) =
      f (N - 1) * G N -
        ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) * G (i + 1) := by
    calc
      (∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * f i)
          = ∑ i ∈ Finset.range N, f i * (-1 : ℝ) ^ i := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
      _ = f (N - 1) * G N -
          ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) * G (i + 1) := by
          simpa [G, smul_eq_mul] using hby
  rw [hsum_eq]
  have hfirst : ‖f (N - 1) * G N‖ ≤ f (N - 1) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hnonneg (N - 1))]
    simpa using mul_le_mul_of_nonneg_left (hG N) (hnonneg (N - 1))
  have hsum : ‖∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) * G (i + 1)‖
      ≤ ∑ i ∈ Finset.range (N - 1), (f i - f (i + 1)) := by
    calc
      ‖∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) * G (i + 1)‖
          ≤ ∑ i ∈ Finset.range (N - 1), ‖(f (i + 1) - f i) * G (i + 1)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (N - 1), (f i - f (i + 1)) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        rw [norm_mul]
        have hle : f (i + 1) ≤ f i := hanti (Nat.le_succ i)
        have hnon : 0 ≤ f i - f (i + 1) := sub_nonneg.mpr hle
        have habs : ‖f (i + 1) - f i‖ = f i - f (i + 1) := by
          rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hle)]
          ring
        rw [habs]
        simpa using mul_le_mul_of_nonneg_left (hG (i + 1)) hnon
  calc
    ‖f (N - 1) * G N -
        ∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) * G (i + 1)‖
        ≤ ‖f (N - 1) * G N‖ +
            ‖∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) * G (i + 1)‖ :=
          norm_sub_le _ _
    _ ≤ f (N - 1) + ∑ i ∈ Finset.range (N - 1), (f i - f (i + 1)) :=
      add_le_add hfirst hsum
    _ = f 0 := by
      have htel0 :
          (∑ i ∈ Finset.range (N - 1), f (i + 1)) -
              ∑ i ∈ Finset.range (N - 1), f i =
            f (N - 1) - f 0 := by
        simpa using Finset.sum_range_sub (fun i ↦ f i) (N - 1)
      rw [Finset.sum_sub_distrib]
      linarith

private lemma putnam_2015_b6_row_bound (n N : ℕ) :
    ‖putnam_2015_b6_row n N‖ ≤ putnam_2015_b6_bound n := by
  let f : ℕ → ℝ := fun r ↦
    1 / (((2 * n + 1 : ℕ) : ℝ) * ((n + r + 1 : ℕ) : ℝ))
  have hrow :
      putnam_2015_b6_row n N =
        (-1 : ℝ) ^ n * ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * f r := by
    simp only [putnam_2015_b6_row, f]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    rw [putnam_2015_b6_sign_eq n r, pow_add]
    ring_nf
  have hanti : Antitone f := by
    intro a b hab
    dsimp [f]
    gcongr
  have hnonneg : ∀ r, 0 ≤ f r := by
    intro r
    dsimp [f]
    positivity
  have hnorm : ‖((-1 : ℝ) ^ n)‖ = 1 := by
    rw [Real.norm_eq_abs, abs_neg_one_pow]
  calc
    ‖putnam_2015_b6_row n N‖ =
        ‖∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * f r‖ := by
      rw [hrow, norm_mul, hnorm, one_mul]
    _ ≤ f 0 :=
      putnam_2015_b6_norm_alternating_sum_range_le_first f hanti hnonneg N
    _ = putnam_2015_b6_bound n := by
      simp [f, putnam_2015_b6_bound]

private lemma putnam_2015_b6_bound_summable : Summable putnam_2015_b6_bound := by
  have hs : Summable (fun n : ℕ ↦ 1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  have hs' : Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [abs_of_nonneg, Nat.cast_add, pow_two] using hs
  refine Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) hs'
  · dsimp [putnam_2015_b6_bound]
    positivity
  · dsimp [putnam_2015_b6_bound]
    have hposc : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hposa : 0 < ((2 * n + 1 : ℕ) : ℝ) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      norm_num
      nlinarith
    rw [pow_two]
    field_simp [hposc.ne', hposa.ne']
    nlinarith

private lemma putnam_2015_b6_rows_tendsto :
    Tendsto
      (fun K : ℕ ↦ ∑' n : ℕ, putnam_2015_b6_row n (K / (2 * n + 1) - n))
      atTop (𝓝 putnam_2015_b6_solution) := by
  unfold putnam_2015_b6_solution
  refine tendsto_tsum_of_dominated_convergence putnam_2015_b6_bound_summable ?_ ?_
  · intro n
    have hidx : Tendsto (fun K : ℕ ↦ K / (2 * n + 1) - n) atTop atTop := by
      exact (tendsto_sub_atTop_nat n).comp (Nat.tendsto_div_const_atTop (by omega))
    exact (putnam_2015_b6_row_tendsto n).comp hidx
  · exact Filter.Eventually.of_forall fun K n ↦
      putnam_2015_b6_row_bound n (K / (2 * n + 1) - n)

private lemma putnam_2015_b6_row_zero_of_large {K n : ℕ} (h : K < n) :
    putnam_2015_b6_row n (K / (2 * n + 1) - n) = 0 := by
  have hdiv : K / (2 * n + 1) ≤ K := Nat.div_le_self K (2 * n + 1)
  have hlen : K / (2 * n + 1) - n = 0 := by omega
  simp [putnam_2015_b6_row, hlen]

private lemma putnam_2015_b6_tsum_rows_eq_sum (K : ℕ) :
    (∑' n : ℕ, putnam_2015_b6_row n (K / (2 * n + 1) - n)) =
      ∑ n ∈ Finset.range (K + 1), putnam_2015_b6_row n (K / (2 * n + 1) - n) := by
  exact tsum_eq_sum (L := SummationFilter.unconditional ℕ)
    (s := Finset.range (K + 1))
    (f := fun n : ℕ ↦ putnam_2015_b6_row n (K / (2 * n + 1) - n)) (by
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      exact putnam_2015_b6_row_zero_of_large (Nat.lt_of_succ_le hn))

private lemma putnam_2015_b6_A_eq_card
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    {k : ℕ} (hk : 0 < k) :
    A k =
      ((Nat.divisors k).filter fun j : ℕ ↦
        Odd j ∧ (j : ℝ) < Real.sqrt (2 * (k : ℝ))).card := by
  classical
  let S : Set ℕ := {j : ℕ | Odd j ∧ j ∣ k ∧
    (j : ℝ) < Real.sqrt (2 * (k : ℝ))}
  let F : Finset ℕ := (Nat.divisors k).filter fun j : ℕ ↦
    Odd j ∧ (j : ℝ) < Real.sqrt (2 * (k : ℝ))
  have hset : S = (F : Set ℕ) := by
    ext j
    simp [S, F, Nat.mem_divisors, hk.ne', and_left_comm]
  have henc : S.encard = (F.card : ℕ∞) := by
    rw [hset]
    simp
  have h := hA k hk
  change (A k : ℕ∞) = S.encard at h
  rw [henc] at h
  exact ENat.coe_inj.mp h

private lemma putnam_2015_b6_term_to_divisor_sum
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    {k : ℕ} (hk : 0 < k) :
    (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ)) =
      ∑ _j ∈ ((Nat.divisors k).filter fun j : ℕ ↦
          Odd j ∧ (j : ℝ) < Real.sqrt (2 * (k : ℝ))),
        (-1 : ℝ) ^ ((k : ℝ) - 1) / (k : ℝ) := by
  rw [putnam_2015_b6_A_eq_card A hA hk]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

private lemma putnam_2015_b6_divisor_sum_to_antidiagonal {k : ℕ} :
    (∑ _j ∈ ((Nat.divisors k).filter fun j : ℕ ↦
        Odd j ∧ (j : ℝ) < Real.sqrt (2 * (k : ℝ))),
      (-1 : ℝ) ^ ((k : ℝ) - 1) / (k : ℝ)) =
      ∑ p ∈ ((Nat.divisorsAntidiagonal k).filter fun p : ℕ × ℕ ↦
          Odd p.1 ∧ (p.1 : ℝ) < Real.sqrt (2 * (k : ℝ))),
        putnam_2015_b6_pairTerm p := by
  classical
  let emb : ℕ ↪ ℕ × ℕ :=
    ⟨fun d ↦ (d, k / d), fun _a _b h ↦ by simpa using congrArg Prod.fst h⟩
  let P : ℕ → Prop := fun j ↦
    Odd j ∧ (j : ℝ) < Real.sqrt (2 * (k : ℝ))
  let Q : ℕ × ℕ → Prop := fun p ↦
    Odd p.1 ∧ (p.1 : ℝ) < Real.sqrt (2 * (k : ℝ))
  have hfilter :
      (((Nat.divisors k).filter P).map emb) =
        (Nat.divisorsAntidiagonal k).filter Q := by
    rw [← Nat.map_div_right_divisors (n := k)]
    ext p
    constructor
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨j, hj, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_map.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩,
          (Finset.mem_filter.mp hj).2⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpmap, hQ⟩
      rcases Finset.mem_map.mp hpmap with ⟨j, hj, rfl⟩
      exact Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hQ⟩, rfl⟩
  rw [← hfilter, Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro j hj
  dsimp [emb, putnam_2015_b6_pairTerm]
  have hjdiv : j ∣ k := (Nat.mem_divisors.mp (Finset.mem_filter.mp hj).1).1
  rw [Nat.mul_div_cancel' hjdiv]

private lemma putnam_2015_b6_antidiagonal_sum_eq_pairDomain (K : ℕ) :
    (∑ k ∈ Finset.Ioc 0 K,
      ∑ p ∈ (Nat.divisorsAntidiagonal k).filter (fun p : ℕ × ℕ ↦
          Odd p.1 ∧ (p.1 : ℝ) < Real.sqrt (2 * (k : ℝ))),
        putnam_2015_b6_pairTerm p) =
      ∑ p ∈ putnam_2015_b6_pairDomain K, putnam_2015_b6_pairTerm p := by
  classical
  trans ∑ k ∈ Finset.Ioc 0 K,
      ∑ p ∈ ((Finset.Ioc 0 K ×ˢ Finset.Ioc 0 K).filter
          (fun p : ℕ × ℕ ↦ p.1 * p.2 = k)).filter
          (fun p : ℕ × ℕ ↦ Odd p.1 ∧ (p.1 : ℝ) < Real.sqrt (2 * (k : ℝ))),
        putnam_2015_b6_pairTerm p
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : k ∈ Finset.Ioc 0 K := hk
    simp only [Finset.mem_Ioc] at hk'
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk'.1.ne' hk'.2]
  · simp_rw [Finset.filter_filter]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [putnam_2015_b6_pairDomain, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro p hp
    simp only [Finset.mem_product, Finset.mem_Ioc] at hp
    rcases p with ⟨j, m⟩
    simp only at hp
    by_cases hle : j * m ≤ K
    · have hposprod : 0 < j * m := Nat.mul_pos hp.1.1 hp.2.1
      have hmem : j * m ∈ Finset.Ioc 0 K := by simp [hposprod, hle]
      rw [Finset.sum_eq_single (j * m)]
      · simp [hle]
      · intro b _hb hbne
        have hneq : ¬(j * m = b) := fun h => hbne h.symm
        rw [if_neg]
        exact fun h => hneq h.1
      · intro hnot
        exact (hnot hmem).elim
    · have hzero : (∑ x ∈ Finset.Ioc 0 K,
          if j * m = x ∧ Odd j ∧ (j : ℝ) < Real.sqrt (2 * (x : ℝ)) then
            putnam_2015_b6_pairTerm (j, m)
          else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        rw [if_neg]
        intro _h
        have hxI := hx
        simp only [Finset.mem_Ioc] at hxI
        have : j * m ≤ K := by omega
        exact hle this
      rw [hzero]
      rw [if_neg]
      intro h
      exact hle h.1

private lemma putnam_2015_b6_odd_eq_two_mul_div_two_add_one {j : ℕ} (hj : Odd j) :
    j = 2 * (j / 2) + 1 := by
  have h := Nat.div_add_mod j 2
  rw [Nat.odd_iff.mp hj] at h
  omega

private lemma putnam_2015_b6_sqrt_cond_to_m_ge {j m : ℕ} (hjpos : 0 < j)
    (hjodd : Odd j) (hlt : (j : ℝ) < Real.sqrt (2 * ((j * m : ℕ) : ℝ))) :
    j / 2 + 1 ≤ m := by
  have hsquare : (j : ℝ) ^ 2 < 2 * ((j * m : ℕ) : ℝ) :=
    (Real.lt_sqrt (by positivity : (0 : ℝ) ≤ (j : ℝ))).mp hlt
  have hjposr : 0 < (j : ℝ) := by exact_mod_cast hjpos
  have hmineq : (j : ℝ) < 2 * (m : ℝ) := by
    rw [Nat.cast_mul] at hsquare
    nlinarith
  have hmnat : j < 2 * m := by exact_mod_cast hmineq
  have hoddform := putnam_2015_b6_odd_eq_two_mul_div_two_add_one hjodd
  omega

private lemma putnam_2015_b6_row_lower_to_sqrt {n m : ℕ} (hm : n + 1 ≤ m) :
    (((2 * n + 1 : ℕ) : ℝ) <
      Real.sqrt (2 * ((((2 * n + 1) * m : ℕ) : ℝ)))) := by
  have hjpos : 0 ≤ (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  rw [Real.lt_sqrt hjpos]
  have hlt : (2 * n + 1 : ℝ) < 2 * (m : ℝ) := by
    exact_mod_cast (by omega : 2 * n + 1 < 2 * m)
  norm_num [Nat.cast_mul]
  nlinarith

private lemma putnam_2015_b6_row_sum_eq_rowSigma (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1), putnam_2015_b6_row n (K / (2 * n + 1) - n)) =
      ∑ q ∈ putnam_2015_b6_rowSigmaDomain K, putnam_2015_b6_rowSigmaTerm q := by
  simp [putnam_2015_b6_rowSigmaDomain, putnam_2015_b6_row,
    putnam_2015_b6_rowSigmaTerm, Finset.sum_sigma']

private lemma putnam_2015_b6_rowSigma_sum_eq_pairDomain (K : ℕ) :
    (∑ q ∈ putnam_2015_b6_rowSigmaDomain K, putnam_2015_b6_rowSigmaTerm q) =
      ∑ p ∈ putnam_2015_b6_pairDomain K, putnam_2015_b6_pairTerm p := by
  classical
  let toPair : (Σ _ : ℕ, ℕ) → ℕ × ℕ :=
    fun q ↦ (2 * q.1 + 1, q.1 + q.2 + 1)
  let toRow : ℕ × ℕ → (Σ _ : ℕ, ℕ) :=
    fun p ↦ Sigma.mk (p.1 / 2) (p.2 - (p.1 / 2 + 1))
  refine Finset.sum_nbij' (s := putnam_2015_b6_rowSigmaDomain K)
    (t := putnam_2015_b6_pairDomain K)
    (f := putnam_2015_b6_rowSigmaTerm) (g := putnam_2015_b6_pairTerm)
    toPair toRow ?hi ?hj ?left ?right ?term
  · intro q hq
    rcases q with ⟨n, r⟩
    simp only [putnam_2015_b6_rowSigmaDomain, Finset.mem_sigma, Finset.mem_range] at hq
    rcases hq with ⟨_hnK, hr⟩
    let j := 2 * n + 1
    let m := n + r + 1
    have hjpos : 0 < j := by dsimp [j]; omega
    have hmpos : 0 < m := by dsimp [m]; omega
    have hqle : m ≤ K / j := by dsimp [m, j] at *; omega
    have hprod_le : j * m ≤ K := by
      exact (Nat.mul_le_mul_left j hqle).trans (Nat.mul_div_le K j)
    have hjle : j ≤ K := (Nat.le_mul_of_pos_right j hmpos).trans hprod_le
    have hmle : m ≤ K := (Nat.le_mul_of_pos_left m hjpos).trans hprod_le
    have hodd : Odd j := by
      dsimp [j]
      exact odd_iff_exists_bit1.mpr ⟨n, rfl⟩
    have hsqrt : (j : ℝ) < Real.sqrt (2 * (((j * m : ℕ) : ℝ))) := by
      dsimp [j, m]
      exact putnam_2015_b6_row_lower_to_sqrt (by omega : n + 1 ≤ n + r + 1)
    simp only [putnam_2015_b6_pairDomain, toPair, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ioc]
    exact ⟨⟨⟨hjpos, hjle⟩, ⟨hmpos, hmle⟩⟩, hprod_le, hodd,
      by simpa [j, m] using hsqrt⟩
  · intro p hp
    rcases p with ⟨j, m⟩
    simp only [putnam_2015_b6_pairDomain, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hjI, _hmI⟩, hprod_le, hjodd, hsqrt⟩
    have hjpos : 0 < j := hjI.1
    have hform : j = 2 * (j / 2) + 1 :=
      putnam_2015_b6_odd_eq_two_mul_div_two_add_one hjodd
    have hmge : j / 2 + 1 ≤ m :=
      putnam_2015_b6_sqrt_cond_to_m_ge hjpos hjodd hsqrt
    have hm_le_div : m ≤ K / j := by
      exact (Nat.le_div_iff_mul_le hjpos).2 (by simpa [Nat.mul_comm] using hprod_le)
    have hnK : j / 2 < K + 1 := by omega
    have hrange : m - (j / 2 + 1) < K / (2 * (j / 2) + 1) - j / 2 := by
      rw [← hform]
      omega
    simp [putnam_2015_b6_rowSigmaDomain, toRow, hnK, hrange]
  · intro q _hq
    rcases q with ⟨n, r⟩
    simp [toPair, toRow]
    constructor <;> omega
  · intro p hp
    rcases p with ⟨j, m⟩
    simp only [putnam_2015_b6_pairDomain, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hjI, _hmI⟩, _hprod_le, hjodd, hsqrt⟩
    have hform : j = 2 * (j / 2) + 1 :=
      putnam_2015_b6_odd_eq_two_mul_div_two_add_one hjodd
    have hmge : j / 2 + 1 ≤ m :=
      putnam_2015_b6_sqrt_cond_to_m_ge hjI.1 hjodd hsqrt
    simp [toPair, toRow]
    constructor <;> omega
  · intro q _hq
    rcases q with ⟨n, r⟩
    simp [putnam_2015_b6_rowSigmaTerm, putnam_2015_b6_pairTerm, toPair]

private lemma putnam_2015_b6_partial_sum_eq_pairDomain
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ))) =
      ∑ p ∈ putnam_2015_b6_pairDomain K, putnam_2015_b6_pairTerm p := by
  have hI : Finset.Icc 1 K = Finset.Ioc 0 K := by
    ext k
    simp
    omega
  rw [hI]
  calc
    (∑ k ∈ Finset.Ioc 0 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ)))
        = ∑ k ∈ Finset.Ioc 0 K,
            ∑ p ∈ (Nat.divisorsAntidiagonal k).filter (fun p : ℕ × ℕ ↦
              Odd p.1 ∧ (p.1 : ℝ) < Real.sqrt (2 * (k : ℝ))),
              putnam_2015_b6_pairTerm p := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hkpos : 0 < k := (Finset.mem_Ioc.mp hk).1
          rw [putnam_2015_b6_term_to_divisor_sum A hA hkpos]
          exact putnam_2015_b6_divisor_sum_to_antidiagonal (k := k)
    _ = ∑ p ∈ putnam_2015_b6_pairDomain K, putnam_2015_b6_pairTerm p :=
      putnam_2015_b6_antidiagonal_sum_eq_pairDomain K

private lemma putnam_2015_b6_partial_sum_eq_row_tsum
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard)
    (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ))) =
      ∑' n : ℕ, putnam_2015_b6_row n (K / (2 * n + 1) - n) := by
  calc
    (∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ)))
        = ∑ p ∈ putnam_2015_b6_pairDomain K, putnam_2015_b6_pairTerm p :=
          putnam_2015_b6_partial_sum_eq_pairDomain A hA K
    _ = ∑ q ∈ putnam_2015_b6_rowSigmaDomain K, putnam_2015_b6_rowSigmaTerm q :=
      (putnam_2015_b6_rowSigma_sum_eq_pairDomain K).symm
    _ = ∑ n ∈ Finset.range (K + 1), putnam_2015_b6_row n (K / (2 * n + 1) - n) :=
      (putnam_2015_b6_row_sum_eq_rowSigma K).symm
    _ = ∑' n : ℕ, putnam_2015_b6_row n (K / (2 * n + 1) - n) :=
      (putnam_2015_b6_tsum_rows_eq_sum K).symm

/--
For each positive integer $k$, let $A(k)$ be the number of odd divisors of $k$ in the interval $[1,\sqrt{2k})$. Evaluate $\sum_{k=1}^\infty (-1)^{k-1}\frac{A(k)}{k}$.
-/
theorem putnam_2015_b6
    (A : ℕ → ℕ)
    (hA : ∀ k > 0, A k = {j : ℕ | Odd j ∧ j ∣ k ∧ j < Real.sqrt (2 * k)}.encard) :
    Tendsto (fun K : ℕ ↦ ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ ((k : ℝ) - 1) * (A k / (k : ℝ)))
      atTop (𝓝 putnam_2015_b6_solution) :=
  putnam_2015_b6_rows_tendsto.congr' <|
    Filter.Eventually.of_forall fun K ↦ (putnam_2015_b6_partial_sum_eq_row_tsum A hA K).symm
