import Mathlib

open Topology Filter Nat Set Function

private lemma putnam_2000_b3_mult_eq_zero_of_ne_zero
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  {g : ℝ → ℝ} {t : ℝ} (hgt : g t ≠ 0) :
  mult g t = 0 := by
  refine Nat.eq_zero_of_not_pos ?_
  intro hpos
  rcases hmult g t ⟨0, by simpa using hgt⟩ with ⟨_, hzero⟩
  exact hgt (by simpa using hzero 0 hpos)

private lemma putnam_2000_b3_mult_pos_iff_eq_zero
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  {g : ℝ → ℝ} {t : ℝ} (hnotflat : ∃ c : ℕ, iteratedDeriv c g t ≠ 0) :
  0 < mult g t ↔ g t = 0 := by
  constructor
  · intro hpos
    rcases hmult g t hnotflat with ⟨_, hzero⟩
    simpa using hzero 0 hpos
  · intro hgt
    rcases hmult g t hnotflat with ⟨hnonzero, _⟩
    exact Nat.pos_of_ne_zero fun hmult0 => hnonzero (by simpa [hmult0] using hgt)

private lemma putnam_2000_b3_mult_eq_analyticOrderNatAt
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  {g : ℝ → ℝ} {t : ℝ}
  (hg : AnalyticAt ℝ g t) (hfinite : analyticOrderAt g t ≠ ⊤) :
  mult g t = analyticOrderNatAt g t := by
  classical
  let n := analyticOrderNatAt g t
  have hncast : (n : ℕ∞) = analyticOrderAt g t := by
    simpa [n] using (Nat.cast_analyticOrderNatAt (f := g) (z₀ := t) hfinite)
  have hzero_lt_n : ∀ i < n, iteratedDeriv i g t = 0 := by
    have hle : (n : ℕ∞) ≤ analyticOrderAt g t := by rw [hncast]
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (𝕜 := ℝ) (E := ℝ) (f := g) (z₀ := t) (n := n) hg).1 hle
  have hn_nonzero : iteratedDeriv n g t ≠ 0 := by
    intro hnzero
    have hzero_succ : ∀ i < n + 1, iteratedDeriv i g t = 0 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hzero_lt_n i hi
      · exact hnzero
    have hle_succ :
        ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g t :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (𝕜 := ℝ) (E := ℝ) (f := g) (z₀ := t) (n := n + 1) hg).2 hzero_succ
    rw [← hncast] at hle_succ
    exact Nat.not_succ_le_self n (ENat.coe_le_coe.mp hle_succ)
  rcases hmult g t ⟨n, hn_nonzero⟩ with ⟨hm_nonzero, hzero_lt_m⟩
  apply le_antisymm
  · exact Nat.le_of_not_gt fun hlt => hn_nonzero (hzero_lt_m n hlt)
  · exact Nat.le_of_not_gt fun hlt => hm_nonzero (hzero_lt_n (mult g t) hlt)

private lemma putnam_2000_b3_mult_deriv_add_one
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  {g : ℝ → ℝ} {t : ℝ}
  (hnotflat : ∃ c : ℕ, iteratedDeriv c g t ≠ 0) (hzero : g t = 0) :
  mult (deriv g) t + 1 = mult g t := by
  classical
  let m := mult g t
  have hmpos : 0 < m := by
    exact (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult hnotflat).2 hzero
  rcases hmult g t hnotflat with ⟨hm_nonzero, hm_zero_lt⟩
  have hm_nonzero_m : iteratedDeriv m g t ≠ 0 := by
    simpa [m] using hm_nonzero
  have hsucc : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hmpos
  have hderiv_nonzero : iteratedDeriv (m - 1) (deriv g) t ≠ 0 := by
    have h := hm_nonzero_m
    rw [← hsucc] at h
    simpa [iteratedDeriv_succ'] using h
  rcases hmult (deriv g) t ⟨m - 1, hderiv_nonzero⟩ with
    ⟨hmd_nonzero, hmd_zero_lt⟩
  have hmd_eq : mult (deriv g) t = m - 1 := by
    apply le_antisymm
    · exact Nat.le_of_not_gt fun hlt => hderiv_nonzero (hmd_zero_lt (m - 1) hlt)
    · refine Nat.le_of_not_gt fun hlt => hmd_nonzero ?_
      have hltm : mult (deriv g) t + 1 < m := by omega
      have hzero_succ := hm_zero_lt (mult (deriv g) t + 1) hltm
      simpa [iteratedDeriv_succ'] using hzero_succ
  rw [hmd_eq, hsucc]

private lemma putnam_2000_b3_tendsto_nat_nhds_iff_eventually_eq
  {u : ℕ → ℕ} {m : ℕ} :
  Tendsto u atTop (𝓝 m) ↔ ∀ᶠ n in atTop, u n = m := by
  constructor
  · intro hu
    have hsingleton : ({m} : Set ℕ) ∈ 𝓝 m := by
      simp
    filter_upwards [hu hsingleton] with n hn
    simpa using hn
  · intro hu s hs
    have hms : m ∈ s := by
      simpa [mem_nhds_discrete] using hs
    rw [mem_map]
    filter_upwards [hu] with n hn
    simpa [hn] using hms

private lemma putnam_2000_b3_tsum_eq_sum_of_support_finite
  {α : Type*} (u : α → ℕ) (hs : (Function.support u).Finite) :
  (∑' a : α, u a) = ∑ a ∈ hs.toFinset, u a := by
  classical
  exact tsum_eq_sum fun a ha => by
    have hanot : a ∉ Function.support u := by
      simpa [Set.Finite.mem_toFinset] using ha
    simpa [Function.mem_support] using hanot

private lemma putnam_2000_b3_card_le_tsum_mult_of_injective_zeros
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  {g : ℝ → ℝ} {m : ℕ} (z : Fin m → Ico (0 : ℝ) 1)
  (hz : ∀ i, g (z i : ℝ) = 0)
  (hnotflat : ∀ i, ∃ c : ℕ, iteratedDeriv c g (z i : ℝ) ≠ 0)
  (hinj : Function.Injective z)
  (hs : (Function.support fun t : Ico (0 : ℝ) 1 => mult g (t : ℝ)).Finite) :
  m ≤ ∑' t : Ico (0 : ℝ) 1, mult g (t : ℝ) := by
  classical
  let u : Ico (0 : ℝ) 1 → ℕ := fun t => mult g (t : ℝ)
  let S := hs.toFinset
  have hzS : ∀ i, z i ∈ S := by
    intro i
    have hpos : 0 < u (z i) :=
      (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult (hnotflat i)).2 (hz i)
    have hmem : z i ∈ Function.support u := by
      simpa [Function.mem_support, u] using hpos.ne'
    simpa [S, Set.Finite.mem_toFinset, u] using hmem
  let emb : Fin m → {x // x ∈ S} := fun i => ⟨z i, hzS i⟩
  have hemb : Function.Injective emb := by
    intro i j hij
    exact hinj (Subtype.ext_iff.mp hij)
  have hcard : m ≤ S.card := by
    simpa [emb, S] using Fintype.card_le_of_injective emb hemb
  have hSsum : S.card ≤ ∑ t ∈ S, u t := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun t ht => by
      have htmem : t ∈ Function.support u := by
        simpa [S, Set.Finite.mem_toFinset] using ht
      exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (by
        simpa [Function.mem_support] using htmem))
  rw [putnam_2000_b3_tsum_eq_sum_of_support_finite u hs]
  exact hcard.trans hSsum

private lemma putnam_2000_b3_iteratedDeriv_finset_sum
  {ι : Type*} (s : Finset ι) (u : ι → ℝ → ℝ) (k : ℕ) (t : ℝ)
  (hu : ∀ i ∈ s, ContDiff ℝ k (u i)) :
  iteratedDeriv k (fun x => ∑ i ∈ s, u i x) t =
    ∑ i ∈ s, iteratedDeriv k (u i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (iteratedDeriv_const (n := k) (c := (0 : ℝ)) (x := t))
  | insert i s his ih =>
      simp only [Finset.sum_insert his]
      have hui : ContDiffAt ℝ k (u i) t :=
        (hu i (Finset.mem_insert_self i s)).contDiffAt
      have hus : ContDiffAt ℝ k (fun x => ∑ j ∈ s, u j x) t := by
        exact (ContDiff.sum fun j hj => hu j (Finset.mem_insert_of_mem hj)).contDiffAt
      rw [iteratedDeriv_fun_add hui hus]
      rw [ih]
      intro j hj
      exact hu j (Finset.mem_insert_of_mem hj)

private lemma putnam_2000_b3_iteratedDeriv_fintype_sum
  {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ) (k : ℕ) (t : ℝ)
  (hu : ∀ i, ContDiff ℝ k (u i)) :
  iteratedDeriv k (fun x => ∑ i : ι, u i x) t =
    ∑ i : ι, iteratedDeriv k (u i) t := by
  classical
  simpa using
    putnam_2000_b3_iteratedDeriv_finset_sum (s := Finset.univ) (u := u) k t
      (fun i _ => hu i)

private lemma putnam_2000_b3_iteratedDeriv_sin_linear (c : ℝ) (k : ℕ) :
  iteratedDeriv k (fun t : ℝ => Real.sin (c * t)) =
    fun t : ℝ => c ^ k * iteratedDeriv k Real.sin (c * t) := by
  simpa using
    (iteratedDeriv_comp_const_mul (𝕜 := ℝ) (f := Real.sin) (n := k)
      Real.contDiff_sin c)

private lemma putnam_2000_b3_iteratedDeriv_const_mul_sin_linear
  (A c : ℝ) (k : ℕ) (t : ℝ) :
  iteratedDeriv k (fun x : ℝ => A * Real.sin (c * x)) t =
    A * c ^ k * iteratedDeriv k Real.sin (c * t) := by
  rw [iteratedDeriv_const_mul]
  · rw [putnam_2000_b3_iteratedDeriv_sin_linear]
    ring
  · exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffAt

private lemma putnam_2000_b3_iteratedDeriv_eq_sum
  (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) (t : ℝ) :
  iteratedDeriv k f t =
    ∑ j : Icc 1 N, a j * (2 * Real.pi * j) ^ k *
      iteratedDeriv k Real.sin ((2 * Real.pi * j) * t) := by
  classical
  calc
    iteratedDeriv k f t =
        iteratedDeriv k
          (fun x : ℝ => ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * x)) t := by
      exact Filter.EventuallyEq.iteratedDeriv_eq k (Eventually.of_forall fun x => hf x)
    _ =
        ∑ j : Icc 1 N,
          iteratedDeriv k (fun x : ℝ => a j * Real.sin (2 * Real.pi * j * x)) t := by
      apply putnam_2000_b3_iteratedDeriv_fintype_sum
      intro j
      fun_prop
    _ =
        ∑ j : Icc 1 N, a j * (2 * Real.pi * j) ^ k *
          iteratedDeriv k Real.sin ((2 * Real.pi * j) * t) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact putnam_2000_b3_iteratedDeriv_const_mul_sin_linear
        (a j) (2 * Real.pi * j) k t

private lemma putnam_2000_b3_periodic_iteratedDeriv_sin (k : ℕ) :
  Function.Periodic (iteratedDeriv k Real.sin) (2 * Real.pi) := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [Real.iteratedDeriv_even_sin]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Real.sin_periodic.smul ((-1 : ℝ) ^ n)
  · rw [Real.iteratedDeriv_odd_sin]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Real.cos_periodic.smul ((-1 : ℝ) ^ n)

private lemma putnam_2000_b3_abs_iteratedDeriv_sin_le_one (k : ℕ) (x : ℝ) :
  |iteratedDeriv k Real.sin x| ≤ 1 := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [Real.iteratedDeriv_even_sin]
    calc
      |((-1 : ℝ) ^ n • Real.sin) x| =
          |(-1 : ℝ) ^ n| * |Real.sin x| := by
            simp [abs_mul]
      _ = |Real.sin x| := by simp
      _ ≤ 1 := Real.abs_sin_le_one x
  · rw [Real.iteratedDeriv_odd_sin]
    calc
      |((-1 : ℝ) ^ n • Real.cos) x| =
          |(-1 : ℝ) ^ n| * |Real.cos x| := by
            simp [abs_mul]
      _ = |Real.cos x| := by simp
      _ ≤ 1 := Real.abs_cos_le_one x

private lemma putnam_2000_b3_tendsto_lower_freq_scaled
  {N : ℕ} (hN : 0 < N) (j : Icc 1 N) (hj : (j : ℕ) < N) (x : ℝ) :
  Tendsto
    (fun k : ℕ =>
      (((j : ℕ) : ℝ) / (N : ℝ)) ^ k *
        iteratedDeriv k Real.sin x)
    atTop (𝓝 0) := by
  have hj_nonneg : 0 ≤ (((j : ℕ) : ℝ) / (N : ℝ)) := by positivity
  have hj_lt_one : (((j : ℕ) : ℝ) / (N : ℝ)) < 1 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_one hNpos]
    exact_mod_cast hj
  have hpow :
      Tendsto (fun k : ℕ => (((j : ℕ) : ℝ) / (N : ℝ)) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hj_nonneg hj_lt_one
  have hbounded :
      IsBoundedUnder (fun y z : ℝ => y ≤ z) (atTop : Filter ℕ)
        (fun k : ℕ => ‖iteratedDeriv k Real.sin x‖) := by
    refine Filter.isBoundedUnder_of (r := fun y z : ℝ => y ≤ z)
      (f := (atTop : Filter ℕ))
      (u := fun k : ℕ => ‖iteratedDeriv k Real.sin x‖) ⟨1, ?_⟩
    intro k
    simpa [Real.norm_eq_abs] using putnam_2000_b3_abs_iteratedDeriv_sin_le_one k x
  simpa [Pi.smul_apply, smul_eq_mul] using hpow.zero_mul_isBoundedUnder_le hbounded

private lemma putnam_2000_b3_tendsto_scaled_lower_sum
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (t : ℝ) :
  Tendsto
    (fun k : ℕ =>
      ∑ j : Icc 1 N,
        (if (j : ℕ) = N then 0 else
          a j * ((((j : ℕ) : ℝ) / (N : ℝ)) ^ k *
            iteratedDeriv k Real.sin ((2 * Real.pi * (j : ℕ)) * t))))
    atTop (𝓝 0) := by
  classical
  have hsum :
      Tendsto
        (fun k : ℕ =>
          ∑ j ∈ (Finset.univ : Finset (Icc 1 N)),
            (if (j : ℕ) = N then 0 else
              a j * ((((j : ℕ) : ℝ) / (N : ℝ)) ^ k *
                iteratedDeriv k Real.sin ((2 * Real.pi * (j : ℕ)) * t))))
        atTop
        (𝓝 (∑ j ∈ (Finset.univ : Finset (Icc 1 N)), (0 : ℝ))) := by
    apply tendsto_finset_sum
    intro j _hj
    by_cases hjN : (j : ℕ) = N
    · simp [hjN]
    · have hjlt : (j : ℕ) < N := by
        exact lt_of_le_of_ne j.property.2 hjN
      simpa [hjN, mul_assoc] using
        (putnam_2000_b3_tendsto_lower_freq_scaled hN j hjlt
          ((2 * Real.pi * (j : ℕ)) * t)).const_mul (a j)
  simpa using hsum

private lemma putnam_2000_b3_scaled_iteratedDeriv_eq_sum
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) (t : ℝ) :
  iteratedDeriv k f t / (2 * Real.pi * (N : ℝ)) ^ k =
    ∑ j : Icc 1 N,
      a j * ((((j : ℕ) : ℝ) / (N : ℝ)) ^ k *
        iteratedDeriv k Real.sin ((2 * Real.pi * (j : ℕ)) * t)) := by
  classical
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have htwopi : 2 * Real.pi ≠ 0 := by positivity
  rw [putnam_2000_b3_iteratedDeriv_eq_sum N a f hf k t, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  have hratio :
      (2 * Real.pi * ((j : ℕ) : ℝ)) ^ k /
          (2 * Real.pi * (N : ℝ)) ^ k =
        (((j : ℕ) : ℝ) / (N : ℝ)) ^ k := by
    rw [← div_pow]
    congr 1
    field_simp [htwopi, hNreal]
  rw [← hratio]
  ring

private lemma putnam_2000_b3_iteratedDeriv_four_mul_sin (n : ℕ) (x : ℝ) :
  iteratedDeriv (4 * n) Real.sin x = Real.sin x := by
  have hidx : 4 * n = 2 * (2 * n) := by ring
  rw [hidx, Real.iteratedDeriv_even_sin]
  simp [pow_mul]

private lemma putnam_2000_b3_iteratedDeriv_four_mul_add_one_sin (n : ℕ) (x : ℝ) :
  iteratedDeriv (4 * n + 1) Real.sin x = Real.cos x := by
  have hidx : 4 * n + 1 = 2 * (2 * n) + 1 := by ring
  rw [hidx, Real.iteratedDeriv_odd_sin]
  simp [pow_mul]

private lemma putnam_2000_b3_iteratedDeriv_four_mul_add_two_sin (n : ℕ) (x : ℝ) :
  iteratedDeriv (4 * n + 2) Real.sin x = -Real.sin x := by
  have hidx : 4 * n + 2 = 2 * (2 * n + 1) := by ring
  rw [hidx, Real.iteratedDeriv_even_sin]
  simp [pow_succ, pow_mul]

private lemma putnam_2000_b3_iteratedDeriv_four_mul_add_three_sin (n : ℕ) (x : ℝ) :
  iteratedDeriv (4 * n + 3) Real.sin x = -Real.cos x := by
  have hidx : 4 * n + 3 = 2 * (2 * n + 1) + 1 := by ring
  rw [hidx, Real.iteratedDeriv_odd_sin]
  simp [pow_succ, pow_mul]

private lemma putnam_2000_b3_tendsto_four_mul_atTop :
  Tendsto (fun n : ℕ => 4 * n) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_id
  have h : 1 * n ≤ 4 * n := Nat.mul_le_mul_right n (by norm_num)
  simpa using h

private lemma putnam_2000_b3_tendsto_four_mul_add_atTop (r : ℕ) :
  Tendsto (fun n : ℕ => 4 * n + r) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_id
  have h : 1 * n ≤ 4 * n := Nat.mul_le_mul_right n (by norm_num)
  have hn : n ≤ 4 * n := by simpa using h
  exact hn.trans (Nat.le_add_right (4 * n) r)

private lemma putnam_2000_b3_tendsto_scaled_subseq
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (t s : ℝ)
  (htop : ∀ n : ℕ,
    iteratedDeriv (q n) Real.sin ((2 * Real.pi * (N : ℕ)) * t) = s) :
  Tendsto
    (fun n : ℕ =>
      iteratedDeriv (q n) f t / (2 * Real.pi * (N : ℝ)) ^ (q n))
    atTop
    (𝓝 (a ⟨N, by simp; omega⟩ * s)) := by
  classical
  let top : Icc 1 N := ⟨N, by simp; omega⟩
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ j : Icc 1 N,
            a j * ((((j : ℕ) : ℝ) / (N : ℝ)) ^ (q n) *
              iteratedDeriv (q n) Real.sin ((2 * Real.pi * (j : ℕ)) * t)))
        atTop
        (𝓝 (∑ j : Icc 1 N,
          if (j : ℕ) = N then a top * s else 0)) := by
    apply tendsto_finset_sum
    intro j _hj
    by_cases hjN : (j : ℕ) = N
    · have hjtop : j = top := Subtype.ext hjN
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      subst j
      simp [top, hNreal, htop]
    · have hjlt : (j : ℕ) < N := by
        exact lt_of_le_of_ne j.property.2 hjN
      have hbase :=
        (putnam_2000_b3_tendsto_lower_freq_scaled hN j hjlt
          ((2 * Real.pi * (j : ℕ)) * t)).comp hq
      simpa [hjN, mul_assoc] using hbase.const_mul (a j)
  have hfun :
      (fun n : ℕ =>
        iteratedDeriv (q n) f t / (2 * Real.pi * (N : ℝ)) ^ (q n)) =
      fun n : ℕ =>
        ∑ j : Icc 1 N,
          a j * ((((j : ℕ) : ℝ) / (N : ℝ)) ^ (q n) *
            iteratedDeriv (q n) Real.sin ((2 * Real.pi * (j : ℕ)) * t)) := by
    funext n
    exact putnam_2000_b3_scaled_iteratedDeriv_eq_sum N hN a f hf (q n) t
  rw [hfun]
  have hlimit :
      (∑ j : Icc 1 N, if (j : ℕ) = N then a top * s else 0) =
        a top * s := by
    rw [Finset.sum_eq_single top]
    · simp [top]
    · intro j _hj hjtop
      have hjN : (j : ℕ) ≠ N := by
        intro h
        exact hjtop (Subtype.ext h)
      simp [hjN]
    · intro htopmem
      simp at htopmem
  simpa [hlimit] using hsum

private lemma putnam_2000_b3_tendsto_scaled_four_mul
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (t : ℝ) :
  Tendsto
    (fun n : ℕ =>
      iteratedDeriv (4 * n) f t / (2 * Real.pi * (N : ℝ)) ^ (4 * n))
    atTop
    (𝓝 (a ⟨N, by simp; omega⟩ * Real.sin ((2 * Real.pi * (N : ℕ)) * t))) := by
  classical
  let top : Icc 1 N := ⟨N, by simp; omega⟩
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ j : Icc 1 N,
            a j * ((((j : ℕ) : ℝ) / (N : ℝ)) ^ (4 * n) *
              iteratedDeriv (4 * n) Real.sin ((2 * Real.pi * (j : ℕ)) * t)))
        atTop
        (𝓝 (∑ j : Icc 1 N,
          if (j : ℕ) = N then
            a top * Real.sin ((2 * Real.pi * (N : ℕ)) * t)
          else 0)) := by
    apply tendsto_finset_sum
    intro j _hj
    by_cases hjN : (j : ℕ) = N
    · have hjtop : j = top := Subtype.ext hjN
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      subst j
      simp [top, putnam_2000_b3_iteratedDeriv_four_mul_sin, hNreal]
    · have hjlt : (j : ℕ) < N := by
        exact lt_of_le_of_ne j.property.2 hjN
      have hbase :=
        (putnam_2000_b3_tendsto_lower_freq_scaled hN j hjlt
          ((2 * Real.pi * (j : ℕ)) * t)).comp
          putnam_2000_b3_tendsto_four_mul_atTop
      simpa [hjN, mul_assoc] using hbase.const_mul (a j)
  have hfun :
      (fun n : ℕ =>
        iteratedDeriv (4 * n) f t / (2 * Real.pi * (N : ℝ)) ^ (4 * n)) =
      fun n : ℕ =>
        ∑ j : Icc 1 N,
          a j * ((((j : ℕ) : ℝ) / (N : ℝ)) ^ (4 * n) *
            iteratedDeriv (4 * n) Real.sin ((2 * Real.pi * (j : ℕ)) * t)) := by
    funext n
    exact putnam_2000_b3_scaled_iteratedDeriv_eq_sum N hN a f hf (4 * n) t
  rw [hfun]
  have hlimit :
      (∑ j : Icc 1 N,
        if (j : ℕ) = N then
          a top * Real.sin ((2 * Real.pi * (N : ℕ)) * t)
        else 0) =
        a top * Real.sin ((2 * Real.pi * (N : ℕ)) * t) := by
    rw [Finset.sum_eq_single top]
    · simp [top]
    · intro j _hj hjtop
      have hjN : (j : ℕ) ≠ N := by
        intro h
        exact hjtop (Subtype.ext h)
      simp [hjN]
    · intro htop
      simp at htop
  simpa [hlimit] using hsum

private lemma putnam_2000_b3_tendsto_scaled_four_mul_add_one
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (t : ℝ) :
  Tendsto
    (fun n : ℕ =>
      iteratedDeriv (4 * n + 1) f t / (2 * Real.pi * (N : ℝ)) ^ (4 * n + 1))
    atTop
    (𝓝 (a ⟨N, by simp; omega⟩ * Real.cos ((2 * Real.pi * (N : ℕ)) * t))) := by
  refine putnam_2000_b3_tendsto_scaled_subseq N hN a f hf
    (fun n : ℕ => 4 * n + 1)
    (putnam_2000_b3_tendsto_four_mul_add_atTop 1) t
    (Real.cos ((2 * Real.pi * (N : ℕ)) * t)) ?_
  intro n
  exact putnam_2000_b3_iteratedDeriv_four_mul_add_one_sin n
    ((2 * Real.pi * (N : ℕ)) * t)

private lemma putnam_2000_b3_tendsto_scaled_four_mul_add_two
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (t : ℝ) :
  Tendsto
    (fun n : ℕ =>
      iteratedDeriv (4 * n + 2) f t / (2 * Real.pi * (N : ℝ)) ^ (4 * n + 2))
    atTop
    (𝓝 (a ⟨N, by simp; omega⟩ * (-Real.sin ((2 * Real.pi * (N : ℕ)) * t)))) := by
  refine putnam_2000_b3_tendsto_scaled_subseq N hN a f hf
    (fun n : ℕ => 4 * n + 2)
    (putnam_2000_b3_tendsto_four_mul_add_atTop 2) t
    (-Real.sin ((2 * Real.pi * (N : ℕ)) * t)) ?_
  intro n
  exact putnam_2000_b3_iteratedDeriv_four_mul_add_two_sin n
    ((2 * Real.pi * (N : ℕ)) * t)

private lemma putnam_2000_b3_tendsto_scaled_four_mul_add_three
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (t : ℝ) :
  Tendsto
    (fun n : ℕ =>
      iteratedDeriv (4 * n + 3) f t / (2 * Real.pi * (N : ℝ)) ^ (4 * n + 3))
    atTop
    (𝓝 (a ⟨N, by simp; omega⟩ * (-Real.cos ((2 * Real.pi * (N : ℕ)) * t)))) := by
  refine putnam_2000_b3_tendsto_scaled_subseq N hN a f hf
    (fun n : ℕ => 4 * n + 3)
    (putnam_2000_b3_tendsto_four_mul_add_atTop 3) t
    (-Real.cos ((2 * Real.pi * (N : ℕ)) * t)) ?_
  intro n
  exact putnam_2000_b3_iteratedDeriv_four_mul_add_three_sin n
    ((2 * Real.pi * (N : ℕ)) * t)

private lemma putnam_2000_b3_periodic_iteratedDeriv_sin_freq
  {N : ℕ} (j : Icc 1 N) (k : ℕ) :
  Function.Periodic
    (fun t : ℝ => iteratedDeriv k Real.sin ((2 * Real.pi * j) * t)) 1 := by
  intro t
  have hp :=
    (putnam_2000_b3_periodic_iteratedDeriv_sin k).nat_mul (j : ℕ)
      ((2 * Real.pi * j) * t)
  calc
    iteratedDeriv k Real.sin ((2 * Real.pi * j) * (t + 1))
        = iteratedDeriv k Real.sin ((2 * Real.pi * j) * t + (j : ℝ) * (2 * Real.pi)) := by
          congr 1
          ring
    _ = iteratedDeriv k Real.sin ((2 * Real.pi * j) * t) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hp

private lemma putnam_2000_b3_periodic_iteratedDeriv_f
  (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) :
  Function.Periodic (iteratedDeriv k f) 1 := by
  classical
  intro t
  rw [putnam_2000_b3_iteratedDeriv_eq_sum N a f hf k (t + 1),
    putnam_2000_b3_iteratedDeriv_eq_sum N a f hf k t]
  apply Finset.sum_congr rfl
  intro j _hj
  have hp := putnam_2000_b3_periodic_iteratedDeriv_sin_freq j k t
  simpa [mul_assoc] using
    congrArg (fun y => a j * (2 * Real.pi * j) ^ k * y) hp

private lemma putnam_2000_b3_contDiff_iteratedDeriv_sin (k : ℕ) :
  ContDiff ℝ ⊤ (iteratedDeriv k Real.sin) := by
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [Real.iteratedDeriv_even_sin]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Real.contDiff_sin.const_smul ((-1 : ℝ) ^ n)
  · rw [Real.iteratedDeriv_odd_sin]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Real.contDiff_cos.const_smul ((-1 : ℝ) ^ n)

private lemma putnam_2000_b3_contDiff_iteratedDeriv_sum
  (N : ℕ) (a : Icc 1 N → ℝ) (k : ℕ) :
  ContDiff ℝ ⊤
    (fun t : ℝ => ∑ j : Icc 1 N, a j * (2 * Real.pi * j) ^ k *
      iteratedDeriv k Real.sin ((2 * Real.pi * j) * t)) := by
  classical
  apply ContDiff.sum
  intro j _hj
  have hsin : ContDiff ℝ ⊤
      (fun t : ℝ => iteratedDeriv k Real.sin ((2 * Real.pi * j) * t)) :=
    (putnam_2000_b3_contDiff_iteratedDeriv_sin k).comp
      (contDiff_const.mul contDiff_id)
  simpa only [Pi.smul_apply, smul_eq_mul] using
    hsin.const_smul (a j * (2 * Real.pi * j) ^ k)

private lemma putnam_2000_b3_contDiff_iteratedDeriv_f
  (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) :
  ContDiff ℝ ⊤ (iteratedDeriv k f) := by
  classical
  have hfun :
      iteratedDeriv k f =
        fun t : ℝ => ∑ j : Icc 1 N, a j * (2 * Real.pi * j) ^ k *
          iteratedDeriv k Real.sin ((2 * Real.pi * j) * t) := by
    funext t
    exact putnam_2000_b3_iteratedDeriv_eq_sum N a f hf k t
  rw [hfun]
  exact putnam_2000_b3_contDiff_iteratedDeriv_sum N a k

private lemma putnam_2000_b3_analyticOnNhd_iteratedDeriv_f
  (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) :
  AnalyticOnNhd ℝ (iteratedDeriv k f) Set.univ := by
  exact (putnam_2000_b3_contDiff_iteratedDeriv_f N a f hf k).analyticOnNhd

private lemma putnam_2000_b3_finite_zero_set_Icc_of_analytic_nonzero
  {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ) {x : ℝ} (hx : g x ≠ 0) :
  ((g ⁻¹' ({0} : Set ℝ)) ∩ Icc (0 : ℝ) 1).Finite := by
  classical
  have hcod : (g ⁻¹' ({0} : Set ℝ))ᶜ ∈ Filter.codiscreteWithin (Icc (0 : ℝ) 1) := by
    exact Filter.codiscreteWithin.mono (U₁ := Icc (0 : ℝ) 1) (U := Set.univ)
      (by intro y hy; trivial) (hg.preimage_zero_mem_codiscrete hx)
  have hdisc : IsDiscrete ((g ⁻¹' ({0} : Set ℝ)) ∩ Icc (0 : ℝ) 1) :=
    isDiscrete_of_codiscreteWithin hcod
  have hcont : Continuous g := (hg.contDiff (n := (0 : WithTop ℕ∞))).continuous
  have hclosed : IsClosed (g ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hcont
  exact (isCompact_Icc.inter_left hclosed).finite hdisc

private lemma putnam_2000_b3_mult_support_finite_Ico_of_finite_zero_set
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  {g : ℝ → ℝ}
  (hzeros : ((g ⁻¹' ({0} : Set ℝ)) ∩ Icc (0 : ℝ) 1).Finite) :
  (Function.support fun t : Ico (0 : ℝ) 1 => mult g t).Finite := by
  classical
  let zIco : Set ℝ := (g ⁻¹' ({0} : Set ℝ)) ∩ Ico (0 : ℝ) 1
  have hzIco : zIco.Finite := by
    refine hzeros.subset ?_
    intro x hx
    exact ⟨hx.1, hx.2.1, le_of_lt hx.2.2⟩
  have hpre :
      ((fun t : Ico (0 : ℝ) 1 => (t : ℝ)) ⁻¹' zIco).Finite := by
    refine hzIco.preimage ?_
    intro x _ y _ hxy
    exact Subtype.ext hxy
  refine hpre.subset ?_
  intro t ht
  change mult g (t : ℝ) ≠ 0 at ht
  have hgt : g (t : ℝ) = 0 := by
    by_contra hne
    exact ht (putnam_2000_b3_mult_eq_zero_of_ne_zero mult hmult hne)
  exact ⟨hgt, t.property⟩

private noncomputable def putnam_2000_b3_cosPoly
  (N : ℕ) (a : Icc 1 N → ℝ) (k : ℕ) : Polynomial ℝ :=
  ∑ j : Icc 1 N,
    Polynomial.C (a j * (2 * Real.pi * (j : ℕ)) ^ k) *
      Polynomial.Chebyshev.T ℝ (j : ℕ)

private noncomputable def putnam_2000_b3_sinPoly
  (N : ℕ) (a : Icc 1 N → ℝ) (k : ℕ) : Polynomial ℝ :=
  ∑ j : Icc 1 N,
    Polynomial.C (a j * (2 * Real.pi * (j : ℕ)) ^ k) *
      Polynomial.Chebyshev.U ℝ (((j : ℕ) - 1 : ℕ) : ℤ)

private lemma putnam_2000_b3_subtype_lt_top
  {N : ℕ} (hN : 0 < N) (j : Icc 1 N)
  (hj : j ≠ ⟨N, by simp; omega⟩) :
  (j : ℕ) < N := by
  have hjle : (j : ℕ) ≤ N := j.property.2
  have hjne : (j : ℕ) ≠ N := by
    intro h
    exact hj (Subtype.ext h)
  exact lt_of_le_of_ne hjle hjne

private lemma putnam_2000_b3_cosPoly_coeff_top
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (k : ℕ) :
  (putnam_2000_b3_cosPoly N a k).coeff N =
    a ⟨N, by simp; omega⟩ * (2 * Real.pi * N) ^ k * 2 ^ (N - 1) := by
  classical
  let top : Icc 1 N := ⟨N, by simp; omega⟩
  rw [putnam_2000_b3_cosPoly, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single top]
  · simp only [top]
    rw [Polynomial.coeff_C_mul]
    have hcoeffT : (Polynomial.Chebyshev.T ℝ (N : ℤ)).coeff N = 2 ^ (N - 1) := by
      have hdeg : (Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree = N := by simp
      calc
        (Polynomial.Chebyshev.T ℝ (N : ℤ)).coeff N =
            (Polynomial.Chebyshev.T ℝ (N : ℤ)).coeff
              (Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree := by rw [hdeg]
        _ = (Polynomial.Chebyshev.T ℝ (N : ℤ)).leadingCoeff := Polynomial.coeff_natDegree
        _ = 2 ^ (N - 1) := by
          rw [Polynomial.Chebyshev.leadingCoeff_T]
          simp [Int.natAbs_natCast]
    rw [hcoeffT]
  · intro j _hj hjtop
    rw [Polynomial.coeff_C_mul]
    have hjlt : (j : ℕ) < N :=
      putnam_2000_b3_subtype_lt_top hN j hjtop
    have hdeglt : (Polynomial.Chebyshev.T ℝ (j : ℤ)).natDegree < N := by
      simpa [Int.natAbs_natCast] using hjlt
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeglt, mul_zero]
  · intro htop
    simp at htop

private lemma putnam_2000_b3_sinPoly_coeff_top
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (k : ℕ) :
  (putnam_2000_b3_sinPoly N a k).coeff (N - 1) =
    a ⟨N, by simp; omega⟩ * (2 * Real.pi * N) ^ k * 2 ^ (N - 1) := by
  classical
  let top : Icc 1 N := ⟨N, by simp; omega⟩
  rw [putnam_2000_b3_sinPoly, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single top]
  · simp only [top]
    rw [Polynomial.coeff_C_mul]
    have hcoeffU :
        (Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).coeff (N - 1) =
          2 ^ (N - 1) := by
      have hdeg : (Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).natDegree = N - 1 := by
        simp
      calc
        (Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).coeff (N - 1) =
            (Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).coeff
              (Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).natDegree := by rw [hdeg]
        _ = (Polynomial.Chebyshev.U ℝ ((N - 1 : ℕ) : ℤ)).leadingCoeff :=
          Polynomial.coeff_natDegree
        _ = 2 ^ (N - 1) := by
          rw [Polynomial.Chebyshev.leadingCoeff_U_natCast]
    rw [hcoeffU]
  · intro j _hj hjtop
    rw [Polynomial.coeff_C_mul]
    have hjlt : (j : ℕ) < N :=
      putnam_2000_b3_subtype_lt_top hN j hjtop
    have hdeglt :
        (Polynomial.Chebyshev.U ℝ (((j : ℕ) - 1 : ℕ) : ℤ)).natDegree < N - 1 := by
      have hjpos : 0 < (j : ℕ) := j.property.1
      rw [Polynomial.Chebyshev.natDegree_U_natCast]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeglt, mul_zero]
  · intro htop
    simp at htop

private lemma putnam_2000_b3_cosPoly_ne_zero
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (k : ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0) :
  putnam_2000_b3_cosPoly N a k ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff N) hzero
  have hcoeff' : (putnam_2000_b3_cosPoly N a k).coeff N = 0 := by
    simpa using hcoeff
  rw [putnam_2000_b3_cosPoly_coeff_top N hN a k] at hcoeff'
  have htwo_pi_pos : 0 < 2 * Real.pi * (N : ℝ) := by positivity
  have hpow_ne : (2 * Real.pi * (N : ℝ)) ^ k ≠ 0 := pow_ne_zero _ htwo_pi_pos.ne'
  have htwo_ne : (2 : ℝ) ^ (N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero (mul_ne_zero haN hpow_ne) htwo_ne hcoeff'

private lemma putnam_2000_b3_sinPoly_ne_zero
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (k : ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0) :
  putnam_2000_b3_sinPoly N a k ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff (N - 1)) hzero
  have hcoeff' : (putnam_2000_b3_sinPoly N a k).coeff (N - 1) = 0 := by
    simpa using hcoeff
  rw [putnam_2000_b3_sinPoly_coeff_top N hN a k] at hcoeff'
  have htwo_pi_pos : 0 < 2 * Real.pi * (N : ℝ) := by positivity
  have hpow_ne : (2 * Real.pi * (N : ℝ)) ^ k ≠ 0 := pow_ne_zero _ htwo_pi_pos.ne'
  have htwo_ne : (2 : ℝ) ^ (N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_ne_zero (mul_ne_zero haN hpow_ne) htwo_ne hcoeff'

private lemma putnam_2000_b3_cosPoly_natDegree_le
  (N : ℕ) (a : Icc 1 N → ℝ) (k : ℕ) :
  (putnam_2000_b3_cosPoly N a k).natDegree ≤ N := by
  classical
  rw [putnam_2000_b3_cosPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _hj
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa [Int.natAbs_natCast] using j.property.2)

private lemma putnam_2000_b3_sinPoly_natDegree_le
  (N : ℕ) (a : Icc 1 N → ℝ) (k : ℕ) :
  (putnam_2000_b3_sinPoly N a k).natDegree ≤ N - 1 := by
  classical
  rw [putnam_2000_b3_sinPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _hj
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by
    have hjpos : 0 < (j : ℕ) := j.property.1
    have hjle : (j : ℕ) ≤ N := j.property.2
    rw [Polynomial.Chebyshev.natDegree_U_natCast]
    omega)

private lemma putnam_2000_b3_cosPoly_eval_cos
  (N : ℕ) (a : Icc 1 N → ℝ) (k : ℕ) (x : ℝ) :
  (putnam_2000_b3_cosPoly N a k).eval (Real.cos x) =
    ∑ j : Icc 1 N,
      a j * (2 * Real.pi * (j : ℕ)) ^ k * Real.cos ((j : ℕ) * x) := by
  classical
  rw [putnam_2000_b3_cosPoly, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos]
  norm_cast

private lemma putnam_2000_b3_sinPoly_eval_cos_mul_sin
  (N : ℕ) (a : Icc 1 N → ℝ) (k : ℕ) (x : ℝ) :
  (putnam_2000_b3_sinPoly N a k).eval (Real.cos x) * Real.sin x =
    ∑ j : Icc 1 N,
      a j * (2 * Real.pi * (j : ℕ)) ^ k * Real.sin ((j : ℕ) * x) := by
  classical
  rw [putnam_2000_b3_sinPoly, Polynomial.eval_finset_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  have hjpos : 0 < (j : ℕ) := j.property.1
  have hidx : ((((j : ℕ) - 1 : ℕ) : ℤ) + 1 : ℤ) = (j : ℕ) := by
    omega
  calc
    Polynomial.eval (Real.cos x)
        (Polynomial.C (a j * (2 * Real.pi * (j : ℕ)) ^ k) *
          Polynomial.Chebyshev.U ℝ (((j : ℕ) - 1 : ℕ) : ℤ)) * Real.sin x
        =
        (a j * (2 * Real.pi * (j : ℕ)) ^ k) *
          ((Polynomial.Chebyshev.U ℝ (((j : ℕ) - 1 : ℕ) : ℤ)).eval (Real.cos x) *
            Real.sin x) := by
          rw [Polynomial.eval_mul, Polynomial.eval_C]
          ring
    _ = (a j * (2 * Real.pi * (j : ℕ)) ^ k) *
          Real.sin (((((j : ℕ) - 1 : ℕ) : ℤ) + 1 : ℤ) * x) := by
          rw [Polynomial.Chebyshev.U_real_cos]
          norm_cast
    _ = a j * (2 * Real.pi * (j : ℕ)) ^ k * Real.sin ((j : ℕ) * x) := by
          rw [hidx]
          norm_cast

private lemma putnam_2000_b3_iteratedDeriv_even_eq_sinPoly
  (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (m : ℕ) (t : ℝ) :
  iteratedDeriv (2 * m) f t =
    (-1 : ℝ) ^ m *
      ((putnam_2000_b3_sinPoly N a (2 * m)).eval (Real.cos (2 * Real.pi * t)) *
        Real.sin (2 * Real.pi * t)) := by
  classical
  rw [putnam_2000_b3_iteratedDeriv_eq_sum N a f hf (2 * m) t]
  calc
    (∑ j : Icc 1 N, a j * (2 * Real.pi * ↑↑j) ^ (2 * m) *
        iteratedDeriv (2 * m) Real.sin (2 * Real.pi * ↑↑j * t))
        =
        ∑ j : Icc 1 N, a j * (2 * Real.pi * ↑↑j) ^ (2 * m) *
          ((-1 : ℝ) ^ m * Real.sin (2 * Real.pi * ↑↑j * t)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Real.iteratedDeriv_even_sin]
          simp
    _ =
        (-1 : ℝ) ^ m *
          ∑ j : Icc 1 N,
            a j * (2 * Real.pi * ↑↑j) ^ (2 * m) *
              Real.sin (↑↑j * (2 * Real.pi * t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring_nf
    _ =
        (-1 : ℝ) ^ m *
          ((putnam_2000_b3_sinPoly N a (2 * m)).eval (Real.cos (2 * Real.pi * t)) *
            Real.sin (2 * Real.pi * t)) := by
          rw [putnam_2000_b3_sinPoly_eval_cos_mul_sin]

private lemma putnam_2000_b3_iteratedDeriv_odd_eq_cosPoly
  (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (m : ℕ) (t : ℝ) :
  iteratedDeriv (2 * m + 1) f t =
    (-1 : ℝ) ^ m *
      (putnam_2000_b3_cosPoly N a (2 * m + 1)).eval (Real.cos (2 * Real.pi * t)) := by
  classical
  rw [putnam_2000_b3_iteratedDeriv_eq_sum N a f hf (2 * m + 1) t]
  calc
    (∑ j : Icc 1 N, a j * (2 * Real.pi * ↑↑j) ^ (2 * m + 1) *
        iteratedDeriv (2 * m + 1) Real.sin (2 * Real.pi * ↑↑j * t))
        =
        ∑ j : Icc 1 N, a j * (2 * Real.pi * ↑↑j) ^ (2 * m + 1) *
          ((-1 : ℝ) ^ m * Real.cos (2 * Real.pi * ↑↑j * t)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Real.iteratedDeriv_odd_sin]
          simp
    _ =
        (-1 : ℝ) ^ m *
          ∑ j : Icc 1 N,
            a j * (2 * Real.pi * ↑↑j) ^ (2 * m + 1) *
              Real.cos (↑↑j * (2 * Real.pi * t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring_nf
    _ =
        (-1 : ℝ) ^ m *
          (putnam_2000_b3_cosPoly N a (2 * m + 1)).eval (Real.cos (2 * Real.pi * t)) := by
          rw [putnam_2000_b3_cosPoly_eval_cos]

private lemma putnam_2000_b3_exists_Ioo_eval_ne_zero
  (p : Polynomial ℝ) (hp : p ≠ 0) :
  ∃ x ∈ Ioo (-1 : ℝ) 1, p.eval x ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hfinite : (Ioo (-1 : ℝ) 1).Finite := by
    exact (Polynomial.finite_setOf_isRoot (p := p) hp).subset fun x hx =>
      (Polynomial.IsRoot.def).2 (h x hx)
  exact (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)) hfinite

private lemma putnam_2000_b3_cos_two_pi_arccos_div
  {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
  Real.cos (2 * Real.pi * (Real.arccos x / (2 * Real.pi))) = x := by
  have htwo_pi_ne : 2 * Real.pi ≠ 0 := Real.two_pi_pos.ne'
  have harg : 2 * Real.pi * (Real.arccos x / (2 * Real.pi)) = Real.arccos x := by
    field_simp [htwo_pi_ne]
  rw [harg]
  exact Real.cos_arccos (le_of_lt hx.1) (le_of_lt hx.2)

private lemma putnam_2000_b3_sin_two_pi_arccos_div_ne_zero
  {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
  Real.sin (2 * Real.pi * (Real.arccos x / (2 * Real.pi))) ≠ 0 := by
  have htwo_pi_ne : 2 * Real.pi ≠ 0 := Real.two_pi_pos.ne'
  have harg : 2 * Real.pi * (Real.arccos x / (2 * Real.pi)) = Real.arccos x := by
    field_simp [htwo_pi_ne]
  rw [harg, Real.sin_arccos]
  have habs : |x| < 1 := abs_lt.mpr hx
  have hsq : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 habs
  exact (Real.sqrt_pos.2 (sub_pos.mpr hsq)).ne'

private lemma putnam_2000_b3_exists_ne_zero_iteratedDeriv
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) :
  ∃ t : ℝ, iteratedDeriv k f t ≠ 0 := by
  classical
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · let p := putnam_2000_b3_sinPoly N a (2 * m)
    have hp : p ≠ 0 := putnam_2000_b3_sinPoly_ne_zero N hN a (2 * m) haN
    rcases putnam_2000_b3_exists_Ioo_eval_ne_zero p hp with ⟨x, hx, hpx⟩
    refine ⟨Real.arccos x / (2 * Real.pi), ?_⟩
    rw [putnam_2000_b3_iteratedDeriv_even_eq_sinPoly N a f hf m]
    have hcos :
        Real.cos (2 * Real.pi * (Real.arccos x / (2 * Real.pi))) = x :=
      putnam_2000_b3_cos_two_pi_arccos_div hx
    have hsin :
        Real.sin (2 * Real.pi * (Real.arccos x / (2 * Real.pi))) ≠ 0 :=
      putnam_2000_b3_sin_two_pi_arccos_div_ne_zero hx
    have hpeval :
        (putnam_2000_b3_sinPoly N a (2 * m)).eval
            (Real.cos (2 * Real.pi * (Real.arccos x / (2 * Real.pi)))) ≠ 0 := by
      simpa [p, hcos] using hpx
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
      (mul_ne_zero hpeval hsin)
  · let p := putnam_2000_b3_cosPoly N a (2 * m + 1)
    have hp : p ≠ 0 := putnam_2000_b3_cosPoly_ne_zero N hN a (2 * m + 1) haN
    rcases putnam_2000_b3_exists_Ioo_eval_ne_zero p hp with ⟨x, hx, hpx⟩
    refine ⟨Real.arccos x / (2 * Real.pi), ?_⟩
    rw [putnam_2000_b3_iteratedDeriv_odd_eq_cosPoly N a f hf m]
    have hcos :
        Real.cos (2 * Real.pi * (Real.arccos x / (2 * Real.pi))) = x :=
      putnam_2000_b3_cos_two_pi_arccos_div hx
    have hpeval :
        (putnam_2000_b3_cosPoly N a (2 * m + 1)).eval
            (Real.cos (2 * Real.pi * (Real.arccos x / (2 * Real.pi)))) ≠ 0 := by
      simpa [p, hcos] using hpx
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) hpeval

private lemma putnam_2000_b3_finite_zero_set_iteratedDeriv
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) :
  (((iteratedDeriv k f) ⁻¹' ({0} : Set ℝ)) ∩ Icc (0 : ℝ) 1).Finite := by
  rcases putnam_2000_b3_exists_ne_zero_iteratedDeriv N hN a f haN hf k with ⟨x, hx⟩
  exact putnam_2000_b3_finite_zero_set_Icc_of_analytic_nonzero
    (putnam_2000_b3_analyticOnNhd_iteratedDeriv_f N a f hf k) hx

private lemma putnam_2000_b3_mult_support_finite_iteratedDeriv
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (k : ℕ) :
  (Function.support fun t : Ico (0 : ℝ) 1 => mult (iteratedDeriv k f) t).Finite := by
  exact putnam_2000_b3_mult_support_finite_Ico_of_finite_zero_set mult hmult
    (putnam_2000_b3_finite_zero_set_iteratedDeriv N hN a f haN hf k)

private lemma putnam_2000_b3_analyticOrderAt_ne_top_iteratedDeriv
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) (t : ℝ) :
  analyticOrderAt (iteratedDeriv k f) t ≠ ⊤ := by
  rcases putnam_2000_b3_exists_ne_zero_iteratedDeriv N hN a f haN hf k with ⟨x, hx⟩
  have hxfinite : analyticOrderAt (iteratedDeriv k f) x ≠ ⊤ := by
    have hxan :
        AnalyticAt ℝ (iteratedDeriv k f) x :=
      (putnam_2000_b3_analyticOnNhd_iteratedDeriv_f N a f hf k) x trivial
    rw [hxan.analyticOrderAt_eq_zero.2 hx]
    exact ENat.zero_ne_top
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (U := Set.univ) (x := x) (y := t)
    (putnam_2000_b3_analyticOnNhd_iteratedDeriv_f N a f hf k)
    isPreconnected_univ trivial trivial hxfinite

private lemma putnam_2000_b3_exists_iteratedDeriv_ne_zero_of_finite_order
  {g : ℝ → ℝ} {t : ℝ}
  (hg : AnalyticAt ℝ g t) (hfinite : analyticOrderAt g t ≠ ⊤) :
  ∃ c : ℕ, iteratedDeriv c g t ≠ 0 := by
  classical
  let n := analyticOrderNatAt g t
  have hncast : (n : ℕ∞) = analyticOrderAt g t := by
    simpa [n] using (Nat.cast_analyticOrderNatAt (f := g) (z₀ := t) hfinite)
  have hzero_lt_n : ∀ i < n, iteratedDeriv i g t = 0 := by
    have hle : (n : ℕ∞) ≤ analyticOrderAt g t := by rw [hncast]
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (𝕜 := ℝ) (E := ℝ) (f := g) (z₀ := t) (n := n) hg).1 hle
  refine ⟨n, ?_⟩
  intro hnzero
  have hzero_succ : ∀ i < n + 1, iteratedDeriv i g t = 0 := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hzero_lt_n i hi
    · exact hnzero
  have hle_succ :
      ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g t :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (𝕜 := ℝ) (E := ℝ) (f := g) (z₀ := t) (n := n + 1) hg).2 hzero_succ
  rw [← hncast] at hle_succ
  exact Nat.not_succ_le_self n (ENat.coe_le_coe.mp hle_succ)

private lemma putnam_2000_b3_mult_eq_analyticOrderNatAt_iteratedDeriv
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (k : ℕ) (t : ℝ) :
  mult (iteratedDeriv k f) t = analyticOrderNatAt (iteratedDeriv k f) t := by
  exact putnam_2000_b3_mult_eq_analyticOrderNatAt mult hmult
    ((putnam_2000_b3_analyticOnNhd_iteratedDeriv_f N a f hf k) t trivial)
    (putnam_2000_b3_analyticOrderAt_ne_top_iteratedDeriv N hN a f haN hf k t)

private lemma putnam_2000_b3_analyticOrderAt_polynomial_eval
  {p : Polynomial ℝ} {x : ℝ} (hp : p ≠ 0) :
  analyticOrderAt (fun y : ℝ => p.eval y) x = (p.rootMultiplicity x : ℕ∞) := by
  classical
  let m := p.rootMultiplicity x
  let q := p /ₘ (Polynomial.X - Polynomial.C x) ^ m
  have hp_eval : (fun y : ℝ => p.eval y) =
      fun y : ℝ => (y - x) ^ m * q.eval y := by
    funext y
    have hpoly := congrArg (fun r : Polynomial ℝ => r.eval y)
      (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p x)
    dsimp [m, q] at hpoly ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hpoly
    exact hpoly.symm
  have hq_ne : q.eval x ≠ 0 := by
    simpa [q, m] using
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero (p := p) x hp
  have hq_an : AnalyticAt ℝ (fun y : ℝ => q.eval y) x := by
    simpa [Polynomial.aeval_def] using
      (analyticAt_id (𝕜 := ℝ) (E := ℝ) (z := x)).aeval_polynomial q
  have hq_order : analyticOrderAt (fun y : ℝ => q.eval y) x = 0 :=
    hq_an.analyticOrderAt_eq_zero.2 hq_ne
  rw [hp_eval]
  change analyticOrderAt
    (((fun y : ℝ => y - x) ^ m) * (fun y : ℝ => q.eval y)) x = (m : ℕ∞)
  have hmono : AnalyticAt ℝ ((fun y : ℝ => y - x) ^ m) x := by
    fun_prop
  rw [analyticOrderAt_mul hmono hq_an, analyticOrderAt_centeredMonomial, hq_order]
  simp

private lemma putnam_2000_b3_analyticOrderNatAt_polynomial_eval
  {p : Polynomial ℝ} {x : ℝ} (hp : p ≠ 0) :
  analyticOrderNatAt (fun y : ℝ => p.eval y) x = p.rootMultiplicity x := by
  have horder := putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p) (x := x) hp
  have hfinite : analyticOrderAt (fun y : ℝ => p.eval y) x ≠ ⊤ := by
    rw [horder]
    exact ENat.coe_ne_top _
  rw [← Nat.cast_inj (R := ℕ∞)]
  rw [Nat.cast_analyticOrderNatAt hfinite, horder]

private lemma putnam_2000_b3_analyticOrderNatAt_polynomial_eval_comp_of_deriv_ne_zero
  {p : Polynomial ℝ} {h : ℝ → ℝ} {t : ℝ} (hp : p ≠ 0)
  (hh : AnalyticAt ℝ h t) (hderiv : deriv h t ≠ 0) :
  analyticOrderNatAt (fun y : ℝ => p.eval (h y)) t = p.rootMultiplicity (h t) := by
  classical
  have hcomp_order :
      analyticOrderAt (fun y : ℝ => p.eval (h y)) t =
        analyticOrderAt (fun x : ℝ => p.eval x) (h t) := by
    simpa [Function.comp_def] using
      (analyticOrderAt_comp_of_deriv_ne_zero
        (f := fun x : ℝ => p.eval x) (g := h) (z₀ := t) hh hderiv)
  have hbase :=
    putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p) (x := h t) hp
  have hfinite : analyticOrderAt (fun y : ℝ => p.eval (h y)) t ≠ ⊤ := by
    rw [hcomp_order, hbase]
    exact ENat.coe_ne_top _
  rw [← Nat.cast_inj (R := ℕ∞)]
  rw [Nat.cast_analyticOrderNatAt hfinite, hcomp_order, hbase]

private lemma putnam_2000_b3_sum_rootMultiplicity_roots_le_natDegree
  (p : Polynomial ℝ) :
  (∑ x ∈ p.roots.toFinset, p.rootMultiplicity x) ≤ p.natDegree := by
  classical
  calc
    (∑ x ∈ p.roots.toFinset, p.rootMultiplicity x) = p.roots.card := by
      rw [← Multiset.toFinset_sum_count_eq p.roots]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Polynomial.count_roots]
    _ ≤ p.natDegree := Polynomial.card_roots' p

private lemma putnam_2000_b3_analyticOrderAt_const_mul
  {g : ℝ → ℝ} {t c : ℝ} (hc : c ≠ 0) (hg : AnalyticAt ℝ g t) :
  analyticOrderAt (fun y : ℝ => c * g y) t = analyticOrderAt g t := by
  change analyticOrderAt ((fun _ : ℝ => c) * g) t = analyticOrderAt g t
  have hc_order : analyticOrderAt (fun _ : ℝ => c) t = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.2 hc
  rw [analyticOrderAt_mul analyticAt_const hg, hc_order]
  simp

private lemma putnam_2000_b3_analyticOrderNatAt_const_mul
  {g : ℝ → ℝ} {t c : ℝ} (hc : c ≠ 0) (hg : AnalyticAt ℝ g t)
  (hfin : analyticOrderAt g t ≠ ⊤) :
  analyticOrderNatAt (fun y : ℝ => c * g y) t = analyticOrderNatAt g t := by
  have h := putnam_2000_b3_analyticOrderAt_const_mul
    (g := g) (t := t) (c := c) hc hg
  have hfin' : analyticOrderAt (fun y : ℝ => c * g y) t ≠ ⊤ := by
    rwa [h]
  rw [← Nat.cast_inj (R := ℕ∞)]
  rw [Nat.cast_analyticOrderNatAt hfin', Nat.cast_analyticOrderNatAt hfin, h]

private lemma putnam_2000_b3_analyticOrderAt_mul_nonzero_right
  {g h : ℝ → ℝ} {t : ℝ}
  (hg : AnalyticAt ℝ g t) (hh : AnalyticAt ℝ h t) (hht : h t ≠ 0) :
  analyticOrderAt (fun y : ℝ => g y * h y) t = analyticOrderAt g t := by
  change analyticOrderAt (g * h) t = analyticOrderAt g t
  have hh_order : analyticOrderAt h t = 0 := hh.analyticOrderAt_eq_zero.2 hht
  rw [analyticOrderAt_mul hg hh, hh_order]
  simp

private lemma putnam_2000_b3_analyticOrderNatAt_mul_nonzero_right
  {g h : ℝ → ℝ} {t : ℝ}
  (hg : AnalyticAt ℝ g t) (hh : AnalyticAt ℝ h t) (hht : h t ≠ 0)
  (hfin : analyticOrderAt g t ≠ ⊤) :
  analyticOrderNatAt (fun y : ℝ => g y * h y) t = analyticOrderNatAt g t := by
  have hfun := putnam_2000_b3_analyticOrderAt_mul_nonzero_right
    (g := g) (h := h) (t := t) hg hh hht
  have hfin' : analyticOrderAt (fun y : ℝ => g y * h y) t ≠ ⊤ := by
    rwa [hfun]
  rw [← Nat.cast_inj (R := ℕ∞)]
  rw [Nat.cast_analyticOrderNatAt hfin', Nat.cast_analyticOrderNatAt hfin, hfun]

private lemma putnam_2000_b3_analyticAt_cos_two_pi (t : ℝ) :
  AnalyticAt ℝ (fun y : ℝ => Real.cos (2 * Real.pi * y)) t := by
  fun_prop

private lemma putnam_2000_b3_analyticAt_sin_two_pi (t : ℝ) :
  AnalyticAt ℝ (fun y : ℝ => Real.sin (2 * Real.pi * y)) t := by
  fun_prop

private lemma putnam_2000_b3_deriv_cos_two_pi (t : ℝ) :
  deriv (fun y : ℝ => Real.cos (2 * Real.pi * y)) t =
    -(2 * Real.pi) * Real.sin (2 * Real.pi * t) := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  have h := (Real.hasDerivAt_cos (2 * Real.pi * t)).comp t hlin
  calc
    deriv (fun y : ℝ => Real.cos (2 * Real.pi * y)) t =
        -Real.sin (2 * Real.pi * t) * (2 * Real.pi) := by
      simpa [Function.comp_def] using h.deriv
    _ = -(2 * Real.pi) * Real.sin (2 * Real.pi * t) := by
      ring

private lemma putnam_2000_b3_analyticOrderAt_sin_pi_zero :
  analyticOrderAt (fun y : ℝ => Real.sin (Real.pi * y)) 0 = 1 := by
  have han : AnalyticAt ℝ (fun y : ℝ => Real.sin (Real.pi * y)) 0 := by
    fun_prop
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul Real.pi
  have hderivAt :
      HasDerivAt (fun y : ℝ => Real.sin (Real.pi * y))
        (Real.cos (Real.pi * 0) * Real.pi) 0 :=
    (Real.hasDerivAt_sin (Real.pi * 0)).comp 0 hlin
  have hderiv :
      deriv (fun y : ℝ => Real.sin (Real.pi * y)) 0 = Real.pi := by
    simpa [Real.cos_zero] using hderivAt.deriv
  have hderiv_ne :
      deriv (fun y : ℝ => Real.sin (Real.pi * y)) 0 ≠ 0 := by
    rw [hderiv]
    exact Real.pi_ne_zero
  have h := han.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv_ne
  simpa using h

private lemma putnam_2000_b3_analyticOrderAt_cos_pi_half :
  analyticOrderAt (fun y : ℝ => Real.cos (Real.pi * y)) (1 / 2) = 1 := by
  have han : AnalyticAt ℝ (fun y : ℝ => Real.cos (Real.pi * y)) (1 / 2 : ℝ) := by
    fun_prop
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi (1 / 2 : ℝ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_mul Real.pi
  have hderivAt :
      HasDerivAt (fun y : ℝ => Real.cos (Real.pi * y))
        (-Real.sin (Real.pi * (1 / 2 : ℝ)) * Real.pi) (1 / 2 : ℝ) :=
    (Real.hasDerivAt_cos (Real.pi * (1 / 2 : ℝ))).comp (1 / 2 : ℝ) hlin
  have harg : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by
    ring
  have hderiv :
      deriv (fun y : ℝ => Real.cos (Real.pi * y)) (1 / 2 : ℝ) = -Real.pi := by
    rw [hderivAt.deriv, harg, Real.sin_pi_div_two]
    ring
  have hderiv_ne :
      deriv (fun y : ℝ => Real.cos (Real.pi * y)) (1 / 2 : ℝ) ≠ 0 := by
    rw [hderiv]
    exact neg_ne_zero.mpr Real.pi_ne_zero
  have h := han.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv_ne
  have hval : Real.cos (Real.pi * (2⁻¹ : ℝ)) = 0 := by
    have harg' : Real.pi * (2⁻¹ : ℝ) = Real.pi / 2 := by
      ring
    rw [harg', Real.cos_pi_div_two]
  simpa [hval] using h

private lemma putnam_2000_b3_analyticOrderAt_cos_two_pi_sub_one_zero :
  analyticOrderAt (fun y : ℝ => Real.cos (2 * Real.pi * y) - 1) 0 = 2 := by
  have hfun :
      (fun y : ℝ => Real.cos (2 * Real.pi * y) - 1) =
        fun y : ℝ => (-2 : ℝ) * (Real.sin (Real.pi * y)) ^ 2 := by
    funext y
    rw [Real.sin_sq_eq_half_sub]
    ring_nf
  rw [hfun]
  have han : AnalyticAt ℝ (fun y : ℝ => Real.sin (Real.pi * y)) 0 := by
    fun_prop
  have hsquare :
      analyticOrderAt (fun y : ℝ => (Real.sin (Real.pi * y)) ^ 2) 0 = 2 := by
    change analyticOrderAt ((fun y : ℝ => Real.sin (Real.pi * y)) ^ 2) 0 = 2
    rw [analyticOrderAt_pow han, putnam_2000_b3_analyticOrderAt_sin_pi_zero]
    norm_num
  change analyticOrderAt
    ((fun _ : ℝ => (-2 : ℝ)) * (fun y : ℝ => (Real.sin (Real.pi * y)) ^ 2)) 0 = 2
  rw [analyticOrderAt_mul
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (-2 : ℝ)) 0) (by fun_prop),
    hsquare]
  have hconst :
      analyticOrderAt (fun _ : ℝ => (-2 : ℝ)) 0 = 0 :=
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (-2 : ℝ)) 0).analyticOrderAt_eq_zero.2
      (by norm_num)
  rw [hconst]
  simp

private lemma putnam_2000_b3_analyticOrderAt_cos_two_pi_add_one_half :
  analyticOrderAt (fun y : ℝ => Real.cos (2 * Real.pi * y) + 1) (1 / 2) = 2 := by
  have hfun :
      (fun y : ℝ => Real.cos (2 * Real.pi * y) + 1) =
        fun y : ℝ => (2 : ℝ) * (Real.cos (Real.pi * y)) ^ 2 := by
    funext y
    rw [Real.cos_sq]
    ring_nf
  rw [hfun]
  have han : AnalyticAt ℝ (fun y : ℝ => Real.cos (Real.pi * y)) (1 / 2 : ℝ) := by
    fun_prop
  have hsquare :
      analyticOrderAt (fun y : ℝ => (Real.cos (Real.pi * y)) ^ 2) (1 / 2 : ℝ) = 2 := by
    change analyticOrderAt ((fun y : ℝ => Real.cos (Real.pi * y)) ^ 2) (1 / 2 : ℝ) = 2
    rw [analyticOrderAt_pow han, putnam_2000_b3_analyticOrderAt_cos_pi_half]
    norm_num
  change analyticOrderAt
    ((fun _ : ℝ => (2 : ℝ)) * (fun y : ℝ => (Real.cos (Real.pi * y)) ^ 2))
      (1 / 2 : ℝ) = 2
  rw [analyticOrderAt_mul
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (2 : ℝ)) (1 / 2 : ℝ)) (by fun_prop),
    hsquare]
  have hconst :
      analyticOrderAt (fun _ : ℝ => (2 : ℝ)) (1 / 2 : ℝ) = 0 :=
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (2 : ℝ)) (1 / 2 : ℝ)).analyticOrderAt_eq_zero.2
      (by norm_num)
  rw [hconst]
  simp

private lemma putnam_2000_b3_analyticOrderAt_sin_two_pi_zero :
  analyticOrderAt (fun y : ℝ => Real.sin (2 * Real.pi * y)) 0 = 1 := by
  have han : AnalyticAt ℝ (fun y : ℝ => Real.sin (2 * Real.pi * y)) 0 := by
    fun_prop
  have hlin : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.pi)
  have hderivAt :
      HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * y))
        (Real.cos (2 * Real.pi * 0) * (2 * Real.pi)) 0 :=
    (Real.hasDerivAt_sin (2 * Real.pi * 0)).comp 0 hlin
  have hderiv :
      deriv (fun y : ℝ => Real.sin (2 * Real.pi * y)) 0 = 2 * Real.pi := by
    simpa [Real.cos_zero] using hderivAt.deriv
  have hderiv_ne :
      deriv (fun y : ℝ => Real.sin (2 * Real.pi * y)) 0 ≠ 0 := by
    rw [hderiv]
    positivity
  have h := han.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv_ne
  simpa [Real.sin_zero] using h

private lemma putnam_2000_b3_analyticOrderAt_sin_two_pi_half :
  analyticOrderAt (fun y : ℝ => Real.sin (2 * Real.pi * y)) (1 / 2) = 1 := by
  have han : AnalyticAt ℝ (fun y : ℝ => Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) := by
    fun_prop
  have hlin : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) (1 / 2 : ℝ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_mul (2 * Real.pi)
  have hderivAt :
      HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * y))
        (Real.cos (2 * Real.pi * (1 / 2 : ℝ)) * (2 * Real.pi)) (1 / 2 : ℝ) :=
    (Real.hasDerivAt_sin (2 * Real.pi * (1 / 2 : ℝ))).comp (1 / 2 : ℝ) hlin
  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by
    ring
  have hderiv :
      deriv (fun y : ℝ => Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) = -(2 * Real.pi) := by
    rw [hderivAt.deriv, harg, Real.cos_pi]
    ring
  have hderiv_ne :
      deriv (fun y : ℝ => Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) ≠ 0 := by
    rw [hderiv]
    exact neg_ne_zero.mpr (by positivity)
  have h := han.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv_ne
  have hval : Real.sin (2 * Real.pi * (2⁻¹ : ℝ)) = 0 := by
    have harg' : 2 * Real.pi * (2⁻¹ : ℝ) = Real.pi := by
      ring
    rw [harg', Real.sin_pi]
  simpa [hval] using h

private lemma putnam_2000_b3_mult_odd_eq_rootMultiplicity_cosPoly_of_sin_ne_zero
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) {t : ℝ} (hsin : Real.sin (2 * Real.pi * t) ≠ 0) :
  mult (iteratedDeriv (2 * m + 1) f) t =
    (putnam_2000_b3_cosPoly N a (2 * m + 1)).rootMultiplicity
      (Real.cos (2 * Real.pi * t)) := by
  classical
  let p := putnam_2000_b3_cosPoly N a (2 * m + 1)
  have hp : p ≠ 0 := putnam_2000_b3_cosPoly_ne_zero N hN a (2 * m + 1) haN
  have hiter :
      (iteratedDeriv (2 * m + 1) f) =
        fun y : ℝ => (-1 : ℝ) ^ m *
          p.eval (Real.cos (2 * Real.pi * y)) := by
    funext y
    simpa [p] using putnam_2000_b3_iteratedDeriv_odd_eq_cosPoly N a f hf m y
  have htwopi : 2 * Real.pi ≠ 0 := by positivity
  have hderiv :
      deriv (fun y : ℝ => Real.cos (2 * Real.pi * y)) t ≠ 0 := by
    rw [putnam_2000_b3_deriv_cos_two_pi]
    exact mul_ne_zero (neg_ne_zero.mpr htwopi) hsin
  have hcomp_order :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t =
        (p.rootMultiplicity (Real.cos (2 * Real.pi * t)) : ℕ∞) := by
    calc
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t =
          analyticOrderAt (fun x : ℝ => p.eval x) (Real.cos (2 * Real.pi * t)) := by
        simpa [Function.comp_def] using
          (analyticOrderAt_comp_of_deriv_ne_zero
            (f := fun x : ℝ => p.eval x)
            (g := fun y : ℝ => Real.cos (2 * Real.pi * y)) (z₀ := t)
            (putnam_2000_b3_analyticAt_cos_two_pi t) hderiv)
      _ = (p.rootMultiplicity (Real.cos (2 * Real.pi * t)) : ℕ∞) :=
        putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p)
          (x := Real.cos (2 * Real.pi * t)) hp
  have hcomp_finite :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t ≠ ⊤ := by
    rw [hcomp_order]
    exact ENat.coe_ne_top _
  have hcomp_nat :
      analyticOrderNatAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t =
        p.rootMultiplicity (Real.cos (2 * Real.pi * t)) := by
    rw [← Nat.cast_inj (R := ℕ∞)]
    rw [Nat.cast_analyticOrderNatAt hcomp_finite, hcomp_order]
  have hcomp_an :
      AnalyticAt ℝ (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t := by
    simpa [Polynomial.aeval_def] using
      (putnam_2000_b3_analyticAt_cos_two_pi t).aeval_polynomial p
  have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [putnam_2000_b3_mult_eq_analyticOrderNatAt_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m + 1) t, hiter]
  rw [putnam_2000_b3_analyticOrderNatAt_const_mul hscalar hcomp_an hcomp_finite,
    hcomp_nat]

private lemma putnam_2000_b3_mult_odd_zero_eq_two_rootMultiplicity_cosPoly
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) :
  mult (iteratedDeriv (2 * m + 1) f) 0 =
    2 * (putnam_2000_b3_cosPoly N a (2 * m + 1)).rootMultiplicity 1 := by
  classical
  let p := putnam_2000_b3_cosPoly N a (2 * m + 1)
  have hp : p ≠ 0 := putnam_2000_b3_cosPoly_ne_zero N hN a (2 * m + 1) haN
  have hiter :
      (iteratedDeriv (2 * m + 1) f) =
        fun y : ℝ => (-1 : ℝ) ^ m *
          p.eval (Real.cos (2 * Real.pi * y)) := by
    funext y
    simpa [p] using putnam_2000_b3_iteratedDeriv_odd_eq_cosPoly N a f hf m y
  have hcomp_an :
      AnalyticAt ℝ (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 := by
    simpa [Polynomial.aeval_def] using
      (putnam_2000_b3_analyticAt_cos_two_pi 0).aeval_polynomial p
  have hpoly_an :
      AnalyticAt ℝ (fun x : ℝ => p.eval x) (Real.cos (2 * Real.pi * 0)) := by
    simpa [Polynomial.aeval_def] using
      (analyticAt_id (𝕜 := ℝ) (E := ℝ) (z := Real.cos (2 * Real.pi * 0))).aeval_polynomial p
  have hcos_an : AnalyticAt ℝ (fun y : ℝ => Real.cos (2 * Real.pi * y)) 0 :=
    putnam_2000_b3_analyticAt_cos_two_pi 0
  have hcos0 : Real.cos (2 * Real.pi * 0) = 1 := by
    simp [Real.cos_zero]
  have hcos_order :
      analyticOrderAt (fun y : ℝ => Real.cos (2 * Real.pi * y) - 1) 0 = 2 :=
    putnam_2000_b3_analyticOrderAt_cos_two_pi_sub_one_zero
  have hcomp_order :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 =
        (p.rootMultiplicity 1 : ℕ∞) * 2 := by
    calc
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 =
          analyticOrderAt ((fun x : ℝ => p.eval x) ∘
            (fun y : ℝ => Real.cos (2 * Real.pi * y))) 0 := by
            rfl
      _ = analyticOrderAt (fun x : ℝ => p.eval x) (Real.cos (2 * Real.pi * 0)) *
            analyticOrderAt
              (fun y : ℝ => Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * 0)) 0 := by
            exact AnalyticAt.analyticOrderAt_comp
              (𝕜 := ℝ) (E := ℝ) (f := fun x : ℝ => p.eval x)
              (g := fun y : ℝ => Real.cos (2 * Real.pi * y)) (z₀ := 0)
              hpoly_an hcos_an
      _ = (p.rootMultiplicity 1 : ℕ∞) * 2 := by
            rw [hcos0, hcos_order,
              putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p) (x := 1) hp]
  have hcomp_finite :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 ≠ ⊤ := by
    rw [hcomp_order]
    change ((p.rootMultiplicity 1 : ℕ∞) * ((2 : ℕ) : ℕ∞)) ≠ ⊤
    rw [← Nat.cast_mul]
    exact ENat.coe_ne_top _
  have hcomp_nat :
      analyticOrderNatAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 =
        2 * p.rootMultiplicity 1 := by
    rw [← Nat.cast_inj (R := ℕ∞)]
    rw [Nat.cast_analyticOrderNatAt hcomp_finite, hcomp_order, Nat.cast_mul]
    norm_num
    rw [mul_comm]
  have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [putnam_2000_b3_mult_eq_analyticOrderNatAt_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m + 1) 0, hiter]
  rw [putnam_2000_b3_analyticOrderNatAt_const_mul hscalar hcomp_an hcomp_finite,
    hcomp_nat]

private lemma putnam_2000_b3_mult_odd_half_eq_two_rootMultiplicity_cosPoly
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) :
  mult (iteratedDeriv (2 * m + 1) f) (1 / 2) =
    2 * (putnam_2000_b3_cosPoly N a (2 * m + 1)).rootMultiplicity (-1) := by
  classical
  let p := putnam_2000_b3_cosPoly N a (2 * m + 1)
  have hp : p ≠ 0 := putnam_2000_b3_cosPoly_ne_zero N hN a (2 * m + 1) haN
  have hiter :
      (iteratedDeriv (2 * m + 1) f) =
        fun y : ℝ => (-1 : ℝ) ^ m *
          p.eval (Real.cos (2 * Real.pi * y)) := by
    funext y
    simpa [p] using putnam_2000_b3_iteratedDeriv_odd_eq_cosPoly N a f hf m y
  have hcomp_an :
      AnalyticAt ℝ (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) := by
    simpa [Polynomial.aeval_def] using
      (putnam_2000_b3_analyticAt_cos_two_pi (1 / 2 : ℝ)).aeval_polynomial p
  have hpoly_an :
      AnalyticAt ℝ (fun x : ℝ => p.eval x)
        (Real.cos (2 * Real.pi * (1 / 2 : ℝ))) := by
    simpa [Polynomial.aeval_def] using
      (analyticAt_id (𝕜 := ℝ) (E := ℝ)
        (z := Real.cos (2 * Real.pi * (1 / 2 : ℝ)))).aeval_polynomial p
  have hcos_an :
      AnalyticAt ℝ (fun y : ℝ => Real.cos (2 * Real.pi * y)) (1 / 2 : ℝ) :=
    putnam_2000_b3_analyticAt_cos_two_pi (1 / 2 : ℝ)
  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by
    ring
  have hcoshalf : Real.cos (2 * Real.pi * (1 / 2 : ℝ)) = -1 := by
    rw [harg, Real.cos_pi]
  have hcos_order :
      analyticOrderAt
        (fun y : ℝ => Real.cos (2 * Real.pi * y) -
          (-1 : ℝ)) (1 / 2 : ℝ) = 2 := by
    simpa [sub_neg_eq_add] using
      putnam_2000_b3_analyticOrderAt_cos_two_pi_add_one_half
  have hcomp_order :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) =
        (p.rootMultiplicity (-1) : ℕ∞) * 2 := by
    calc
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) =
          analyticOrderAt ((fun x : ℝ => p.eval x) ∘
            (fun y : ℝ => Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) := by
            rfl
      _ = analyticOrderAt (fun x : ℝ => p.eval x)
            (Real.cos (2 * Real.pi * (1 / 2 : ℝ))) *
            analyticOrderAt
              (fun y : ℝ => Real.cos (2 * Real.pi * y) -
                Real.cos (2 * Real.pi * (1 / 2 : ℝ))) (1 / 2 : ℝ) := by
            exact AnalyticAt.analyticOrderAt_comp
              (𝕜 := ℝ) (E := ℝ) (f := fun x : ℝ => p.eval x)
              (g := fun y : ℝ => Real.cos (2 * Real.pi * y)) (z₀ := (1 / 2 : ℝ))
              hpoly_an hcos_an
      _ = (p.rootMultiplicity (-1) : ℕ∞) * 2 := by
            rw [hcoshalf, hcos_order,
              putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p) (x := -1) hp]
  have hcomp_finite :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) ≠ ⊤ := by
    rw [hcomp_order]
    change ((p.rootMultiplicity (-1) : ℕ∞) * ((2 : ℕ) : ℕ∞)) ≠ ⊤
    rw [← Nat.cast_mul]
    exact ENat.coe_ne_top _
  have hcomp_nat :
      analyticOrderNatAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) =
        2 * p.rootMultiplicity (-1) := by
    rw [← Nat.cast_inj (R := ℕ∞)]
    rw [Nat.cast_analyticOrderNatAt hcomp_finite, hcomp_order, Nat.cast_mul]
    norm_num
    rw [mul_comm]
  have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [putnam_2000_b3_mult_eq_analyticOrderNatAt_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m + 1) (1 / 2 : ℝ), hiter]
  rw [putnam_2000_b3_analyticOrderNatAt_const_mul hscalar hcomp_an hcomp_finite,
    hcomp_nat]

private lemma putnam_2000_b3_mult_even_eq_rootMultiplicity_sinPoly_of_sin_ne_zero
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) {t : ℝ} (hsin : Real.sin (2 * Real.pi * t) ≠ 0) :
  mult (iteratedDeriv (2 * m) f) t =
    (putnam_2000_b3_sinPoly N a (2 * m)).rootMultiplicity
      (Real.cos (2 * Real.pi * t)) := by
  classical
  let p := putnam_2000_b3_sinPoly N a (2 * m)
  have hp : p ≠ 0 := putnam_2000_b3_sinPoly_ne_zero N hN a (2 * m) haN
  have hiter :
      (iteratedDeriv (2 * m) f) =
        fun y : ℝ => (-1 : ℝ) ^ m *
          (p.eval (Real.cos (2 * Real.pi * y)) *
            Real.sin (2 * Real.pi * y)) := by
    funext y
    simpa [p] using putnam_2000_b3_iteratedDeriv_even_eq_sinPoly N a f hf m y
  have htwopi : 2 * Real.pi ≠ 0 := by positivity
  have hderiv :
      deriv (fun y : ℝ => Real.cos (2 * Real.pi * y)) t ≠ 0 := by
    rw [putnam_2000_b3_deriv_cos_two_pi]
    exact mul_ne_zero (neg_ne_zero.mpr htwopi) hsin
  have hcomp_order :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t =
        (p.rootMultiplicity (Real.cos (2 * Real.pi * t)) : ℕ∞) := by
    calc
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t =
          analyticOrderAt (fun x : ℝ => p.eval x) (Real.cos (2 * Real.pi * t)) := by
        simpa [Function.comp_def] using
          (analyticOrderAt_comp_of_deriv_ne_zero
            (f := fun x : ℝ => p.eval x)
            (g := fun y : ℝ => Real.cos (2 * Real.pi * y)) (z₀ := t)
            (putnam_2000_b3_analyticAt_cos_two_pi t) hderiv)
      _ = (p.rootMultiplicity (Real.cos (2 * Real.pi * t)) : ℕ∞) :=
        putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p)
          (x := Real.cos (2 * Real.pi * t)) hp
  have hcomp_finite :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t ≠ ⊤ := by
    rw [hcomp_order]
    exact ENat.coe_ne_top _
  have hcomp_nat :
      analyticOrderNatAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t =
        p.rootMultiplicity (Real.cos (2 * Real.pi * t)) := by
    rw [← Nat.cast_inj (R := ℕ∞)]
    rw [Nat.cast_analyticOrderNatAt hcomp_finite, hcomp_order]
  have hcomp_an :
      AnalyticAt ℝ (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t := by
    simpa [Polynomial.aeval_def] using
      (putnam_2000_b3_analyticAt_cos_two_pi t).aeval_polynomial p
  have hsin_an : AnalyticAt ℝ (fun y : ℝ => Real.sin (2 * Real.pi * y)) t :=
    putnam_2000_b3_analyticAt_sin_two_pi t
  have hprod_order :
      analyticOrderAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) t =
        analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) t :=
    putnam_2000_b3_analyticOrderAt_mul_nonzero_right hcomp_an hsin_an hsin
  have hprod_finite :
      analyticOrderAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) t ≠ ⊤ := by
    rw [hprod_order]
    exact hcomp_finite
  have hprod_nat :
      analyticOrderNatAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) t =
        p.rootMultiplicity (Real.cos (2 * Real.pi * t)) := by
    rw [putnam_2000_b3_analyticOrderNatAt_mul_nonzero_right hcomp_an hsin_an hsin
      hcomp_finite, hcomp_nat]
  have hprod_an :
      AnalyticAt ℝ
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) t := hcomp_an.mul hsin_an
  have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [putnam_2000_b3_mult_eq_analyticOrderNatAt_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m) t, hiter]
  rw [putnam_2000_b3_analyticOrderNatAt_const_mul hscalar hprod_an hprod_finite,
    hprod_nat]

private lemma putnam_2000_b3_mult_even_zero_eq_two_rootMultiplicity_sinPoly_add_one
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) :
  mult (iteratedDeriv (2 * m) f) 0 =
    2 * (putnam_2000_b3_sinPoly N a (2 * m)).rootMultiplicity 1 + 1 := by
  classical
  let p := putnam_2000_b3_sinPoly N a (2 * m)
  have hp : p ≠ 0 := putnam_2000_b3_sinPoly_ne_zero N hN a (2 * m) haN
  have hiter :
      (iteratedDeriv (2 * m) f) =
        fun y : ℝ => (-1 : ℝ) ^ m *
          (p.eval (Real.cos (2 * Real.pi * y)) *
            Real.sin (2 * Real.pi * y)) := by
    funext y
    simpa [p] using putnam_2000_b3_iteratedDeriv_even_eq_sinPoly N a f hf m y
  have hcomp_an :
      AnalyticAt ℝ (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 := by
    simpa [Polynomial.aeval_def] using
      (putnam_2000_b3_analyticAt_cos_two_pi 0).aeval_polynomial p
  have hsin_an : AnalyticAt ℝ (fun y : ℝ => Real.sin (2 * Real.pi * y)) 0 :=
    putnam_2000_b3_analyticAt_sin_two_pi 0
  have hprod_an :
      AnalyticAt ℝ
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) 0 := hcomp_an.mul hsin_an
  have hpoly_an :
      AnalyticAt ℝ (fun x : ℝ => p.eval x) (Real.cos (2 * Real.pi * 0)) := by
    simpa [Polynomial.aeval_def] using
      (analyticAt_id (𝕜 := ℝ) (E := ℝ) (z := Real.cos (2 * Real.pi * 0))).aeval_polynomial p
  have hcos_an : AnalyticAt ℝ (fun y : ℝ => Real.cos (2 * Real.pi * y)) 0 :=
    putnam_2000_b3_analyticAt_cos_two_pi 0
  have hcos0 : Real.cos (2 * Real.pi * 0) = 1 := by
    simp [Real.cos_zero]
  have hcos_order :
      analyticOrderAt (fun y : ℝ => Real.cos (2 * Real.pi * y) - 1) 0 = 2 :=
    putnam_2000_b3_analyticOrderAt_cos_two_pi_sub_one_zero
  have hcomp_order :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 =
        (p.rootMultiplicity 1 : ℕ∞) * 2 := by
    calc
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) 0 =
          analyticOrderAt ((fun x : ℝ => p.eval x) ∘
            (fun y : ℝ => Real.cos (2 * Real.pi * y))) 0 := by
            rfl
      _ = analyticOrderAt (fun x : ℝ => p.eval x) (Real.cos (2 * Real.pi * 0)) *
            analyticOrderAt
              (fun y : ℝ => Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * 0)) 0 := by
            exact AnalyticAt.analyticOrderAt_comp
              (𝕜 := ℝ) (E := ℝ) (f := fun x : ℝ => p.eval x)
              (g := fun y : ℝ => Real.cos (2 * Real.pi * y)) (z₀ := 0)
              hpoly_an hcos_an
      _ = (p.rootMultiplicity 1 : ℕ∞) * 2 := by
            rw [hcos0, hcos_order,
              putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p) (x := 1) hp]
  have hprod_order :
      analyticOrderAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) 0 =
        (p.rootMultiplicity 1 : ℕ∞) * 2 + 1 := by
    change analyticOrderAt
      ((fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) *
        (fun y : ℝ => Real.sin (2 * Real.pi * y))) 0 =
        (p.rootMultiplicity 1 : ℕ∞) * 2 + 1
    rw [analyticOrderAt_mul hcomp_an hsin_an, hcomp_order,
      putnam_2000_b3_analyticOrderAt_sin_two_pi_zero]
  have hprod_finite :
      analyticOrderAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) 0 ≠ ⊤ := by
    rw [hprod_order]
    change ((p.rootMultiplicity 1 : ℕ∞) * ((2 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞)) ≠ ⊤
    rw [← Nat.cast_mul, ← Nat.cast_add]
    exact ENat.coe_ne_top _
  have hprod_nat :
      analyticOrderNatAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) 0 =
        2 * p.rootMultiplicity 1 + 1 := by
    rw [← Nat.cast_inj (R := ℕ∞)]
    rw [Nat.cast_analyticOrderNatAt hprod_finite, hprod_order, Nat.cast_add, Nat.cast_mul]
    norm_num
    rw [mul_comm]
  have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [putnam_2000_b3_mult_eq_analyticOrderNatAt_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m) 0, hiter]
  rw [putnam_2000_b3_analyticOrderNatAt_const_mul hscalar hprod_an hprod_finite,
    hprod_nat]

private lemma putnam_2000_b3_mult_even_half_eq_two_rootMultiplicity_sinPoly_add_one
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) :
  mult (iteratedDeriv (2 * m) f) (1 / 2) =
    2 * (putnam_2000_b3_sinPoly N a (2 * m)).rootMultiplicity (-1) + 1 := by
  classical
  let p := putnam_2000_b3_sinPoly N a (2 * m)
  have hp : p ≠ 0 := putnam_2000_b3_sinPoly_ne_zero N hN a (2 * m) haN
  have hiter :
      (iteratedDeriv (2 * m) f) =
        fun y : ℝ => (-1 : ℝ) ^ m *
          (p.eval (Real.cos (2 * Real.pi * y)) *
            Real.sin (2 * Real.pi * y)) := by
    funext y
    simpa [p] using putnam_2000_b3_iteratedDeriv_even_eq_sinPoly N a f hf m y
  have hcomp_an :
      AnalyticAt ℝ (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) := by
    simpa [Polynomial.aeval_def] using
      (putnam_2000_b3_analyticAt_cos_two_pi (1 / 2 : ℝ)).aeval_polynomial p
  have hsin_an :
      AnalyticAt ℝ (fun y : ℝ => Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) :=
    putnam_2000_b3_analyticAt_sin_two_pi (1 / 2 : ℝ)
  have hprod_an :
      AnalyticAt ℝ
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) := hcomp_an.mul hsin_an
  have hpoly_an :
      AnalyticAt ℝ (fun x : ℝ => p.eval x)
        (Real.cos (2 * Real.pi * (1 / 2 : ℝ))) := by
    simpa [Polynomial.aeval_def] using
      (analyticAt_id (𝕜 := ℝ) (E := ℝ)
        (z := Real.cos (2 * Real.pi * (1 / 2 : ℝ)))).aeval_polynomial p
  have hcos_an :
      AnalyticAt ℝ (fun y : ℝ => Real.cos (2 * Real.pi * y)) (1 / 2 : ℝ) :=
    putnam_2000_b3_analyticAt_cos_two_pi (1 / 2 : ℝ)
  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by
    ring
  have hcoshalf : Real.cos (2 * Real.pi * (1 / 2 : ℝ)) = -1 := by
    rw [harg, Real.cos_pi]
  have hcos_order :
      analyticOrderAt
        (fun y : ℝ => Real.cos (2 * Real.pi * y) -
          (-1 : ℝ)) (1 / 2 : ℝ) = 2 := by
    simpa [sub_neg_eq_add] using
      putnam_2000_b3_analyticOrderAt_cos_two_pi_add_one_half
  have hcomp_order :
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) =
        (p.rootMultiplicity (-1) : ℕ∞) * 2 := by
    calc
      analyticOrderAt (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) =
          analyticOrderAt ((fun x : ℝ => p.eval x) ∘
            (fun y : ℝ => Real.cos (2 * Real.pi * y))) (1 / 2 : ℝ) := by
            rfl
      _ = analyticOrderAt (fun x : ℝ => p.eval x)
            (Real.cos (2 * Real.pi * (1 / 2 : ℝ))) *
            analyticOrderAt
              (fun y : ℝ => Real.cos (2 * Real.pi * y) -
                Real.cos (2 * Real.pi * (1 / 2 : ℝ))) (1 / 2 : ℝ) := by
            exact AnalyticAt.analyticOrderAt_comp
              (𝕜 := ℝ) (E := ℝ) (f := fun x : ℝ => p.eval x)
              (g := fun y : ℝ => Real.cos (2 * Real.pi * y)) (z₀ := (1 / 2 : ℝ))
              hpoly_an hcos_an
      _ = (p.rootMultiplicity (-1) : ℕ∞) * 2 := by
            rw [hcoshalf, hcos_order,
              putnam_2000_b3_analyticOrderAt_polynomial_eval (p := p) (x := -1) hp]
  have hprod_order :
      analyticOrderAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) =
        (p.rootMultiplicity (-1) : ℕ∞) * 2 + 1 := by
    change analyticOrderAt
      ((fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y))) *
        (fun y : ℝ => Real.sin (2 * Real.pi * y))) (1 / 2 : ℝ) =
        (p.rootMultiplicity (-1) : ℕ∞) * 2 + 1
    rw [analyticOrderAt_mul hcomp_an hsin_an, hcomp_order,
      putnam_2000_b3_analyticOrderAt_sin_two_pi_half]
  have hprod_finite :
      analyticOrderAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) ≠ ⊤ := by
    rw [hprod_order]
    change ((p.rootMultiplicity (-1) : ℕ∞) * ((2 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞)) ≠ ⊤
    rw [← Nat.cast_mul, ← Nat.cast_add]
    exact ENat.coe_ne_top _
  have hprod_nat :
      analyticOrderNatAt
        (fun y : ℝ => p.eval (Real.cos (2 * Real.pi * y)) *
          Real.sin (2 * Real.pi * y)) (1 / 2 : ℝ) =
        2 * p.rootMultiplicity (-1) + 1 := by
    rw [← Nat.cast_inj (R := ℕ∞)]
    rw [Nat.cast_analyticOrderNatAt hprod_finite, hprod_order, Nat.cast_add, Nat.cast_mul]
    norm_num
    rw [mul_comm]
  have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [putnam_2000_b3_mult_eq_analyticOrderNatAt_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m) (1 / 2 : ℝ), hiter]
  rw [putnam_2000_b3_analyticOrderNatAt_const_mul hscalar hprod_an hprod_finite,
    hprod_nat]

private lemma putnam_2000_b3_exists_nonzero_iteratedDeriv_at
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (k : ℕ) (t : ℝ) :
  ∃ c : ℕ, iteratedDeriv c (iteratedDeriv k f) t ≠ 0 := by
  exact putnam_2000_b3_exists_iteratedDeriv_ne_zero_of_finite_order
    ((putnam_2000_b3_analyticOnNhd_iteratedDeriv_f N a f hf k) t trivial)
    (putnam_2000_b3_analyticOrderAt_ne_top_iteratedDeriv N hN a f haN hf k t)

private lemma putnam_2000_b3_mult_iteratedDeriv_succ_add_one
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  {k : ℕ} {t : ℝ} (hzero : iteratedDeriv k f t = 0) :
  mult (iteratedDeriv (k + 1) f) t + 1 = mult (iteratedDeriv k f) t := by
  rw [iteratedDeriv_succ]
  exact putnam_2000_b3_mult_deriv_add_one mult hmult
    (putnam_2000_b3_exists_nonzero_iteratedDeriv_at N hN a f haN hf k t) hzero

private lemma putnam_2000_b3_card_le_sdiff_of_cyclic_interleaved
  {α : Type*} [LinearOrder α] [DecidableEq α] (s t : Finset α)
  (hbetween :
    ∀ x ∈ s, ∀ y ∈ s, x < y →
      (∀ z ∈ s, z ∉ Set.Ioo x y) →
        ∃ z ∈ t \ s, x < z ∧ z < y)
  (hwrap :
    ∀ hs : s.Nonempty,
      ∃ z ∈ t \ s,
        ¬ (s.min' hs < z ∧ z < s.max' hs)) :
  s.card ≤ (t \ s).card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let lo := s.min' hs
  let hi := s.max' hs
  let between : Finset α := (t \ s).filter fun z => lo < z ∧ z < hi
  have hcard_between : s.card ≤ between.card + 1 := by
    refine Finset.card_le_of_interleaved (s := s) (t := between) ?_
    intro x hx y hy hxy hno
    rcases hbetween x hx y hy hxy hno with ⟨z, hzts, hxz, hzy⟩
    have hloz : lo < z := lt_of_le_of_lt (s.min'_le x hx) hxz
    have hzhi : z < hi := lt_of_lt_of_le hzy (s.le_max' y hy)
    exact ⟨z, by simp [between, lo, hi, hzts, hloz, hzhi], hxz, hzy⟩
  rcases hwrap hs with ⟨w, hwts, hwoutside⟩
  have hwnot : w ∉ between := by
    intro hw
    exact hwoutside (by simpa [between, lo, hi] using (Finset.mem_filter.mp hw).2)
  have hinsert : insert w between ⊆ t \ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzbetween
    · exact hwts
    · exact (Finset.mem_filter.mp hzbetween).1
  calc
    s.card ≤ between.card + 1 := hcard_between
    _ = (insert w between).card := by
      rw [Finset.card_insert_of_notMem hwnot]
    _ ≤ (t \ s).card := Finset.card_mono hinsert

private lemma putnam_2000_b3_card_support_le_deriv_new_support
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (k : ℕ) :
  let S := (putnam_2000_b3_mult_support_finite_iteratedDeriv
    N hN a f mult haN hf hmult k).toFinset
  let T := (putnam_2000_b3_mult_support_finite_iteratedDeriv
    N hN a f mult haN hf hmult (k + 1)).toFinset
  S.card ≤ (T \ S).card := by
  classical
  intro S T
  let u : Ico (0 : ℝ) 1 → ℕ := fun t => mult (iteratedDeriv k f) (t : ℝ)
  let v : Ico (0 : ℝ) 1 → ℕ := fun t => mult (iteratedDeriv (k + 1) f) (t : ℝ)
  let g := iteratedDeriv k f
  have hSmem : ∀ t : Ico (0 : ℝ) 1, t ∈ S ↔ u t ≠ 0 := by
    intro t
    simp [S, u, Set.Finite.mem_toFinset, Function.mem_support]
  have hTmem : ∀ t : Ico (0 : ℝ) 1, t ∈ T ↔ v t ≠ 0 := by
    intro t
    simp [T, v, Set.Finite.mem_toFinset, Function.mem_support]
  have hzero_of_mem :
      ∀ t : Ico (0 : ℝ) 1, t ∈ S → g (t : ℝ) = 0 := by
    intro t ht
    have htne : u t ≠ 0 := (hSmem t).1 ht
    have htpos : 0 < u t := Nat.pos_of_ne_zero htne
    exact (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult
      (putnam_2000_b3_exists_nonzero_iteratedDeriv_at
        N hN a f haN hf k (t : ℝ))).1 (by simpa [u, g] using htpos)
  have hmem_T_of_deriv_zero :
      ∀ t : Ico (0 : ℝ) 1,
        iteratedDeriv (k + 1) f (t : ℝ) = 0 → t ∈ T := by
    intro t htzero
    have htpos : 0 < v t :=
      (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult
        (putnam_2000_b3_exists_nonzero_iteratedDeriv_at
          N hN a f haN hf (k + 1) (t : ℝ))).2 (by simpa [v] using htzero)
    exact (hTmem t).2 htpos.ne'
  refine putnam_2000_b3_card_le_sdiff_of_cyclic_interleaved S T ?_ ?_
  · intro x hx y hy hxy hno
    have hxzero : g (x : ℝ) = 0 := hzero_of_mem x hx
    have hyzero : g (y : ℝ) = 0 := hzero_of_mem y hy
    have hcont : ContinuousOn g (Icc (x : ℝ) (y : ℝ)) :=
      (putnam_2000_b3_contDiff_iteratedDeriv_f N a f hf k).continuous.continuousOn
    rcases exists_deriv_eq_zero (f := g) (a := (x : ℝ)) (b := (y : ℝ))
      (by simpa using hxy) hcont (hxzero.trans hyzero.symm) with
      ⟨c, hc, hcderiv⟩
    have hcIco : c ∈ Ico (0 : ℝ) 1 := by
      exact ⟨le_of_lt (lt_of_le_of_lt x.property.1 hc.1),
        lt_trans hc.2 y.property.2⟩
    let z : Ico (0 : ℝ) 1 := ⟨c, hcIco⟩
    have hzderiv : iteratedDeriv (k + 1) f (z : ℝ) = 0 := by
      simpa [z, g, iteratedDeriv_succ] using hcderiv
    have hzT : z ∈ T := hmem_T_of_deriv_zero z hzderiv
    have hznotS : z ∉ S := by
      intro hzS
      exact hno z hzS ⟨by simpa [z] using hc.1, by simpa [z] using hc.2⟩
    exact ⟨z, Finset.mem_sdiff.mpr ⟨hzT, hznotS⟩,
      by simpa [z] using hc.1, by simpa [z] using hc.2⟩
  · intro hSnonempty
    let lo := S.min' hSnonempty
    let hi := S.max' hSnonempty
    have hloS : lo ∈ S := S.min'_mem hSnonempty
    have hhiS : hi ∈ S := S.max'_mem hSnonempty
    have hlozero : g (lo : ℝ) = 0 := hzero_of_mem lo hloS
    have hhizero : g (hi : ℝ) = 0 := hzero_of_mem hi hhiS
    have hwrap_lt : (hi : ℝ) < (lo : ℝ) + 1 := by
      have hhi_lt_one : (hi : ℝ) < 1 := hi.property.2
      have hlo_nonneg : 0 ≤ (lo : ℝ) := lo.property.1
      linarith
    have hcont : ContinuousOn g (Icc (hi : ℝ) ((lo : ℝ) + 1)) :=
      (putnam_2000_b3_contDiff_iteratedDeriv_f N a f hf k).continuous.continuousOn
    have hperiod_g := putnam_2000_b3_periodic_iteratedDeriv_f N a f hf k
    have hrightzero : g ((lo : ℝ) + 1) = 0 := by
      simpa [g] using (hperiod_g (lo : ℝ)).trans hlozero
    rcases exists_deriv_eq_zero (f := g) (a := (hi : ℝ)) (b := (lo : ℝ) + 1)
      hwrap_lt hcont (hhizero.trans hrightzero.symm) with
      ⟨c, hc, hcderiv⟩
    have hcderiv' : iteratedDeriv (k + 1) f c = 0 := by
      simpa [g, iteratedDeriv_succ] using hcderiv
    by_cases hc_lt_one : c < 1
    · have hcIco : c ∈ Ico (0 : ℝ) 1 := by
        exact ⟨le_of_lt (lt_of_le_of_lt hi.property.1 hc.1), hc_lt_one⟩
      let z : Ico (0 : ℝ) 1 := ⟨c, hcIco⟩
      have hzT : z ∈ T := hmem_T_of_deriv_zero z (by simpa [z] using hcderiv')
      have hhi_lt_z : hi < z := by simpa [z] using hc.1
      have hznotS : z ∉ S := by
        intro hzS
        exact (not_lt_of_ge (S.le_max' z hzS)) hhi_lt_z
      refine ⟨z, Finset.mem_sdiff.mpr ⟨hzT, hznotS⟩, ?_⟩
      intro hbetween
      exact (not_lt_of_ge (le_of_lt hhi_lt_z)) hbetween.2
    · have hc_ge_one : 1 ≤ c := le_of_not_gt hc_lt_one
      have hz_nonneg : 0 ≤ c - 1 := sub_nonneg.mpr hc_ge_one
      have hz_lt_lo : c - 1 < (lo : ℝ) := by
        have hc_right : c < (lo : ℝ) + 1 := hc.2
        linarith
      have hz_lt_one : c - 1 < 1 := lt_trans hz_lt_lo lo.property.2
      let z : Ico (0 : ℝ) 1 := ⟨c - 1, hz_nonneg, hz_lt_one⟩
      have hperiod_dg := putnam_2000_b3_periodic_iteratedDeriv_f N a f hf (k + 1)
      have hzderiv : iteratedDeriv (k + 1) f (z : ℝ) = 0 := by
        have hper := hperiod_dg (c - 1)
        have hcsub : c - 1 + 1 = c := by ring
        rw [← hper, hcsub]
        exact hcderiv'
      have hzT : z ∈ T := hmem_T_of_deriv_zero z hzderiv
      have hz_lt_lo_sub : z < lo := by simpa [z] using hz_lt_lo
      have hznotS : z ∉ S := by
        intro hzS
        exact (not_lt_of_ge (S.min'_le z hzS)) hz_lt_lo_sub
      refine ⟨z, Finset.mem_sdiff.mpr ⟨hzT, hznotS⟩, ?_⟩
      intro hbetween
      exact (not_lt_of_ge (le_of_lt hz_lt_lo_sub)) hbetween.1

private lemma putnam_2000_b3_sin_two_pi_eq_zero_of_Ico
  {t : Ico (0 : ℝ) 1} (h : Real.sin (2 * Real.pi * (t : ℝ)) = 0) :
  (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 2 := by
  rcases (Real.sin_eq_zero_iff.mp h) with ⟨n, hn⟩
  have hnr : (n : ℝ) = 2 * (t : ℝ) := by
    nlinarith [hn, Real.pi_pos]
  have hn_nonneg_real : (0 : ℝ) ≤ (n : ℝ) := by
    rw [hnr]
    nlinarith [t.property.1]
  have hn_nonneg : (0 : ℤ) ≤ n := by exact_mod_cast hn_nonneg_real
  have hn_lt_two_real : (n : ℝ) < 2 := by
    rw [hnr]
    nlinarith [t.property.2]
  have hn_lt_two : n < (2 : ℤ) := by exact_mod_cast hn_lt_two_real
  have hn_cases : n = 0 ∨ n = 1 := by omega
  rcases hn_cases with rfl | rfl
  · norm_num at hnr
    left
    simpa using hnr
  · norm_num at hnr
    right
    nlinarith

private lemma putnam_2000_b3_cos_two_pi_eq_of_Ico
  {t u : Ico (0 : ℝ) 1}
  (h : Real.cos (2 * Real.pi * (u : ℝ)) =
      Real.cos (2 * Real.pi * (t : ℝ))) :
  (u : ℝ) = (t : ℝ) ∨ (u : ℝ) = 1 - (t : ℝ) := by
  rcases (Real.cos_eq_cos_iff.mp h) with ⟨k, hk | hk⟩
  · have hkr : (k : ℝ) = (t : ℝ) - (u : ℝ) := by
      nlinarith [hk, Real.pi_pos]
    have hk_gt_neg_one_real : (-1 : ℝ) < (k : ℝ) := by
      rw [hkr]
      nlinarith [t.property.1, u.property.2]
    have hk_gt_neg_one : (-1 : ℤ) < k := by exact_mod_cast hk_gt_neg_one_real
    have hk_lt_one_real : (k : ℝ) < 1 := by
      rw [hkr]
      nlinarith [t.property.2, u.property.1]
    have hk_lt_one : k < (1 : ℤ) := by exact_mod_cast hk_lt_one_real
    have hk0 : k = 0 := by omega
    subst k
    norm_num at hkr
    left
    nlinarith
  · have hkr : (k : ℝ) = (t : ℝ) + (u : ℝ) := by
      nlinarith [hk, Real.pi_pos]
    have hk_nonneg_real : (0 : ℝ) ≤ (k : ℝ) := by
      rw [hkr]
      nlinarith [t.property.1, u.property.1]
    have hk_nonneg : (0 : ℤ) ≤ k := by exact_mod_cast hk_nonneg_real
    have hk_lt_two_real : (k : ℝ) < 2 := by
      rw [hkr]
      nlinarith [t.property.2, u.property.2]
    have hk_lt_two : k < (2 : ℤ) := by exact_mod_cast hk_lt_two_real
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hkr
      left
      nlinarith [u.property.1, t.property.1]
    · norm_num at hkr
      right
      nlinarith

private lemma putnam_2000_b3_cos_fiber_card_le_two
  (s : Finset (Ico (0 : ℝ) 1)) (x : ℝ) :
  (s.filter fun t : Ico (0 : ℝ) 1 =>
      Real.cos (2 * Real.pi * (t : ℝ)) = x).card ≤ 2 := by
  classical
  let F : Finset (Ico (0 : ℝ) 1) :=
    s.filter fun t : Ico (0 : ℝ) 1 =>
      Real.cos (2 * Real.pi * (t : ℝ)) = x
  by_cases hF : F.Nonempty
  · rcases hF with ⟨t0, ht0F⟩
    have hsubset : F.image (fun t : Ico (0 : ℝ) 1 => (t : ℝ)) ⊆
        ({(t0 : ℝ), 1 - (t0 : ℝ)} : Finset ℝ) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨u, huF, rfl⟩
      have hu : Real.cos (2 * Real.pi * (u : ℝ)) = x := by
        simpa [F] using (Finset.mem_filter.mp huF).2
      have ht0 : Real.cos (2 * Real.pi * (t0 : ℝ)) = x := by
        simpa [F] using (Finset.mem_filter.mp ht0F).2
      rcases putnam_2000_b3_cos_two_pi_eq_of_Ico
          (t := t0) (u := u) (by rw [hu, ht0]) with hEq | hEq
      · simp [hEq]
      · simp [hEq]
    calc
      F.card = (F.image (fun t : Ico (0 : ℝ) 1 => (t : ℝ))).card := by
        rw [Finset.card_image_of_injective]
        intro a b h
        exact Subtype.ext h
      _ ≤ ({(t0 : ℝ), 1 - (t0 : ℝ)} : Finset ℝ).card :=
        Finset.card_mono hsubset
      _ ≤ 2 := Finset.card_le_two
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [F, hzero]

private lemma putnam_2000_b3_endpoint_filter_sum_rootMultiplicity
  {p : Polynomial ℝ} (hp : p ≠ 0) (c : ℝ) :
  (p.roots.toFinset.filter fun x : ℝ => x = c).sum
      (fun x => p.rootMultiplicity x) =
    p.rootMultiplicity c := by
  classical
  let R := p.roots.toFinset
  by_cases hc : c ∈ R
  · rw [Finset.sum_eq_single_of_mem c]
    · simp [R, hc]
    · intro x hx hxc
      exact False.elim (hxc (Finset.mem_filter.mp hx).2)
  · have hfilter_empty : R.filter (fun x : ℝ => x = c) = ∅ := by
      ext x
      constructor
      · intro hx
        have hxR : x ∈ R := (Finset.mem_filter.mp hx).1
        have hxc : x = c := (Finset.mem_filter.mp hx).2
        exact False.elim (hc (by simpa [hxc] using hxR))
      · intro hx
        simp at hx
    have hnotroot : ¬p.IsRoot c := by
      intro hroot
      exact hc (by simpa [R] using (Polynomial.mem_roots hp).2 hroot)
    rw [show (p.roots.toFinset.filter fun x : ℝ => x = c) = ∅ by
      simpa [R] using hfilter_empty]
    rw [Finset.sum_empty, Polynomial.rootMultiplicity_eq_zero hnotroot]

private lemma putnam_2000_b3_rootMultiplicity_endpoint_partition
  {p : Polynomial ℝ} (hp : p ≠ 0) :
  p.rootMultiplicity 1 + p.rootMultiplicity (-1) +
      (p.roots.toFinset.filter fun x : ℝ => x ≠ 1 ∧ x ≠ -1).sum
        (fun x => p.rootMultiplicity x) =
    p.roots.toFinset.sum (fun x => p.rootMultiplicity x) := by
  classical
  let R := p.roots.toFinset
  have h1 := putnam_2000_b3_endpoint_filter_sum_rootMultiplicity
    (p := p) hp (1 : ℝ)
  have hm1 := putnam_2000_b3_endpoint_filter_sum_rootMultiplicity
    (p := p) hp (-1 : ℝ)
  have hsplit1 :
      R.sum (fun x => p.rootMultiplicity x) =
        (R.filter fun x : ℝ => x = 1).sum (fun x => p.rootMultiplicity x) +
        (R.filter fun x : ℝ => x ≠ 1).sum (fun x => p.rootMultiplicity x) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := R)
      (p := fun x : ℝ => x = 1) (f := fun x => p.rootMultiplicity x)]
  have hsplit2 :
      (R.filter fun x : ℝ => x ≠ 1).sum (fun x => p.rootMultiplicity x) =
        ((R.filter fun x : ℝ => x ≠ 1).filter fun x : ℝ => x = -1).sum
          (fun x => p.rootMultiplicity x) +
        ((R.filter fun x : ℝ => x ≠ 1).filter fun x : ℝ => x ≠ -1).sum
          (fun x => p.rootMultiplicity x) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := R.filter fun x : ℝ => x ≠ 1) (p := fun x : ℝ => x = -1)
      (f := fun x => p.rootMultiplicity x)]
  have hfilter_m1 :
      ((R.filter fun x : ℝ => x ≠ 1).filter fun x : ℝ => x = -1) =
        (R.filter fun x : ℝ => x = -1) := by
    ext x
    by_cases hx : x = -1
    · subst x
      simp [show ((-1 : ℝ) ≠ 1) by norm_num]
    · simp [hx]
  have hfilter_rest :
      ((R.filter fun x : ℝ => x ≠ 1).filter fun x : ℝ => x ≠ -1) =
        (R.filter fun x : ℝ => x ≠ 1 ∧ x ≠ -1) := by
    ext x
    simp [and_assoc]
  rw [hsplit1, hsplit2, hfilter_m1, hfilter_rest]
  rw [show (R.filter fun x : ℝ => x = 1).sum
      (fun x => p.rootMultiplicity x) = p.rootMultiplicity 1 by
    simpa [R] using h1]
  rw [show (R.filter fun x : ℝ => x = -1).sum
      (fun x => p.rootMultiplicity x) = p.rootMultiplicity (-1) by
    simpa [R] using hm1]
  ring

private lemma putnam_2000_b3_tsum_odd_le_two_mul_N
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) :
  (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv (2 * m + 1) f) (t : ℝ)) ≤
    2 * N := by
  classical
  let p := putnam_2000_b3_cosPoly N a (2 * m + 1)
  let u : Ico (0 : ℝ) 1 → ℕ :=
    fun t => mult (iteratedDeriv (2 * m + 1) f) (t : ℝ)
  let hs := putnam_2000_b3_mult_support_finite_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m + 1)
  let S := hs.toFinset
  let R := p.roots.toFinset
  have hp : p ≠ 0 := putnam_2000_b3_cosPoly_ne_zero N hN a (2 * m + 1) haN
  have hSmem : ∀ t : Ico (0 : ℝ) 1, t ∈ S ↔ u t ≠ 0 := by
    intro t
    simp [S, u, Set.Finite.mem_toFinset, Function.mem_support]
  have hzero_of_mem :
      ∀ t : Ico (0 : ℝ) 1, t ∈ S →
        iteratedDeriv (2 * m + 1) f (t : ℝ) = 0 := by
    intro t ht
    have htne : u t ≠ 0 := (hSmem t).1 ht
    have htpos : 0 < u t := Nat.pos_of_ne_zero htne
    exact (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult
      (putnam_2000_b3_exists_nonzero_iteratedDeriv_at
        N hN a f haN hf (2 * m + 1) (t : ℝ))).1 (by simpa [u] using htpos)
  have hroot_of_mem :
      ∀ t : Ico (0 : ℝ) 1, t ∈ S →
        p.IsRoot (Real.cos (2 * Real.pi * (t : ℝ))) := by
    intro t ht
    have hzero := hzero_of_mem t ht
    have hform := putnam_2000_b3_iteratedDeriv_odd_eq_cosPoly N a f hf m (t : ℝ)
    have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hform] at hzero
    have hpeval : p.eval (Real.cos (2 * Real.pi * (t : ℝ))) = 0 := by
      exact mul_eq_zero.mp hzero |>.resolve_left hscalar
    exact (Polynomial.IsRoot.def).2 hpeval
  have htsum :
      (∑' t : Ico (0 : ℝ) 1, u t) = ∑ t ∈ S, u t := by
    simpa [u, S, hs] using
      putnam_2000_b3_tsum_eq_sum_of_support_finite u (by simpa [u] using hs)
  change (∑' t : Ico (0 : ℝ) 1, u t) ≤ 2 * N
  rw [htsum]
  by_cases hR : R.Nonempty
  · rcases hR with ⟨r0, hr0⟩
    let rootOf : Ico (0 : ℝ) 1 → {x : ℝ // x ∈ R} := fun t =>
      if ht : t ∈ S then
        ⟨Real.cos (2 * Real.pi * (t : ℝ)),
          by
            simpa [R] using (Polynomial.mem_roots hp).2 (hroot_of_mem t ht)⟩
      else
        ⟨r0, hr0⟩
    have hrootOf_val :
        ∀ t : Ico (0 : ℝ) 1, t ∈ S →
          (rootOf t : ℝ) = Real.cos (2 * Real.pi * (t : ℝ)) := by
      intro t ht
      simp [rootOf, ht]
    have hfiber_bound :
        ∀ x : {x : ℝ // x ∈ R},
          (∑ t ∈ S.filter (fun t : Ico (0 : ℝ) 1 => rootOf t = x), u t) ≤
            2 * p.rootMultiplicity (x : ℝ) := by
      intro x
      let F : Finset (Ico (0 : ℝ) 1) :=
        S.filter fun t : Ico (0 : ℝ) 1 => rootOf t = x
      have hF_eq :
          (∑ t ∈ S.filter (fun t : Ico (0 : ℝ) 1 => rootOf t = x), u t) =
            F.sum u := by rfl
      rw [hF_eq]
      let z0 : Ico (0 : ℝ) 1 := ⟨0, by norm_num⟩
      let zH : Ico (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
      by_cases hx1 : (x : ℝ) = 1
      · have hFsubset : F ⊆ ({z0} : Finset (Ico (0 : ℝ) 1)) := by
          intro t htF
          have htS : t ∈ S := (Finset.mem_filter.mp htF).1
          have htx : rootOf t = x := (Finset.mem_filter.mp htF).2
          have hcos : Real.cos (2 * Real.pi * (t : ℝ)) = 1 := by
            rw [← hrootOf_val t htS, htx, hx1]
          have hcos0 : Real.cos (2 * Real.pi * (z0 : ℝ)) =
              Real.cos (2 * Real.pi * (t : ℝ)) := by
            simp [z0, hcos]
          rcases putnam_2000_b3_cos_two_pi_eq_of_Ico
              (t := t) (u := z0) hcos0 with hz | hz
          · exact by simpa [z0] using Subtype.ext hz.symm
          · have htone : (t : ℝ) = 1 := by
              have hz0 : (z0 : ℝ) = 0 := rfl
              linarith
            exact False.elim (not_lt_of_ge (le_of_eq htone.symm) t.property.2)
        have hsum_le : F.sum u ≤ ({z0} : Finset (Ico (0 : ℝ) 1)).sum u :=
          Finset.sum_le_sum_of_subset_of_nonneg hFsubset (by
            intro t _ _
            exact Nat.zero_le _)
        have hz0 :
            u z0 = 2 * p.rootMultiplicity 1 := by
          simpa [u, p, z0] using
            putnam_2000_b3_mult_odd_zero_eq_two_rootMultiplicity_cosPoly
              N hN a f mult haN hf hmult m
        calc
          F.sum u ≤ ({z0} : Finset (Ico (0 : ℝ) 1)).sum u := hsum_le
          _ = 2 * p.rootMultiplicity (x : ℝ) := by
            simp [hz0, hx1]
      · by_cases hxm1 : (x : ℝ) = -1
        · have hFsubset : F ⊆ ({zH} : Finset (Ico (0 : ℝ) 1)) := by
            intro t htF
            have htS : t ∈ S := (Finset.mem_filter.mp htF).1
            have htx : rootOf t = x := (Finset.mem_filter.mp htF).2
            have hcos : Real.cos (2 * Real.pi * (t : ℝ)) = -1 := by
              rw [← hrootOf_val t htS, htx, hxm1]
            have hcosH : Real.cos (2 * Real.pi * (zH : ℝ)) =
                Real.cos (2 * Real.pi * (t : ℝ)) := by
              have harg : 2 * Real.pi * (zH : ℝ) = Real.pi := by
                norm_num [zH]
                ring
              rw [harg, Real.cos_pi, hcos]
            rcases putnam_2000_b3_cos_two_pi_eq_of_Ico
                (t := t) (u := zH) hcosH with hz | hz
            · exact by
                apply Finset.mem_singleton.mpr
                exact Subtype.ext hz.symm
            · have hz' : (t : ℝ) = 1 / 2 := by
                have hz' : (t : ℝ) = 1 - (zH : ℝ) := by linarith
                norm_num [zH] at hz'
                exact hz'
              exact by
                apply Finset.mem_singleton.mpr
                exact Subtype.ext hz'
          have hsum_le : F.sum u ≤ ({zH} : Finset (Ico (0 : ℝ) 1)).sum u :=
            Finset.sum_le_sum_of_subset_of_nonneg hFsubset (by
              intro t _ _
              exact Nat.zero_le _)
          have hzH :
              u zH = 2 * p.rootMultiplicity (-1) := by
            simpa [u, p, zH] using
              putnam_2000_b3_mult_odd_half_eq_two_rootMultiplicity_cosPoly
                N hN a f mult haN hf hmult m
          calc
            F.sum u ≤ ({zH} : Finset (Ico (0 : ℝ) 1)).sum u := hsum_le
            _ = 2 * p.rootMultiplicity (x : ℝ) := by
              simp [hzH, hxm1]
        · have hu_eq :
              ∀ t ∈ F, u t = p.rootMultiplicity (x : ℝ) := by
            intro t htF
            have htS : t ∈ S := (Finset.mem_filter.mp htF).1
            have htx : rootOf t = x := (Finset.mem_filter.mp htF).2
            have hcosx : Real.cos (2 * Real.pi * (t : ℝ)) = (x : ℝ) := by
              rw [← hrootOf_val t htS, htx]
            have hsin_ne : Real.sin (2 * Real.pi * (t : ℝ)) ≠ 0 := by
              intro hsin
              rcases putnam_2000_b3_sin_two_pi_eq_zero_of_Ico hsin with ht0 | htH
              · have hx : (x : ℝ) = 1 := by
                  rw [← hcosx, ht0]
                  simp [Real.cos_zero]
                exact hx1 hx
              · have hx : (x : ℝ) = -1 := by
                  rw [← hcosx, htH]
                  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
                  rw [harg, Real.cos_pi]
                exact hxm1 hx
            calc
              u t =
                  (putnam_2000_b3_cosPoly N a (2 * m + 1)).rootMultiplicity
                    (Real.cos (2 * Real.pi * (t : ℝ))) := by
                simpa [u] using
                  putnam_2000_b3_mult_odd_eq_rootMultiplicity_cosPoly_of_sin_ne_zero
                    N hN a f mult haN hf hmult m hsin_ne
              _ = p.rootMultiplicity (x : ℝ) := by
                simp [p, hcosx]
          have hcard : F.card ≤ 2 := by
            have hsubset : F ⊆
                S.filter (fun t : Ico (0 : ℝ) 1 =>
                  Real.cos (2 * Real.pi * (t : ℝ)) = (x : ℝ)) := by
              intro t htF
              have htS : t ∈ S := (Finset.mem_filter.mp htF).1
              have htx : rootOf t = x := (Finset.mem_filter.mp htF).2
              have hcosx : Real.cos (2 * Real.pi * (t : ℝ)) = (x : ℝ) := by
                rw [← hrootOf_val t htS, htx]
              exact Finset.mem_filter.mpr ⟨htS, hcosx⟩
            exact (Finset.card_mono hsubset).trans
              (putnam_2000_b3_cos_fiber_card_le_two S (x : ℝ))
          have hsum_le_card :
              F.sum u ≤ F.card • p.rootMultiplicity (x : ℝ) := by
            exact Finset.sum_le_card_nsmul F u (p.rootMultiplicity (x : ℝ))
              (fun t ht => by rw [hu_eq t ht])
          calc
            F.sum u ≤ F.card • p.rootMultiplicity (x : ℝ) := hsum_le_card
            _ ≤ 2 * p.rootMultiplicity (x : ℝ) := by
              simpa [Nat.nsmul_eq_mul] using
                Nat.mul_le_mul_right (p.rootMultiplicity (x : ℝ)) hcard
    have hfiber_sum := Finset.sum_fiberwise S rootOf u
    calc
      ∑ t ∈ S, u t =
          ∑ x : {x : ℝ // x ∈ R},
            ∑ t ∈ S.filter (fun t : Ico (0 : ℝ) 1 => rootOf t = x), u t := by
        exact hfiber_sum.symm
      _ ≤ ∑ x : {x : ℝ // x ∈ R}, 2 * p.rootMultiplicity (x : ℝ) := by
        exact Finset.sum_le_sum fun x _ => hfiber_bound x
      _ = ∑ x ∈ R, 2 * p.rootMultiplicity x := by
        symm
        exact Finset.sum_subtype R (by intro x; rfl)
          (fun x => 2 * p.rootMultiplicity x)
      _ = 2 * R.sum (fun x => p.rootMultiplicity x) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * p.natDegree := by
        exact Nat.mul_le_mul_left 2 (by
          simpa [R] using putnam_2000_b3_sum_rootMultiplicity_roots_le_natDegree p)
      _ ≤ 2 * N := by
        exact Nat.mul_le_mul_left 2 (putnam_2000_b3_cosPoly_natDegree_le N a (2 * m + 1))
  · have hsum_zero : ∑ t ∈ S, u t = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hroot : Real.cos (2 * Real.pi * (t : ℝ)) ∈ R :=
        by simpa [R] using (Polynomial.mem_roots hp).2 (hroot_of_mem t ht)
      exact False.elim (hR ⟨_, hroot⟩)
    rw [hsum_zero]
    exact Nat.zero_le _

private lemma putnam_2000_b3_tsum_even_le_two_mul_N
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (m : ℕ) :
  (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv (2 * m) f) (t : ℝ)) ≤
    2 * N := by
  classical
  let p := putnam_2000_b3_sinPoly N a (2 * m)
  let u : Ico (0 : ℝ) 1 → ℕ :=
    fun t => mult (iteratedDeriv (2 * m) f) (t : ℝ)
  let hs := putnam_2000_b3_mult_support_finite_iteratedDeriv
    N hN a f mult haN hf hmult (2 * m)
  let S := hs.toFinset
  let R := p.roots.toFinset
  let z0 : Ico (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let zH : Ico (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  have hp : p ≠ 0 := putnam_2000_b3_sinPoly_ne_zero N hN a (2 * m) haN
  have hSmem : ∀ t : Ico (0 : ℝ) 1, t ∈ S ↔ u t ≠ 0 := by
    intro t
    simp [S, u, Set.Finite.mem_toFinset, Function.mem_support]
  have htsum :
      (∑' t : Ico (0 : ℝ) 1, u t) = ∑ t ∈ S, u t := by
    simpa [u, S, hs] using
      putnam_2000_b3_tsum_eq_sum_of_support_finite u (by simpa [u] using hs)
  have hz0 :
      u z0 = 2 * p.rootMultiplicity 1 + 1 := by
    simpa [u, p, z0] using
      putnam_2000_b3_mult_even_zero_eq_two_rootMultiplicity_sinPoly_add_one
        N hN a f mult haN hf hmult m
  have hzH :
      u zH = 2 * p.rootMultiplicity (-1) + 1 := by
    simpa [u, p, zH] using
      putnam_2000_b3_mult_even_half_eq_two_rootMultiplicity_sinPoly_add_one
        N hN a f mult haN hf hmult m
  let Send : Finset (Ico (0 : ℝ) 1) :=
    S.filter fun t : Ico (0 : ℝ) 1 =>
      Real.sin (2 * Real.pi * (t : ℝ)) = 0
  let Sint : Finset (Ico (0 : ℝ) 1) :=
    S.filter fun t : Ico (0 : ℝ) 1 =>
      ¬ Real.sin (2 * Real.pi * (t : ℝ)) = 0
  have hsplit :
      ∑ t ∈ S, u t = Send.sum u + Sint.sum u := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := S)
      (p := fun t : Ico (0 : ℝ) 1 => Real.sin (2 * Real.pi * (t : ℝ)) = 0)
      (f := u)]
  have hend_le :
      Send.sum u ≤ (2 * p.rootMultiplicity 1 + 1) +
        (2 * p.rootMultiplicity (-1) + 1) := by
    have hsubset : Send ⊆ ({z0, zH} : Finset (Ico (0 : ℝ) 1)) := by
      intro t ht
      have hsin : Real.sin (2 * Real.pi * (t : ℝ)) = 0 :=
        (Finset.mem_filter.mp ht).2
      rcases putnam_2000_b3_sin_two_pi_eq_zero_of_Ico hsin with ht0 | htH
      · apply Finset.mem_insert.mpr
        left
        exact Subtype.ext ht0
      · apply Finset.mem_insert.mpr
        right
        exact Finset.mem_singleton.mpr (Subtype.ext htH)
    have hsum_le : Send.sum u ≤ ({z0, zH} : Finset (Ico (0 : ℝ) 1)).sum u :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro t _ _
        exact Nat.zero_le _)
    calc
      Send.sum u ≤ ({z0, zH} : Finset (Ico (0 : ℝ) 1)).sum u := hsum_le
      _ ≤ u z0 + u zH := by
        have hzh : z0 ≠ zH := by
          intro h
          have hval : (0 : ℝ) = 1 / 2 := by
            simpa [z0, zH] using congrArg (fun t : Ico (0 : ℝ) 1 => (t : ℝ)) h
          norm_num at hval
        simp [hzh]
      _ = (2 * p.rootMultiplicity 1 + 1) +
          (2 * p.rootMultiplicity (-1) + 1) := by
        rw [hz0, hzH]
  have hinter_le :
      Sint.sum u ≤
        2 * (R.filter fun x : ℝ => x ≠ 1 ∧ x ≠ -1).sum
          (fun x => p.rootMultiplicity x) := by
    by_cases hR : R.Nonempty
    · rcases hR with ⟨r0, hr0⟩
      have hroot_of_mem :
          ∀ t : Ico (0 : ℝ) 1, t ∈ Sint →
            p.IsRoot (Real.cos (2 * Real.pi * (t : ℝ))) := by
        intro t ht
        have htS : t ∈ S := (Finset.mem_filter.mp ht).1
        have hsin_ne : Real.sin (2 * Real.pi * (t : ℝ)) ≠ 0 :=
          (Finset.mem_filter.mp ht).2
        have htne : u t ≠ 0 := (hSmem t).1 htS
        have htpos : 0 < u t := Nat.pos_of_ne_zero htne
        have hzero : iteratedDeriv (2 * m) f (t : ℝ) = 0 :=
          (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult
            (putnam_2000_b3_exists_nonzero_iteratedDeriv_at
              N hN a f haN hf (2 * m) (t : ℝ))).1 (by simpa [u] using htpos)
        have hform := putnam_2000_b3_iteratedDeriv_even_eq_sinPoly N a f hf m (t : ℝ)
        have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [hform] at hzero
        have hprod : p.eval (Real.cos (2 * Real.pi * (t : ℝ))) *
            Real.sin (2 * Real.pi * (t : ℝ)) = 0 := by
          exact mul_eq_zero.mp hzero |>.resolve_left hscalar
        have hpeval : p.eval (Real.cos (2 * Real.pi * (t : ℝ))) = 0 :=
          (mul_eq_zero.mp hprod).resolve_right hsin_ne
        exact (Polynomial.IsRoot.def).2 hpeval
      let rootOf : Ico (0 : ℝ) 1 → {x : ℝ // x ∈ R} := fun t =>
        if ht : t ∈ Sint then
          ⟨Real.cos (2 * Real.pi * (t : ℝ)),
            by simpa [R] using (Polynomial.mem_roots hp).2 (hroot_of_mem t ht)⟩
        else
          ⟨r0, hr0⟩
      have hrootOf_val :
          ∀ t : Ico (0 : ℝ) 1, t ∈ Sint →
            (rootOf t : ℝ) = Real.cos (2 * Real.pi * (t : ℝ)) := by
        intro t ht
        simp [rootOf, ht]
      have hfiber_bound :
          ∀ x : {x : ℝ // x ∈ R},
            (∑ t ∈ Sint.filter (fun t : Ico (0 : ℝ) 1 => rootOf t = x), u t) ≤
              (if (x : ℝ) = 1 ∨ (x : ℝ) = -1 then 0
                else 2 * p.rootMultiplicity (x : ℝ)) := by
        intro x
        let F : Finset (Ico (0 : ℝ) 1) :=
          Sint.filter fun t : Ico (0 : ℝ) 1 => rootOf t = x
        have hF_eq :
            (∑ t ∈ Sint.filter (fun t : Ico (0 : ℝ) 1 => rootOf t = x), u t) =
              F.sum u := by rfl
        rw [hF_eq]
        by_cases hxend : (x : ℝ) = 1 ∨ (x : ℝ) = -1
        · have hFzero : F.sum u = 0 := by
            apply Finset.sum_eq_zero
            intro t htF
            have htSint : t ∈ Sint := (Finset.mem_filter.mp htF).1
            have htx : rootOf t = x := (Finset.mem_filter.mp htF).2
            have hsin_ne : Real.sin (2 * Real.pi * (t : ℝ)) ≠ 0 :=
              (Finset.mem_filter.mp htSint).2
            have hcosx : Real.cos (2 * Real.pi * (t : ℝ)) = (x : ℝ) := by
              rw [← hrootOf_val t htSint, htx]
            have hsin_zero : Real.sin (2 * Real.pi * (t : ℝ)) = 0 := by
              rcases hxend with hx1 | hxm1
              · rcases putnam_2000_b3_cos_two_pi_eq_of_Ico
                    (t := z0) (u := t) (by
                      simp [z0]
                      exact hcosx.trans hx1) with ht0 | ht1
                · have ht0' : (t : ℝ) = 0 := by simpa [z0] using ht0
                  rw [ht0']
                  simp
                · have htone : (t : ℝ) = 1 := by simpa [z0] using ht1
                  exact False.elim (not_lt_of_ge (le_of_eq htone.symm) t.property.2)
              · rcases putnam_2000_b3_cos_two_pi_eq_of_Ico
                    (t := zH) (u := t) (by
                      have harg : 2 * Real.pi * (zH : ℝ) = Real.pi := by
                        norm_num [zH]
                        ring
                      rw [harg, Real.cos_pi]
                      exact hcosx.trans hxm1) with htH | htH'
                · have ht : (t : ℝ) = 1 / 2 := by simpa [zH] using htH
                  rw [ht]
                  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
                  rw [harg, Real.sin_pi]
                · have ht : (t : ℝ) = 1 / 2 := by
                    have ht' : (t : ℝ) = 1 - (zH : ℝ) := by linarith
                    norm_num [zH] at ht'
                    exact ht'
                  rw [ht]
                  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
                  rw [harg, Real.sin_pi]
            exact False.elim (hsin_ne hsin_zero)
          simp [hxend, hFzero]
        · have hu_eq :
              ∀ t ∈ F, u t = p.rootMultiplicity (x : ℝ) := by
            intro t htF
            have htSint : t ∈ Sint := (Finset.mem_filter.mp htF).1
            have htx : rootOf t = x := (Finset.mem_filter.mp htF).2
            have hsin_ne : Real.sin (2 * Real.pi * (t : ℝ)) ≠ 0 :=
              (Finset.mem_filter.mp htSint).2
            have hcosx : Real.cos (2 * Real.pi * (t : ℝ)) = (x : ℝ) := by
              rw [← hrootOf_val t htSint, htx]
            calc
              u t =
                  (putnam_2000_b3_sinPoly N a (2 * m)).rootMultiplicity
                    (Real.cos (2 * Real.pi * (t : ℝ))) := by
                simpa [u] using
                  putnam_2000_b3_mult_even_eq_rootMultiplicity_sinPoly_of_sin_ne_zero
                    N hN a f mult haN hf hmult m hsin_ne
              _ = p.rootMultiplicity (x : ℝ) := by
                simp [p, hcosx]
          have hcard : F.card ≤ 2 := by
            have hsubset : F ⊆
                Sint.filter (fun t : Ico (0 : ℝ) 1 =>
                  Real.cos (2 * Real.pi * (t : ℝ)) = (x : ℝ)) := by
              intro t htF
              have htSint : t ∈ Sint := (Finset.mem_filter.mp htF).1
              have htx : rootOf t = x := (Finset.mem_filter.mp htF).2
              have hcosx : Real.cos (2 * Real.pi * (t : ℝ)) = (x : ℝ) := by
                rw [← hrootOf_val t htSint, htx]
              exact Finset.mem_filter.mpr ⟨htSint, hcosx⟩
            exact (Finset.card_mono hsubset).trans
              (putnam_2000_b3_cos_fiber_card_le_two Sint (x : ℝ))
          have hsum_le_card :
              F.sum u ≤ F.card • p.rootMultiplicity (x : ℝ) := by
            exact Finset.sum_le_card_nsmul F u (p.rootMultiplicity (x : ℝ))
              (fun t ht => by rw [hu_eq t ht])
          have hle :
              F.sum u ≤ 2 * p.rootMultiplicity (x : ℝ) := by
            calc
              F.sum u ≤ F.card • p.rootMultiplicity (x : ℝ) := hsum_le_card
              _ ≤ 2 * p.rootMultiplicity (x : ℝ) := by
                simpa [Nat.nsmul_eq_mul] using
                  Nat.mul_le_mul_right (p.rootMultiplicity (x : ℝ)) hcard
          simpa [hxend] using hle
      have hfiber_sum := Finset.sum_fiberwise Sint rootOf u
      calc
        Sint.sum u =
            ∑ x : {x : ℝ // x ∈ R},
              ∑ t ∈ Sint.filter (fun t : Ico (0 : ℝ) 1 => rootOf t = x), u t := by
          exact hfiber_sum.symm
        _ ≤ ∑ x : {x : ℝ // x ∈ R},
              (if (x : ℝ) = 1 ∨ (x : ℝ) = -1 then 0
                else 2 * p.rootMultiplicity (x : ℝ)) := by
          exact Finset.sum_le_sum fun x _ => hfiber_bound x
        _ = ∑ x ∈ R.filter (fun x : ℝ => x ≠ 1 ∧ x ≠ -1),
              2 * p.rootMultiplicity x := by
          calc
            ∑ x : {x : ℝ // x ∈ R},
                (if (x : ℝ) = 1 ∨ (x : ℝ) = -1 then 0
                  else 2 * p.rootMultiplicity (x : ℝ))
                =
                ∑ x ∈ R,
                  (if x = 1 ∨ x = -1 then 0 else 2 * p.rootMultiplicity x) := by
              symm
              exact Finset.sum_subtype R (by intro x; rfl)
                (fun x => if x = 1 ∨ x = -1 then 0 else 2 * p.rootMultiplicity x)
            _ = ∑ x ∈ R.filter (fun x : ℝ => x ≠ 1 ∧ x ≠ -1),
                  2 * p.rootMultiplicity x := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases hx1 : x = 1
              · simp [hx1]
              · by_cases hxm1 : x = -1
                · simp [hxm1]
                · simp [hx1, hxm1]
        _ = 2 * (R.filter fun x : ℝ => x ≠ 1 ∧ x ≠ -1).sum
              (fun x => p.rootMultiplicity x) := by
          rw [Finset.mul_sum]
    · have hsum_zero : Sint.sum u = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        have htS : t ∈ S := (Finset.mem_filter.mp ht).1
        have hsin_ne : Real.sin (2 * Real.pi * (t : ℝ)) ≠ 0 :=
          (Finset.mem_filter.mp ht).2
        have htne : u t ≠ 0 := (hSmem t).1 htS
        have htpos : 0 < u t := Nat.pos_of_ne_zero htne
        have hzero : iteratedDeriv (2 * m) f (t : ℝ) = 0 :=
          (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult
            (putnam_2000_b3_exists_nonzero_iteratedDeriv_at
              N hN a f haN hf (2 * m) (t : ℝ))).1 (by simpa [u] using htpos)
        have hform := putnam_2000_b3_iteratedDeriv_even_eq_sinPoly N a f hf m (t : ℝ)
        have hscalar : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [hform] at hzero
        have hprod : p.eval (Real.cos (2 * Real.pi * (t : ℝ))) *
            Real.sin (2 * Real.pi * (t : ℝ)) = 0 := by
          exact mul_eq_zero.mp hzero |>.resolve_left hscalar
        have hpeval : p.eval (Real.cos (2 * Real.pi * (t : ℝ))) = 0 :=
          (mul_eq_zero.mp hprod).resolve_right hsin_ne
        have hroot : Real.cos (2 * Real.pi * (t : ℝ)) ∈ R :=
          by simpa [R] using (Polynomial.mem_roots hp).2 ((Polynomial.IsRoot.def).2 hpeval)
        exact False.elim (hR ⟨_, hroot⟩)
      rw [hsum_zero]
      exact Nat.zero_le _
  change (∑' t : Ico (0 : ℝ) 1, u t) ≤ 2 * N
  rw [htsum, hsplit]
  have hrootdeg : R.sum (fun x => p.rootMultiplicity x) ≤ p.natDegree := by
    simpa [R] using putnam_2000_b3_sum_rootMultiplicity_roots_le_natDegree p
  have hpart :
      p.rootMultiplicity 1 + p.rootMultiplicity (-1) +
          (R.filter fun x : ℝ => x ≠ 1 ∧ x ≠ -1).sum
            (fun x => p.rootMultiplicity x) =
        R.sum (fun x => p.rootMultiplicity x) := by
    simpa [R] using putnam_2000_b3_rootMultiplicity_endpoint_partition (p := p) hp
  calc
    Send.sum u + Sint.sum u ≤
        ((2 * p.rootMultiplicity 1 + 1) +
          (2 * p.rootMultiplicity (-1) + 1)) +
          2 * (R.filter fun x : ℝ => x ≠ 1 ∧ x ≠ -1).sum
            (fun x => p.rootMultiplicity x) := by
      exact Nat.add_le_add hend_le hinter_le
    _ = 2 * (p.rootMultiplicity 1 + p.rootMultiplicity (-1) +
          (R.filter fun x : ℝ => x ≠ 1 ∧ x ≠ -1).sum
            (fun x => p.rootMultiplicity x)) + 2 := by
      ring
    _ = 2 * R.sum (fun x => p.rootMultiplicity x) + 2 := by
      rw [hpart]
    _ ≤ 2 * p.natDegree + 2 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hrootdeg) 2
    _ ≤ 2 * (N - 1) + 2 := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 (putnam_2000_b3_sinPoly_natDegree_le N a (2 * m))) 2
    _ ≤ 2 * N := by
      omega

private lemma putnam_2000_b3_tsum_iteratedDeriv_le_two_mul_N
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (k : ℕ) :
  (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) (t : ℝ)) ≤ 2 * N := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · exact putnam_2000_b3_tsum_even_le_two_mul_N
      N hN a f mult haN hf hmult m
  · exact putnam_2000_b3_tsum_odd_le_two_mul_N
      N hN a f mult haN hf hmult m

private lemma putnam_2000_b3_cos_grid_left
  (N : ℕ) (hN : 0 < N) (i : Fin (2 * N)) :
  Real.cos (2 * Real.pi * (N : ℝ) *
      (((i : ℕ) : ℝ) / (2 * (N : ℝ)))) =
    (-1 : ℝ) ^ (i : ℕ) := by
  have hden : (2 * (N : ℝ)) ≠ 0 := by positivity
  have harg :
      2 * Real.pi * (N : ℝ) *
          (((i : ℕ) : ℝ) / (2 * (N : ℝ))) =
        ((i : ℕ) : ℝ) * Real.pi := by
    field_simp [hden]
  rw [harg]
  exact Real.cos_nat_mul_pi (i : ℕ)

private lemma putnam_2000_b3_cos_grid_right
  (N : ℕ) (hN : 0 < N) (i : Fin (2 * N)) :
  Real.cos (2 * Real.pi * (N : ℝ) *
      ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ)))) =
    (-1 : ℝ) ^ ((i : ℕ) + 1) := by
  have hden : (2 * (N : ℝ)) ≠ 0 := by positivity
  have harg :
      2 * Real.pi * (N : ℝ) *
          ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) =
        (((i : ℕ) + 1 : ℕ) : ℝ) * Real.pi := by
    field_simp [hden]
  rw [harg]
  exact Real.cos_nat_mul_pi ((i : ℕ) + 1)

private lemma putnam_2000_b3_grid_limit_product_neg
  (N : ℕ) (hN : 0 < N) (A : ℝ) (hA : A ≠ 0) (i : Fin (2 * N)) :
  (A * Real.cos (2 * Real.pi * (N : ℝ) *
      (((i : ℕ) : ℝ) / (2 * (N : ℝ))))) *
    (A * Real.cos (2 * Real.pi * (N : ℝ) *
      ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))))) < 0 := by
  rw [putnam_2000_b3_cos_grid_left N hN i,
    putnam_2000_b3_cos_grid_right N hN i]
  have hsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hpow : (-1 : ℝ) ^ ((i : ℕ) + 1) =
      -((-1 : ℝ) ^ (i : ℕ)) := by
    rw [pow_succ]
    ring
  rw [hpow]
  have hpmul : ((-1 : ℝ) ^ (i : ℕ)) *
      ((-1 : ℝ) ^ (i : ℕ)) = 1 := by
    rw [← pow_add]
    have : ((-1 : ℝ) ^ (2 * (i : ℕ))) = 1 := by simp [pow_mul]
    convert this using 1
    ring
  nlinarith

private lemma putnam_2000_b3_grid_left_nonneg
  (N : ℕ) (i : Fin (2 * N)) :
  0 ≤ (((i : ℕ) : ℝ) / (2 * (N : ℝ))) := by
  positivity

private lemma putnam_2000_b3_grid_left_lt_right
  (N : ℕ) (hN : 0 < N) (i : Fin (2 * N)) :
  (((i : ℕ) : ℝ) / (2 * (N : ℝ))) <
    ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) := by
  have hden : 0 < 2 * (N : ℝ) := by positivity
  have hnum : ((i : ℕ) : ℝ) < (((i : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self (i : ℕ)
  exact div_lt_div_of_pos_right hnum hden

private lemma putnam_2000_b3_grid_right_le_one
  (N : ℕ) (hN : 0 < N) (i : Fin (2 * N)) :
  ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) ≤ 1 := by
  have hden_pos : 0 < 2 * (N : ℝ) := by positivity
  have hle_nat : (i : ℕ) + 1 ≤ 2 * N := Nat.succ_le_of_lt i.isLt
  have hle_real : ((((i : ℕ) + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hle_nat
  have hdiv := div_le_div_of_nonneg_right hle_real (le_of_lt hden_pos)
  have hden_div : (2 * (N : ℝ)) / (2 * (N : ℝ)) = 1 := by
    field_simp [hden_pos.ne']
  linarith

private lemma putnam_2000_b3_grid_right_le_left_of_lt
  (N : ℕ) (hN : 0 < N) {i j : Fin (2 * N)}
  (hij : (i : ℕ) < (j : ℕ)) :
  ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) ≤
    (((j : ℕ) : ℝ) / (2 * (N : ℝ))) := by
  have hden_pos : 0 < 2 * (N : ℝ) := by positivity
  have hle_nat : (i : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_of_lt hij
  have hle_real : ((((i : ℕ) + 1 : ℕ) : ℝ)) ≤ ((j : ℕ) : ℝ) := by
    exact_mod_cast hle_nat
  exact div_le_div_of_nonneg_right hle_real (le_of_lt hden_pos)

private lemma putnam_2000_b3_eventually_grid_product_neg
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (i : Fin (2 * N)) :
  ∀ᶠ n in atTop,
    iteratedDeriv (4 * n + 1) f
        (((i : ℕ) : ℝ) / (2 * (N : ℝ))) *
      iteratedDeriv (4 * n + 1) f
        ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) < 0 := by
  let A := a ⟨N, by simp; omega⟩
  let left : ℝ := ((i : ℕ) : ℝ) / (2 * (N : ℝ))
  let right : ℝ := (((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))
  have hleft := putnam_2000_b3_tendsto_scaled_four_mul_add_one
    N hN a f hf left
  have hright := putnam_2000_b3_tendsto_scaled_four_mul_add_one
    N hN a f hf right
  have hprod := hleft.mul hright
  have hlim_neg :
      (A * Real.cos ((2 * Real.pi * (N : ℕ)) * left)) *
        (A * Real.cos ((2 * Real.pi * (N : ℕ)) * right)) < 0 := by
    simpa [A, left, right, mul_assoc] using
      putnam_2000_b3_grid_limit_product_neg N hN A haN i
  have hnhds : Iio (0 : ℝ) ∈
      𝓝 ((A * Real.cos ((2 * Real.pi * (N : ℕ)) * left)) *
        (A * Real.cos ((2 * Real.pi * (N : ℕ)) * right))) :=
    isOpen_Iio.mem_nhds hlim_neg
  filter_upwards [hprod hnhds] with n hn
  let D : ℝ := (2 * Real.pi * (N : ℝ)) ^ (4 * n + 1)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDne : D ≠ 0 := hDpos.ne'
  have hEq :
      iteratedDeriv (4 * n + 1) f left *
          iteratedDeriv (4 * n + 1) f right =
        ((iteratedDeriv (4 * n + 1) f left / D) *
          (iteratedDeriv (4 * n + 1) f right / D)) * (D * D) := by
    field_simp [hDne]
  rw [hEq]
  exact mul_neg_of_neg_of_pos hn (mul_pos hDpos hDpos)

private lemma putnam_2000_b3_exists_many_zeros_high_deriv
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0)) :
  ∃ K : ℕ,
    2 * N ≤
      ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv K f) (t : ℝ) := by
  classical
  have hall_eventually :
      ∀ᶠ n in atTop, ∀ i : Fin (2 * N),
        iteratedDeriv (4 * n + 1) f
            (((i : ℕ) : ℝ) / (2 * (N : ℝ))) *
          iteratedDeriv (4 * n + 1) f
            ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) < 0 := by
    rw [Filter.eventually_all]
    intro i
    exact putnam_2000_b3_eventually_grid_product_neg N hN a f haN hf i
  rcases Filter.eventually_atTop.1 hall_eventually with ⟨n0, hn0⟩
  let K : ℕ := 4 * n0 + 1
  let g : ℝ → ℝ := iteratedDeriv K f
  have hex :
      ∀ i : Fin (2 * N),
        ∃ z : Ico (0 : ℝ) 1,
          (((i : ℕ) : ℝ) / (2 * (N : ℝ))) < (z : ℝ) ∧
            (z : ℝ) < ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) ∧
            g (z : ℝ) = 0 := by
    intro i
    let l : ℝ := ((i : ℕ) : ℝ) / (2 * (N : ℝ))
    let r : ℝ := (((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))
    have hlr : l < r := putnam_2000_b3_grid_left_lt_right N hN i
    have hprod : g l * g r < 0 := by
      simpa [K, g, l, r] using hn0 n0 le_rfl i
    have hcont : ContinuousOn g (Icc l r) :=
      (putnam_2000_b3_contDiff_iteratedDeriv_f N a f hf K).continuous.continuousOn
    have hsign := mul_neg_iff.mp hprod
    have hzeroIcc : ∃ c ∈ Icc l r, g c = 0 := by
      rcases hsign with hposneg | hnegpos
      · have hmem : (0 : ℝ) ∈ Icc (g r) (g l) :=
          ⟨le_of_lt hposneg.2, le_of_lt hposneg.1⟩
        rcases intermediate_value_Icc' (le_of_lt hlr) hcont hmem with ⟨c, hc, hc0⟩
        exact ⟨c, hc, hc0⟩
      · have hmem : (0 : ℝ) ∈ Icc (g l) (g r) :=
          ⟨le_of_lt hnegpos.1, le_of_lt hnegpos.2⟩
        rcases intermediate_value_Icc (le_of_lt hlr) hcont hmem with ⟨c, hc, hc0⟩
        exact ⟨c, hc, hc0⟩
    rcases hzeroIcc with ⟨c, hc, hczero⟩
    have hgl_ne : g l ≠ 0 := by
      intro hgl
      rw [hgl, zero_mul] at hprod
      exact not_lt_of_ge le_rfl hprod
    have hgr_ne : g r ≠ 0 := by
      intro hgr
      rw [hgr, mul_zero] at hprod
      exact not_lt_of_ge le_rfl hprod
    have hlc : l < c := by
      refine lt_of_le_of_ne hc.1 ?_
      intro hcl
      exact hgl_ne (by simpa [hcl] using hczero)
    have hcr : c < r := by
      refine lt_of_le_of_ne hc.2 ?_
      intro hcr_eq
      exact hgr_ne (by simpa [hcr_eq] using hczero)
    have hcIco : c ∈ Ico (0 : ℝ) 1 := by
      have hl_nonneg : 0 ≤ l := by
        simpa [l] using putnam_2000_b3_grid_left_nonneg N i
      have hr_le_one : r ≤ 1 := by
        simpa [r] using putnam_2000_b3_grid_right_le_one N hN i
      exact ⟨le_trans hl_nonneg (le_of_lt hlc), lt_of_lt_of_le hcr hr_le_one⟩
    exact ⟨⟨c, hcIco⟩, by simpa [l] using hlc, by simpa [r] using hcr,
      by simpa [g] using hczero⟩
  let z : Fin (2 * N) → Ico (0 : ℝ) 1 := fun i => Classical.choose (hex i)
  have hz_left :
      ∀ i : Fin (2 * N),
        (((i : ℕ) : ℝ) / (2 * (N : ℝ))) < (z i : ℝ) := by
    intro i
    exact (Classical.choose_spec (hex i)).1
  have hz_right :
      ∀ i : Fin (2 * N),
        (z i : ℝ) < ((((i : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ))) := by
    intro i
    exact (Classical.choose_spec (hex i)).2.1
  have hz_zero : ∀ i : Fin (2 * N), g (z i : ℝ) = 0 := by
    intro i
    exact (Classical.choose_spec (hex i)).2.2
  have hinj : Function.Injective z := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have hij_ne : (i : ℕ) ≠ (j : ℕ) := by
      intro h
      exact hne h
    rcases lt_or_gt_of_ne hij_ne with hijlt | hjilt
    · have hle := putnam_2000_b3_grid_right_le_left_of_lt N hN hijlt
      have hlt_left := hz_left j
      have hlt_right := hz_right i
      have hz_eq : (z i : ℝ) = (z j : ℝ) := congrArg (fun t : Ico (0 : ℝ) 1 => (t : ℝ)) hij
      linarith
    · have hle := putnam_2000_b3_grid_right_le_left_of_lt N hN hjilt
      have hlt_left := hz_left i
      have hlt_right := hz_right j
      have hz_eq : (z j : ℝ) = (z i : ℝ) := congrArg (fun t : Ico (0 : ℝ) 1 => (t : ℝ)) hij.symm
      linarith
  have hnotflat :
      ∀ i : Fin (2 * N), ∃ c : ℕ, iteratedDeriv c g (z i : ℝ) ≠ 0 := by
    intro i
    simpa [g, K] using
      putnam_2000_b3_exists_nonzero_iteratedDeriv_at
        N hN a f haN hf K (z i : ℝ)
  have hsK := putnam_2000_b3_mult_support_finite_iteratedDeriv
    N hN a f mult haN hf hmult K
  refine ⟨K, ?_⟩
  simpa [g] using
    putnam_2000_b3_card_le_tsum_mult_of_injective_zeros
      mult hmult z hz_zero hnotflat hinj hsK

private lemma putnam_2000_b3_tsum_iteratedDeriv_le_succ
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (k : ℕ) :
  (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) (t : ℝ)) ≤
    ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv (k + 1) f) (t : ℝ) := by
  classical
  let u : Ico (0 : ℝ) 1 → ℕ := fun t => mult (iteratedDeriv k f) (t : ℝ)
  let v : Ico (0 : ℝ) 1 → ℕ := fun t => mult (iteratedDeriv (k + 1) f) (t : ℝ)
  let hs0 := putnam_2000_b3_mult_support_finite_iteratedDeriv
    N hN a f mult haN hf hmult k
  let ht0 := putnam_2000_b3_mult_support_finite_iteratedDeriv
    N hN a f mult haN hf hmult (k + 1)
  let S := hs0.toFinset
  let T := ht0.toFinset
  have hSmem : ∀ t : Ico (0 : ℝ) 1, t ∈ S ↔ u t ≠ 0 := by
    intro t
    simp [S, u, Set.Finite.mem_toFinset, Function.mem_support]
  have hTmem : ∀ t : Ico (0 : ℝ) 1, t ∈ T ↔ v t ≠ 0 := by
    intro t
    simp [T, v, Set.Finite.mem_toFinset, Function.mem_support]
  have hzero_of_mem :
      ∀ t : Ico (0 : ℝ) 1, t ∈ S → iteratedDeriv k f (t : ℝ) = 0 := by
    intro t ht
    have htne : u t ≠ 0 := (hSmem t).1 ht
    have htpos : 0 < u t := Nat.pos_of_ne_zero htne
    exact (putnam_2000_b3_mult_pos_iff_eq_zero mult hmult
      (putnam_2000_b3_exists_nonzero_iteratedDeriv_at
        N hN a f haN hf k (t : ℝ))).1 (by simpa [u] using htpos)
  have huv : ∀ t : Ico (0 : ℝ) 1, t ∈ S → u t = v t + 1 := by
    intro t ht
    have hzero := hzero_of_mem t ht
    exact (putnam_2000_b3_mult_iteratedDeriv_succ_add_one
      N hN a f mult haN hf hmult (k := k) (t := (t : ℝ)) hzero).symm
  have hcard : S.card ≤ (T \ S).card := by
    simpa [S, T, hs0, ht0] using
      putnam_2000_b3_card_support_le_deriv_new_support
        N hN a f mult haN hf hmult k
  have hcard_sum : (T \ S).card ≤ ∑ t ∈ T \ S, v t := by
    have h := Finset.card_nsmul_le_sum (T \ S) v 1 (fun t ht => by
      have htT : t ∈ T := (Finset.mem_sdiff.mp ht).1
      have htne : v t ≠ 0 := (hTmem t).1 htT
      exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero htne))
    simpa using h
  have hnew : S.card ≤ ∑ t ∈ T \ S, v t := hcard.trans hcard_sum
  have hS_eq_inter : (∑ t ∈ S, v t) = ∑ t ∈ T ∩ S, v t := by
    exact (Finset.sum_subset (s₁ := T ∩ S) (s₂ := S) Finset.inter_subset_right
      (fun t htS htNot => by
        have htNotT : t ∉ T := by
          intro htT
          exact htNot (by exact Finset.mem_inter.mpr ⟨htT, htS⟩)
        by_contra htv
        exact htNotT ((hTmem t).2 htv))).symm
  have hdiff : T \ (T ∩ S) = T \ S := by
    ext t
    constructor
    · intro ht
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp ht).1, fun htS =>
          (Finset.mem_sdiff.mp ht).2 (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp ht).1, htS⟩)⟩
    · intro ht
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp ht).1, fun htTS =>
          (Finset.mem_sdiff.mp ht).2 (Finset.mem_inter.mp htTS).2⟩
  have hsplit : (∑ t ∈ T \ S, v t) + (∑ t ∈ T ∩ S, v t) = ∑ t ∈ T, v t := by
    simpa [hdiff] using
      (Finset.sum_sdiff (s₁ := T ∩ S) (s₂ := T) Finset.inter_subset_left
        (f := v))
  have htsum_u :
      (∑' t : Ico (0 : ℝ) 1, u t) = ∑ t ∈ S, u t := by
    simpa [u, S, hs0] using
      putnam_2000_b3_tsum_eq_sum_of_support_finite u (by simpa [u] using hs0)
  have htsum_v :
      (∑' t : Ico (0 : ℝ) 1, v t) = ∑ t ∈ T, v t := by
    simpa [v, T, ht0] using
      putnam_2000_b3_tsum_eq_sum_of_support_finite v (by simpa [v] using ht0)
  change (∑' t : Ico (0 : ℝ) 1, u t) ≤ ∑' t : Ico (0 : ℝ) 1, v t
  rw [htsum_u, htsum_v]
  calc
    (∑ t ∈ S, u t) = ∑ t ∈ S, (v t + 1) := by
      exact Finset.sum_congr rfl fun t ht => huv t ht
    _ = (∑ t ∈ S, v t) + S.card := by
      rw [Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    _ = (∑ t ∈ T ∩ S, v t) + S.card := by
      rw [hS_eq_inter]
    _ ≤ (∑ t ∈ T ∩ S, v t) + (∑ t ∈ T \ S, v t) := by
      exact Nat.add_le_add le_rfl hnew
    _ = ∑ t ∈ T, v t := by
      rw [add_comm, hsplit]

private lemma putnam_2000_b3_tsum_iteratedDeriv_monotone
  (N : ℕ) (hN : 0 < N) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
    (iteratedDeriv (mult g t) g t ≠ 0 ∧
      ∀ k < (mult g t), iteratedDeriv k g t = 0)) :
  ∀ i j : ℕ, i ≤ j →
    (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv i f) (t : ℝ)) ≤
      ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv j f) (t : ℝ) := by
  intro i j hij
  induction hij with
  | refl => exact le_rfl
  | step hij ih =>
      exact ih.trans
        (putnam_2000_b3_tsum_iteratedDeriv_le_succ
          N hN a f mult haN hf hmult _)

private lemma putnam_2000_b3_of_tsum_monotone_eventually
  (N : ℕ) (f : ℝ → ℝ) (mult : (ℝ → ℝ) → ℝ → ℕ) (M : ℕ → ℕ)
  (hM : ∀ k, M k = ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) t)
  (hmono : ∀ i j : ℕ, i ≤ j →
    (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv i f) t) ≤
      ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv j f) t)
  (heventual : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) t) = 2 * N) :
  ((∀ i j : ℕ, i ≤ j → M i ≤ M j) ∧ Tendsto M atTop (𝓝 (2 * N))) := by
  constructor
  · intro i j hij
    rw [hM i, hM j]
    exact hmono i j hij
  · rw [putnam_2000_b3_tendsto_nat_nhds_iff_eventually_eq]
    rcases heventual with ⟨K, hK⟩
    filter_upwards [eventually_ge_atTop K] with k hk
    rw [hM k, hK k hk]

/--
Let $f(t)=\sum_{j=1}^N a_j \sin(2\pi jt)$, where each $a_j$ is real and $a_N$ is not equal to $0$. Let $N_k$ denote the number of zeroes (including multiplicities) of $\frac{d^k f}{dt^k}$. Prove that
\[
N_0\leq N_1\leq N_2\leq \cdots \mbox{ and } \lim_{k\to\infty} N_k = 2N.
\]
-/
theorem putnam_2000_b3
  (N : ℕ) (hN : N > 0)
  (a : Icc 1 N → ℝ)
  (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (M : ℕ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) → (iteratedDeriv (mult g t) g t ≠ 0 ∧ ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (hM : ∀ k, M k = ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) t) :
  ((∀ i j : ℕ, i ≤ j → M i ≤ M j) ∧ Tendsto M atTop (𝓝 (2 * N))) :=
by
  classical
  refine putnam_2000_b3_of_tsum_monotone_eventually N f mult M hM ?_ ?_
  · exact putnam_2000_b3_tsum_iteratedDeriv_monotone
      N hN a f mult haN hf hmult
  · rcases putnam_2000_b3_exists_many_zeros_high_deriv
      N hN a f mult haN hf hmult with ⟨K, hKlower⟩
    refine ⟨K, ?_⟩
    intro k hk
    have hupper :
        (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) t) ≤ 2 * N := by
      simpa using
        putnam_2000_b3_tsum_iteratedDeriv_le_two_mul_N
          N hN a f mult haN hf hmult k
    have hlower :
        2 * N ≤
          ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) t := by
      have hmonoK :
          (∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv K f) t) ≤
            ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) t := by
        simpa using
          putnam_2000_b3_tsum_iteratedDeriv_monotone
            N hN a f mult haN hf hmult K k hk
      exact hKlower.trans hmonoK
    exact le_antisymm hupper hlower
