import Mathlib

open Topology Filter Set Polynomial Function

private def putnam_1981_a1_F (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, m * (m.factorization 5)

private def putnam_1981_a1_T (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 n, r

private lemma putnam_1981_a1_pow_factorization (m : ℕ) :
    (m ^ m).factorization 5 = m * (m.factorization 5) := by
  simp [Nat.factorization_pow, Finsupp.smul_apply]

private lemma putnam_1981_a1_prod_factorization (n : ℕ) :
    (∏ m ∈ Finset.Icc 1 n, m ^ m).factorization 5 = putnam_1981_a1_F n := by
  rw [putnam_1981_a1_F, Nat.factorization_prod_apply]
  · refine Finset.sum_congr rfl ?_
    intro m hm
    exact putnam_1981_a1_pow_factorization m
  · intro m hm
    exact pow_ne_zero m (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)

private lemma putnam_1981_a1_sum_multiples (n : ℕ) (f : ℕ → ℕ) :
    (∑ m ∈ (Finset.Icc 1 n).filter (fun m => 5 ∣ m), f m) =
      ∑ r ∈ Finset.Icc 1 (n / 5), f (5 * r) := by
  refine Finset.sum_bij
    (s := (Finset.Icc 1 n).filter (fun m => 5 ∣ m))
    (t := Finset.Icc 1 (n / 5))
    (f := f) (g := fun r => f (5 * r))
    (fun m _ => m / 5) ?_ ?_ ?_ ?_
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmIcc, hdvd⟩
    have hmIcc' := Finset.mem_Icc.mp hmIcc
    rw [Finset.mem_Icc]
    constructor
    · have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hmIcc'.1
      have h5le : 5 ≤ m := Nat.le_of_dvd hmpos hdvd
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).2 (by simpa using h5le)
    · exact Nat.div_le_div_right hmIcc'.2
  · intro a ha b hb hab
    rcases Finset.mem_filter.mp ha with ⟨_, hadvd⟩
    rcases Finset.mem_filter.mp hb with ⟨_, hbdvd⟩
    have haeq : a = 5 * (a / 5) := by
      calc
        a = a / 5 * 5 := (Nat.div_mul_cancel hadvd).symm
        _ = 5 * (a / 5) := Nat.mul_comm _ _
    have hbeq : b = 5 * (b / 5) := by
      calc
        b = b / 5 * 5 := (Nat.div_mul_cancel hbdvd).symm
        _ = 5 * (b / 5) := Nat.mul_comm _ _
    have hab' : a / 5 = b / 5 := by simpa using hab
    rw [haeq, hbeq, hab']
  · intro r hr
    refine ⟨5 * r, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc] at ⊢
      rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
      constructor
      · constructor
        · nlinarith
        · exact by
            have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).1 hr2
            nlinarith
      · exact dvd_mul_right 5 r
    · change (5 * r) / 5 = r
      rw [Nat.mul_comm]
      exact Nat.mul_div_left r (by norm_num : 0 < 5)
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨_, hdvd⟩
    have hm_eq : m = 5 * (m / 5) := by
      calc
        m = m / 5 * 5 := (Nat.div_mul_cancel hdvd).symm
        _ = 5 * (m / 5) := Nat.mul_comm _ _
    change f m = f (5 * (m / 5))
    exact congrArg f hm_eq

private lemma putnam_1981_a1_factorization_five_mul {r : ℕ} (hr : r ≠ 0) :
    (5 * r).factorization 5 = 1 + r.factorization 5 := by
  have h5 : (5 : ℕ).Prime := by norm_num
  rw [Nat.factorization_mul (by norm_num) hr]
  simp [h5.factorization_self]

private lemma putnam_1981_a1_F_rec (n : ℕ) :
    putnam_1981_a1_F n =
      5 * putnam_1981_a1_F (n / 5) + 5 * putnam_1981_a1_T (n / 5) := by
  rw [putnam_1981_a1_F]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 n) (p := fun m => 5 ∣ m)
    (f := fun m => m * m.factorization 5)]
  have hnot :
      (∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬5 ∣ m), m * m.factorization 5) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨_, hmdvd⟩
    simp [Nat.factorization_eq_zero_of_not_dvd hmdvd]
  rw [hnot, add_zero]
  rw [putnam_1981_a1_sum_multiples]
  calc
    (∑ r ∈ Finset.Icc 1 (n / 5), (5 * r) * (5 * r).factorization 5)
        = ∑ r ∈ Finset.Icc 1 (n / 5), (5 * (r * r.factorization 5) + 5 * r) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hrne : r ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hr).1)
          rw [putnam_1981_a1_factorization_five_mul hrne]
          ring
    _ = 5 * putnam_1981_a1_F (n / 5) + 5 * putnam_1981_a1_T (n / 5) := by
          rw [Finset.sum_add_distrib, putnam_1981_a1_F, putnam_1981_a1_T,
            ← Finset.mul_sum, ← Finset.mul_sum]

private lemma putnam_1981_a1_T_le_sq (n : ℕ) : putnam_1981_a1_T n ≤ n ^ 2 := by
  rw [putnam_1981_a1_T]
  calc
    (∑ r ∈ Finset.Icc 1 n, r) ≤ ∑ _r ∈ Finset.Icc 1 n, n := by
      refine Finset.sum_le_sum ?_
      intro r hr
      exact (Finset.mem_Icc.mp hr).2
    _ = (Finset.Icc 1 n).card * n := by simp
    _ ≤ n * n := by
      exact Nat.mul_le_mul_right n (by simp)
    _ = n ^ 2 := by ring

private lemma putnam_1981_a1_F_le_sq (n : ℕ) : putnam_1981_a1_F n ≤ n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [putnam_1981_a1_F]
      | succ n =>
          set N := n + 1
          set q := N / 5
          have hq_lt : q < N := by
            exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num : 1 < 5)
          have hqF : putnam_1981_a1_F q ≤ q ^ 2 := ih q hq_lt
          have hqT : putnam_1981_a1_T q ≤ q ^ 2 := putnam_1981_a1_T_le_sq q
          have hqmul : q * 5 ≤ N := by
            simpa [q, Nat.mul_comm] using Nat.div_mul_le_self N 5
          rw [putnam_1981_a1_F_rec, show (n + 1) / 5 = q by rfl]
          calc
            5 * putnam_1981_a1_F q + 5 * putnam_1981_a1_T q
                ≤ 5 * q ^ 2 + 5 * q ^ 2 := by gcongr
            _ ≤ N ^ 2 := by nlinarith

private def putnam_1981_a1_partial (M n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 M, 5 ^ i * putnam_1981_a1_T (n / 5 ^ i)

private lemma putnam_1981_a1_partial_succ (M n : ℕ) :
    putnam_1981_a1_partial (M + 1) n =
      putnam_1981_a1_partial M n + 5 ^ (M + 1) * putnam_1981_a1_T (n / 5 ^ (M + 1)) := by
  rw [putnam_1981_a1_partial, putnam_1981_a1_partial]
  rw [Finset.sum_Icc_succ_top (by exact Nat.succ_pos M)]

private lemma putnam_1981_a1_div_pow_succ (n M : ℕ) :
    n / 5 ^ M / 5 = n / 5 ^ (M + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

private lemma putnam_1981_a1_F_iter (M n : ℕ) :
    putnam_1981_a1_F n =
      putnam_1981_a1_partial M n + 5 ^ M * putnam_1981_a1_F (n / 5 ^ M) := by
  induction M with
  | zero =>
      simp [putnam_1981_a1_partial]
  | succ M ih =>
      calc
        putnam_1981_a1_F n =
            putnam_1981_a1_partial M n + 5 ^ M * putnam_1981_a1_F (n / 5 ^ M) := ih
        _ = putnam_1981_a1_partial M n +
            5 ^ M * (5 * putnam_1981_a1_F (n / 5 ^ (M + 1)) +
              5 * putnam_1981_a1_T (n / 5 ^ (M + 1))) := by
              rw [putnam_1981_a1_F_rec, putnam_1981_a1_div_pow_succ]
        _ = putnam_1981_a1_partial (M + 1) n +
            5 ^ (M + 1) * putnam_1981_a1_F (n / 5 ^ (M + 1)) := by
              rw [putnam_1981_a1_partial_succ, pow_succ]
              ring

private lemma putnam_1981_a1_T_cast_real (n : ℕ) :
    (putnam_1981_a1_T n : ℝ) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero =>
      simp [putnam_1981_a1_T]
  | succ n ih =>
      have hsucc : putnam_1981_a1_T (n + 1) = putnam_1981_a1_T n + (n + 1) := by
        rw [putnam_1981_a1_T, putnam_1981_a1_T]
        rw [Finset.sum_Icc_succ_top (by exact Nat.succ_pos n)]
      rw [hsucc, Nat.cast_add, ih]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private lemma putnam_1981_a1_tendsto_div_const (c : ℕ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((n / c : ℕ) : ℝ) / n) atTop (𝓝 ((1 : ℝ) / c)) := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have h :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (1 : ℝ) / c) (by positivity)).comp
      tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  refine Eventually.of_forall ?_
  intro n
  have hfloor : ⌊((1 : ℝ) / c) * n⌋₊ = n / c := by
    rw [← Nat.floor_div_eq_div (K := ℝ) n c]
    congr 1
    field_simp [hcR]
  by_cases hn : n = 0
  · simp [hn]
  · have hfloor' : ⌊(↑c : ℝ)⁻¹ * ↑n⌋₊ = n / c := by
      simpa [div_eq_mul_inv, mul_comm] using hfloor
    simp [hfloor']

private lemma putnam_1981_a1_term_tendsto (i : ℕ) :
    Tendsto
      (fun n : ℕ => ((5 ^ i * putnam_1981_a1_T (n / 5 ^ i) : ℕ) : ℝ) / n ^ 2)
      atTop (𝓝 ((1 : ℝ) / (2 * (5 ^ i : ℝ)))) := by
  have hpow_pos : 0 < 5 ^ i := pow_pos (by norm_num : 0 < 5) i
  have hpow_ne : (5 ^ i : ℝ) ≠ 0 := by exact_mod_cast hpow_pos.ne'
  have hq :
      Tendsto (fun n : ℕ => ((n / 5 ^ i : ℕ) : ℝ) / n)
        atTop (𝓝 ((1 : ℝ) / (5 ^ i : ℝ))) := by
    simpa [Nat.cast_pow] using putnam_1981_a1_tendsto_div_const (5 ^ i) hpow_pos
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hqsucc :
      Tendsto (fun n : ℕ => (((n / 5 ^ i : ℕ) : ℝ) + 1) / n)
        atTop (𝓝 ((1 : ℝ) / (5 ^ i : ℝ))) := by
    simpa [add_div, zero_add] using hq.add hinv
  have hmain :
      Tendsto
        (fun n : ℕ =>
          ((5 ^ i : ℝ) / 2) *
            (((n / 5 ^ i : ℕ) : ℝ) / n) *
            ((((n / 5 ^ i : ℕ) : ℝ) + 1) / n))
        atTop
        (𝓝 (((5 ^ i : ℝ) / 2) * ((1 : ℝ) / (5 ^ i : ℝ)) *
          ((1 : ℝ) / (5 ^ i : ℝ)))) :=
    (tendsto_const_nhds.mul hq).mul hqsucc
  convert hmain using 1
  · ext n
    rw [Nat.cast_mul, putnam_1981_a1_T_cast_real]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    ring_nf
  · field_simp [hpow_ne]

private lemma putnam_1981_a1_partial_tendsto (M : ℕ) :
    Tendsto (fun n : ℕ => (putnam_1981_a1_partial M n : ℝ) / n ^ 2) atTop
      (𝓝 (∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (2 * (5 ^ i : ℝ)))) := by
  have h :=
    tendsto_finset_sum (Finset.Icc 1 M) fun i _ => putnam_1981_a1_term_tendsto i
  simpa [putnam_1981_a1_partial, Finset.sum_div] using h

private lemma putnam_1981_a1_coeff_sum (M : ℕ) :
    (∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (2 * (5 ^ i : ℝ))) =
      (1 / 8 : ℝ) * (1 - (1 / 5 : ℝ) ^ M) := by
  induction M with
  | zero =>
      norm_num
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by exact Nat.succ_pos M), ih]
      have hpow : (1 / 5 : ℝ) ^ M * 5 ^ M = 1 := by
        rw [← mul_pow]
        norm_num
      field_simp
      ring_nf
      rw [hpow]
      ring

private lemma putnam_1981_a1_coeff_tendsto :
    Tendsto (fun M : ℕ => ∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (2 * (5 ^ i : ℝ)))
      atTop (𝓝 (1 / 8 : ℝ)) := by
  have hp : Tendsto (fun M : ℕ => (1 / 5 : ℝ) ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)) using 1
  · ext M
    rw [putnam_1981_a1_coeff_sum]
  · ring_nf

private lemma putnam_1981_a1_upper_coeff_tendsto :
    Tendsto
      (fun M : ℕ => (∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (2 * (5 ^ i : ℝ))) +
        (1 / 5 : ℝ) ^ M)
      atTop (𝓝 (1 / 8 : ℝ)) := by
  have hp : Tendsto (fun M : ℕ => (1 / 5 : ℝ) ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using putnam_1981_a1_coeff_tendsto.add hp

private lemma putnam_1981_a1_partial_le_F (M n : ℕ) :
    (putnam_1981_a1_partial M n : ℝ) / n ^ 2 ≤ (putnam_1981_a1_F n : ℝ) / n ^ 2 := by
  have hnat : putnam_1981_a1_partial M n ≤ putnam_1981_a1_F n := by
    rw [putnam_1981_a1_F_iter M n]
    exact Nat.le_add_right _ _
  exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (sq_nonneg _)

private lemma putnam_1981_a1_tail_bound (M n : ℕ) :
    ((5 ^ M * putnam_1981_a1_F (n / 5 ^ M) : ℕ) : ℝ) / n ^ 2 ≤ (1 / 5 : ℝ) ^ M := by
  by_cases hn : n = 0
  · simp [hn]
  · set c : ℕ := 5 ^ M
    set q : ℕ := n / c
    have hcpos : 0 < c := by
      dsimp [c]
      exact pow_pos (by norm_num : 0 < 5) M
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hFq : putnam_1981_a1_F q ≤ q ^ 2 := putnam_1981_a1_F_le_sq q
    have hqle : (q : ℝ) ≤ (n : ℝ) / c := by
      dsimp [q, c]
      exact Nat.cast_div_le
    have hmul : c * putnam_1981_a1_F q ≤ c * q ^ 2 := Nat.mul_le_mul_left c hFq
    calc
      ((5 ^ M * putnam_1981_a1_F (n / 5 ^ M) : ℕ) : ℝ) / n ^ 2
          = ((c * putnam_1981_a1_F q : ℕ) : ℝ) / n ^ 2 := by rfl
      _ ≤ ((c * q ^ 2 : ℕ) : ℝ) / n ^ 2 := by
          gcongr
      _ = ((c : ℝ) * (q : ℝ) ^ 2) / n ^ 2 := by
          norm_num [pow_two]
      _ ≤ ((c : ℝ) * ((n : ℝ) / c) ^ 2) / n ^ 2 := by
          gcongr
      _ = (1 / 5 : ℝ) ^ M := by
          subst c
          field_simp [hnR]
          rw [Nat.cast_pow, ← mul_pow]
          norm_num

private lemma putnam_1981_a1_F_le_partial_add_tail (M n : ℕ) :
    (putnam_1981_a1_F n : ℝ) / n ^ 2 ≤
      (putnam_1981_a1_partial M n : ℝ) / n ^ 2 + (1 / 5 : ℝ) ^ M := by
  rw [putnam_1981_a1_F_iter M n]
  have ht := putnam_1981_a1_tail_bound M n
  calc
    ((putnam_1981_a1_partial M n + 5 ^ M * putnam_1981_a1_F (n / 5 ^ M) : ℕ) : ℝ) /
        n ^ 2
        = (putnam_1981_a1_partial M n : ℝ) / n ^ 2 +
          ((5 ^ M * putnam_1981_a1_F (n / 5 ^ M) : ℕ) : ℝ) / n ^ 2 := by
          rw [Nat.cast_add, add_div]
    _ ≤ (putnam_1981_a1_partial M n : ℝ) / n ^ 2 + (1 / 5 : ℝ) ^ M := by
          exact add_le_add le_rfl ht

private lemma putnam_1981_a1_F_tendsto :
    Tendsto (fun n : ℕ => (putnam_1981_a1_F n : ℝ) / n ^ 2) atTop (𝓝 (1 / 8 : ℝ)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    rcases ((tendsto_order.1 putnam_1981_a1_coeff_tendsto).1 a ha).exists with ⟨M, hM⟩
    exact (((tendsto_order.1 (putnam_1981_a1_partial_tendsto M)).1 a hM).mono
      fun n hn => lt_of_lt_of_le hn (putnam_1981_a1_partial_le_F M n))
  · intro b hb
    rcases ((tendsto_order.1 putnam_1981_a1_upper_coeff_tendsto).2 b hb).exists with ⟨M, hM⟩
    have hlim :
        Tendsto (fun n : ℕ => (putnam_1981_a1_partial M n : ℝ) / n ^ 2 +
          (1 / 5 : ℝ) ^ M) atTop
          (𝓝 ((∑ i ∈ Finset.Icc 1 M, (1 : ℝ) / (2 * (5 ^ i : ℝ))) +
            (1 / 5 : ℝ) ^ M)) :=
      (putnam_1981_a1_partial_tendsto M).add tendsto_const_nhds
    exact (((tendsto_order.1 hlim).2 b hM).mono
      fun n hn => lt_of_le_of_lt (putnam_1981_a1_F_le_partial_add_tail M n) hn)

private lemma putnam_1981_a1_int_prod_eq (n : ℕ) :
    ((∏ m ∈ Finset.Icc 1 n, m ^ m : ℕ) : ℤ) =
      ∏ m ∈ Finset.Icc 1 n, (m ^ m : ℤ) := by
  norm_cast

private lemma putnam_1981_a1_nat_prod_ne_zero (n : ℕ) :
    (∏ m ∈ Finset.Icc 1 n, m ^ m : ℕ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro m hm
  exact pow_ne_zero m (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)

-- 1/8
/--
Let $E(n)$ be the greatest integer $k$ such that $5^k$ divides $1^1 2^2 3^3 \cdots n^n$. Find $\lim_{n \rightarrow \infty} \frac{E(n)}{n^2}$.
-/
theorem putnam_1981_a1
    (P : ℕ → ℕ → Prop)
    (hP : ∀ n k, P n k ↔ 5^k ∣ ∏ m ∈ Finset.Icc 1 n, (m^m : ℤ))
    (E : ℕ → ℕ)
    (hE : ∀ n ∈ Ici 1, P n (E n) ∧ ∀ k : ℕ, P n k → k ≤ E n) :
    Tendsto (fun n : ℕ => ((E n) : ℝ)/n^2) atTop (𝓝 ((1/8) : ℝ )) := by
  have hp5 : (5 : ℕ).Prime := by norm_num
  have hE_eq_F : ∀ n ∈ Ici 1, E n = putnam_1981_a1_F n := by
    intro n hn
    set A : ℕ := ∏ m ∈ Finset.Icc 1 n, m ^ m
    have hA0 : A ≠ 0 := by
      dsimp [A]
      exact putnam_1981_a1_nat_prod_ne_zero n
    have hAfact : A.factorization 5 = putnam_1981_a1_F n := by
      dsimp [A]
      exact putnam_1981_a1_prod_factorization n
    have hPF : P n (putnam_1981_a1_F n) := by
      rw [hP n (putnam_1981_a1_F n)]
      have hnat :
          5 ^ putnam_1981_a1_F n ∣ A := by
        rw [hp5.pow_dvd_iff_le_factorization hA0, hAfact]
      rw [← putnam_1981_a1_int_prod_eq n]
      exact_mod_cast hnat
    have hP_le_F : ∀ k : ℕ, P n k → k ≤ putnam_1981_a1_F n := by
      intro k hk
      have hint : (5 ^ k : ℤ) ∣ (A : ℤ) := by
        have := (hP n k).1 hk
        rwa [← putnam_1981_a1_int_prod_eq n] at this
      have hnat : 5 ^ k ∣ A := by
        exact_mod_cast hint
      have hkfac : k ≤ A.factorization 5 :=
        (hp5.pow_dvd_iff_le_factorization hA0).1 hnat
      rwa [hAfact] at hkfac
    have hEn := hE n hn
    exact le_antisymm (hP_le_F (E n) hEn.1) (hEn.2 (putnam_1981_a1_F n) hPF)
  have heq :
      (fun n : ℕ => ((E n) : ℝ) / n ^ 2) =ᶠ[atTop]
        (fun n : ℕ => ((putnam_1981_a1_F n) : ℝ) / n ^ 2) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [hE_eq_F n (by simpa [Set.mem_Ici] using hn)]
  exact putnam_1981_a1_F_tendsto.congr' heq.symm
