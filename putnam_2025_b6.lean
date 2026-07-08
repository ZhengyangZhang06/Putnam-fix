import Mathlib

open Real

noncomputable abbrev putnam_2025_b6_solution : ℝ := (2 : ℝ) ^ (-2 : ℝ)

private def putnam_2025_b6_polyLower (g : ℕ → ℕ) (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ β ≤ (g n : ℝ)

private lemma putnam_2025_b6_eventually_rpow_le_const_mul_rpow
    {C p q : ℝ} (hC : 0 < C) (hpq : q < p) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ q ≤ C * (n : ℝ) ^ p := by
  have hdiff : 0 < p - q := sub_pos.mpr hpq
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (p - q)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hdiff).comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1, ht.eventually_ge_atTop C⁻¹] with n hn hlarge
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  have hnonneg : 0 ≤ (n : ℝ) ^ q := by positivity
  have hmul : C⁻¹ * (n : ℝ) ^ q ≤ (n : ℝ) ^ (p - q) * (n : ℝ) ^ q := by
    exact mul_le_mul_of_nonneg_right hlarge hnonneg
  have hmulC :
      C * (C⁻¹ * (n : ℝ) ^ q) ≤
        C * ((n : ℝ) ^ (p - q) * (n : ℝ) ^ q) := by
    exact mul_le_mul_of_nonneg_left hmul hC.le
  calc
    (n : ℝ) ^ q = C * (C⁻¹ * (n : ℝ) ^ q) := by
      rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
    _ ≤ C * ((n : ℝ) ^ (p - q) * (n : ℝ) ^ q) := hmulC
    _ = C * (n : ℝ) ^ p := by
      rw [← Real.rpow_add hnpos, sub_add_cancel]

private lemma putnam_2025_b6_sum_Ico_gap (g : ℕ → ℕ) {n m : ℕ} (hnm : n ≤ m) :
    (∑ i ∈ Finset.Ico n m, ((g (i + 1) : ℝ) - (g i : ℝ))) =
      (g m : ℝ) - (g n : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ hnm]
  have hm := Finset.sum_range_sub (fun i => (g i : ℝ)) m
  have hn := Finset.sum_range_sub (fun i => (g i : ℝ)) n
  rw [hm, hn]
  ring

private lemma putnam_2025_b6_div_two_ge_third {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) / 3 ≤ (m / 2 : ℕ) := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have hnat : m ≤ 3 * (m / 2) := by omega
  have hnat' : m ≤ (m / 2) * 3 := by simpa [mul_comm] using hnat
  exact_mod_cast hnat'

private lemma putnam_2025_b6_sub_div_two_ge_third {m : ℕ} (_hm : 2 ≤ m) :
    (m : ℝ) / 3 ≤ (m - m / 2 : ℕ) := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have hnat : m ≤ 3 * (m - m / 2) := by omega
  have hnat' : m ≤ (m - m / 2) * 3 := by simpa [mul_comm] using hnat
  exact_mod_cast hnat'

private lemma putnam_2025_b6_polyLower_of_gap
    {g : ℕ → ℕ} {K p : ℝ} (hK : 0 < K) (hp : 0 ≤ p)
    (hgap : ∀ᶠ n : ℕ in Filter.atTop,
      K * (n : ℝ) ^ p ≤ (g (n + 1) : ℝ) - (g n : ℝ)) :
    putnam_2025_b6_polyLower g (p + 1) := by
  refine ⟨K * ((1 / 3 : ℝ) ^ (p + 1)), ?_, ?_⟩
  · positivity
  · rcases Filter.eventually_atTop.mp hgap with ⟨N, hN⟩
    rw [Filter.eventually_atTop]
    refine ⟨max (2 * N) 2, ?_⟩
    intro m hm
    let n := m / 2
    have hm2 : 2 ≤ m := le_trans (Nat.le_max_right (2 * N) 2) hm
    have hnN : N ≤ n := by
      have h2N : 2 * N ≤ m := le_trans (Nat.le_max_left (2 * N) 2) hm
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by simpa [mul_comm] using h2N)
    have hnm : n ≤ m := Nat.div_le_self m 2
    have hsum_const :
        (∑ i ∈ Finset.Ico n m, K * (n : ℝ) ^ p) =
          (m - n : ℝ) * (K * (n : ℝ) ^ p) := by
      rw [Finset.sum_const, Nat.card_Ico]
      simp [nsmul_eq_mul, Nat.cast_sub hnm]
    have hsum_lower :
        (m - n : ℝ) * (K * (n : ℝ) ^ p) ≤
          (∑ i ∈ Finset.Ico n m, ((g (i + 1) : ℝ) - (g i : ℝ))) := by
      rw [← hsum_const]
      refine Finset.sum_le_sum ?_
      intro i hi
      have hiI := Finset.mem_Ico.mp hi
      have hiN : N ≤ i := le_trans hnN hiI.1
      have hgi := hN i hiN
      have hpow : (n : ℝ) ^ p ≤ (i : ℝ) ^ p := by
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hiI.1) hp
      exact (mul_le_mul_of_nonneg_left hpow hK.le).trans hgi
    have hsum_gap :
        (m - n : ℝ) * (K * (n : ℝ) ^ p) ≤ (g m : ℝ) - (g n : ℝ) := by
      simpa [putnam_2025_b6_sum_Ico_gap g hnm] using hsum_lower
    have hto_gm : (m - n : ℝ) * (K * (n : ℝ) ^ p) ≤ (g m : ℝ) := by
      have hgn : 0 ≤ (g n : ℝ) := by positivity
      nlinarith
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm2)
    have hthird_nonneg : 0 ≤ (m : ℝ) / 3 := by positivity
    have hthird_n : (m : ℝ) / 3 ≤ (n : ℝ) := putnam_2025_b6_div_two_ge_third hm2
    have hthird_len : (m : ℝ) / 3 ≤ (m - n : ℕ) :=
      putnam_2025_b6_sub_div_two_ge_third hm2
    have hpow_third : ((m : ℝ) / 3) ^ p ≤ (n : ℝ) ^ p := by
      exact Real.rpow_le_rpow hthird_nonneg hthird_n hp
    have hcoef :
        K * (((m : ℝ) / 3) ^ p) ≤ K * (n : ℝ) ^ p := by
      exact mul_le_mul_of_nonneg_left hpow_third hK.le
    have hprod :
        ((m : ℝ) / 3) * (K * (((m : ℝ) / 3) ^ p)) ≤
          (m - n : ℝ) * (K * (n : ℝ) ^ p) := by
      have hthird_len' : (m : ℝ) / 3 ≤ (m : ℝ) - (n : ℝ) := by
        simpa [Nat.cast_sub hnm] using hthird_len
      have hleftcoef_nonneg : 0 ≤ K * (((m : ℝ) / 3) ^ p) := by
        exact mul_nonneg hK.le (by positivity)
      have hlen_nonneg : 0 ≤ (m : ℝ) - (n : ℝ) := by
        exact sub_nonneg.mpr (by exact_mod_cast hnm)
      exact mul_le_mul hthird_len' hcoef hleftcoef_nonneg hlen_nonneg
    have hrewrite :
        K * ((1 / 3 : ℝ) ^ (p + 1)) * (m : ℝ) ^ (p + 1) =
          ((m : ℝ) / 3) * (K * (((m : ℝ) / 3) ^ p)) := by
      have hthird : 0 < (m : ℝ) / 3 := by positivity
      have hmul : (m : ℝ) * (1 / 3 : ℝ) = (m : ℝ) / 3 := by ring
      calc
        K * ((1 / 3 : ℝ) ^ (p + 1)) * (m : ℝ) ^ (p + 1)
            = K * (((m : ℝ) * (1 / 3 : ℝ)) ^ (p + 1)) := by
              rw [Real.mul_rpow hmpos.le (by norm_num : (0 : ℝ) ≤ (1 / 3 : ℝ))]
              ring
        _ = K * (((m : ℝ) / 3) ^ (p + 1)) := by rw [hmul]
        _ = K * ((((m : ℝ) / 3) ^ p) * ((m : ℝ) / 3)) := by
              rw [Real.rpow_add hthird p 1, Real.rpow_one]
        _ = ((m : ℝ) / 3) * (K * (((m : ℝ) / 3) ^ p)) := by ring
    exact hrewrite.trans_le (hprod.trans hto_gm)

/--
Let $\mathbb{N} = \{1, 2, 3, \ldots\}$. Find the largest real constant $r$ such that
there exists a function $g: \mathbb{N} \to \mathbb{N}$ such that
$$g(n+1) - g(n) \geq (g(g(n)))^r$$
for all $n \in \mathbb{N}$.
-/
theorem putnam_2025_b6 :
    IsGreatest
      {r : ℝ | ∃ g : ℕ → ℕ, (∀ n : ℕ, 0 < n → 0 < g n) ∧
        ∀ n : ℕ, 0 < n → ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ)}
      putnam_2025_b6_solution := by
  constructor
  · refine ⟨fun n => n ^ 2, ?_, ?_⟩
    · intro n hn
      exact Nat.pow_pos hn
    · intro n hn
      have hroot : (((n ^ 4 : ℕ) : ℝ) ^ putnam_2025_b6_solution) = (n : ℝ) := by
        have hsol : putnam_2025_b6_solution = (1 : ℝ) / 4 := by
          norm_num [putnam_2025_b6_solution]
        have hnnon : 0 ≤ (n : ℝ) := by positivity
        rw [hsol]
        rw [Nat.cast_pow]
        rw [← Real.rpow_natCast (n : ℝ) 4]
        rw [← Real.rpow_mul hnnon]
        norm_num [Real.rpow_one]
      have hsimp : ((fun n : ℕ => n ^ 2) ((fun n : ℕ => n ^ 2) n)) = n ^ 4 := by
        simp [pow_succ, mul_assoc]
      rw [hsimp, hroot]
      norm_num
      have hnnon : 0 ≤ (n : ℝ) := by positivity
      nlinarith
  · intro r hr
    rcases hr with ⟨g, hpos, hineq⟩
    by_contra hnot
    have hsol : putnam_2025_b6_solution = (1 : ℝ) / 4 := by
      norm_num [putnam_2025_b6_solution]
    have hrgt_solution : putnam_2025_b6_solution < r := lt_of_not_ge hnot
    have hrgt : (1 : ℝ) / 4 < r := by
      exact hsol ▸ hrgt_solution
    have hrpos : 0 < r := by nlinarith
    have hstep : ∀ n : ℕ, 0 < n → g n < g (n + 1) := by
      intro n hn
      have hgnpos : 0 < g n := hpos n hn
      have hggnpos : 0 < (g (g n) : ℝ) := by
        exact_mod_cast hpos (g n) hgnpos
      have hlhspos : 0 < ((g (g n) : ℝ) ^ r) := Real.rpow_pos_of_pos hggnpos r
      have hgap_pos : 0 < (g (n + 1) : ℝ) - (g n : ℝ) :=
        lt_of_lt_of_le hlhspos (hineq n hn)
      have hreal : (g n : ℝ) < (g (n + 1) : ℝ) := by linarith
      exact_mod_cast hreal
    have hmono : ∀ {m n : ℕ}, 0 < m → m ≤ n → g m ≤ g n := by
      intro m n hm hmn
      induction hmn with
      | refl => exact le_rfl
      | @step k hmk ih =>
          exact le_trans ih (le_of_lt (hstep k (lt_of_lt_of_le hm hmk)))
    have hge_id : ∀ n : ℕ, 0 < n → n ≤ g n := by
      intro n hn
      induction n with
      | zero => cases hn
      | succ k ih =>
          cases k with
          | zero =>
              simpa using hpos 1 (by norm_num)
          | succ k =>
              have ih' : k + 1 ≤ g (k + 1) := ih (Nat.succ_pos k)
              have hs : g (k + 1) < g (k + 1 + 1) := hstep (k + 1) (Nat.succ_pos k)
              exact Nat.succ_le_of_lt (lt_of_le_of_lt ih' hs)
    have hpoly_one : putnam_2025_b6_polyLower g 1 := by
      refine ⟨1, by norm_num, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hnpos : 0 < n := hn
      have hge := hge_id n hnpos
      have hgeR : (n : ℝ) ≤ (g n : ℝ) := by exact_mod_cast hge
      simpa [Real.rpow_one] using hgeR
    have hpoly_step :
        ∀ {β : ℝ}, 1 ≤ β → putnam_2025_b6_polyLower g β →
          putnam_2025_b6_polyLower g (1 + r * β ^ 2) := by
      intro β hβ hpoly
      rcases hpoly with ⟨C, hC, hCev⟩
      rcases Filter.eventually_atTop.mp hCev with ⟨N, hN⟩
      let D : ℝ := C * C ^ β
      have hDpos : 0 < D := by
        dsimp [D]
        positivity
      have hgap :
          ∀ᶠ n : ℕ in Filter.atTop,
            D ^ r * (n : ℝ) ^ (r * β ^ 2) ≤
              (g (n + 1) : ℝ) - (g n : ℝ) := by
        rw [Filter.eventually_atTop]
        refine ⟨max N 1, ?_⟩
        intro n hn
        have hnN : N ≤ n := le_trans (Nat.le_max_left N 1) hn
        have hn1 : 1 ≤ n := le_trans (Nat.le_max_right N 1) hn
        have hnpos : 0 < n := hn1
        have hgnN : N ≤ g n := le_trans hnN (hge_id n hnpos)
        have hn_lb := hN n hnN
        have hgn_lb := hN (g n) hgnN
        have hβnonneg : 0 ≤ β := le_trans zero_le_one hβ
        have hCn_nonneg : 0 ≤ C * (n : ℝ) ^ β := by positivity
        have hpow_lb : (C * (n : ℝ) ^ β) ^ β ≤ (g n : ℝ) ^ β := by
          exact Real.rpow_le_rpow hCn_nonneg hn_lb hβnonneg
        have hcomp :
            D * (n : ℝ) ^ (β * β) ≤ (g (g n) : ℝ) := by
          have hleft :
              C * (C * (n : ℝ) ^ β) ^ β =
                D * (n : ℝ) ^ (β * β) := by
            dsimp [D]
            rw [Real.mul_rpow hC.le (by positivity : 0 ≤ (n : ℝ) ^ β)]
            rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ))]
            ring
          calc
            D * (n : ℝ) ^ (β * β) = C * (C * (n : ℝ) ^ β) ^ β := hleft.symm
            _ ≤ C * (g n : ℝ) ^ β := mul_le_mul_of_nonneg_left hpow_lb hC.le
            _ ≤ (g (g n) : ℝ) := hgn_lb
        have hcomp_pow :
            (D * (n : ℝ) ^ (β * β)) ^ r ≤ ((g (g n) : ℝ) ^ r) := by
          exact Real.rpow_le_rpow (by positivity) hcomp hrpos.le
        have hrewrite :
            (D * (n : ℝ) ^ (β * β)) ^ r =
              D ^ r * (n : ℝ) ^ (r * β ^ 2) := by
          rw [Real.mul_rpow hDpos.le (by positivity : 0 ≤ (n : ℝ) ^ (β * β))]
          rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ))]
          ring_nf
        exact hrewrite ▸ hcomp_pow.trans (hineq n hnpos)
      have hKpos : 0 < D ^ r := Real.rpow_pos_of_pos hDpos r
      have hpnonneg : 0 ≤ r * β ^ 2 := mul_nonneg hrpos.le (sq_nonneg β)
      simpa [add_comm] using
        putnam_2025_b6_polyLower_of_gap (g := g) hKpos hpnonneg hgap
    let beta : ℕ → ℝ := fun k => Nat.recOn k (1 : ℝ) (fun _ b => 1 + r * b ^ 2)
    have hbeta_zero : beta 0 = 1 := by simp [beta]
    have hbeta_succ : ∀ k : ℕ, beta (k + 1) = 1 + r * (beta k) ^ 2 := by
      intro k
      simp [beta]
    have hbeta_ge1 : ∀ k : ℕ, 1 ≤ beta k := by
      intro k
      induction k with
      | zero =>
          simp [hbeta_zero]
      | succ k ih =>
          rw [hbeta_succ]
          have hnonneg : 0 ≤ r * (beta k) ^ 2 := mul_nonneg hrpos.le (sq_nonneg (beta k))
          nlinarith
    have hpoly_iter : ∀ k : ℕ, putnam_2025_b6_polyLower g (beta k) := by
      intro k
      induction k with
      | zero =>
          simpa [hbeta_zero] using hpoly_one
      | succ k ih =>
          simpa [hbeta_succ] using hpoly_step (hbeta_ge1 k) ih
    let delta : ℝ := r - (1 : ℝ) / 4
    have hdelta_pos : 0 < delta := by
      dsimp [delta]
      nlinarith
    have hy_step : ∀ k : ℕ, r * beta k + delta ≤ r * beta (k + 1) := by
      intro k
      rw [hbeta_succ]
      dsimp [delta]
      have hsquare : 0 ≤ (r * beta k - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
      nlinarith
    have hy_lower : ∀ k : ℕ, r + (k : ℝ) * delta ≤ r * beta k := by
      intro k
      induction k with
      | zero =>
          simp [hbeta_zero]
      | succ k ih =>
          have h1 : r + (k : ℝ) * delta + delta ≤ r * beta k + delta := by
            nlinarith
          have h2 : r * beta k + delta ≤ r * beta (k + 1) := hy_step k
          have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
          rw [hcast]
          nlinarith
    obtain ⟨k, hk_big⟩ : ∃ k : ℕ, 1 < r * beta k := by
      obtain ⟨k, hk⟩ := exists_nat_gt ((1 - r) / delta)
      refine ⟨k, ?_⟩
      have hmul : 1 - r < (k : ℝ) * delta := by
        rw [div_lt_iff₀ hdelta_pos] at hk
        simpa [mul_comm] using hk
      have htarget : 1 < r + (k : ℝ) * delta := by nlinarith
      exact lt_of_lt_of_le htarget (hy_lower k)
    let β : ℝ := beta k
    have hβ_ge1 : 1 ≤ β := hbeta_ge1 k
    have hpolyβ : putnam_2025_b6_polyLower g β := by
      dsimp [β]
      exact hpoly_iter k
    have hrβ_gt_one : 1 < r * β := by
      dsimp [β]
      exact hk_big
    let q : ℝ := (1 + r * β) / 2
    have hq_gt_one : 1 < q := by
      dsimp [q]
      nlinarith
    have hq_pos : 0 < q := lt_trans zero_lt_one hq_gt_one
    have hq_lt_rβ : q < r * β := by
      dsimp [q]
      nlinarith
    rcases hpolyβ with ⟨C, hC, hCev⟩
    have hCrpos : 0 < C ^ r := Real.rpow_pos_of_pos hC r
    rcases Filter.eventually_atTop.mp
        (putnam_2025_b6_eventually_rpow_le_const_mul_rpow hCrpos hq_lt_rβ) with
      ⟨M, hM⟩
    rcases Filter.eventually_atTop.mp hCev with ⟨N, hN⟩
    have hsuper_gap :
        ∀ᶠ n : ℕ in Filter.atTop,
          (g n : ℝ) ^ q ≤ (g (n + 1) : ℝ) - (g n : ℝ) := by
      rw [Filter.eventually_atTop]
      refine ⟨max (max N M) 1, ?_⟩
      intro n hn
      have hnN : N ≤ n := le_trans (Nat.le_max_left N M) (le_trans (Nat.le_max_left (max N M) 1) hn)
      have hnM : M ≤ n := le_trans (Nat.le_max_right N M) (le_trans (Nat.le_max_left (max N M) 1) hn)
      have hn1 : 1 ≤ n := le_trans (Nat.le_max_right (max N M) 1) hn
      have hnpos : 0 < n := hn1
      have hgn_ge_n : n ≤ g n := hge_id n hnpos
      have hgnN : N ≤ g n := le_trans hnN hgn_ge_n
      have hgnM : M ≤ g n := le_trans hnM hgn_ge_n
      have hcomp : C * (g n : ℝ) ^ β ≤ (g (g n) : ℝ) := hN (g n) hgnN
      have habsorb : (g n : ℝ) ^ q ≤ C ^ r * (g n : ℝ) ^ (r * β) := hM (g n) hgnM
      have hpow_comp :
          (C * (g n : ℝ) ^ β) ^ r ≤ ((g (g n) : ℝ) ^ r) := by
        exact Real.rpow_le_rpow (by positivity) hcomp hrpos.le
      have hrewrite :
          (C * (g n : ℝ) ^ β) ^ r = C ^ r * (g n : ℝ) ^ (r * β) := by
        rw [Real.mul_rpow hC.le (by positivity : 0 ≤ (g n : ℝ) ^ β)]
        rw [← Real.rpow_mul (by positivity : 0 ≤ (g n : ℝ))]
        ring_nf
      exact habsorb.trans (hrewrite ▸ hpow_comp.trans (hineq n hnpos))
    rcases Filter.eventually_atTop.mp hsuper_gap with ⟨Ns, hNs⟩
    let N0 : ℕ := max Ns 2
    have hN0_ge_Ns : Ns ≤ N0 := Nat.le_max_left Ns 2
    have hN0_ge_two : 2 ≤ N0 := Nat.le_max_right Ns 2
    have hgap_two : ∀ n : ℕ, N0 ≤ n → g n + 2 ≤ g (n + 1) := by
      intro n hnN0
      have hnNs : Ns ≤ n := le_trans hN0_ge_Ns hnN0
      have hn2 : 2 ≤ n := le_trans hN0_ge_two hnN0
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn2
      have hgn_ge_two : 2 ≤ g n := le_trans hn2 (hge_id n hnpos)
      have hbase_gt_one : (1 : ℝ) < (g n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hgn_ge_two)
      have hone_lt : (1 : ℝ) < (g n : ℝ) ^ q := Real.one_lt_rpow hbase_gt_one hq_pos
      have hgap_real : (g n : ℝ) ^ q ≤ (g (n + 1) : ℝ) - (g n : ℝ) := hNs n hnNs
      have hreal : (g n : ℝ) + 1 < (g (n + 1) : ℝ) := by nlinarith
      have hnatlt : g n + 1 < g (n + 1) := by exact_mod_cast hreal
      exact Nat.succ_le_of_lt hnatlt
    have hdiff_unbounded :
        ∀ B : ℕ, ∃ n : ℕ, N0 ≤ n ∧ B ≤ g n - n := by
      intro B
      induction B with
      | zero =>
          exact ⟨N0, le_rfl, Nat.zero_le _⟩
      | succ B ih =>
          rcases ih with ⟨n, hnN0, hB⟩
          have hn2 : 2 ≤ n := le_trans hN0_ge_two hnN0
          have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn2
          have hgn : n ≤ g n := hge_id n hnpos
          have hgapN := hgap_two n hnN0
          refine ⟨n + 1, le_trans hnN0 (Nat.le_succ n), ?_⟩
          have hdiff_step : g n - n + 1 ≤ g (n + 1) - (n + 1) := by omega
          exact (Nat.succ_le_succ hB).trans hdiff_step
    have htq : Filter.Tendsto (fun B : ℕ => q ^ B) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hq_gt_one
    rcases Filter.tendsto_atTop_atTop.mp htq (1 / r + 1) with ⟨B, hBtail⟩
    have hqB_large : 1 / r < q ^ B := by
      have := hBtail B le_rfl
      nlinarith
    have hrqB_gt_one : 1 < r * q ^ B := by
      have := (div_lt_iff₀ hrpos).mp hqB_large
      nlinarith [this]
    rcases hdiff_unbounded (B + 1) with ⟨n, hnN0, hBdiff⟩
    have hn2 : 2 ≤ n := le_trans hN0_ge_two hnN0
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn2
    have hn_le_gn : n ≤ g n := hge_id n hnpos
    have hn1_le_gn : n + 1 ≤ g n := by omega
    let L : ℕ := g n - (n + 1)
    have hLgeB : B ≤ L := by
      dsimp [L]
      omega
    have hrec : ∀ k : ℕ, N0 ≤ k → (g k : ℝ) ^ q ≤ (g (k + 1) : ℝ) := by
      intro k hkN0
      have hkNs : Ns ≤ k := le_trans hN0_ge_Ns hkN0
      have hgapk := hNs k hkNs
      have hgk_nonneg : 0 ≤ (g k : ℝ) := by positivity
      nlinarith
    have hbase_pos : 0 < (g (n + 1) : ℝ) := by
      exact_mod_cast hpos (n + 1) (Nat.succ_pos n)
    have hiter :
        ∀ t : ℕ, n + 1 + t ≤ g n →
          (g (n + 1) : ℝ) ^ (q ^ t : ℝ) ≤ (g (n + 1 + t) : ℝ) := by
      intro t ht
      induction t with
      | zero =>
          simp
      | succ t ih =>
          have htprev : n + 1 + t ≤ g n := by omega
          have hih := ih htprev
          have hkN0 : N0 ≤ n + 1 + t := by omega
          have hreck := hrec (n + 1 + t) hkN0
          have hpowle :
              ((g (n + 1) : ℝ) ^ (q ^ t : ℝ)) ^ q ≤
                (g (n + 1 + t) : ℝ) ^ q := by
            exact Real.rpow_le_rpow (by positivity) hih hq_pos.le
          have hpowsucc :
              (g (n + 1) : ℝ) ^ (q ^ (t + 1) : ℝ) =
                ((g (n + 1) : ℝ) ^ (q ^ t : ℝ)) ^ q := by
            rw [← Real.rpow_mul hbase_pos.le]
            rw [pow_succ]
          calc
            (g (n + 1) : ℝ) ^ (q ^ (t + 1) : ℝ)
                = ((g (n + 1) : ℝ) ^ (q ^ t : ℝ)) ^ q := hpowsucc
            _ ≤ (g (n + 1 + t) : ℝ) ^ q := hpowle
            _ ≤ (g (n + 1 + (t + 1)) : ℝ) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hreck
    have hL_index : n + 1 + L = g n := by
      dsimp [L]
      omega
    have hiterL : (g (n + 1) : ℝ) ^ (q ^ L : ℝ) ≤ (g (g n) : ℝ) := by
      simpa [hL_index] using hiter L (by omega)
    have hpow_lower :
        (g (n + 1) : ℝ) ^ (r * (q ^ L : ℝ)) ≤ ((g (g n) : ℝ) ^ r) := by
      have hraise :
          ((g (n + 1) : ℝ) ^ (q ^ L : ℝ)) ^ r ≤ ((g (g n) : ℝ) ^ r) := by
        exact Real.rpow_le_rpow (by positivity) hiterL hrpos.le
      have hrewrite :
          (g (n + 1) : ℝ) ^ (r * (q ^ L : ℝ)) =
            ((g (n + 1) : ℝ) ^ (q ^ L : ℝ)) ^ r := by
        rw [← Real.rpow_mul hbase_pos.le]
        ring_nf
      exact hrewrite.trans_le hraise
    have hdiff_le_base :
        (g (n + 1) : ℝ) - (g n : ℝ) ≤ (g (n + 1) : ℝ) := by
      have hgn_nonneg : 0 ≤ (g n : ℝ) := by positivity
      nlinarith
    have hupper_power :
        (g (n + 1) : ℝ) ^ (r * (q ^ L : ℝ)) ≤ (g (n + 1) : ℝ) :=
      hpow_lower.trans ((hineq n hnpos).trans hdiff_le_base)
    have hqB_le_qL : q ^ B ≤ q ^ L := pow_le_pow_right₀ hq_gt_one.le hLgeB
    have hrqL_gt_one : 1 < r * q ^ L := by
      exact lt_of_lt_of_le hrqB_gt_one (mul_le_mul_of_nonneg_left hqB_le_qL hrpos.le)
    have hbase_gt_one : (1 : ℝ) < (g (n + 1) : ℝ) := by
      have hgapN := hgap_two n hnN0
      have htwo : 2 ≤ g (n + 1) := by omega
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) htwo)
    have hstrict :
        (g (n + 1) : ℝ) < (g (n + 1) : ℝ) ^ (r * (q ^ L : ℝ)) :=
      Real.self_lt_rpow_of_one_lt hbase_gt_one hrqL_gt_one
    exact (not_lt_of_ge hupper_power hstrict)
