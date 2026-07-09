import Mathlib

open Real

private def putnam_2025_b6_PolyLower (g : ℕ → ℕ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ) ^ a ≤ (g n : ℝ)

private def putnam_2025_b6_exp (r : ℝ) : ℕ → ℝ :=
  fun k => Nat.rec (motive := fun _ => ℝ) 1 (fun _ x => 1 + r * x * x) k

private lemma putnam_2025_b6_sum_Ico_sub (F : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (F (i + 1) - F i) = F n - F m := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := Finset.sum_range_sub (fun k : ℕ => F (m + k)) (n - m)
  simpa [Nat.add_sub_of_le hmn, Nat.add_assoc] using h

private lemma putnam_2025_b6_rpow_block_lower
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 ≤ β) (m n : ℕ) :
    D * (m : ℝ) ^ β * (n - m : ℕ) ≤
      ∑ i ∈ Finset.Ico m n, D * (i : ℝ) ^ β := by
  have hsum :
      ∑ i ∈ Finset.Ico m n, D * (m : ℝ) ^ β ≤
        ∑ i ∈ Finset.Ico m n, D * (i : ℝ) ^ β := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hmi : m ≤ i := (Finset.mem_Ico.mp hi).1
    have hp : (m : ℝ) ^ β ≤ (i : ℝ) ^ β := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmi) hβ
    exact mul_le_mul_of_nonneg_left hp hD
  simpa [mul_assoc, mul_comm, mul_left_comm] using hsum

private lemma putnam_2025_b6_rpow_mul_const
    {C a r x : ℝ} (hC : 0 < C) (hx : 0 ≤ x) :
    (C * (C * x ^ a) ^ a) ^ r = (C * C ^ a) ^ r * x ^ (r * a * a) := by
  calc
    (C * (C * x ^ a) ^ a) ^ r
        = C ^ r * (C * x ^ a) ^ (a * r) := by
          rw [Real.mul_rpow hC.le (Real.rpow_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hx _)) _)]
          rw [← Real.rpow_mul (mul_nonneg hC.le (Real.rpow_nonneg hx _))]
    _ = C ^ r * (C ^ (a * r) * (x ^ a) ^ (a * r)) := by
          rw [Real.mul_rpow hC.le (Real.rpow_nonneg hx _)]
    _ = C ^ r * (C ^ (a * r) * x ^ (a * (a * r))) := by
          rw [← Real.rpow_mul hx]
    _ = (C * C ^ a) ^ r * x ^ (r * a * a) := by
          rw [Real.mul_rpow hC.le (Real.rpow_nonneg hC.le _)]
          rw [← Real.rpow_mul hC.le]
          ring_nf

private lemma putnam_2025_b6_step_strict {g : ℕ → ℕ} {r : ℝ}
    (hpos : ∀ n : ℕ, 0 < n → 0 < g n)
    (hineq : ∀ n : ℕ, 0 < n →
      ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ)) :
    ∀ n : ℕ, 0 < n → g n < g (n + 1) := by
  intro n hn
  have hgnpos : 0 < g n := hpos n hn
  have hbasepos : 0 < (g (g n) : ℝ) := by
    exact_mod_cast hpos (g n) hgnpos
  have hpowpos : 0 < ((g (g n) : ℝ) ^ r) := Real.rpow_pos_of_pos hbasepos r
  have hdiffpos : 0 < (g (n + 1) : ℝ) - (g n : ℝ) :=
    lt_of_lt_of_le hpowpos (hineq n hn)
  exact_mod_cast (show (g n : ℝ) < (g (n + 1) : ℝ) by linarith)

private lemma putnam_2025_b6_self_le {g : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < n → 0 < g n)
    (hstep : ∀ n : ℕ, 0 < n → g n < g (n + 1)) :
    ∀ n : ℕ, 0 < n → n ≤ g n := by
  intro n
  induction n with
  | zero =>
      intro hn
      cases hn
  | succ n ih =>
      intro hn
      cases n with
      | zero =>
          exact hpos 1 (by norm_num)
      | succ k =>
          have hkpos : 0 < k.succ := Nat.succ_pos k
          have hle : k.succ ≤ g k.succ := ih hkpos
          have hlt : g k.succ < g (k.succ + 1) := hstep k.succ hkpos
          exact Nat.succ_le_of_lt (lt_of_le_of_lt hle hlt)

private lemma putnam_2025_b6_mono {g : ℕ → ℕ}
    (hstep : ∀ n : ℕ, 0 < n → g n < g (n + 1)) :
    ∀ {m n : ℕ}, 0 < m → m ≤ n → g m ≤ g n := by
  intro m n hm hmn
  exact Nat.le_induction (le_refl (g m)) (fun k hmk ih => by
    have hkpos : 0 < k := lt_of_lt_of_le hm hmk
    exact le_trans ih (le_of_lt (hstep k hkpos))) n hmn

private lemma putnam_2025_b6_two_step {g : ℕ → ℕ} {r : ℝ}
    (hpos : ∀ n : ℕ, 0 < n → 0 < g n)
    (hineq : ∀ n : ℕ, 0 < n →
      ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ))
    (hself : ∀ n : ℕ, 0 < n → n ≤ g n) (hr : 0 < r) :
    ∀ n : ℕ, 2 ≤ n → g n + 2 ≤ g (n + 1) := by
  intro n hn
  have hnpos : 0 < n := by omega
  have hgn_ge : n ≤ g n := hself n hnpos
  have hbase_ge : 2 ≤ g (g n) := by
    have hgnpos : 0 < g n := hpos n hnpos
    have : g n ≤ g (g n) := hself (g n) hgnpos
    exact hn.trans (hgn_ge.trans this)
  have hbase_gt1 : (1 : ℝ) < (g (g n) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ)) hbase_ge)
  have hpow_gt1 : (1 : ℝ) < ((g (g n) : ℝ) ^ r) :=
    Real.one_lt_rpow hbase_gt1 hr
  have hdiff_gt1 : (1 : ℝ) < (g (n + 1) : ℝ) - (g n : ℝ) :=
    lt_of_lt_of_le hpow_gt1 (hineq n hnpos)
  have hltreal : (g n + 1 : ℕ) < g (n + 1) := by
    exact_mod_cast (show ((g n : ℝ) + 1) < (g (n + 1) : ℝ) by linarith)
  exact Nat.succ_le_of_lt hltreal

private lemma putnam_2025_b6_index_two_ahead {g : ℕ → ℕ}
    (hself : ∀ n : ℕ, 0 < n → n ≤ g n)
    (hgap2 : ∀ n : ℕ, 2 ≤ n → g n + 2 ≤ g (n + 1)) :
    ∀ n : ℕ, 4 ≤ n → n + 2 ≤ g n := by
  intro n hn
  have h2 : 0 < n - 2 := by omega
  have hself2 : n - 2 ≤ g (n - 2) := hself (n - 2) h2
  have hgapA : g (n - 2) + 2 ≤ g ((n - 2) + 1) := hgap2 (n - 2) (by omega)
  have hgapB : g ((n - 2) + 1) + 2 ≤ g n := by
    simpa [show ((n - 2) + 1) + 1 = n by omega] using
      hgap2 ((n - 2) + 1) (by omega)
  omega

private lemma putnam_2025_b6_poly_start {g : ℕ → ℕ}
    (hself : ∀ n : ℕ, 0 < n → n ≤ g n) :
    putnam_2025_b6_PolyLower g 1 := by
  refine ⟨1, by norm_num, 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have h := hself n hnpos
  simpa using (Nat.cast_le.mpr h : (n : ℝ) ≤ (g n : ℝ))

private lemma putnam_2025_b6_poly_step {g : ℕ → ℕ} {r a : ℝ}
    (hineq : ∀ n : ℕ, 0 < n →
      ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ))
    (hself : ∀ n : ℕ, 0 < n → n ≤ g n)
    (hr : 0 < r) (ha : 0 ≤ a)
    (hP : putnam_2025_b6_PolyLower g a) :
    putnam_2025_b6_PolyLower g (1 + r * a * a) := by
  rcases hP with ⟨C, hC, N, hN⟩
  let β : ℝ := r * a * a
  let D : ℝ := (C * C ^ a) ^ r
  have hβ : 0 ≤ β := by
    have haa : 0 ≤ a * a := mul_nonneg ha ha
    exact mul_nonneg (mul_nonneg hr.le ha) ha
  have hDpos : 0 < D := by
    have hCa : 0 < C ^ a := Real.rpow_pos_of_pos hC a
    exact Real.rpow_pos_of_pos (mul_pos hC hCa) r
  let N0 : ℕ := max N 1
  let M : ℕ := max 2 (2 * N0)
  refine ⟨D * (1 / 3 : ℝ) ^ (β + 1), ?_, M, ?_⟩
  · exact mul_pos hDpos (Real.rpow_pos_of_pos (by norm_num) (β + 1))
  · intro n hnM
    let m : ℕ := n / 2
    have hMtwo : 2 ≤ n := (le_max_left 2 (2 * N0)).trans hnM
    have hMN0 : 2 * N0 ≤ n := (le_max_right 2 (2 * N0)).trans hnM
    have hmN0 : N0 ≤ m := by
      dsimp [m]
      omega
    have hmN : N ≤ m := (le_max_left N 1).trans hmN0
    have hmpos : 0 < m := lt_of_lt_of_le (by dsimp [N0]; exact Nat.lt_of_lt_of_le zero_lt_one (le_max_right N 1)) hmN0
    have hmn : m ≤ n := Nat.div_le_self n 2
    have hinc :
        ∀ i ∈ Finset.Ico m n,
          D * (i : ℝ) ^ β ≤ (g (i + 1) : ℝ) - (g i : ℝ) := by
      intro i hi
      have hmi : m ≤ i := (Finset.mem_Ico.mp hi).1
      have hiN : N ≤ i := hmN.trans hmi
      have hipos : 0 < i := lt_of_lt_of_le hmpos hmi
      have hgiN : N ≤ g i := hiN.trans (hself i hipos)
      have hCi : C * (i : ℝ) ^ a ≤ (g i : ℝ) := hN i hiN
      have hCgi : C * (g i : ℝ) ^ a ≤ (g (g i) : ℝ) := hN (g i) hgiN
      have hCipow :
          (C * (i : ℝ) ^ a) ^ a ≤ (g i : ℝ) ^ a := by
        exact Real.rpow_le_rpow
          (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg i) a)) hCi ha
      have hbase :
          C * (C * (i : ℝ) ^ a) ^ a ≤ (g (g i) : ℝ) := by
        calc
          C * (C * (i : ℝ) ^ a) ^ a ≤ C * (g i : ℝ) ^ a :=
            mul_le_mul_of_nonneg_left hCipow hC.le
          _ ≤ (g (g i) : ℝ) := hCgi
      have hleft_nonneg : 0 ≤ C * (C * (i : ℝ) ^ a) ^ a :=
        mul_nonneg hC.le
          (Real.rpow_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg i) a)) a)
      have hpow :
          (C * (C * (i : ℝ) ^ a) ^ a) ^ r ≤ ((g (g i) : ℝ) ^ r) :=
        Real.rpow_le_rpow hleft_nonneg hbase hr.le
      calc
        D * (i : ℝ) ^ β = (C * (C * (i : ℝ) ^ a) ^ a) ^ r := by
          rw [show D = (C * C ^ a) ^ r by rfl, show β = r * a * a by rfl,
            ← putnam_2025_b6_rpow_mul_const (C := C) (a := a) (r := r) (x := (i : ℝ))
              hC (Nat.cast_nonneg i)]
        _ ≤ ((g (g i) : ℝ) ^ r) := hpow
        _ ≤ (g (i + 1) : ℝ) - (g i : ℝ) := hineq i hipos
    have hsum :
        ∑ i ∈ Finset.Ico m n, D * (i : ℝ) ^ β ≤
          ∑ i ∈ Finset.Ico m n, ((g (i + 1) : ℝ) - (g i : ℝ)) := by
      exact Finset.sum_le_sum hinc
    have hblock :
        D * (m : ℝ) ^ β * (n - m : ℕ) ≤
          ∑ i ∈ Finset.Ico m n, D * (i : ℝ) ^ β :=
      putnam_2025_b6_rpow_block_lower hDpos.le hβ m n
    have htel :
        ∑ i ∈ Finset.Ico m n, ((g (i + 1) : ℝ) - (g i : ℝ)) =
          (g n : ℝ) - (g m : ℝ) :=
      putnam_2025_b6_sum_Ico_sub (fun k : ℕ => (g k : ℝ)) hmn
    have hlower_le_gn : D * (m : ℝ) ^ β * (n - m : ℕ) ≤ (g n : ℝ) := by
      have hle_sub : D * (m : ℝ) ^ β * (n - m : ℕ) ≤ (g n : ℝ) - (g m : ℝ) := by
        exact hblock.trans (hsum.trans (le_of_eq htel))
      have hsub_le : (g n : ℝ) - (g m : ℝ) ≤ (g n : ℝ) := by
        have hgmnonneg : 0 ≤ (g m : ℝ) := Nat.cast_nonneg (g m)
        linarith
      exact hle_sub.trans hsub_le
    have hthird : (n : ℝ) / 3 ≤ (m : ℝ) := by
      have hnat : n ≤ 3 * m := by
        dsimp [m]
        omega
      have hreal : (n : ℝ) ≤ 3 * (m : ℕ) := by exact_mod_cast hnat
      nlinarith
    have hγ : 0 ≤ β + 1 := by nlinarith
    have hpowthird : ((n : ℝ) / 3) ^ (β + 1) ≤ (m : ℝ) ^ (β + 1) :=
      Real.rpow_le_rpow (by positivity) hthird hγ
    have hmposreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hcount : m ≤ n - m := by
      dsimp [m]
      omega
    have hcountreal : (m : ℝ) ≤ (n - m : ℕ) := by exact_mod_cast hcount
    have hpow_m :
        (m : ℝ) ^ (β + 1) = (m : ℝ) ^ β * (m : ℝ) := by
      rw [Real.rpow_add hmposreal β 1]
      simp
    have hconst_to_m :
        D * (1 / 3 : ℝ) ^ (β + 1) * (n : ℝ) ^ (β + 1) ≤
          D * (m : ℝ) ^ β * (n - m : ℕ) := by
      calc
        D * (1 / 3 : ℝ) ^ (β + 1) * (n : ℝ) ^ (β + 1)
            = D * ((n : ℝ) / 3) ^ (β + 1) := by
              rw [show (n : ℝ) / 3 = (1 / 3 : ℝ) * (n : ℝ) by ring]
              rw [Real.mul_rpow (by norm_num : 0 ≤ (1 / 3 : ℝ)) (Nat.cast_nonneg n)]
              ring
        _ ≤ D * (m : ℝ) ^ (β + 1) :=
              mul_le_mul_of_nonneg_left hpowthird hDpos.le
        _ = D * ((m : ℝ) ^ β * (m : ℝ)) := by rw [hpow_m]
        _ ≤ D * (m : ℝ) ^ β * (n - m : ℕ) := by
              have hnonneg : 0 ≤ D * (m : ℝ) ^ β :=
                mul_nonneg hDpos.le (Real.rpow_nonneg (Nat.cast_nonneg m) β)
              nlinarith
    simpa [β, add_comm, add_left_comm, add_assoc] using hconst_to_m.trans hlower_le_gn

private lemma putnam_2025_b6_exp_nonneg {r : ℝ} (hr : 0 ≤ r) :
    ∀ k : ℕ, 0 ≤ putnam_2025_b6_exp r k := by
  intro k
  induction k with
  | zero =>
      simp [putnam_2025_b6_exp]
  | succ k ih =>
      change 0 ≤ 1 + r * putnam_2025_b6_exp r k * putnam_2025_b6_exp r k
      have hsq : 0 ≤ putnam_2025_b6_exp r k * putnam_2025_b6_exp r k :=
        mul_self_nonneg (putnam_2025_b6_exp r k)
      have hmul : 0 ≤ r * (putnam_2025_b6_exp r k * putnam_2025_b6_exp r k) :=
        mul_nonneg hr hsq
      nlinarith

private lemma putnam_2025_b6_exp_large {r : ℝ} (hr : (1 / 4 : ℝ) < r) :
    ∃ k : ℕ, 1 / (r * r) < putnam_2025_b6_exp r k := by
  have hrpos : 0 < r := by nlinarith
  obtain ⟨δ, hδ, hstep⟩ :
      ∃ δ > 0, ∀ x : ℝ, x + δ ≤ 1 + r * x * x := by
    refine ⟨1 - 1 / (4 * r), ?_, ?_⟩
    · field_simp [hrpos.ne']
      nlinarith
    · intro x
      have hs : 0 ≤ (2 * r * x - 1) ^ 2 := sq_nonneg _
      field_simp [hrpos.ne']
      nlinarith
  have hlin : ∀ k : ℕ, 1 + (k : ℝ) * δ ≤ putnam_2025_b6_exp r k := by
    intro k
    induction k with
    | zero =>
        simp [putnam_2025_b6_exp]
    | succ k ih =>
        change
          1 + (Nat.succ k : ℝ) * δ ≤
            1 + r * putnam_2025_b6_exp r k * putnam_2025_b6_exp r k
        have hs := hstep (putnam_2025_b6_exp r k)
        have hk :
            1 + ((k : ℝ) + 1) * δ ≤
              1 + r * putnam_2025_b6_exp r k * putnam_2025_b6_exp r k := by
          nlinarith
        simpa [Nat.cast_succ] using hk
  have ht0 : Filter.Tendsto (fun k : ℕ => (k : ℝ) * δ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hδ (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht : Filter.Tendsto (fun k : ℕ => (k : ℝ) * δ + 1) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_add ht0 tendsto_const_nhds
  obtain ⟨k, hk⟩ := (Filter.Tendsto.eventually_gt_atTop ht (1 / (r * r))).exists
  refine ⟨k, lt_of_lt_of_le ?_ (hlin k)⟩
  simpa [add_comm] using hk

private lemma putnam_2025_b6_tendsto_g {g : ℕ → ℕ}
    (hself : ∀ n : ℕ, 0 < n → n ≤ g n) :
    Filter.Tendsto (fun n : ℕ => (g n : ℝ)) Filter.atTop Filter.atTop := by
  have hpoint : ∀ n : ℕ, (n : ℝ) ≤ (g n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · exact_mod_cast hself n (Nat.pos_of_ne_zero hn)
  exact Filter.tendsto_atTop_mono hpoint (tendsto_natCast_atTop_atTop (R := ℝ))

private lemma putnam_2025_b6_eventual_gap_power {g : ℕ → ℕ} {r α q : ℝ}
    (hineq : ∀ n : ℕ, 0 < n →
      ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ))
    (hself : ∀ n : ℕ, 0 < n → n ≤ g n)
    (hr : 0 < r) (hP : putnam_2025_b6_PolyLower g α)
    (hq : q < r * α) :
    ∀ᶠ k : ℕ in Filter.atTop,
      (g k : ℝ) ^ q ≤ (g (k + 1) : ℝ) - (g k : ℝ) := by
  rcases hP with ⟨C, hC, N, hN⟩
  let p : ℝ := r * α
  let B : ℝ := C ^ r
  have hpq : 0 < p - q := by dsimp [p]; linarith
  have hBpos : 0 < B := Real.rpow_pos_of_pos hC r
  have hg_tendsto := putnam_2025_b6_tendsto_g hself
  have hpow_tendsto :
      Filter.Tendsto (fun k : ℕ => (g k : ℝ) ^ (p - q)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hpq).comp hg_tendsto
  obtain ⟨M0, hM0⟩ :=
    Filter.eventually_atTop.1 (Filter.Tendsto.eventually_ge_atTop hpow_tendsto (1 / B))
  refine Filter.eventually_atTop.2 ⟨max (max N 1) M0, ?_⟩
  intro k hk
  have hkM0 : M0 ≤ k := (le_max_right (max N 1) M0).trans hk
  have hkN : N ≤ k := (le_max_left N 1).trans ((le_max_left (max N 1) M0).trans hk)
  have hkpos : 0 < k := by
    have : 1 ≤ k := (le_max_right N 1).trans ((le_max_left (max N 1) M0).trans hk)
    omega
  have hgkN : N ≤ g k := hkN.trans (hself k hkpos)
  have hxpos : 0 < (g k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hkpos (hself k hkpos)
  have hCgg : C * (g k : ℝ) ^ α ≤ (g (g k) : ℝ) := hN (g k) hgkN
  have hleft_nonneg : 0 ≤ C * (g k : ℝ) ^ α :=
    mul_nonneg hC.le (Real.rpow_nonneg hxpos.le α)
  have hpow :
      (C * (g k : ℝ) ^ α) ^ r ≤ ((g (g k) : ℝ) ^ r) :=
    Real.rpow_le_rpow hleft_nonneg hCgg hr.le
  have hCx :
      (C * (g k : ℝ) ^ α) ^ r = B * (g k : ℝ) ^ p := by
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hxpos.le α)]
    rw [← Real.rpow_mul hxpos.le]
    simp [B, p, mul_comm]
  have hlarge : 1 / B ≤ (g k : ℝ) ^ (p - q) := hM0 k hkM0
  have hBlarge : 1 ≤ B * (g k : ℝ) ^ (p - q) := by
    have := mul_le_mul_of_nonneg_left hlarge hBpos.le
    field_simp [hBpos.ne'] at this
    nlinarith
  have hsplit : (g k : ℝ) ^ p = (g k : ℝ) ^ q * (g k : ℝ) ^ (p - q) := by
    rw [← Real.rpow_add hxpos]
    ring_nf
  have hq_to_Bp : (g k : ℝ) ^ q ≤ B * (g k : ℝ) ^ p := by
    calc
      (g k : ℝ) ^ q = (g k : ℝ) ^ q * 1 := by ring
      _ ≤ (g k : ℝ) ^ q * (B * (g k : ℝ) ^ (p - q)) :=
          mul_le_mul_of_nonneg_left hBlarge (Real.rpow_nonneg hxpos.le q)
      _ = B * ((g k : ℝ) ^ q * (g k : ℝ) ^ (p - q)) := by ring
      _ = B * (g k : ℝ) ^ p := by rw [hsplit]
  calc
    (g k : ℝ) ^ q ≤ B * (g k : ℝ) ^ p := hq_to_Bp
    _ = (C * (g k : ℝ) ^ α) ^ r := hCx.symm
    _ ≤ ((g (g k) : ℝ) ^ r) := hpow
    _ ≤ (g (k + 1) : ℝ) - (g k : ℝ) := hineq k hkpos

private lemma putnam_2025_b6_large_poly_false {g : ℕ → ℕ} {r α : ℝ}
    (hineq : ∀ n : ℕ, 0 < n →
      ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ))
    (hmono : ∀ {m n : ℕ}, 0 < m → m ≤ n → g m ≤ g n)
    (hself : ∀ n : ℕ, 0 < n → n ≤ g n)
    (hindex2 : ∀ n : ℕ, 4 ≤ n → n + 2 ≤ g n)
    (hr : 0 < r) (hP : putnam_2025_b6_PolyLower g α)
    (hα : 1 / (r * r) < α) : False := by
  let q : ℝ := (1 / r + r * α) / 2
  have hrrα : 1 < r * r * α := by
    have hrr : 0 < r * r := mul_pos hr hr
    have hmul := mul_lt_mul_of_pos_left hα hrr
    field_simp [ne_of_gt hrr] at hmul
    nlinarith
  have hq_lt : q < r * α := by
    have h1 : 1 / r < r * α := by
      field_simp [hr.ne'] at hα ⊢
      nlinarith
    dsimp [q]
    nlinarith
  have hqr : 1 < q * r := by
    dsimp [q]
    field_simp [hr.ne']
    ring_nf
    nlinarith
  obtain ⟨K, hK⟩ :=
    Filter.eventually_atTop.1
      (putnam_2025_b6_eventual_gap_power hineq hself hr hP hq_lt)
  let n : ℕ := max 4 K
  have hn4 : 4 ≤ n := le_max_left 4 K
  have hKnp1 : K ≤ n + 1 := by
    dsimp [n]
    omega
  have hgap_np1 :
      (g (n + 1) : ℝ) ^ q ≤ (g ((n + 1) + 1) : ℝ) - (g (n + 1) : ℝ) :=
    hK (n + 1) hKnp1
  have hnpos : 0 < n := by omega
  have hn1pos : 0 < n + 1 := by omega
  have hn2pos : 0 < n + 2 := by omega
  have hidx : n + 2 ≤ g n := hindex2 n hn4
  have hmono_idx : g (n + 2) ≤ g (g n) := hmono hn2pos hidx
  have hxq_le_ggn : (g (n + 1) : ℝ) ^ q ≤ (g (g n) : ℝ) := by
    have hdiff_le : (g ((n + 1) + 1) : ℝ) - (g (n + 1) : ℝ) ≤
        (g ((n + 1) + 1) : ℝ) := by
      have hnonneg : 0 ≤ (g (n + 1) : ℝ) := Nat.cast_nonneg (g (n + 1))
      linarith
    have hto_n2 : (g (n + 1) : ℝ) ^ q ≤ (g (n + 2) : ℝ) := by
      simpa [Nat.add_assoc] using hgap_np1.trans hdiff_le
    exact hto_n2.trans (Nat.cast_le.mpr hmono_idx)
  have hggpow_le_x : ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) := by
    have hdiff_le : (g (n + 1) : ℝ) - (g n : ℝ) ≤ (g (n + 1) : ℝ) := by
      have hnonneg : 0 ≤ (g n : ℝ) := Nat.cast_nonneg (g n)
      linarith
    exact (hineq n hnpos).trans hdiff_le
  let x : ℝ := (g (n + 1) : ℝ)
  have hxnonneg : 0 ≤ x := by dsimp [x]; exact Nat.cast_nonneg (g (n + 1))
  have hle : x ^ (q * r) ≤ x := by
    calc
      x ^ (q * r) = (x ^ q) ^ r := by
        rw [Real.rpow_mul hxnonneg]
      _ ≤ ((g (g n) : ℝ) ^ r) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hxnonneg q) (by simpa [x] using hxq_le_ggn) hr.le
      _ ≤ x := by simpa [x] using hggpow_le_x
  have hxgt1 : 1 < x := by
    have hn1_ge_two : 2 ≤ n + 1 := by omega
    have hnat : 2 ≤ g (n + 1) := hn1_ge_two.trans (hself (n + 1) hn1pos)
    dsimp [x]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ)) hnat)
  have hlt : x < x ^ (q * r) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hxgt1 hqr
  linarith

-- 1 / 4

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
      ((1 / 4) : ℝ ) := by
  constructor
  · refine ⟨fun n => n ^ 2, ?_, ?_⟩
    · intro n hn
      exact pow_pos hn 2
    · intro n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hroot : ((((n ^ 2) ^ 2 : ℕ) : ℝ) ^ ((1 / 4 : ℝ))) = (n : ℝ) := by
        have hcast : (((n ^ 2) ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 4 := by
          norm_num
          ring
        rw [hcast]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hnR.le]
        norm_num
      change ((((n ^ 2) ^ 2 : ℕ) : ℝ) ^ ((1 / 4 : ℝ))) ≤
        (((n + 1) ^ 2 : ℕ) : ℝ) - ((n ^ 2 : ℕ) : ℝ)
      rw [hroot]
      norm_num
      nlinarith [hnR]
  · intro r hrmem
    rcases hrmem with ⟨g, hpos, hineq⟩
    by_contra hle
    have hrgt : (1 / 4 : ℝ) < r := lt_of_not_ge hle
    have hrpos : 0 < r := by nlinarith
    have hstep := putnam_2025_b6_step_strict hpos hineq
    have hself := putnam_2025_b6_self_le hpos hstep
    have hmono : ∀ {m n : ℕ}, 0 < m → m ≤ n → g m ≤ g n :=
      putnam_2025_b6_mono hstep
    have hgap2 := putnam_2025_b6_two_step hpos hineq hself hrpos
    have hindex2 := putnam_2025_b6_index_two_ahead hself hgap2
    have hexp_nonneg := putnam_2025_b6_exp_nonneg hrpos.le
    have hpoly : ∀ k : ℕ, putnam_2025_b6_PolyLower g (putnam_2025_b6_exp r k) := by
      intro k
      induction k with
      | zero =>
          simpa [putnam_2025_b6_exp] using putnam_2025_b6_poly_start hself
      | succ k ih =>
          change putnam_2025_b6_PolyLower g
            (1 + r * putnam_2025_b6_exp r k * putnam_2025_b6_exp r k)
          exact putnam_2025_b6_poly_step hineq hself hrpos (hexp_nonneg k) ih
    obtain ⟨k, hk⟩ := putnam_2025_b6_exp_large hrgt
    exact putnam_2025_b6_large_poly_false hineq hmono hself hindex2 hrpos (hpoly k) hk
