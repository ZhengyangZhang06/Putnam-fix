import Mathlib

open EuclideanGeometry Topology Filter Complex

private lemma putnam_1965_b4_odd_sum_extend (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i + 1) : ℝ) * x ^ i) =
    (∑ i ∈ Finset.Icc 0 ((n - 1) / 2), (n.choose (2 * i + 1) : ℝ) * x ^ i) := by
  rw [← Nat.range_succ_eq_Icc_zero (n / 2),
    ← Nat.range_succ_eq_Icc_zero ((n - 1) / 2)]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · cases m with
    | zero => simp
    | succ m =>
      have h1 : (2 * (m + 1)) / 2 = m + 1 := by omega
      have h2 : (2 * (m + 1) - 1) / 2 = m := by omega
      rw [h1, h2]
      rw [Finset.sum_range_succ]
      simp
  · have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m + 1 - 1) / 2 = m := by omega
    rw [h1, h2]

private lemma putnam_1965_b4_v_sum_succ (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.Icc 0 (((n + 1) - 1) / 2),
        ((n + 1).choose (2 * i + 1) : ℝ) * x ^ i) =
      (∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i) : ℝ) * x ^ i) +
      (∑ i ∈ Finset.Icc 0 ((n - 1) / 2),
        (n.choose (2 * i + 1) : ℝ) * x ^ i) := by
  have htop : ((n + 1) - 1) / 2 = n / 2 := by omega
  rw [htop]
  rw [← putnam_1965_b4_odd_sum_extend n x]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← add_mul]
  norm_num [Nat.choose_succ_succ]

private lemma putnam_1965_b4_even_sum_extend (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.Icc 0 ((n + 1) / 2), (n.choose (2 * i) : ℝ) * x ^ i) =
    (∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i) : ℝ) * x ^ i) := by
  rw [← Nat.range_succ_eq_Icc_zero ((n + 1) / 2),
    ← Nat.range_succ_eq_Icc_zero (n / 2)]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m) / 2 = m := by omega
    rw [h1, h2]
  · have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1, h2]
    rw [Finset.sum_range_succ]
    have hzero : (2 * m + 1).choose (2 * (m + 1)) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    simp [hzero]

private lemma putnam_1965_b4_odd_mul_shift (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (∑ i ∈ Finset.range ((n + 1) / 2),
        (n.choose (2 * i + 1) : ℝ) * x ^ (i + 1)) =
      x * (∑ i ∈ Finset.Icc 0 ((n - 1) / 2),
        (n.choose (2 * i + 1) : ℝ) * x ^ i) := by
  rw [← Nat.range_succ_eq_Icc_zero ((n - 1) / 2)]
  have hlen : (n + 1) / 2 = (n - 1) / 2 + 1 := by omega
  rw [hlen]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

private lemma putnam_1965_b4_even_split (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.Icc 0 ((n + 1) / 2),
        (n.choose (2 * i) : ℝ) * x ^ i) =
      1 + ∑ i ∈ Finset.range ((n + 1) / 2),
        (n.choose (2 * (i + 1)) : ℝ) * x ^ (i + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero ((n + 1) / 2)]
  rw [Finset.sum_range_succ']
  simp [Nat.choose_zero_right, add_comm]

private lemma putnam_1965_b4_u_sum_succ (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (∑ i ∈ Finset.Icc 0 ((n + 1) / 2),
        ((n + 1).choose (2 * i) : ℝ) * x ^ i) =
      (∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i) : ℝ) * x ^ i) +
      x * (∑ i ∈ Finset.Icc 0 ((n - 1) / 2),
        (n.choose (2 * i + 1) : ℝ) * x ^ i) := by
  rw [← Nat.range_succ_eq_Icc_zero ((n + 1) / 2)]
  rw [Finset.sum_range_succ']
  simp
  have hpascal :
      (∑ i ∈ Finset.range ((n + 1) / 2),
          ((n + 1).choose (2 * (i + 1)) : ℝ) * x ^ (i + 1)) =
        (∑ i ∈ Finset.range ((n + 1) / 2),
          (n.choose (2 * i + 1) : ℝ) * x ^ (i + 1)) +
        (∑ i ∈ Finset.range ((n + 1) / 2),
          (n.choose (2 * (i + 1)) : ℝ) * x ^ (i + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hidx : 2 * (i + 1) = (2 * i + 1).succ := by omega
    rw [hidx, Nat.choose_succ_succ]
    norm_num
    ring
  rw [hpascal]
  rw [putnam_1965_b4_odd_mul_shift n hn x]
  have heven := putnam_1965_b4_even_split n x
  rw [putnam_1965_b4_even_sum_extend n x] at heven
  rw [heven]
  ring

private lemma putnam_1965_b4_even_sum_zero (n : ℕ) :
    (∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i) : ℝ) * (0 : ℝ) ^ i) = 1 := by
  rw [Finset.sum_eq_single_of_mem 0 (by simp) (by
    intro b hb hb0
    have hpow : (0 : ℝ) ^ b = 0 := zero_pow hb0
    simp [hpow])]
  simp

private lemma putnam_1965_b4_odd_sum_zero (n : ℕ) :
    (∑ i ∈ Finset.Icc 0 ((n - 1) / 2),
        (n.choose (2 * i + 1) : ℝ) * (0 : ℝ) ^ i) = n := by
  rw [Finset.sum_eq_single_of_mem 0 (by simp) (by
    intro b hb hb0
    have hpow : (0 : ℝ) ^ b = 0 := zero_pow hb0
    simp [hpow])]
  simp [Nat.choose_one_right]

private lemma putnam_1965_b4_abs_one_sub_lt_one_add {y : ℝ} (hy : 0 < y) :
    |1 - y| < 1 + y := by
  rw [abs_lt]
  constructor <;> linarith

private lemma putnam_1965_b4_one_sub_pow_lt_one_add_pow {y : ℝ} (hy : 0 < y)
    {n : ℕ} (hn : 0 < n) :
    (1 - y) ^ n < (1 + y) ^ n := by
  have hbase_abs : |1 - y| < 1 + y := putnam_1965_b4_abs_one_sub_lt_one_add hy
  have hbase_nonneg : 0 ≤ |1 - y| := abs_nonneg _
  have hpow_abs : |1 - y| ^ n < (1 + y) ^ n :=
    pow_lt_pow_left₀ hbase_abs hbase_nonneg (Nat.ne_of_gt hn)
  have hle_abs : (1 - y) ^ n ≤ |1 - y| ^ n := by
    rw [← abs_pow]
    exact le_abs_self _
  exact lt_of_le_of_lt hle_abs hpow_abs

private lemma putnam_1965_b4_diff_pos {y : ℝ} (hy : 0 < y)
    {n : ℕ} (hn : 0 < n) :
    0 < (1 + y) ^ n - (1 - y) ^ n := by
  have h := putnam_1965_b4_one_sub_pow_lt_one_add_pow hy hn
  linarith

-- ((fun h : ℝ → ℝ => h + (fun x : ℝ => x), fun h : ℝ → ℝ => h + (fun _ : ℝ => 1)), ({x : ℝ | x ≥ 0}, Real.sqrt))
/--
Let $$f(x, n) = \frac{{n \choose 0} + {n \choose 2}x + {n \choose 4}x^2 + \cdots}{{n \choose 1} + {n \choose 3}x + {n \choose 5}x^2 + \cdots}$$ for all real numbers $x$ and positive integers $n$. Express $f(x, n+1)$ as a rational function involving $f(x, n)$ and $x$, and find $\lim_{n \to \infty} f(x, n)$ for all $x$ for which this limit converges.
-/
theorem putnam_1965_b4
    (f u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = ∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i)) * x ^ i)
    (hv : ∀ n > 0, ∀ x, v n x = ∑ i ∈ Finset.Icc 0 ((n - 1) / 2), (n.choose (2 * i + 1)) * x ^ i)
    (hf : ∀ n > 0, ∀ x, f n x = u n x / v n x)
    (n : ℕ)
    (hn : 0 < n) :
    let ⟨⟨p, q⟩, ⟨s, g⟩⟩ := (((fun h : ℝ → ℝ => h + (fun x : ℝ => x), fun h : ℝ → ℝ => h + (fun _ : ℝ => 1)), ({x : ℝ | x ≥ 0}, Real.sqrt)) : ((((ℝ → ℝ) → (ℝ → ℝ)) × ((ℝ → ℝ) → (ℝ → ℝ))) × ((Set ℝ) × (ℝ → ℝ))) )
    (∀ x, v n x ≠ 0 → v (n + 1) x ≠ 0 → q (f n) x ≠ 0 → f (n + 1) x = p (f n) x / q (f n) x) ∧
    s = {x | ∃ l, Tendsto (fun n ↦ f n x) atTop (𝓝 l)} ∧
    ∀ x ∈ s, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  have hu_succ : ∀ m > 0, ∀ x, u (m + 1) x = u m x + x * v m x := by
    intro m hm x
    rw [hu (m + 1) (Nat.succ_pos _) x, hu m hm x, hv m hm x]
    exact putnam_1965_b4_u_sum_succ m hm x
  have hv_succ : ∀ m > 0, ∀ x, v (m + 1) x = u m x + v m x := by
    intro m hm x
    rw [hv (m + 1) (Nat.succ_pos _) x, hu m hm x, hv m hm x]
    exact putnam_1965_b4_v_sum_succ m x
  have hf_succ : ∀ m > 0, ∀ x, v m x ≠ 0 → v (m + 1) x ≠ 0 →
      f m x + 1 ≠ 0 → f (m + 1) x = (f m x + x) / (f m x + 1) := by
    intro m hm x hvm hvmp1 hq
    have hvm_sum : u m x + v m x ≠ 0 := by
      simpa [hv_succ m hm x] using hvmp1
    have hq' : u m x / v m x + 1 ≠ 0 := by
      simpa [hf m hm x] using hq
    rw [hf (m + 1) (Nat.succ_pos _) x, hf m hm x, hu_succ m hm x, hv_succ m hm x]
    field_simp [hvm, hvm_sum, hq']
  have h_invariant : ∀ m > 0, ∀ x, (u m x) ^ 2 - x * (v m x) ^ 2 = (1 - x) ^ m := by
    intro m hm x
    induction' m with m ih
    · exact (Nat.not_lt_zero _ hm).elim
    · cases m with
      | zero =>
        rw [hu 1 (by norm_num) x, hv 1 (by norm_num) x]
        norm_num
      | succ m =>
        have hmpos : 0 < m + 1 := Nat.succ_pos _
        have hstep : 0 < m + 1 := hmpos
        have hih := ih hstep
        rw [hu_succ (m + 1) hstep x, hv_succ (m + 1) hstep x]
        calc
          (u (m + 1) x + x * v (m + 1) x) ^ 2 -
              x * (u (m + 1) x + v (m + 1) x) ^ 2
              = (1 - x) * ((u (m + 1) x) ^ 2 - x * (v (m + 1) x) ^ 2) := by
                ring
          _ = (1 - x) * (1 - x) ^ (m + 1) := by rw [hih]
          _ = (1 - x) ^ (m + 1 + 1) := by
                rw [pow_succ]
                ring
  have f_zero : ∀ m > 0, f m 0 = 1 / (m : ℝ) := by
    intro m hm
    have hu0 : u m 0 = 1 := by
      rw [hu m hm 0]
      exact putnam_1965_b4_even_sum_zero m
    have hv0 : v m 0 = (m : ℝ) := by
      rw [hv m hm 0]
      exact putnam_1965_b4_odd_sum_zero m
    rw [hf m hm 0, hu0, hv0]
  have tendsto_nonneg : ∀ x, 0 ≤ x → Tendsto (fun m ↦ f m x) atTop (𝓝 (Real.sqrt x)) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      have heq : (fun m : ℕ => (1 : ℝ) / (m : ℝ)) =ᶠ[atTop] fun m => f m 0 := by
        exact Filter.eventually_atTop.2
          ⟨1, fun m hm => (f_zero m (by exact hm)).symm⟩
      simpa [Real.sqrt_zero] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' heq
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      let y : ℝ := Real.sqrt x
      have hypos : 0 < y := Real.sqrt_pos_of_pos hxpos
      have hy2 : y ^ 2 = x := by
        simpa [y] using Real.sq_sqrt hx
      have hclosed : ∀ m > 0,
          u m (y ^ 2) = ((1 + y) ^ m + (1 - y) ^ m) / 2 ∧
          y * v m (y ^ 2) = ((1 + y) ^ m - (1 - y) ^ m) / 2 := by
        intro m hm
        induction' m with m ih
        · exact (Nat.not_lt_zero _ hm).elim
        · cases m with
          | zero =>
            rw [hu 1 (by norm_num) (y ^ 2), hv 1 (by norm_num) (y ^ 2)]
            norm_num
          | succ m =>
            have hmpos : 0 < m + 1 := Nat.succ_pos _
            rcases ih hmpos with ⟨hU, hV⟩
            constructor
            · rw [hu_succ (m + 1) hmpos (y ^ 2), hU]
              have hVmul :
                  y ^ 2 * v (m + 1) (y ^ 2) =
                    y * (((1 + y) ^ (m + 1) - (1 - y) ^ (m + 1)) / 2) := by
                calc
                  y ^ 2 * v (m + 1) (y ^ 2) =
                      y * (y * v (m + 1) (y ^ 2)) := by ring
                  _ = y * (((1 + y) ^ (m + 1) - (1 - y) ^ (m + 1)) / 2) := by
                      rw [hV]
              rw [hVmul]
              ring
            · rw [hv_succ (m + 1) hmpos (y ^ 2), mul_add, hU, hV]
              ring
      have f_formula : ∀ m > 0,
          f m x =
            y * (((1 + y) ^ m + (1 - y) ^ m) /
              ((1 + y) ^ m - (1 - y) ^ m)) := by
        intro m hm
        rcases hclosed m hm with ⟨hU, hV⟩
        have hDpos : 0 < (1 + y) ^ m - (1 - y) ^ m :=
          putnam_1965_b4_diff_pos hypos hm
        have hDne : (1 + y) ^ m - (1 - y) ^ m ≠ 0 := ne_of_gt hDpos
        have hvne : v m (y ^ 2) ≠ 0 := by
          intro hv0
          rw [hv0, mul_zero] at hV
          linarith
        rw [hy2.symm, hf m hm (y ^ 2), hU]
        field_simp [hvne, hDne] at hV ⊢
        rw [← hV]
      let r : ℝ := (1 - y) / (1 + y)
      have honepos : 0 < 1 + y := by linarith
      have hnormr : ‖r‖ < 1 := by
        have habs : |1 - y| / (1 + y) < 1 := by
          rw [div_lt_one honepos]
          exact putnam_1965_b4_abs_one_sub_lt_one_add hypos
        have hdenabs : |1 + y| = 1 + y := abs_of_pos honepos
        simpa [r, Real.norm_eq_abs, abs_div, hdenabs] using habs
      have hpow : Tendsto (fun m : ℕ => r ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnormr
      have hfrac : Tendsto (fun m : ℕ => (1 + r ^ m) / (1 - r ^ m)) atTop (𝓝 1) := by
        have hnum : Tendsto (fun m : ℕ => 1 + r ^ m) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add hpow
        have hden : Tendsto (fun m : ℕ => 1 - r ^ m) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub hpow
        simpa using hnum.div hden (by norm_num)
      have hlim_formula :
          Tendsto (fun m : ℕ => y * ((1 + r ^ m) / (1 - r ^ m))) atTop (𝓝 y) := by
        simpa using tendsto_const_nhds.mul hfrac
      have hformula_eq :
          (fun m : ℕ => y * ((1 + r ^ m) / (1 - r ^ m))) =ᶠ[atTop]
            fun m => f m x := by
        refine Filter.eventually_atTop.2 ⟨1, fun m hm => ?_⟩
        have hmpos : 0 < m := by exact hm
        have hAne : (1 + y) ^ m ≠ 0 := ne_of_gt (pow_pos honepos m)
        have hrpow : r ^ m = (1 - y) ^ m / (1 + y) ^ m := by
          simp [r, div_pow]
        change y * ((1 + r ^ m) / (1 - r ^ m)) = f m x
        rw [f_formula m hmpos]
        rw [hrpow]
        field_simp [hAne]
      simpa [y] using hlim_formula.congr' hformula_eq
  have no_limit_neg : ∀ x, x < 0 → ¬ ∃ l, Tendsto (fun m ↦ f m x) atTop (𝓝 l) := by
    intro x hxlt hlim
    rcases hlim with ⟨l, hconv⟩
    have hv_eventually : ∀ᶠ m in atTop, v m x ≠ 0 := by
      by_contra hnot
      have hfreqv : ∃ᶠ m in atTop, v m x = 0 := by
        simpa using (Filter.not_eventually.mp hnot)
      have hpos_eventually : ∀ᶠ m in atTop, 0 < m :=
        Filter.eventually_atTop.2 ⟨1, fun m hm => by exact hm⟩
      have hfreqvpos : ∃ᶠ m in atTop, v m x = 0 ∧ 0 < m :=
        hfreqv.and_eventually hpos_eventually
      have hfreq0 : ∃ᶠ m in atTop, f m x ∈ ({0} : Set ℝ) := by
        refine hfreqvpos.mono ?_
        intro m hm
        rcases hm with ⟨hvm, hmpos⟩
        have hfm : f m x = 0 := by
          rw [hf m hmpos x, hvm, div_zero]
        simp [hfm]
      have hfreq1 : ∃ᶠ m in atTop, f (m + 1) x ∈ ({1} : Set ℝ) := by
        refine hfreqvpos.mono ?_
        intro m hm
        rcases hm with ⟨hvm, hmpos⟩
        have hum_ne : u m x ≠ 0 := by
          intro hum0
          have hposrhs : 0 < (1 - x) ^ m := pow_pos (by linarith) m
          have hzero_lhs : (u m x) ^ 2 - x * (v m x) ^ 2 = 0 := by
            simp [hum0, hvm]
          have hinv := h_invariant m hmpos x
          nlinarith
        have hfm1 : f (m + 1) x = 1 := by
          rw [hf (m + 1) (Nat.succ_pos _) x, hu_succ m hmpos x, hv_succ m hmpos x]
          simp [hvm, hum_ne]
        simp [hfm1]
      have hl0mem : l ∈ ({0} : Set ℝ) :=
        isClosed_singleton.mem_of_frequently_of_tendsto hfreq0 hconv
      have hl0 : l = 0 := by simpa using hl0mem
      have hconv_shift : Tendsto (fun m : ℕ => f (m + 1) x) atTop (𝓝 l) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2 hconv
      have hl1mem : l ∈ ({1} : Set ℝ) :=
        isClosed_singleton.mem_of_frequently_of_tendsto hfreq1 hconv_shift
      have hl1 : l = 1 := by simpa using hl1mem
      nlinarith
    have hv_next_eventually : ∀ᶠ m in atTop, v (m + 1) x ≠ 0 :=
      (Filter.tendsto_add_atTop_nat 1).eventually hv_eventually
    have hpos_eventually : ∀ᶠ m in atTop, 0 < m :=
      Filter.eventually_atTop.2 ⟨1, fun m hm => by exact hm⟩
    have hbasic_eventually :
        ∀ᶠ m in atTop, 0 < m ∧ v m x ≠ 0 ∧ v (m + 1) x ≠ 0 :=
      hpos_eventually.and (hv_eventually.and hv_next_eventually)
    have hq_eventually : ∀ᶠ m in atTop, f m x + 1 ≠ 0 := by
      refine hbasic_eventually.mono ?_
      intro m hm
      rcases hm with ⟨hmpos, hvm, hvmp1⟩
      intro hq0
      have hfm : f m x = -1 := by linarith
      have hum_eq : u m x = -v m x := by
        have hdiv : u m x / v m x = -1 := by
          simpa [hf m hmpos x] using hfm
        field_simp [hvm] at hdiv
        linarith
      have hvzero : v (m + 1) x = 0 := by
        rw [hv_succ m hmpos x, hum_eq]
        ring
      exact hvmp1 hvzero
    have hrec_eventually :
        (fun m : ℕ => f (m + 1) x * (f m x + 1)) =ᶠ[atTop]
          fun m => f m x + x := by
      refine (hbasic_eventually.and hq_eventually).mono ?_
      intro m hm
      rcases hm with ⟨⟨hmpos, hvm, hvmp1⟩, hq⟩
      have hrec := hf_succ m hmpos x hvm hvmp1 hq
      change f (m + 1) x * (f m x + 1) = f m x + x
      rw [hrec]
      field_simp [hq]
    have hconv_shift : Tendsto (fun m : ℕ => f (m + 1) x) atTop (𝓝 l) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 hconv
    have hleft :
        Tendsto (fun m : ℕ => f (m + 1) x * (f m x + 1)) atTop
          (𝓝 (l * (l + 1))) :=
      hconv_shift.mul (hconv.add tendsto_const_nhds)
    have hright : Tendsto (fun m : ℕ => f m x + x) atTop (𝓝 (l + x)) :=
      hconv.add tendsto_const_nhds
    have hright' : Tendsto (fun m : ℕ => f m x + x) atTop (𝓝 (l * (l + 1))) :=
      hleft.congr' hrec_eventually
    have hlim_eq : l * (l + 1) = l + x := tendsto_nhds_unique hright' hright
    have hxnonneg : 0 ≤ x := by
      have hsq : l ^ 2 = x := by nlinarith
      rw [← hsq]
      exact sq_nonneg l
    linarith
  dsimp
  constructor
  · intro x hvm hvnp1 hq
    exact hf_succ n hn x hvm hvnp1 hq
  constructor
  · ext x
    constructor
    · intro hxnonneg
      exact ⟨Real.sqrt x, tendsto_nonneg x hxnonneg⟩
    · intro hxlim
      by_contra hxnonneg
      exact no_limit_neg x (lt_of_not_ge hxnonneg) hxlim
  · intro x hxnonneg
    exact tendsto_nonneg x hxnonneg
