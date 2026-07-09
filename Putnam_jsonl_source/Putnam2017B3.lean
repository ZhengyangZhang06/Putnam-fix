import Mathlib

open Topology Filter

/--
Suppose that $f(x) = \sum_{i=0}^\infty c_i x^i$ is a power series for which each coefficient $c_i$ is $0$ or $1$. Show that if $f(2/3) = 3/2$, then $f(1/2)$ must be irrational.
-/
theorem putnam_2017_b3
(f : ℝ → ℝ)
(c : ℕ → ℝ)
(hc : ∀ n, c n = 0 ∨ c n = 1)
(hf : ∀ x, f x = ∑' n : ℕ, (c n) * x^n)
: f (2/3) = 3/2 → Irrational (f 1/2) := by
  classical
  intro h23
  let d : ℕ → ℕ := fun n => if c n = 0 then 0 else 1
  have hd : ∀ n, d n = 0 ∨ d n = 1 := by
    intro n
    by_cases h : c n = 0
    · left
      simp [d, h]
    · right
      simp [d, h]
  have hcd : ∀ n, c n = (d n : ℝ) := by
    intro n
    by_cases h : c n = 0
    · simp [d, h]
    · have h1 : c n = 1 := by
        rcases hc n with h0 | h1
        · exact (h h0).elim
        · exact h1
      simp [d, h1]
  have hsumm : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun n => (d n : ℝ) * r ^ n) := by
    intro r hr0 hr1
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hr1) ?_
    intro n
    rcases hd n with hn | hn
    · simp [hn, pow_nonneg hr0 n]
    · simp [hn, abs_of_nonneg hr0]
  have hsum23 : (∑' n : ℕ, (d n : ℝ) * ((2 / 3 : ℝ) ^ n)) = 3 / 2 := by
    calc
      (∑' n : ℕ, (d n : ℝ) * ((2 / 3 : ℝ) ^ n))
          = ∑' n : ℕ, c n * ((2 / 3 : ℝ) ^ n) := by
            apply tsum_congr
            intro n
            rw [hcd n]
      _ = f (2 / 3) := by rw [hf]
      _ = 3 / 2 := h23
  by_contra hrat
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  have hsum12 : (∑' n : ℕ, (d n : ℝ) * ((1 / 2 : ℝ) ^ n)) = (q : ℝ) := by
    calc
      (∑' n : ℕ, (d n : ℝ) * ((1 / 2 : ℝ) ^ n))
          = ∑' n : ℕ, c n * ((1 / 2 : ℝ) ^ n) := by
            apply tsum_congr
            intro n
            rw [hcd n]
      _ = f (1 / 2) := by rw [hf]
      _ = (q : ℝ) := hq
  let tail : ℕ → ℝ := fun n => ∑' k : ℕ, (d (n + k) : ℝ) * ((1 / 2 : ℝ) ^ k)
  have hsumm_shift12 : ∀ n, Summable (fun k => (d (n + k) : ℝ) * ((1 / 2 : ℝ) ^ k)) := by
    intro n
    refine Summable.of_norm_bounded
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)) ?_
    intro k
    rcases hd (n + k) with hk | hk <;> simp [hk]
  have htail0 : tail 0 = (q : ℝ) := by
    simpa [tail] using hsum12
  have htail_rec : ∀ n, tail n = (d n : ℝ) + (1 / 2 : ℝ) * tail (n + 1) := by
    intro n
    dsimp [tail]
    rw [(hsumm_shift12 n).tsum_eq_zero_add]
    simp only [pow_zero, mul_one, Nat.add_zero]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    ring_nf
  have htail_bounds : ∀ n, 0 ≤ tail n ∧ tail n ≤ 2 := by
    intro n
    constructor
    · dsimp [tail]
      exact tsum_nonneg (fun k => by rcases hd (n + k) with hk | hk <;> simp [hk])
    · dsimp [tail]
      have hle := Summable.tsum_mono (hsumm_shift12 n)
        (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
        (fun k => by rcases hd (n + k) with hk | hk <;> simp [hk])
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)] at hle
      norm_num at hle
      exact hle
  let T : ℕ → ℤ :=
    fun n => Nat.rec q.num (fun k z => 2 * (z - (q.den : ℤ) * (d k : ℤ))) n
  have hT_rec : ∀ n, T (n + 1) = 2 * (T n - (q.den : ℤ) * (d n : ℤ)) := by
    intro n
    simp [T]
  have hT_tail : ∀ n, (Int.cast (T n) / (q.den : ℝ)) = tail n := by
    intro n
    induction n with
    | zero =>
        calc
          (Int.cast (T 0) / (q.den : ℝ)) = ((q.num : ℝ) / (q.den : ℝ)) := by simp [T]
          _ = (q : ℝ) := (Rat.cast_def q).symm
          _ = tail 0 := htail0.symm
    | succ n ih =>
        calc
          (Int.cast (T (n + 1)) / (q.den : ℝ))
              = 2 * ((Int.cast (T n) / (q.den : ℝ)) - (d n : ℝ)) := by
                rw [hT_rec]
                have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
                field_simp [hden]
                norm_num
          _ = 2 * (tail n - (d n : ℝ)) := by rw [ih]
          _ = tail (n + 1) := by
                have hrec := htail_rec n
                nlinarith
  have hT_bounds : ∀ n, 0 ≤ T n ∧ T n ≤ 2 * (q.den : ℤ) := by
    intro n
    have hdenpos : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
    have hb := htail_bounds n
    constructor
    · have hdiv : (0 : ℝ) ≤ Int.cast (T n) / (q.den : ℝ) := by
        rw [hT_tail n]
        exact hb.1
      have hmul := mul_le_mul_of_nonneg_left hdiv hdenpos.le
      have hTR : (0 : ℝ) ≤ Int.cast (T n) := by
        field_simp [ne_of_gt hdenpos] at hmul
        linarith
      exact_mod_cast hTR
    · have hdiv : Int.cast (T n) / (q.den : ℝ) ≤ 2 := by
        rw [hT_tail n]
        exact hb.2
      have hmul := mul_le_mul_of_nonneg_left hdiv hdenpos.le
      have hTR : Int.cast (T n) ≤ 2 * (q.den : ℝ) := by
        field_simp [ne_of_gt hdenpos] at hmul
        linarith
      exact_mod_cast hTR
  have hd_of_lt : ∀ n, T n < (q.den : ℤ) → d n = 0 := by
    intro n hlt
    rcases hd n with h0 | h1
    · exact h0
    · exfalso
      have hdenpos : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
      have hltR : Int.cast (T n) < (q.den : ℝ) := by exact_mod_cast hlt
      have htail_lt : tail n < 1 := by
        rw [← hT_tail n]
        rw [div_lt_iff₀ hdenpos]
        simpa using hltR
      have htail_ge : 1 ≤ tail n := by
        rw [htail_rec n, h1]
        nlinarith [((htail_bounds (n + 1)).1)]
      linarith
  have hd_of_gt : ∀ n, (q.den : ℤ) < T n → d n = 1 := by
    intro n hgt
    rcases hd n with h0 | h1
    · exfalso
      have hdenpos : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
      have hgtR : (q.den : ℝ) < Int.cast (T n) := by exact_mod_cast hgt
      have htail_gt : 1 < tail n := by
        rw [← hT_tail n]
        rw [lt_div_iff₀ hdenpos]
        simpa using hgtR
      have htail_le : tail n ≤ 1 := by
        rw [htail_rec n, h0]
        nlinarith [((htail_bounds (n + 1)).2)]
      linarith
    · exact h1
  have hzero_const : ∀ r, T r = 0 → ∀ k, d (r + k) = 0 := by
    intro r hr k
    have hdenposZ : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.den_pos
    have hstep : ∀ k, T (r + k) = 0 ∧ d (r + k) = 0 := by
      intro k
      induction k with
      | zero =>
          have hlt : T r < (q.den : ℤ) := by omega
          exact ⟨by simpa using hr, hd_of_lt r hlt⟩
      | succ k ih =>
          have hprevT : T (r + k) = 0 := ih.1
          have hprevd : d (r + k) = 0 := ih.2
          have hnextT : T (r + (k + 1)) = 0 := by
            have hrec := hT_rec (r + k)
            rw [hprevT, hprevd] at hrec
            have hidx : r + (k + 1) = r + k + 1 := by omega
            rw [hidx]
            simpa using hrec
          have hlt : T (r + (k + 1)) < (q.den : ℤ) := by omega
          exact ⟨hnextT, hd_of_lt (r + (k + 1)) hlt⟩
    exact (hstep k).2
  have htop_const : ∀ r, T r = 2 * (q.den : ℤ) → ∀ k, d (r + k) = 1 := by
    intro r hr k
    have hdenposZ : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.den_pos
    have hstep : ∀ k, T (r + k) = 2 * (q.den : ℤ) ∧ d (r + k) = 1 := by
      intro k
      induction k with
      | zero =>
          have hgt : (q.den : ℤ) < T r := by omega
          exact ⟨by simpa using hr, hd_of_gt r hgt⟩
      | succ k ih =>
          have hprevT : T (r + k) = 2 * (q.den : ℤ) := ih.1
          have hprevd : d (r + k) = 1 := ih.2
          have hnextT : T (r + (k + 1)) = 2 * (q.den : ℤ) := by
            have hrec := hT_rec (r + k)
            rw [hprevT, hprevd] at hrec
            have hidx : r + (k + 1) = r + k + 1 := by omega
            rw [hidx]
            ring_nf at hrec ⊢
            exact hrec
          have hgt : (q.den : ℤ) < T (r + (k + 1)) := by omega
          exact ⟨hnextT, hd_of_gt (r + (k + 1)) hgt⟩
    exact (hstep k).2
  have hperiod : ∃ N p, 0 < p ∧ ∀ k, d (N + p + k) = d (N + k) := by
    obtain ⟨m, n, hmn, hmnT⟩ :
        ∃ m n, m < n ∧ T m = T n :=
      Set.Finite.exists_lt_map_eq_of_forall_mem
        (t := Set.Icc (0 : ℤ) (2 * (q.den : ℤ))) (f := T)
        (fun n => Set.mem_Icc.mpr (hT_bounds n)) (Set.finite_Icc _ _)
    letI : Decidable (∃ r, m ≤ r ∧ T r = (q.den : ℤ)) := Classical.propDecidable _
    by_cases hhit : ∃ r, m ≤ r ∧ T r = (q.den : ℤ)
    case pos =>
      obtain ⟨r, -, hr⟩ := hhit
      rcases hd r with hr0 | hr1
      · refine ⟨r + 1, 1, by norm_num, ?_⟩
        have hnext : T (r + 1) = 2 * (q.den : ℤ) := by
          have hrec := hT_rec r
          rw [hr, hr0] at hrec
          ring_nf at hrec ⊢
          exact hrec
        have hconst := htop_const (r + 1) hnext
        intro k
        rw [show r + 1 + 1 + k = r + 1 + (1 + k) by omega, hconst (1 + k), hconst k]
      · refine ⟨r + 1, 1, by norm_num, ?_⟩
        have hnext : T (r + 1) = 0 := by
          have hrec := hT_rec r
          rw [hr, hr1] at hrec
          ring_nf at hrec ⊢
          exact hrec
        have hconst := hzero_const (r + 1) hnext
        intro k
        rw [show r + 1 + 1 + k = r + 1 + (1 + k) by omega, hconst (1 + k), hconst k]
    case neg =>
      have hcycle : ∀ k, T (m + k) = T (n + k) ∧ d (m + k) = d (n + k) := by
        intro k
        induction k with
        | zero =>
            have hmne : T m ≠ (q.den : ℤ) := by
              intro hm
              exact hhit ⟨m, le_rfl, hm⟩
            have hdigit : d m = d n := by
              rcases lt_trichotomy (T m) (q.den : ℤ) with hlt | heq | hgt
              · have hlt' : T n < (q.den : ℤ) := by rw [← hmnT]; exact hlt
                rw [hd_of_lt m hlt, hd_of_lt n hlt']
              · exact (hmne heq).elim
              · have hgt' : (q.den : ℤ) < T n := by rw [← hmnT]; exact hgt
                rw [hd_of_gt m hgt, hd_of_gt n hgt']
            simpa using And.intro hmnT hdigit
        | succ k ih =>
            have hTnext : T (m + (k + 1)) = T (n + (k + 1)) := by
              have hmrec := hT_rec (m + k)
              have hnrec := hT_rec (n + k)
              have hmidx : m + (k + 1) = m + k + 1 := by omega
              have hnidx : n + (k + 1) = n + k + 1 := by omega
              rw [hmidx, hnidx, hmrec, hnrec, ih.1, ih.2]
            have hmle : m ≤ m + (k + 1) := by omega
            have hmne : T (m + (k + 1)) ≠ (q.den : ℤ) := by
              intro hm
              exact hhit ⟨m + (k + 1), hmle, hm⟩
            have hdigit : d (m + (k + 1)) = d (n + (k + 1)) := by
              rcases lt_trichotomy (T (m + (k + 1))) (q.den : ℤ) with hlt | heq | hgt
              · have hlt' : T (n + (k + 1)) < (q.den : ℤ) := by rw [← hTnext]; exact hlt
                rw [hd_of_lt (m + (k + 1)) hlt, hd_of_lt (n + (k + 1)) hlt']
              · exact (hmne heq).elim
              · have hgt' : (q.den : ℤ) < T (n + (k + 1)) := by rw [← hTnext]; exact hgt
                rw [hd_of_gt (m + (k + 1)) hgt, hd_of_gt (n + (k + 1)) hgt']
            exact ⟨hTnext, hdigit⟩
      refine ⟨m, n - m, by omega, ?_⟩
      intro k
      have hk := (hcycle k).2
      have hidx : m + (n - m) + k = n + k := by omega
      rw [hidx]
      exact hk.symm
  obtain ⟨N, p, hp, hper⟩ := hperiod
  have hsumm_shift23 : ∀ n, Summable (fun k => (d (n + k) : ℝ) * ((2 / 3 : ℝ) ^ k)) := by
    intro n
    refine Summable.of_norm_bounded
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 / 3 : ℝ) < 1)) ?_
    intro k
    rcases hd (n + k) with hk | hk
    · simp [hk, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) k]
    · simp [hk]
  let r : ℝ := 2 / 3
  let P : ℝ := ∑ i ∈ Finset.range N, (d i : ℝ) * r ^ i
  let U : ℝ := ∑' k : ℕ, (d (N + k) : ℝ) * r ^ k
  let A : ℝ := ∑ k ∈ Finset.range p, (d (N + k) : ℝ) * r ^ k
  have hSsplit : (3 / 2 : ℝ) = P + r ^ N * U := by
    calc
      (3 / 2 : ℝ) = ∑' n : ℕ, (d n : ℝ) * r ^ n := by simpa [r] using hsum23.symm
      _ = P + ∑' i : ℕ, (d (i + N) : ℝ) * r ^ (i + N) := by
            dsimp [P, r]
            exact ((hsumm (2 / 3) (by norm_num : (0 : ℝ) ≤ 2 / 3)
              (by norm_num : (2 / 3 : ℝ) < 1)).sum_add_tsum_nat_add N).symm
      _ = P + r ^ N * U := by
            congr 1
            dsimp [U, r]
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            have hidx : k + N = N + k := by omega
            rw [hidx]
            ring
  have hUeq : U = A + r ^ p * U := by
    calc
      U = A + ∑' i : ℕ, (d (N + (i + p)) : ℝ) * r ^ (i + p) := by
            dsimp [U, A, r]
            exact ((hsumm_shift23 N).sum_add_tsum_nat_add p).symm
      _ = A + r ^ p * U := by
            congr 1
            dsimp [U, r]
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            have hidx : N + (k + p) = N + p + k := by omega
            rw [hidx, hper k]
            ring
  have hden : 1 - r ^ p ≠ 0 := by
    have hpowlt : r ^ p < 1 := by
      exact pow_lt_one₀ (by norm_num [r]) (by norm_num [r]) hp.ne'
    linarith
  have hUsol : U = A / (1 - r ^ p) := by
    have hmul : U * (1 - r ^ p) = A := by nlinarith [hUeq]
    rw [eq_div_iff hden]
    exact hmul
  have hSsol : (3 / 2 : ℝ) = P + (2 / 3 : ℝ) ^ N * (A / (1 - (2 / 3 : ℝ) ^ p)) := by
    simpa [r, hUsol] using hSsplit
  have hscaled :
      (3 / 2 : ℝ) * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p) =
        P * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p) +
          A * (2 : ℝ) ^ N * (3 : ℝ) ^ p := by
    have h3N : (3 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3p : (3 : ℝ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
    have hden' : 1 - (2 / 3 : ℝ) ^ p ≠ 0 := by
      simpa [r] using hden
    have hpowN : ((2 / 3 : ℝ) ^ N) * (3 : ℝ) ^ N = (2 : ℝ) ^ N := by
      rw [div_pow]
      field_simp [h3N]
    have hdeneq : (1 - (2 / 3 : ℝ) ^ p) * (3 : ℝ) ^ p = (3 : ℝ) ^ p - (2 : ℝ) ^ p := by
      have hpowp : ((2 / 3 : ℝ) ^ p) * (3 : ℝ) ^ p = (2 : ℝ) ^ p := by
        rw [div_pow]
        field_simp [h3p]
      rw [sub_mul, one_mul, hpowp]
    have hfac :
        (1 - (2 / 3 : ℝ) ^ p)⁻¹ * (2 / 3 : ℝ) ^ N * (3 : ℝ) ^ N *
            ((3 : ℝ) ^ p - (2 : ℝ) ^ p)
          = (2 : ℝ) ^ N * (3 : ℝ) ^ p := by
      calc
        (1 - (2 / 3 : ℝ) ^ p)⁻¹ * (2 / 3 : ℝ) ^ N * (3 : ℝ) ^ N *
            ((3 : ℝ) ^ p - (2 : ℝ) ^ p)
            = ((2 / 3 : ℝ) ^ N * (3 : ℝ) ^ N) *
                ((1 - (2 / 3 : ℝ) ^ p)⁻¹ * ((3 : ℝ) ^ p - (2 : ℝ) ^ p)) := by ring
        _ = (2 : ℝ) ^ N *
                ((1 - (2 / 3 : ℝ) ^ p)⁻¹ *
                  ((1 - (2 / 3 : ℝ) ^ p) * (3 : ℝ) ^ p)) := by rw [hpowN, hdeneq]
        _ = (2 : ℝ) ^ N * (3 : ℝ) ^ p := by field_simp [hden']
    calc
      (3 / 2 : ℝ) * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p)
          = (P + ((2 / 3 : ℝ) ^ N) * (A / (1 - (2 / 3 : ℝ) ^ p))) *
              (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p) := by rw [hSsol]
      _ = P * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p) +
            A * ((1 - (2 / 3 : ℝ) ^ p)⁻¹ * (2 / 3 : ℝ) ^ N * (3 : ℝ) ^ N *
              ((3 : ℝ) ^ p - (2 : ℝ) ^ p)) := by ring
      _ = P * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p) +
            A * (2 : ℝ) ^ N * (3 : ℝ) ^ p := by rw [hfac]; ring
  let zP : ℤ :=
    ∑ i ∈ Finset.range N,
      (d i : ℤ) * (2 : ℤ) ^ i * (3 : ℤ) ^ (N - i) *
        ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
  let zA : ℤ :=
    ∑ j ∈ Finset.range p,
      (d (N + j) : ℤ) * (2 : ℤ) ^ (N + j) * (3 : ℤ) ^ (p - j)
  have hPint :
      P * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p) = (zP : ℝ) := by
    dsimp [P, zP, r]
    rw [Finset.sum_mul, Finset.sum_mul]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    have hN : N = i + (N - i) := by omega
    rw [hN, pow_add]
    rw [div_pow]
    field_simp [pow_ne_zero i (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hAint : A * (2 : ℝ) ^ N * (3 : ℝ) ^ p = (zA : ℝ) := by
    dsimp [A, zA, r]
    rw [Finset.sum_mul, Finset.sum_mul]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hpj : p = j + (p - j) := by omega
    rw [hpj, pow_add]
    norm_num
    rw [show (2 : ℝ) ^ (N + j) = (2 : ℝ) ^ N * (2 : ℝ) ^ j by rw [pow_add]]
    rw [div_pow]
    field_simp [pow_ne_zero j (by norm_num : (3 : ℝ) ≠ 0)]
  have hleft_int :
      ∃ z : ℤ,
        (3 / 2 : ℝ) * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p) = (z : ℝ) := by
    refine ⟨zP + zA, ?_⟩
    rw [hscaled, hPint, hAint]
    norm_num
  obtain ⟨z, hz⟩ := hleft_int
  have hzint :
      (2 * z : ℤ) = (3 : ℤ) ^ (N + 1) * ((3 : ℤ) ^ p - (2 : ℤ) ^ p) := by
    apply (Int.cast_injective (α := ℝ))
    calc
      ((2 * z : ℤ) : ℝ) = 2 * (z : ℝ) := by norm_num
      _ = 2 * ((3 / 2 : ℝ) * (3 : ℝ) ^ N * ((3 : ℝ) ^ p - (2 : ℝ) ^ p)) := by rw [hz]
      _ = (((3 : ℤ) ^ (N + 1) * ((3 : ℤ) ^ p - (2 : ℤ) ^ p) : ℤ) : ℝ) := by
            push_cast
            rw [pow_succ']
            norm_num
            ring
  have hodd_rhs : Odd ((3 : ℤ) ^ (N + 1) * ((3 : ℤ) ^ p - (2 : ℤ) ^ p)) := by
    have hodd3N : Odd ((3 : ℤ) ^ (N + 1)) := Odd.pow (by norm_num)
    have hodd3p : Odd ((3 : ℤ) ^ p) := Odd.pow (by norm_num)
    have heven2p : Even ((2 : ℤ) ^ p) :=
      Even.pow_of_ne_zero (show Even (2 : ℤ) by norm_num) hp.ne'
    exact hodd3N.mul (hodd3p.sub_even heven2p)
  have heven_lhs : Even (2 * z : ℤ) := ⟨z, by ring⟩
  have hnot_even_rhs : ¬ Even ((3 : ℤ) ^ (N + 1) * ((3 : ℤ) ^ p - (2 : ℤ) ^ p)) :=
    (Int.not_even_iff_odd).2 hodd_rhs
  exact hnot_even_rhs (hzint ▸ heven_lhs)
