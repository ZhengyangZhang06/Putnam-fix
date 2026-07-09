import Mathlib

open Set

private lemma putnam_2022_a6_geom_sum
    (r : ℂ) (n : ℕ) (hpow : r ^ (2 * n + 1) = -1) (hr : 1 + r ≠ 0) :
    (∑ a ∈ Finset.range n, (r ^ (2 * a + 1) - r ^ (2 * a + 2))) = 1 := by
  have htel : ∀ n : ℕ,
      (1 + r) * (∑ a ∈ Finset.range n, (r ^ (2 * a + 1) - r ^ (2 * a + 2))) =
        r - r ^ (2 * n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        rw [mul_add, ih]
        ring_nf
  have h := htel n
  rw [hpow] at h
  have h2 : (1 + r) * (∑ a ∈ Finset.range n, (r ^ (2 * a + 1) - r ^ (2 * a + 2))) =
      (1 + r) * 1 := by
    simpa [sub_neg_eq_add, add_comm, add_left_comm, add_assoc] using h
  exact mul_left_cancel₀ hr h2

private lemma putnam_2022_a6_exp_pow_eq_neg_one
    (N : ℕ) (hN : N ≠ 0) (q : ℤ) (hqodd : Odd q) :
    (Complex.exp (((q : ℂ) * ((Real.pi : ℂ) / (N : ℂ))) * Complex.I)) ^ N = -1 := by
  rw [← Complex.exp_nat_mul]
  have harg : (N : ℂ) * (((q : ℂ) * ((Real.pi : ℂ) / (N : ℂ))) * Complex.I) =
      (q : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    field_simp [Nat.cast_ne_zero.mpr hN]
  rw [harg]
  rw [Complex.exp_int_mul]
  simpa using (hqodd.neg_one_zpow (α := ℂ))

private lemma putnam_2022_a6_exp_mul_I_ne_neg_one {θ : ℝ} (hθ : |θ| < Real.pi) :
    Complex.exp ((θ : ℂ) * Complex.I) ≠ -1 := by
  intro h
  have hre : (Complex.exp ((θ : ℂ) * Complex.I)).re = (-1 : ℂ).re := congrArg Complex.re h
  have hcos : Real.cos θ = -1 := by
    simpa [Complex.exp_mul_I, Complex.ofReal_re] using hre
  have hgt : -1 < Real.cos θ := by
    by_cases hnonneg : 0 ≤ θ
    · have hlt : θ < Real.pi := lt_of_le_of_lt (le_abs_self θ) hθ
      have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi hnonneg le_rfl hlt
      simpa using hcoslt
    · have hneg : 0 ≤ -θ := by linarith
      have hlt : -θ < Real.pi := by
        have := abs_lt.mp hθ
        linarith
      have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi hneg le_rfl hlt
      rw [Real.cos_neg] at hcoslt
      simpa using hcoslt
  linarith

private lemma putnam_2022_a6_sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    (∑ i ∈ Finset.Icc 1 n, f i) = ∑ a ∈ Finset.range n, f (a + 1) := by
  have hset : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext i
    simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hset]
  simpa [Nat.add_comm] using (Finset.sum_Ico_eq_sum_range f 1 (n + 1))

private lemma putnam_2022_a6_geom_sum_Icc
    (r : ℂ) (n : ℕ) (hpow : r ^ (2 * n + 1) = -1) (hr : 1 + r ≠ 0) :
    (∑ i ∈ Finset.Icc 1 n, (r ^ (2 * i - 1) - r ^ (2 * i))) = 1 := by
  rw [putnam_2022_a6_sum_Icc_one_eq_range]
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using putnam_2022_a6_geom_sum r n hpow hr

private lemma putnam_2022_a6_exp_term
    (N j p a : ℕ) (ha : a ≤ p) :
    Complex.exp ((((j : ℂ) * ((Real.pi : ℂ) / (N : ℂ))) * Complex.I)) ^ a *
      Complex.exp (-((j : ℂ) * ((Real.pi : ℂ) / (N : ℂ))) * Complex.I) ^ (p - a)
    =
      (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
        ((Real.pi : ℂ) / (N : ℂ))) * Complex.I)) ^ j := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  rw [← Complex.exp_nat_mul]
  congr 1
  have hpa : ((p - a : ℕ) : ℂ) = (p : ℂ) - (a : ℂ) := by
    norm_num [Nat.cast_sub ha]
  have hq : ((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) = (2 * (a : ℂ) - (p : ℂ))) := by
    have h : ((a : ℤ) - (p - a : ℤ) : ℤ) = 2 * (a : ℤ) - (p : ℤ) := by
      omega
    rw [h]
    norm_num
  rw [hpa, hq]
  ring_nf

private lemma putnam_2022_a6_two_cos_pow
    (N p j : ℕ) :
    (((2 : ℝ) * Real.cos ((j : ℝ) * Real.pi / (N : ℝ))) ^ p : ℂ) =
      ∑ a ∈ Finset.range (p + 1), (p.choose a : ℂ) *
        (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
          ((Real.pi : ℂ) / (N : ℂ))) * Complex.I)) ^ j := by
  change ((2 : ℂ) * ↑(Real.cos ((j : ℝ) * Real.pi / (N : ℝ)))) ^ p = _
  rw [Complex.ofReal_cos]
  have hangle : (((j : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) =
      (j : ℂ) * ((Real.pi : ℂ) / (N : ℂ)) := by
    norm_num [Complex.ofReal_mul, Complex.ofReal_div]
    ring
  rw [hangle]
  rw [Complex.two_cos]
  rw [add_pow]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hale : a ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  rw [putnam_2022_a6_exp_term N j p a hale]
  ring

private lemma putnam_2022_a6_frequency_sum
    (n p a : ℕ) (hpodd : Odd p) (hpN : p < 2 * n + 1)
    (ha : a ∈ Finset.range (p + 1)) :
    let q : ℤ := (a : ℤ) - (p - a : ℤ)
    (∑ i ∈ Finset.Icc 1 n,
        ((Complex.exp (((q : ℂ) *
            ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i - 1) -
          (Complex.exp (((q : ℂ) *
            ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i))) = 1 := by
  dsimp
  let q : ℤ := (a : ℤ) - (p - a : ℤ)
  have hale : a ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  have hqodd : Odd q := by
    rcases hpodd with ⟨s, hs⟩
    use (a : ℤ) - (s : ℤ) - 1
    dsimp [q]
    omega
  have htheta : |((q : ℝ) * (Real.pi / ((2 * n + 1 : ℕ) : ℝ)))| < Real.pi := by
    have hqabsZ : |q| ≤ (p : ℤ) := by
      dsimp [q]
      rw [abs_le]
      constructor <;> omega
    have hqabsR : |(q : ℝ)| ≤ (p : ℝ) := by
      exact_mod_cast hqabsZ
    have hNpos : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
    have hfrac_nonneg : 0 ≤ Real.pi / (((2 * n + 1 : ℕ) : ℝ)) := by positivity
    calc
      |(q : ℝ) * (Real.pi / (((2 * n + 1 : ℕ) : ℝ)))|
          = |(q : ℝ)| * (Real.pi / (((2 * n + 1 : ℕ) : ℝ))) := by
            rw [abs_mul, abs_of_nonneg hfrac_nonneg]
      _ ≤ (p : ℝ) * (Real.pi / (((2 * n + 1 : ℕ) : ℝ))) := by gcongr
      _ < (((2 * n + 1 : ℕ) : ℝ)) *
          (Real.pi / (((2 * n + 1 : ℕ) : ℝ))) := by gcongr
      _ = Real.pi := by field_simp [ne_of_gt hNpos]
  let r : ℂ := Complex.exp (((q : ℂ) *
    ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)
  have hpow : r ^ (2 * n + 1) = -1 := by
    dsimp [r]
    exact putnam_2022_a6_exp_pow_eq_neg_one (2 * n + 1) (by omega) q hqodd
  have hr : 1 + r ≠ 0 := by
    have hne : r ≠ -1 := by
      dsimp [r]
      have harg : ((q : ℂ) * ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I =
          (((q : ℝ) * (Real.pi / (((2 * n + 1 : ℕ) : ℝ))) : ℝ) : ℂ) * Complex.I := by
        norm_num [Complex.ofReal_mul, Complex.ofReal_div]
      rw [harg]
      exact putnam_2022_a6_exp_mul_I_ne_neg_one htheta
    intro h
    apply hne
    calc
      r = (1 + r) - 1 := by ring
      _ = -1 := by rw [h]; ring
  exact putnam_2022_a6_geom_sum_Icc r n hpow hr

private lemma putnam_2022_a6_scaled_sum
    (s : Finset ℕ) (p : ℕ) (A B : ℕ → ℝ) :
    ((2 : ℂ) ^ p) * Complex.ofReal (∑ i ∈ s, (A i ^ p - B i ^ p))
      = ∑ i ∈ s,
          (Complex.ofReal (((2 : ℝ) * A i) ^ p) -
            Complex.ofReal (((2 : ℝ) * B i) ^ p)) := by
  have hsum := Complex.ofReal_sum s (fun i => A i ^ p - B i ^ p)
  rw [hsum]
  simp_rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  norm_num
  ring

private lemma putnam_2022_a6_sum_swap
    (s t : Finset ℕ) (c : ℕ → ℂ) (R S : ℕ → ℕ → ℂ) :
    (∑ i ∈ s, ((∑ a ∈ t, c a * R a i) - (∑ a ∈ t, c a * S a i))) =
      ∑ a ∈ t, c a * (∑ i ∈ s, (R a i - S a i)) := by
  calc
    (∑ i ∈ s, ((∑ a ∈ t, c a * R a i) - (∑ a ∈ t, c a * S a i)))
        = ∑ i ∈ s, ∑ a ∈ t, (c a * R a i - c a * S a i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_sub_distrib]
    _ = ∑ a ∈ t, ∑ i ∈ s, (c a * R a i - c a * S a i) := by
          rw [Finset.sum_comm]
    _ = ∑ a ∈ t, c a * (∑ i ∈ s, (R a i - S a i)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

private lemma putnam_2022_a6_alt_cos_power_sum
    (n p : ℕ) (hpodd : Odd p) (hpN : p < 2 * n + 1) :
    (∑ i ∈ Finset.Icc 1 n,
      (Real.cos (((2 * i - 1 : ℕ) : ℝ) * Real.pi / ((2 * n + 1 : ℕ) : ℝ)) ^ p -
        Real.cos (((2 * i : ℕ) : ℝ) * Real.pi / ((2 * n + 1 : ℕ) : ℝ)) ^ p)) = 1 := by
  apply Complex.ofReal_injective
  have htwo : ((2 : ℂ) ^ p) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ htwo
  calc
    ((2 : ℂ) ^ p) * Complex.ofReal
        (∑ i ∈ Finset.Icc 1 n,
          (Real.cos (((2 * i - 1 : ℕ) : ℝ) * Real.pi / ((2 * n + 1 : ℕ) : ℝ)) ^ p -
            Real.cos (((2 * i : ℕ) : ℝ) * Real.pi / ((2 * n + 1 : ℕ) : ℝ)) ^ p))
        = ∑ i ∈ Finset.Icc 1 n,
            (Complex.ofReal (((2 : ℝ) *
                Real.cos (((2 * i - 1 : ℕ) : ℝ) * Real.pi /
                  ((2 * n + 1 : ℕ) : ℝ))) ^ p) -
              Complex.ofReal (((2 : ℝ) *
                Real.cos (((2 * i : ℕ) : ℝ) * Real.pi /
                  ((2 * n + 1 : ℕ) : ℝ))) ^ p)) := by
          exact putnam_2022_a6_scaled_sum (Finset.Icc 1 n) p
            (fun i => Real.cos (((2 * i - 1 : ℕ) : ℝ) * Real.pi /
              ((2 * n + 1 : ℕ) : ℝ)))
            (fun i => Real.cos (((2 * i : ℕ) : ℝ) * Real.pi /
              ((2 * n + 1 : ℕ) : ℝ)))
    _ = ∑ i ∈ Finset.Icc 1 n,
          ((∑ a ∈ Finset.range (p + 1), (p.choose a : ℂ) *
              (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
                ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i - 1)) -
            (∑ a ∈ Finset.range (p + 1), (p.choose a : ℂ) *
              (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
                ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hodd := putnam_2022_a6_two_cos_pow (2 * n + 1) p (2 * i - 1)
          have heven := putnam_2022_a6_two_cos_pow (2 * n + 1) p (2 * i)
          have hodd' :
              Complex.ofReal (((2 : ℝ) *
                Real.cos (((2 * i - 1 : ℕ) : ℝ) * Real.pi /
                  ((2 * n + 1 : ℕ) : ℝ))) ^ p) =
                ∑ a ∈ Finset.range (p + 1), (p.choose a : ℂ) *
                  (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
                    ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^
                    (2 * i - 1) := by
            simpa [Complex.ofReal_pow, Complex.ofReal_mul] using hodd
          have heven' :
              Complex.ofReal (((2 : ℝ) *
                Real.cos (((2 * i : ℕ) : ℝ) * Real.pi /
                  ((2 * n + 1 : ℕ) : ℝ))) ^ p) =
                ∑ a ∈ Finset.range (p + 1), (p.choose a : ℂ) *
                  (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
                    ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^
                    (2 * i) := by
            simpa [Complex.ofReal_pow, Complex.ofReal_mul] using heven
          exact congrArg₂ (fun x y : ℂ => x - y) hodd' heven'
    _ = ∑ a ∈ Finset.range (p + 1), (p.choose a : ℂ) *
          (∑ i ∈ Finset.Icc 1 n,
            ((Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
              ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i - 1) -
              (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
                ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i))) := by
          exact putnam_2022_a6_sum_swap (Finset.Icc 1 n) (Finset.range (p + 1))
            (fun a => (p.choose a : ℂ))
            (fun a i => (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
              ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i - 1))
            (fun a i => (Complex.exp (((((a : ℤ) - (p - a : ℤ) : ℤ) : ℂ) *
              ((Real.pi : ℂ) / ((2 * n + 1 : ℕ) : ℂ))) * Complex.I)) ^ (2 * i))
    _ = ∑ a ∈ Finset.range (p + 1), (p.choose a : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [putnam_2022_a6_frequency_sum n p a hpodd hpN ha]
          ring
    _ = (2 : ℂ) ^ p := by
          norm_num [← Nat.cast_sum, Nat.sum_range_choose]
    _ = ((2 : ℂ) ^ p) * Complex.ofReal (1 : ℝ) := by norm_num

private lemma putnam_2022_a6_cheb_strictMono
    (N : ℕ) (hN : 0 < N) :
    StrictMono (fun j : ℕ =>
      if j ≤ N then -Polynomial.Chebyshev.node N j else (j : ℝ)) := by
  intro a b hab
  by_cases hb : b ≤ N
  · have ha : a ≤ N := (Nat.le_of_lt hab).trans hb
    simp [ha, hb]
    exact Polynomial.Chebyshev.node_lt hb hab
  · by_cases ha : a ≤ N
    · simp [ha, hb]
      have hmem : Polynomial.Chebyshev.node N a ∈ Set.Icc (-1) 1 :=
        Polynomial.Chebyshev.node_mem_Icc
      have hle : -Polynomial.Chebyshev.node N a ≤ 1 := by
        linarith [hmem.1]
      have hbgt : 1 < (b : ℝ) := by
        exact_mod_cast (by omega : 1 < b)
      exact lt_of_le_of_lt hle hbgt
    · have hb' : ¬b ≤ N := hb
      simp [ha, hb']
      exact_mod_cast hab

private lemma putnam_2022_a6_newton_eval
    (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) (u : σ → ℝ) :
    (k : ℝ) * ((Finset.univ.val.map u).esymm k) =
      ((-1 : ℝ) ^ (k + 1)) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        ((-1 : ℝ) ^ a.1) * ((Finset.univ.val.map u).esymm a.1) *
          (∑ i : σ, u i ^ a.2) := by
  have h := congrArg (MvPolynomial.aeval u) (MvPolynomial.mul_esymm_eq_sum σ ℝ k)
  simpa [MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum,
    map_sum, map_mul, map_pow] using h

private lemma putnam_2022_a6_esymm_eq_of_psum_eq
    (σ : Type*) [Fintype σ] [DecidableEq σ] (u v : σ → ℝ)
    (hpsum : ∀ k, 1 ≤ k → k ≤ Fintype.card σ →
      (∑ i : σ, u i ^ k) = ∑ i : σ, v i ^ k) :
    ∀ k, k ≤ Fintype.card σ →
      (Finset.univ.val.map u).esymm k = (Finset.univ.val.map v).esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hkD
      cases k with
      | zero => simp [Multiset.esymm]
      | succ k =>
          have hu := putnam_2022_a6_newton_eval σ (k + 1) u
          have hv := putnam_2022_a6_newton_eval σ (k + 1) v
          have hterms :
              (∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                ((-1 : ℝ) ^ a.1) * ((Finset.univ.val.map u).esymm a.1) *
                  (∑ i : σ, u i ^ a.2)) =
              (∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                ((-1 : ℝ) ^ a.1) * ((Finset.univ.val.map v).esymm a.1) *
                  (∑ i : σ, v i ^ a.2)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.mem_filter] at ha
            have hsum : a.1 + a.2 = k + 1 := Finset.mem_antidiagonal.mp ha.1
            have ha1lt : a.1 < k + 1 := ha.2
            have ha1D : a.1 ≤ Fintype.card σ := by omega
            have ha2pos : 1 ≤ a.2 := by omega
            have ha2D : a.2 ≤ Fintype.card σ := by omega
            have he := ih a.1 ha1lt ha1D
            have hp := hpsum a.2 ha2pos ha2D
            rw [he, hp]
          have hmul :
              ((k + 1 : ℝ) * ((Finset.univ.val.map u).esymm (k + 1))) =
              ((k + 1 : ℝ) * ((Finset.univ.val.map v).esymm (k + 1))) := by
            calc
              ((k + 1 : ℝ) * ((Finset.univ.val.map u).esymm (k + 1)))
                  = ((-1 : ℝ) ^ (k + 1 + 1)) *
                    ∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                      ((-1 : ℝ) ^ a.1) * ((Finset.univ.val.map u).esymm a.1) *
                        (∑ i : σ, u i ^ a.2) := by
                    simpa [Nat.cast_add, Nat.cast_one] using hu
              _ = ((-1 : ℝ) ^ (k + 1 + 1)) *
                    ∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                      ((-1 : ℝ) ^ a.1) * ((Finset.univ.val.map v).esymm a.1) *
                        (∑ i : σ, v i ^ a.2) := by
                    rw [hterms]
              _ = ((k + 1 : ℝ) * ((Finset.univ.val.map v).esymm (k + 1))) := by
                    simpa [Nat.cast_add, Nat.cast_one] using hv.symm
          exact mul_left_cancel₀ (by positivity : (k + 1 : ℝ) ≠ 0) hmul

private lemma putnam_2022_a6_prod_poly_eq_of_esymm_eq
    (σ : Type*) [Fintype σ] (u v : σ → ℝ)
    (hesymm : ∀ k, k ≤ Fintype.card σ →
      (Finset.univ.val.map u).esymm k = (Finset.univ.val.map v).esymm k) :
    (Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (u i))).prod =
      (Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (v i))).prod := by
  have hu : Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (u i)) =
      (Finset.univ.val.map u).map (fun t : ℝ => Polynomial.X - Polynomial.C t) := by
    simp [Multiset.map_map]
  have hv : Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (v i)) =
      (Finset.univ.val.map v).map (fun t : ℝ => Polynomial.X - Polynomial.C t) := by
    simp [Multiset.map_map]
  rw [hu, hv]
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
  have hcardu : (Finset.univ.val.map u).card = Fintype.card σ := by simp
  have hcardv : (Finset.univ.val.map v).card = Fintype.card σ := by simp
  simp_rw [hcardu, hcardv]
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact congrArg (fun z => (-1 : Polynomial ℝ) ^ k * (Polynomial.C z *
    Polynomial.X ^ (Fintype.card σ - k))) (hesymm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

-- Note: uses (ℕ → ℝ) instead of (Fin (2 * n) → ℝ)
-- (fun n : ℕ => n)
/--
Let $n$ be a positive integer. Determine, in terms of $n$, the largest integer $m$ with the following property: There exist real numbers $x_1,\dots,x_{2n}$ with $-1< x_1< x_2<\cdots< x_{2n}<1$ such that the sum of the lengths of the $n$ intervals $[x_1^{2k-1},x_2^{2k-1}],[x_3^{2k-1},x_4^{2k-1}],\dots,[x_{2n-1}^{2k-1},x_{2n}^{2k-1}]$ is equal to $1$ for all integers $k$ with $1 \leq k \leq m$.
-/
theorem putnam_2022_a6
    (n : ℕ) (hn : 0 < n) :
    IsGreatest
      {m : ℕ | ∃ x : ℕ → ℝ,
        StrictMono x ∧ -1 < x 1 ∧ x (2 * n) < 1 ∧
        ∀ k ∈ Icc 1 m, ∑ i ∈ Icc 1 n, ((x (2 * i) : ℝ) ^ (2 * k - 1) - (x (2 * i - 1)) ^ (2 * k - 1)) = 1}
    (((fun n : ℕ => n) : ℕ → ℕ ) n) := by
  classical
  dsimp
  constructor
  · let N : ℕ := 2 * n + 1
    let x : ℕ → ℝ := fun j =>
      if j ≤ N then -Polynomial.Chebyshev.node N j else (j : ℝ)
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · exact putnam_2022_a6_cheb_strictMono N (by dsimp [N]; omega)
    · have h1N : 1 ≤ N := by dsimp [N]; omega
      have hnode : Polynomial.Chebyshev.node N 1 < 1 := by
        have hlt := Polynomial.Chebyshev.node_lt (n := N) (i := 0) (j := 1) h1N
          (by norm_num)
        simpa [Polynomial.Chebyshev.node_eq_one] using hlt
      simp [x, N, h1N]
      linarith
    · have h2nN : 2 * n ≤ N := by dsimp [N]; omega
      have hNne : N ≠ 0 := by dsimp [N]; omega
      have hlt2nN : 2 * n < N := by dsimp [N]; omega
      have hnode : -1 < Polynomial.Chebyshev.node N (2 * n) := by
        have hlt := Polynomial.Chebyshev.node_lt (n := N) (i := 2 * n) (j := N)
          (le_rfl) hlt2nN
        simpa [Polynomial.Chebyshev.node_eq_neg_one hNne] using hlt
      simp [x, N, h2nN]
      linarith
    · intro k hk
      have hk1 : 1 ≤ k := (Set.mem_Icc.mp hk).1
      have hkn : k ≤ n := (Set.mem_Icc.mp hk).2
      let p : ℕ := 2 * k - 1
      have hpodd : Odd p := by
        dsimp [p]
        use k - 1
        omega
      have hpN : p < 2 * n + 1 := by
        dsimp [p]
        omega
      have hcos := putnam_2022_a6_alt_cos_power_sum n p hpodd hpN
      trans
        ∑ i ∈ Finset.Icc 1 n,
          (Real.cos (((2 * i - 1 : ℕ) : ℝ) * Real.pi /
              ((2 * n + 1 : ℕ) : ℝ)) ^ p -
            Real.cos (((2 * i : ℕ) : ℝ) * Real.pi /
              ((2 * n + 1 : ℕ) : ℝ)) ^ p)
      · have hset : (Icc 1 n).toFinset = Finset.Icc 1 n := by
          ext i
          simp [Finset.mem_Icc]
        refine Finset.sum_congr hset ?_
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
        have h_even : 2 * i ≤ N := by dsimp [N]; omega
        have h_odd : 2 * i - 1 ≤ N := by dsimp [N]; omega
        simp [x, N, p, h_even, h_odd, Polynomial.Chebyshev.node, hpodd.neg_pow]
        ring
      · simpa [p] using hcos
  · intro m hm
    rcases hm with ⟨x, hmono, hx1, hx2n, hcond⟩
    by_contra hmn
    have hnm : n + 1 ≤ m := by omega
    let u : (Fin n ⊕ Fin n) ⊕ Unit → ℝ := fun s =>
      match s with
      | Sum.inl (Sum.inl i) => x (2 * (i.1 + 1))
      | Sum.inl (Sum.inr i) => -x (2 * (i.1 + 1) - 1)
      | Sum.inr _ => -1
    let v : (Fin n ⊕ Fin n) ⊕ Unit → ℝ := fun s =>
      match s with
      | Sum.inl (Sum.inl i) => x (2 * (i.1 + 1) - 1)
      | Sum.inl (Sum.inr i) => -x (2 * (i.1 + 1))
      | Sum.inr _ => 1
    have hpsum : ∀ k, 1 ≤ k →
        k ≤ Fintype.card ((Fin n ⊕ Fin n) ⊕ Unit) →
        (∑ s : (Fin n ⊕ Fin n) ⊕ Unit, u s ^ k) =
          ∑ s : (Fin n ⊕ Fin n) ⊕ Unit, v s ^ k := by
      intro k hk1 hkcard
      have hkcard' : k ≤ 2 * n + 1 := by
        have : k ≤ n + n + 1 := by simpa using hkcard
        omega
      by_cases hkeven : Even k
      · simp [u, v, hkeven.neg_pow]
        ac_rfl
      · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
        rcases hkodd with ⟨r, rfl⟩
        have hrle : r ≤ n := by omega
        have hraw := hcond (r + 1) (by
          exact Set.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hraw' :
            (∑ i ∈ Icc 1 n,
              (x (2 * i) ^ (2 * r + 1) - x (2 * i - 1) ^ (2 * r + 1))) = 1 := by
          simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hraw
        have hfin :
            (∑ i : Fin n,
              (x (2 * (i.1 + 1)) ^ (2 * r + 1) -
                x (2 * (i.1 + 1) - 1) ^ (2 * r + 1))) = 1 := by
          have hset : (Icc 1 n).toFinset = Finset.Icc 1 n := by
            ext i
            simp [Finset.mem_Icc]
          have hraw'' :
              (∑ i ∈ Finset.Icc 1 n,
                (x (2 * i) ^ (2 * r + 1) - x (2 * i - 1) ^ (2 * r + 1))) = 1 := by
            simpa [hset] using hraw'
          have hfinrange := Fin.sum_univ_eq_sum_range
            (fun j => x (2 * (j + 1)) ^ (2 * r + 1) -
              x (2 * (j + 1) - 1) ^ (2 * r + 1)) n
          rw [hfinrange]
          simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using (putnam_2022_a6_sum_Icc_one_eq_range n
              (fun i => x (2 * i) ^ (2 * r + 1) -
                x (2 * i - 1) ^ (2 * r + 1))).symm.trans hraw''
        have hsplit :
            (∑ i : Fin n, x (2 * (i.1 + 1)) ^ (2 * r + 1)) -
              (∑ i : Fin n, x (2 * (i.1 + 1) - 1) ^ (2 * r + 1)) = 1 := by
          simpa [Finset.sum_sub_distrib] using hfin
        simp [u, v, (show Odd (2 * r + 1) by exact ⟨r, rfl⟩).neg_pow]
        linarith
    have hesymm := putnam_2022_a6_esymm_eq_of_psum_eq
      ((Fin n ⊕ Fin n) ⊕ Unit) u v hpsum
    have hpoly := putnam_2022_a6_prod_poly_eq_of_esymm_eq
      ((Fin n ⊕ Fin n) ⊕ Unit) u v hesymm
    have heval : (∏ s : (Fin n ⊕ Fin n) ⊕ Unit, (1 - u s)) =
        ∏ s : (Fin n ⊕ Fin n) ⊕ Unit, (1 - v s) := by
      have := congrArg (Polynomial.eval (1 : ℝ)) hpoly
      simpa [Polynomial.eval_prod] using this
    have hleftpos : 0 < ∏ s : (Fin n ⊕ Fin n) ⊕ Unit, (1 - u s) := by
      simp [u]
      apply mul_pos
      · apply Finset.prod_pos
        intro i hi
        have hle : x (2 * (i.1 + 1)) ≤ x (2 * n) := by
          apply hmono.monotone
          omega
        linarith
      · apply Finset.prod_pos
        intro i hi
        have hle : x 1 ≤ x (2 * (i.1 + 1) - 1) := by
          apply hmono.monotone
          omega
        linarith
    have hright : (∏ s : (Fin n ⊕ Fin n) ⊕ Unit, (1 - v s)) = 0 := by
      simp [v]
    linarith
