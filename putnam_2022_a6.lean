import Mathlib

open Set

abbrev putnam_2022_a6_solution : ℕ → ℕ := fun n => n

open scoped BigOperators

open Polynomial

open MeasureTheory

lemma putnam_2022_a6_exp_int_mul_pi_I_eq_one (q : ℤ) (hq : Even q) :
    Complex.exp (((q : ℝ) * Real.pi : ℝ) * Complex.I) = 1 := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_int_mul_pi, Real.sin_int_mul_pi]
  have hone : q.negOnePow = 1 := Int.negOnePow_even q hq
  rw [← Int.cast_negOnePow ℝ q, hone]
  norm_num

lemma putnam_2022_a6_exp_angle_ne_one
    (N : ℕ) (hN : 0 < N) (q : ℤ) (hql : -(N : ℤ) < q) (hqu : q < (N : ℤ)) :
    Complex.exp ((((q : ℝ) / (N : ℝ) + 1) * Real.pi : ℝ) * Complex.I) ≠ 1 := by
  intro hz
  rcases Complex.exp_eq_one_iff.mp hz with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp at him
  have hEq : (q : ℝ) / (N : ℝ) + 1 = (2 * m : ℝ) := by
    nlinarith [Real.pi_pos]
  have hEq2 : (q : ℝ) + (N : ℝ) = (2 * m : ℝ) * (N : ℝ) := by
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hN)] at hEq ⊢
    nlinarith
  have hposZ : 0 < q + (N : ℤ) := by omega
  have hltZ : q + (N : ℤ) < 2 * (N : ℤ) := by omega
  have hpos : 0 < (q : ℝ) + (N : ℝ) := by exact_mod_cast hposZ
  have hlt : (q : ℝ) + (N : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hltZ
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmpos : 0 < (m : ℝ) := by nlinarith [hpos, hEq2, hNreal]
  have hmlt : (m : ℝ) < 1 := by nlinarith [hlt, hEq2, hNreal]
  have hm_int_pos : (0 : ℤ) < m := by exact_mod_cast hmpos
  have hm_int_lt : m < 1 := by exact_mod_cast hmlt
  omega

lemma putnam_2022_a6_root_sum_range
    (N : ℕ) (hNpos : 0 < N) (hNodd : Odd N)
    (q : ℤ) (hqodd : Odd q) (hql : -(N : ℤ) < q) (hqu : q < (N : ℤ)) :
    let z := Complex.exp ((((q : ℝ) / (N : ℝ) + 1) * Real.pi : ℝ) * Complex.I)
    ∑ r ∈ Finset.range (N - 1), z ^ (r + 1) = -1 := by
  intro z
  have hEven : Even (q + (N : ℤ)) := by
    rcases hqodd with ⟨a, ha⟩
    rcases hNodd with ⟨b, hb⟩
    use a + b + 1
    subst q
    subst N
    norm_num
    ring
  have hzN : z ^ N = 1 := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    have hNcomplex : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
    have harg :
        (N : ℂ) * (((((q : ℝ) / (N : ℝ) + 1) * Real.pi : ℝ) : ℂ) * Complex.I) =
          ((((q + (N : ℤ) : ℤ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp [hNcomplex]
    rw [harg]
    exact putnam_2022_a6_exp_int_mul_pi_I_eq_one (q + (N : ℤ)) hEven
  have hz_ne : z ≠ 1 := by
    dsimp [z]
    exact putnam_2022_a6_exp_angle_ne_one N hNpos q hql hqu
  have hsum0 : ∑ r ∈ Finset.range N, z ^ r = 0 := by
    rw [geom_sum_eq hz_ne, hzN]
    simp
  have hN_eq : N = (N - 1) + 1 := by omega
  rw [hN_eq, Finset.sum_range_succ'] at hsum0
  have : ∑ r ∈ Finset.range (N - 1), z ^ (r + 1) + 1 = 0 := by
    simpa using hsum0
  exact eq_neg_of_add_eq_zero_left this

lemma putnam_2022_a6_signed_exp_sum_range
    (N : ℕ) (hNpos : 0 < N) (hNodd : Odd N)
    (q : ℤ) (hqodd : Odd q) (hql : -(N : ℤ) < q) (hqu : q < (N : ℤ)) :
    ∑ r ∈ Finset.range (N - 1),
      (-1 : ℂ) ^ (r + 1) *
        Complex.exp ((((q : ℝ) * (r + 1 : ℝ) / (N : ℝ)) * Real.pi : ℝ) * Complex.I) = -1 := by
  let z := Complex.exp ((((q : ℝ) / (N : ℝ) + 1) * Real.pi : ℝ) * Complex.I)
  have hroot := putnam_2022_a6_root_sum_range N hNpos hNodd q hqodd hql hqu
  dsimp only at hroot
  have hterm : ∀ r : ℕ, z ^ (r + 1) =
      (-1 : ℂ) ^ (r + 1) *
        Complex.exp ((((q : ℝ) * (r + 1 : ℝ) / (N : ℝ)) * Real.pi : ℝ) * Complex.I) := by
    intro r
    let w := Complex.exp ((((q : ℝ) / (N : ℝ)) * Real.pi : ℝ) * Complex.I)
    have hz : z = (-1 : ℂ) * w := by
      dsimp [z, w]
      have harg :
          ((((q : ℝ) / (N : ℝ) + 1) * Real.pi : ℝ) : ℂ) * Complex.I =
            ((((q : ℝ) / (N : ℝ)) * Real.pi : ℝ) : ℂ) * Complex.I +
              (Real.pi : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [hz, mul_pow]
    congr 1
    rw [← Complex.exp_nat_mul]
    have harg2 :
        ((r + 1 : ℕ) : ℂ) * (((((q : ℝ) / (N : ℝ)) * Real.pi : ℝ) : ℂ) * Complex.I) =
          ((((q : ℝ) * (r + 1 : ℝ) / (N : ℝ)) * Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg2]
  calc
    ∑ r ∈ Finset.range (N - 1),
      (-1 : ℂ) ^ (r + 1) *
        Complex.exp ((((q : ℝ) * (r + 1 : ℝ) / (N : ℝ)) * Real.pi : ℝ) * Complex.I)
        = ∑ r ∈ Finset.range (N - 1), z ^ (r + 1) := by
          apply Finset.sum_congr rfl
          intro r _hr
          exact (hterm r).symm
    _ = -1 := hroot

lemma putnam_2022_a6_complex_cos_pow_expansion (p : ℕ) (a : ℝ) :
    (Complex.cos (a : ℂ)) ^ p =
      ((2 : ℂ) ^ p)⁻¹ *
        ∑ l ∈ Finset.range (p + 1),
          (p.choose l : ℂ) *
            Complex.exp ((((2 * (l : ℤ) - (p : ℤ) : ℤ) : ℝ) * a : ℝ) * Complex.I) := by
  have hpow := congrArg (fun z : ℂ => z ^ p) (Complex.two_cos (a : ℂ))
  dsimp at hpow
  rw [mul_pow] at hpow
  rw [add_pow] at hpow
  calc
    Complex.cos (a : ℂ) ^ p =
        ((2 : ℂ) ^ p)⁻¹ * ((2 : ℂ) ^ p * Complex.cos (a : ℂ) ^ p) := by
      rw [inv_mul_cancel_left₀]
      norm_num
    _ = ((2 : ℂ) ^ p)⁻¹ *
        ∑ l ∈ Finset.range (p + 1),
          (Complex.exp ((a : ℂ) * Complex.I)) ^ l *
            (Complex.exp (-(a : ℂ) * Complex.I)) ^ (p - l) * (p.choose l : ℂ) := by
      rw [hpow]
    _ = ((2 : ℂ) ^ p)⁻¹ *
        ∑ l ∈ Finset.range (p + 1),
          (p.choose l : ℂ) *
            Complex.exp ((((2 * (l : ℤ) - (p : ℤ) : ℤ) : ℝ) * a : ℝ) * Complex.I) := by
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      calc
        Complex.exp ((a : ℂ) * Complex.I) ^ l *
            Complex.exp (-(a : ℂ) * Complex.I) ^ (p - l) * (p.choose l : ℂ)
            = (p.choose l : ℂ) *
                (Complex.exp ((a : ℂ) * Complex.I) ^ l *
                  Complex.exp (-(a : ℂ) * Complex.I) ^ (p - l)) := by ring
        _ = (p.choose l : ℂ) *
            Complex.exp ((((2 * (l : ℤ) - (p : ℤ) : ℤ) : ℝ) * a : ℝ) * Complex.I) := by
          congr 1
          rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
          congr 1
          have hsubcast : ((p - l : ℕ) : ℂ) = (p : ℂ) - (l : ℂ) := by
            norm_num [Nat.cast_sub hlp]
          rw [hsubcast]
          push_cast
          ring

lemma putnam_2022_a6_signed_cos_pow_sum_range
    (N p : ℕ) (hNpos : 0 < N) (hNodd : Odd N)
    (hpodd : Odd p) (hp_lt : p < N) :
    ∑ r ∈ Finset.range (N - 1),
      (-1 : ℝ) ^ (r + 1) * (Real.cos (((r + 1 : ℝ) * Real.pi) / (N : ℝ))) ^ p = -1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_cos]
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one]
  calc
    ∑ x ∈ Finset.range (N - 1),
        (-1 : ℂ) ^ (x + 1) * Complex.cos ↑((↑x + 1) * Real.pi / ↑N) ^ p
        = ((2 : ℂ) ^ p)⁻¹ *
          ∑ l ∈ Finset.range (p + 1), (p.choose l : ℂ) *
            (∑ x ∈ Finset.range (N - 1),
              (-1 : ℂ) ^ (x + 1) *
                Complex.exp ((((2 * (l : ℤ) - (p : ℤ) : ℤ) : ℝ) *
                    (x + 1 : ℝ) / (N : ℝ) * Real.pi : ℝ) * Complex.I)) := by
          simp_rw [putnam_2022_a6_complex_cos_pow_expansion]
          rw [Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _hl
          apply Finset.sum_congr rfl
          intro x _hx
          ring_nf
    _ = ((2 : ℂ) ^ p)⁻¹ *
        (∑ l ∈ Finset.range (p + 1), (p.choose l : ℂ) * (-1 : ℂ)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro l hl
          congr 1
          let q : ℤ := 2 * (l : ℤ) - (p : ℤ)
          have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have hqodd : Odd q := by
            rcases hpodd with ⟨t, ht⟩
            dsimp [q]
            rw [ht]
            use (l : ℤ) - (t : ℤ) - 1
            norm_num
            ring
          have hql : -(N : ℤ) < q := by
            dsimp [q]
            have hpZ : (p : ℤ) < (N : ℤ) := by exact_mod_cast hp_lt
            omega
          have hqu : q < (N : ℤ) := by
            dsimp [q]
            have hpZ : (p : ℤ) < (N : ℤ) := by exact_mod_cast hp_lt
            have hlpZ : (l : ℤ) ≤ (p : ℤ) := by exact_mod_cast hlp
            omega
          have hsum := putnam_2022_a6_signed_exp_sum_range N hNpos hNodd q hqodd hql hqu
          dsimp [q] at hsum ⊢
          simpa [mul_assoc] using hsum
    _ = -1 := by
          rw [← Finset.sum_mul]
          rw [← Nat.cast_sum]
          rw [Nat.sum_range_choose]
          push_cast
          field_simp [pow_ne_zero p (by norm_num : (2 : ℂ) ≠ 0)]

lemma putnam_2022_a6_sum_Icc_one_eq_sum_range
    {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ t ∈ Finset.range n, f (t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top]
      · rw [ih, Finset.sum_range_succ]
      · omega

lemma putnam_2022_a6_sum_set_Icc_one_eq_sum_range
    {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i ∈ (Set.Icc 1 n).toFinset, f i = ∑ t ∈ Finset.range n, f (t + 1) := by
  rw [show (Set.Icc 1 n).toFinset = Finset.Icc 1 n by
    ext i
    simp]
  exact putnam_2022_a6_sum_Icc_one_eq_sum_range n f

lemma putnam_2022_a6_pair_sum_eq_neg_alt (n : ℕ) (A : ℕ → ℝ) :
    ∑ t ∈ Finset.range n, (A (2 * t + 1) - A (2 * t + 2)) =
      -∑ r ∈ Finset.range (2 * n), (-1 : ℝ) ^ (r + 1) * A (r + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have htwo : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [htwo]
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      have hoddNat : Odd (2 * n + 1) := by exact odd_two_mul_add_one n
      have hodd : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_pow hoddNat
      have hevenNat : Even (2 * n + 1 + 1) := by
        use n + 1
        ring
      have heven : (-1 : ℝ) ^ (2 * n + 1 + 1) = 1 := Even.neg_one_pow hevenNat
      rw [hodd, heven]
      ring

noncomputable def putnam_2022_a6_witness (n : ℕ) (j : ℕ) : ℝ :=
  if j ≤ 2 * n then
    -Real.cos (((j : ℝ) * Real.pi) / (2 * n + 1 : ℝ))
  else
    (j : ℝ)

lemma putnam_2022_a6_witness_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMono (putnam_2022_a6_witness n) := by
  intro a b hab
  by_cases hb : b ≤ 2 * n
  · have ha : a ≤ 2 * n := le_trans (Nat.le_of_lt hab) hb
    simp [putnam_2022_a6_witness, ha, hb]
    have hNpos : 0 < (2 * n + 1 : ℝ) := by positivity
    have hangle_nonneg : 0 ≤ ((a : ℝ) * Real.pi) / (2 * n + 1 : ℝ) := by positivity
    have hbN : (b : ℝ) ≤ (2 * n + 1 : ℝ) := by
      exact_mod_cast (le_trans hb (by omega : 2 * n ≤ 2 * n + 1))
    have hmul_le : (b : ℝ) * Real.pi ≤ (2 * n + 1 : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hbN (le_of_lt Real.pi_pos)
    have hangle_le_pi : ((b : ℝ) * Real.pi) / (2 * n + 1 : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ hNpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_le
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have hmul_lt : (a : ℝ) * Real.pi < (b : ℝ) * Real.pi :=
      mul_lt_mul_of_pos_right habR Real.pi_pos
    have hangle_lt :
        ((a : ℝ) * Real.pi) / (2 * n + 1 : ℝ) <
          ((b : ℝ) * Real.pi) / (2 * n + 1 : ℝ) := by
      exact (div_lt_div_iff_of_pos_right hNpos).mpr hmul_lt
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hangle_nonneg hangle_le_pi hangle_lt
    linarith
  · have hbgt : 2 * n < b := Nat.lt_of_not_ge hb
    by_cases ha : a ≤ 2 * n
    · simp [putnam_2022_a6_witness, ha, hb]
      have hcos : -Real.cos (((a : ℝ) * Real.pi) / (2 * n + 1 : ℝ)) ≤ 1 := by
        have := Real.neg_one_le_cos (((a : ℝ) * Real.pi) / (2 * n + 1 : ℝ))
        linarith
      have hb_one : (1 : ℝ) < b := by
        have hb_nat : 1 < b := by omega
        exact_mod_cast hb_nat
      linarith
    · simp [putnam_2022_a6_witness, ha, hb]
      exact_mod_cast hab

lemma putnam_2022_a6_witness_one_gt_neg_one (n : ℕ) (hn : 0 < n) :
    -1 < putnam_2022_a6_witness n 1 := by
  have hle : 1 ≤ 2 * n := by omega
  simp [putnam_2022_a6_witness, hle]
  have hNpos : 0 < (2 * n + 1 : ℝ) := by positivity
  have hangle_pos : 0 < ((1 : ℝ) * Real.pi) / (2 * n + 1 : ℝ) := by positivity
  have hN_ge_one : (1 : ℝ) ≤ (2 * n + 1 : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
  have hangle_le_pi : ((1 : ℝ) * Real.pi) / (2 * n + 1 : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hNpos]
    nlinarith [Real.pi_pos, hN_ge_one]
  have hcos_lt_one :
      Real.cos (Real.pi / (2 * n + 1 : ℝ)) < 1 := by
    simpa using
      Real.cos_lt_cos_of_nonneg_of_le_pi (show 0 ≤ (0 : ℝ) by norm_num) hangle_le_pi
        hangle_pos
  linarith

lemma putnam_2022_a6_witness_last_lt_one (n : ℕ) (hn : 0 < n) :
    putnam_2022_a6_witness n (2 * n) < 1 := by
  have hle : 2 * n ≤ 2 * n := le_rfl
  simp [putnam_2022_a6_witness]
  have hNpos : 0 < (2 * n + 1 : ℝ) := by positivity
  have hangle_nonneg : 0 ≤ (((2 * n : ℕ) : ℝ) * Real.pi) / (2 * n + 1 : ℝ) := by positivity
  have hltN_nat : 2 * n < 2 * n + 1 := by omega
  have hltN : ((2 * n : ℕ) : ℝ) < (2 * n + 1 : ℝ) := by exact_mod_cast hltN_nat
  have hmul_lt : ((2 * n : ℕ) : ℝ) * Real.pi < (2 * n + 1 : ℝ) * Real.pi :=
    mul_lt_mul_of_pos_right hltN Real.pi_pos
  have hangle_lt_pi : (((2 * n : ℕ) : ℝ) * Real.pi) / (2 * n + 1 : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hNpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_lt
  have hcos_gt_neg_one :
      -1 < Real.cos ((2 * (n : ℝ) * Real.pi) / (2 * n + 1 : ℝ)) := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hangle_nonneg (le_refl Real.pi) hangle_lt_pi
    simpa [Nat.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm, mul_assoc] using hcos
  linarith

lemma putnam_2022_a6_witness_moment
    (n k : ℕ) (hn : 0 < n) (hk : k ∈ Icc 1 n) :
    ∑ i ∈ Icc 1 n,
      ((putnam_2022_a6_witness n (2 * i) : ℝ) ^ (2 * k - 1) -
        (putnam_2022_a6_witness n (2 * i - 1)) ^ (2 * k - 1)) = 1 := by
  let p : ℕ := 2 * k - 1
  let A : ℕ → ℝ := fun r => (Real.cos (((r : ℝ) * Real.pi) / (2 * n + 1 : ℝ))) ^ p
  have hk1 : 1 ≤ k := (Set.mem_Icc.mp hk).1
  have hkn : k ≤ n := (Set.mem_Icc.mp hk).2
  have hpodd : Odd p := by
    dsimp [p]
    use k - 1
    omega
  have hp_lt : p < 2 * n + 1 := by
    dsimp [p]
    omega
  have hNpos : 0 < 2 * n + 1 := by omega
  have hNodd : Odd (2 * n + 1) := by
    use n
  have hcos_sum :
      ∑ r ∈ Finset.range (2 * n),
        (-1 : ℝ) ^ (r + 1) *
          (Real.cos (((r + 1 : ℝ) * Real.pi) / (2 * n + 1 : ℝ))) ^ p = -1 := by
    simpa [show 2 * n + 1 - 1 = 2 * n by omega] using
      putnam_2022_a6_signed_cos_pow_sum_range (2 * n + 1) p hNpos hNodd hpodd hp_lt
  have hbranch_even (t : ℕ) (ht : t ∈ Finset.range n) :
      putnam_2022_a6_witness n (2 * (t + 1)) =
        -Real.cos ((((2 * (t + 1) : ℕ) : ℝ) * Real.pi) / (2 * n + 1 : ℝ)) := by
    have htlt : t < n := Finset.mem_range.mp ht
    have hle : 2 * (t + 1) ≤ 2 * n := by omega
    simp [putnam_2022_a6_witness, hle]
  have hbranch_odd (t : ℕ) (ht : t ∈ Finset.range n) :
      putnam_2022_a6_witness n (2 * (t + 1) - 1) =
        -Real.cos ((((2 * (t + 1) - 1 : ℕ) : ℝ) * Real.pi) / (2 * n + 1 : ℝ)) := by
    have htlt : t < n := Finset.mem_range.mp ht
    have hle : 2 * (t + 1) - 1 ≤ 2 * n := by omega
    simp [putnam_2022_a6_witness, hle]
  calc
    ∑ i ∈ Icc 1 n,
      ((putnam_2022_a6_witness n (2 * i) : ℝ) ^ (2 * k - 1) -
        (putnam_2022_a6_witness n (2 * i - 1)) ^ (2 * k - 1))
        = ∑ t ∈ Finset.range n,
          ((putnam_2022_a6_witness n (2 * (t + 1)) : ℝ) ^ p -
            (putnam_2022_a6_witness n (2 * (t + 1) - 1)) ^ p) := by
          rw [putnam_2022_a6_sum_set_Icc_one_eq_sum_range]
    _ = ∑ t ∈ Finset.range n, (A (2 * t + 1) - A (2 * t + 2)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hbranch_even t ht, hbranch_odd t ht]
          have hodd_pow (y : ℝ) : (-y) ^ p = - y ^ p := by
            exact Odd.neg_pow hpodd y
          have heven_nat : 2 * (t + 1) = 2 * t + 2 := by ring
          have hodd_nat : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
          dsimp [A]
          rw [hodd_pow, hodd_pow]
          simp [heven_nat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_comm, add_comm]
          ring
    _ = 1 := by
          rw [putnam_2022_a6_pair_sum_eq_neg_alt n A]
          simpa [A, Nat.cast_add, Nat.cast_one, add_comm, mul_comm, mul_left_comm,
            mul_assoc] using congrArg Neg.neg hcos_sum

noncomputable def putnam_2022_a6_evenPart (p : ℝ[X]) : ℝ[X] :=
  p.sum fun k c => if Even k then Polynomial.C c * Polynomial.X ^ k else 0

lemma putnam_2022_a6_eval_support_sum (p : ℝ[X]) (t : ℝ) :
    p.eval t = ∑ k ∈ p.support, p.coeff k * t ^ k := by
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  rw [Polynomial.eval_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k _hk
  simp [Polynomial.eval_mul]

lemma putnam_2022_a6_evenPart_eval_eq (p : ℝ[X]) (t : ℝ) :
    (putnam_2022_a6_evenPart p).eval t = (p.eval t + p.eval (-t)) / 2 := by
  unfold putnam_2022_a6_evenPart
  rw [Polynomial.sum_def, Polynomial.eval_finset_sum]
  rw [putnam_2022_a6_eval_support_sum p t, putnam_2022_a6_eval_support_sum p (-t)]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hke : Even k
  · rcases hke with ⟨r, hr⟩
    subst k
    simp
  · have hodd : Odd k := Nat.not_even_iff_odd.mp hke
    have hneg : (-t) ^ k = -t ^ k := Odd.neg_pow hodd t
    simp [hke, hneg]

lemma putnam_2022_a6_evenPart_integral_formula (p : ℝ[X]) (a b : ℝ) :
    (∫ t in a..b, (putnam_2022_a6_evenPart p).eval t) =
      p.sum (fun k c =>
        if Even k then c * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℝ)) else 0) := by
  unfold putnam_2022_a6_evenPart
  simp_rw [Polynomial.sum_def, Polynomial.eval_finset_sum]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _hk
    by_cases hke : Even k <;>
      simp [hke, Polynomial.eval_mul, intervalIntegral.integral_const_mul,
        integral_pow]
  · intro k _hk
    by_cases hke : Even k <;> simp [hke]

lemma putnam_2022_a6_evenPart_moment_eq
    (n : ℕ) (a b : ℕ → ℝ)
    (hmom : ∀ r ≤ n,
      ∑ i ∈ Finset.Icc 1 n, (b i ^ (2 * r + 1) - a i ^ (2 * r + 1)) = 1)
    (p : ℝ[X]) (hdeg : p.natDegree ≤ 2 * n) :
    ∑ i ∈ Finset.Icc 1 n, (∫ t in a i..b i, (putnam_2022_a6_evenPart p).eval t) =
      ∫ t in (0 : ℝ)..1, (putnam_2022_a6_evenPart p).eval t := by
  simp_rw [putnam_2022_a6_evenPart_integral_formula]
  simp_rw [Polynomial.sum_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hke : Even k
  · rcases hke with ⟨r, hr⟩
    have hkdeg : k ≤ 2 * n := by
      exact le_trans (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)) hdeg
    have hrn : r ≤ n := by omega
    subst k
    simp [show Even (r + r) by exact ⟨r, rfl⟩]
    rw [← Finset.mul_sum, ← Finset.sum_div]
    have hsum :
        ∑ i ∈ Finset.Icc 1 n, (b i ^ (r + r + 1) - a i ^ (r + r + 1)) = 1 := by
      simpa [two_mul] using hmom r hrn
    rw [hsum]
    ring
  · simp [hke]

noncomputable def putnam_2022_a6_endpointPoly (n : ℕ) (x : ℕ → ℝ) : ℝ[X] :=
  ∏ i ∈ Finset.Icc 1 n,
    ((Polynomial.X - Polynomial.C (x (2 * i - 1))) *
      (Polynomial.X - Polynomial.C (x (2 * i))))

noncomputable def putnam_2022_a6_endpointVal (n : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, ((t - x (2 * i - 1)) * (t - x (2 * i)))

def putnam_2022_a6_endpointSet (n : ℕ) (x : ℕ → ℝ) : Set ℝ :=
  ⋃ i ∈ Finset.Icc 1 n, Ioc (x (2 * i - 1)) (x (2 * i))

def putnam_2022_a6_reflectedSet (n : ℕ) (x : ℕ → ℝ) : Set ℝ :=
  ⋃ i ∈ Finset.Icc 1 n, Ioc (-x (2 * i)) (-x (2 * i - 1))

lemma putnam_2022_a6_endpointPoly_eval
    (n : ℕ) (x : ℕ → ℝ) (t : ℝ) :
    (putnam_2022_a6_endpointPoly n x).eval t =
      putnam_2022_a6_endpointVal n x t := by
  simp [putnam_2022_a6_endpointPoly, putnam_2022_a6_endpointVal,
    Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_sub]

lemma putnam_2022_a6_endpointPoly_natDegree_le (n : ℕ) (x : ℕ → ℝ) :
    (putnam_2022_a6_endpointPoly n x).natDegree ≤ 2 * n := by
  unfold putnam_2022_a6_endpointPoly
  calc
    (∏ i ∈ Finset.Icc 1 n,
      ((Polynomial.X - Polynomial.C (x (2 * i - 1))) *
        (Polynomial.X - Polynomial.C (x (2 * i)))) : ℝ[X]).natDegree
        ≤ ∑ i ∈ Finset.Icc 1 n,
            (((Polynomial.X - Polynomial.C (x (2 * i - 1))) *
              (Polynomial.X - Polynomial.C (x (2 * i)))) : ℝ[X]).natDegree := by
          exact Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ Finset.Icc 1 n, 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          calc
            (((Polynomial.X - Polynomial.C (x (2 * i - 1))) *
              (Polynomial.X - Polynomial.C (x (2 * i)))) : ℝ[X]).natDegree
                ≤ (Polynomial.X - Polynomial.C (x (2 * i - 1)) : ℝ[X]).natDegree +
                    (Polynomial.X - Polynomial.C (x (2 * i)) : ℝ[X]).natDegree :=
                  Polynomial.natDegree_mul_le
            _ ≤ 1 + 1 := by
                  exact Nat.add_le_add (Polynomial.natDegree_X_sub_C_le _)
                    (Polynomial.natDegree_X_sub_C_le _)
            _ = 2 := by norm_num
    _ = 2 * n := by
          rw [Finset.sum_const]
          simp [Nat.card_Icc]
          ring

lemma putnam_2022_a6_endpointSet_mem {n : ℕ} {x : ℕ → ℝ} {t : ℝ} :
    t ∈ putnam_2022_a6_endpointSet n x ↔
      ∃ i, i ∈ Finset.Icc 1 n ∧ t ∈ Ioc (x (2 * i - 1)) (x (2 * i)) := by
  simp [putnam_2022_a6_endpointSet, and_assoc, and_left_comm, and_comm]

lemma putnam_2022_a6_reflectedSet_mem {n : ℕ} {x : ℕ → ℝ} {t : ℝ} :
    t ∈ putnam_2022_a6_reflectedSet n x ↔
      ∃ i, i ∈ Finset.Icc 1 n ∧ t ∈ Ioc (-x (2 * i)) (-x (2 * i - 1)) := by
  simp [putnam_2022_a6_reflectedSet, and_assoc, and_left_comm, and_comm]

lemma putnam_2022_a6_measurable_endpointSet (n : ℕ) (x : ℕ → ℝ) :
    MeasurableSet (putnam_2022_a6_endpointSet n x) := by
  unfold putnam_2022_a6_endpointSet
  exact Finset.measurableSet_biUnion _ (fun i _hi =>
    (measurableSet_Ioc :
      MeasurableSet (Ioc (x (2 * i - 1)) (x (2 * i)) : Set ℝ)))

lemma putnam_2022_a6_measurable_reflectedSet (n : ℕ) (x : ℕ → ℝ) :
    MeasurableSet (putnam_2022_a6_reflectedSet n x) := by
  unfold putnam_2022_a6_reflectedSet
  exact Finset.measurableSet_biUnion _ (fun i _hi =>
    (measurableSet_Ioc :
      MeasurableSet (Ioc (-x (2 * i)) (-x (2 * i - 1)) : Set ℝ)))

lemma putnam_2022_a6_pair_nonneg_of_not_mem {a b t : ℝ}
    (hab : a ≤ b) (h : t ∉ Ioc a b) :
    0 ≤ (t - a) * (t - b) := by
  by_cases hta : t ≤ a
  · have htb : t ≤ b := le_trans hta hab
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hta) (sub_nonpos.mpr htb)
  · have hat : a < t := lt_of_not_ge hta
    have hbt : b < t := by
      by_contra hnb
      have htb : t ≤ b := le_of_not_gt hnb
      exact h ⟨hat, htb⟩
    exact mul_nonneg (sub_nonneg.mpr hat.le) (sub_nonneg.mpr hbt.le)

lemma putnam_2022_a6_pair_nonpos_of_mem {a b t : ℝ}
    (h : t ∈ Ioc a b) :
    (t - a) * (t - b) ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.1.le) (sub_nonpos.mpr h.2)

lemma putnam_2022_a6_endpointVal_nonneg_of_not_mem
    {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {t : ℝ}
    (ht : t ∉ putnam_2022_a6_endpointSet n x) :
    0 ≤ putnam_2022_a6_endpointVal n x t := by
  unfold putnam_2022_a6_endpointVal
  apply Finset.prod_nonneg
  intro i hi
  have hnot : t ∉ Ioc (x (2 * i - 1)) (x (2 * i)) := by
    intro hmem
    exact ht (putnam_2022_a6_endpointSet_mem.mpr ⟨i, hi, hmem⟩)
  have hle : x (2 * i - 1) ≤ x (2 * i) := by
    have _hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hlt : 2 * i - 1 < 2 * i := by omega
    exact (hx hlt).le
  exact putnam_2022_a6_pair_nonneg_of_not_mem hle hnot

lemma putnam_2022_a6_endpoint_intervals_disjoint
    {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {i j : ℕ}
    (_hi : i ∈ Finset.Icc 1 n) (_hj : j ∈ Finset.Icc 1 n) (hij : i ≠ j) :
    Disjoint (Ioc (x (2 * i - 1)) (x (2 * i)))
      (Ioc (x (2 * j - 1)) (x (2 * j))) := by
  rw [Set.disjoint_left]
  intro t hti htj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hidx : 2 * i < 2 * j - 1 := by omega
    have hxlt : x (2 * i) < x (2 * j - 1) := hx hidx
    linarith [hti.2, htj.1, hxlt]
  · have hidx : 2 * j < 2 * i - 1 := by omega
    have hxlt : x (2 * j) < x (2 * i - 1) := hx hidx
    linarith [htj.2, hti.1, hxlt]

lemma putnam_2022_a6_endpointVal_nonpos_of_mem
    {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {t : ℝ}
    (ht : t ∈ putnam_2022_a6_endpointSet n x) :
    putnam_2022_a6_endpointVal n x t ≤ 0 := by
  rcases putnam_2022_a6_endpointSet_mem.mp ht with ⟨i, hi, hti⟩
  unfold putnam_2022_a6_endpointVal
  rw [Finset.prod_eq_mul_prod_diff_singleton hi, Finset.sdiff_singleton_eq_erase]
  have hpair : (t - x (2 * i - 1)) * (t - x (2 * i)) ≤ 0 :=
    putnam_2022_a6_pair_nonpos_of_mem hti
  have hrest :
      0 ≤ ∏ j ∈ (Finset.Icc 1 n).erase i,
        (t - x (2 * j - 1)) * (t - x (2 * j)) := by
    apply Finset.prod_nonneg
    intro j hj
    have hjmem : j ∈ Finset.Icc 1 n := Finset.mem_of_mem_erase hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hnot : t ∉ Ioc (x (2 * j - 1)) (x (2 * j)) := by
      intro htj
      have hdis := putnam_2022_a6_endpoint_intervals_disjoint hx hi hjmem hji.symm
      exact (Set.disjoint_left.mp hdis) hti htj
    have hle : x (2 * j - 1) ≤ x (2 * j) := by
      have _hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
      have hlt : 2 * j - 1 < 2 * j := by omega
      exact (hx hlt).le
    exact putnam_2022_a6_pair_nonneg_of_not_mem hle hnot
  exact mul_nonpos_of_nonpos_of_nonneg hpair hrest

lemma putnam_2022_a6_reflected_intervals_disjoint
    {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {i j : ℕ}
    (_hi : i ∈ Finset.Icc 1 n) (_hj : j ∈ Finset.Icc 1 n) (hij : i ≠ j) :
    Disjoint (Ioc (-x (2 * i)) (-x (2 * i - 1)))
      (Ioc (-x (2 * j)) (-x (2 * j - 1))) := by
  rw [Set.disjoint_left]
  intro t hti htj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hidx : 2 * i < 2 * j - 1 := by omega
    have hxlt : x (2 * i) < x (2 * j - 1) := hx hidx
    linarith [hti.1, htj.2, hxlt]
  · have hidx : 2 * j < 2 * i - 1 := by omega
    have hxlt : x (2 * j) < x (2 * i - 1) := hx hidx
    linarith [htj.1, hti.2, hxlt]

lemma putnam_2022_a6_endpointSet_integral_eq_sum
    (n : ℕ) (x : ℕ → ℝ) (hx : StrictMono x) (p : ℝ[X]) :
    ∫ t in putnam_2022_a6_endpointSet n x, p.eval t =
      ∑ i ∈ Finset.Icc 1 n, ∫ t in x (2 * i - 1)..x (2 * i), p.eval t := by
  unfold putnam_2022_a6_endpointSet
  rw [MeasureTheory.integral_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro i hi
    have hle : x (2 * i - 1) ≤ x (2 * i) := by
      have _hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hlt : 2 * i - 1 < 2 * i := by omega
      exact (hx hlt).le
    rw [intervalIntegral.integral_of_le hle]
  · intro i _hi
    exact (measurableSet_Ioc :
      MeasurableSet (Ioc (x (2 * i - 1)) (x (2 * i)) : Set ℝ))
  · intro i hi j hj hij
    exact putnam_2022_a6_endpoint_intervals_disjoint hx hi hj hij
  · intro _i _hi
    have hc : Continuous fun t : ℝ => p.eval t := by fun_prop
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

lemma putnam_2022_a6_reflectedSet_integral_eq_sum
    (n : ℕ) (x : ℕ → ℝ) (hx : StrictMono x) (p : ℝ[X]) :
    ∫ t in putnam_2022_a6_reflectedSet n x, p.eval t =
      ∑ i ∈ Finset.Icc 1 n, ∫ t in (-x (2 * i))..(-x (2 * i - 1)), p.eval t := by
  unfold putnam_2022_a6_reflectedSet
  rw [MeasureTheory.integral_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro i hi
    have hle : -x (2 * i) ≤ -x (2 * i - 1) := by
      have _hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hlt : 2 * i - 1 < 2 * i := by omega
      exact neg_le_neg (hx hlt).le
    rw [intervalIntegral.integral_of_le hle]
  · intro i _hi
    exact (measurableSet_Ioc :
      MeasurableSet (Ioc (-x (2 * i)) (-x (2 * i - 1)) : Set ℝ))
  · intro i hi j hj hij
    exact putnam_2022_a6_reflected_intervals_disjoint hx hi hj hij
  · intro _i _hi
    have hc : Continuous fun t : ℝ => p.eval t := by fun_prop
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

lemma putnam_2022_a6_endpointSet_subset_Ioc
    {n : ℕ} (_hn : 0 < n) {x : ℕ → ℝ}
    (hx : StrictMono x) (hxone : -1 < x 1) (hxlast : x (2 * n) < 1) :
    putnam_2022_a6_endpointSet n x ⊆ Ioc (-1 : ℝ) 1 := by
  intro t ht
  rcases putnam_2022_a6_endpointSet_mem.mp ht with ⟨i, hi, hti⟩
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
  have hleftidx : 1 ≤ 2 * i - 1 := by omega
  have hrightidx : 2 * i ≤ 2 * n := by omega
  have hxleft : x 1 ≤ x (2 * i - 1) := hx.monotone hleftidx
  have hxright : x (2 * i) ≤ x (2 * n) := hx.monotone hrightidx
  exact ⟨lt_of_lt_of_le hxone (le_trans hxleft hti.1.le), le_of_lt <|
    lt_of_le_of_lt hti.2 (lt_of_le_of_lt hxright hxlast)⟩

lemma putnam_2022_a6_reflectedSet_subset_Ioc
    {n : ℕ} (_hn : 0 < n) {x : ℕ → ℝ}
    (hx : StrictMono x) (hxone : -1 < x 1) (hxlast : x (2 * n) < 1) :
    putnam_2022_a6_reflectedSet n x ⊆ Ioc (-1 : ℝ) 1 := by
  intro t ht
  rcases putnam_2022_a6_reflectedSet_mem.mp ht with ⟨i, hi, hti⟩
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
  have hleftidx : 1 ≤ 2 * i - 1 := by omega
  have hrightidx : 2 * i ≤ 2 * n := by omega
  have hxleft : x 1 ≤ x (2 * i - 1) := hx.monotone hleftidx
  have hxright : x (2 * i) ≤ x (2 * n) := hx.monotone hrightidx
  constructor
  · have hneg : -1 < -x (2 * i) := by linarith [lt_of_le_of_lt hxright hxlast]
    linarith [hneg, hti.1]
  · have hneg : -x (2 * i - 1) < 1 := by linarith [hxone, hxleft]
    exact le_of_lt (lt_of_le_of_lt hti.2 hneg)

lemma putnam_2022_a6_endpointVal_pos_left
    {n : ℕ} (_hn : 0 < n) {x : ℕ → ℝ} (hx : StrictMono x)
    {t : ℝ} (ht : t < x 1) :
    0 < putnam_2022_a6_endpointVal n x t := by
  unfold putnam_2022_a6_endpointVal
  apply Finset.prod_pos
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hleftidx : 1 ≤ 2 * i - 1 := by omega
  have hrightidx : 2 * i - 1 ≤ 2 * i := by omega
  have hxleft : x 1 ≤ x (2 * i - 1) := hx.monotone hleftidx
  have hxright : x (2 * i - 1) ≤ x (2 * i) := hx.monotone hrightidx
  have htleft : t < x (2 * i - 1) := lt_of_lt_of_le ht hxleft
  have htright : t < x (2 * i) := lt_of_lt_of_le htleft hxright
  exact mul_pos_of_neg_of_neg (sub_neg.mpr htleft) (sub_neg.mpr htright)

lemma putnam_2022_a6_reflected_integral_lt_complement
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ)
    (hx : StrictMono x) (hxone : -1 < x 1) (hxlast : x (2 * n) < 1) :
    ∫ t in putnam_2022_a6_reflectedSet n x,
        (putnam_2022_a6_endpointPoly n x).eval t
      < ∫ t in (Ioc (-1 : ℝ) 1 \ putnam_2022_a6_endpointSet n x),
        (putnam_2022_a6_endpointPoly n x).eval t := by
  let P : ℝ[X] := putnam_2022_a6_endpointPoly n x
  let E : Set ℝ := putnam_2022_a6_endpointSet n x
  let R : Set ℝ := putnam_2022_a6_reflectedSet n x
  let Cset : Set ℝ := Ioc (-1 : ℝ) 1 \ E
  let f : ℝ → ℝ := fun t => P.eval t
  have hEmeas : MeasurableSet E := putnam_2022_a6_measurable_endpointSet n x
  have hRmeas : MeasurableSet R := putnam_2022_a6_measurable_reflectedSet n x
  have hCmeas : MeasurableSet Cset := measurableSet_Ioc.diff hEmeas
  have hEsubIoc : E ⊆ Ioc (-1 : ℝ) 1 :=
    putnam_2022_a6_endpointSet_subset_Ioc hn hx hxone hxlast
  have hRsubIoc : R ⊆ Ioc (-1 : ℝ) 1 :=
    putnam_2022_a6_reflectedSet_subset_Ioc hn hx hxone hxlast
  have hCsubIcc : Cset ⊆ Icc (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨le_of_lt ht.1.1, ht.1.2⟩
  have hRsubIcc : R ⊆ Icc (-1 : ℝ) 1 := by
    intro t ht
    exact ⟨le_of_lt (hRsubIoc ht).1, (hRsubIoc ht).2⟩
  have hcont : Continuous f := by
    dsimp [f, P]
    fun_prop
  have hIntIcc : IntegrableOn f (Icc (-1 : ℝ) 1) := hcont.integrableOn_Icc
  have hfInt : Integrable (R.indicator f) := (hIntIcc.mono_set hRsubIcc).integrable_indicator hRmeas
  have hgInt : Integrable (Cset.indicator f) := (hIntIcc.mono_set hCsubIcc).integrable_indicator hCmeas
  have hlefg : R.indicator f ≤ Cset.indicator f := by
    intro t
    by_cases hR : t ∈ R
    · rw [Set.indicator_of_mem hR]
      by_cases hC : t ∈ Cset
      · rw [Set.indicator_of_mem hC]
      · rw [Set.indicator_of_notMem hC]
        have htIoc : t ∈ Ioc (-1 : ℝ) 1 := hRsubIoc hR
        have htE : t ∈ E := by
          by_contra htE
          exact hC ⟨htIoc, htE⟩
        have hval := putnam_2022_a6_endpointVal_nonpos_of_mem hx htE
        simpa [f, P, putnam_2022_a6_endpointPoly_eval] using hval
    · rw [Set.indicator_of_notMem hR]
      by_cases hC : t ∈ Cset
      · rw [Set.indicator_of_mem hC]
        have hval := putnam_2022_a6_endpointVal_nonneg_of_not_mem hx hC.2
        simpa [f, P, putnam_2022_a6_endpointPoly_eval] using hval
      · rw [Set.indicator_of_notMem hC]
  have hdiff_nonneg : 0 ≤ fun t => Cset.indicator f t - R.indicator f t := by
    intro t
    exact sub_nonneg.mpr (hlefg t)
  have hdiff_int : Integrable (fun t => Cset.indicator f t - R.indicator f t) :=
    hgInt.sub hfInt
  have hsupport_pos :
      0 < volume (Function.support (fun t => Cset.indicator f t - R.indicator f t)) := by
    let u : ℝ := min (x 1) (-x (2 * n))
    let d : ℝ := ((-1 : ℝ) + u) / 2
    have hu : -1 < u := by
      dsimp [u]
      exact lt_min hxone (by linarith [hxlast])
    have hdu : d < u := by dsimp [d]; linarith
    have hnegd : -1 < d := by dsimp [d]; linarith
    have hJpos : 0 < volume (Ioc (-1 : ℝ) d) := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    have hJsub :
        Ioc (-1 : ℝ) d ⊆
          Function.support (fun t => Cset.indicator f t - R.indicator f t) := by
      intro t ht
      have htu : t < u := lt_of_le_of_lt ht.2 hdu
      have htx1 : t < x 1 := lt_of_lt_of_le htu (min_le_left _ _)
      have htx2n : t < -x (2 * n) := lt_of_lt_of_le htu (min_le_right _ _)
      have htNotE : t ∉ E := by
        intro htE
        rcases putnam_2022_a6_endpointSet_mem.mp htE with ⟨i, hi, hti⟩
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hidx : 1 ≤ 2 * i - 1 := by omega
        have hxle : x 1 ≤ x (2 * i - 1) := hx.monotone hidx
        linarith [hti.1, htx1, hxle]
      have htNotR : t ∉ R := by
        intro htR
        rcases putnam_2022_a6_reflectedSet_mem.mp htR with ⟨i, hi, hti⟩
        have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
        have hidx : 2 * i ≤ 2 * n := by omega
        have hxle : x (2 * i) ≤ x (2 * n) := hx.monotone hidx
        have hneg : -x (2 * n) ≤ -x (2 * i) := neg_le_neg hxle
        linarith [hti.1, htx2n, hneg]
      have htC : t ∈ Cset := by
        refine ⟨?_, htNotE⟩
        have hx1lt1 : x 1 < 1 := by
          have hidx : 1 < 2 * n := by omega
          exact lt_trans (hx hidx) hxlast
        exact ⟨ht.1, le_of_lt (lt_trans htx1 hx1lt1)⟩
      have hposP : 0 < f t := by
        dsimp [f, P]
        rw [putnam_2022_a6_endpointPoly_eval]
        exact putnam_2022_a6_endpointVal_pos_left hn hx htx1
      rw [Function.mem_support]
      rw [Set.indicator_of_mem htC, Set.indicator_of_notMem htNotR]
      exact sub_ne_zero.mpr (ne_of_gt hposP)
    exact lt_of_lt_of_le hJpos (measure_mono hJsub)
  have hdiff_pos :
      0 < ∫ t, Cset.indicator f t - R.indicator f t :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg hdiff_nonneg hdiff_int).2 hsupport_pos
  rw [MeasureTheory.integral_sub hgInt hfInt] at hdiff_pos
  have hglobal : ∫ t, R.indicator f t < ∫ t, Cset.indicator f t := by linarith
  rw [MeasureTheory.integral_indicator hRmeas, MeasureTheory.integral_indicator hCmeas] at hglobal
  simpa [P, E, R, Cset, f] using hglobal

lemma putnam_2022_a6_endpoint_evenPart_integral_lt
    (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ)
    (hx : StrictMono x) (hxone : -1 < x 1) (hxlast : x (2 * n) < 1) :
    ∑ i ∈ Finset.Icc 1 n,
        ∫ t in x (2 * i - 1)..x (2 * i),
          (putnam_2022_a6_evenPart (putnam_2022_a6_endpointPoly n x)).eval t
      < ∫ t in (0 : ℝ)..1,
          (putnam_2022_a6_evenPart (putnam_2022_a6_endpointPoly n x)).eval t := by
  let P : ℝ[X] := putnam_2022_a6_endpointPoly n x
  let E : Set ℝ := putnam_2022_a6_endpointSet n x
  let R : Set ℝ := putnam_2022_a6_reflectedSet n x
  let f : ℝ → ℝ := fun t => P.eval t
  have hcont : Continuous f := by
    dsimp [f, P]
    fun_prop
  have hEmeas : MeasurableSet E := putnam_2022_a6_measurable_endpointSet n x
  have hEsubIoc : E ⊆ Ioc (-1 : ℝ) 1 :=
    putnam_2022_a6_endpointSet_subset_Ioc hn hx hxone hxlast
  have hIntIoc : IntegrableOn f (Ioc (-1 : ℝ) 1) := by
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hcomp := putnam_2022_a6_reflected_integral_lt_complement n hn x hx hxone hxlast
  have hcomp' :
      (∑ i ∈ Finset.Icc 1 n, ∫ t in (-x (2 * i))..(-x (2 * i - 1)), f t)
        < ((∫ t in (-1 : ℝ)..1, f t) -
          (∑ i ∈ Finset.Icc 1 n, ∫ t in x (2 * i - 1)..x (2 * i), f t)) := by
    have hdiff :
        ∫ t in (Ioc (-1 : ℝ) 1 \ E), f t =
          (∫ t in Ioc (-1 : ℝ) 1, f t) - (∫ t in E, f t) := by
      simpa using (MeasureTheory.integral_diff (μ := volume) hEmeas hIntIoc hEsubIoc)
    rw [show (∫ t in R, f t) =
        ∑ i ∈ Finset.Icc 1 n, ∫ t in (-x (2 * i))..(-x (2 * i - 1)), f t by
          simpa [R, f, P] using putnam_2022_a6_reflectedSet_integral_eq_sum n x hx P] at hcomp
    rw [show (∫ t in (Ioc (-1 : ℝ) 1 \ E), f t) =
        (∫ t in Ioc (-1 : ℝ) 1, f t) - (∫ t in E, f t) by
          simpa [E, f] using hdiff] at hcomp
    rw [show (∫ t in E, f t) =
        ∑ i ∈ Finset.Icc 1 n, ∫ t in x (2 * i - 1)..x (2 * i), f t by
          simpa [E, f, P] using putnam_2022_a6_endpointSet_integral_eq_sum n x hx P] at hcomp
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hcomp
    simpa only [f, P] using hcomp
  have hsum_lt :
      (∑ i ∈ Finset.Icc 1 n, ∫ t in x (2 * i - 1)..x (2 * i), f t) +
        (∑ i ∈ Finset.Icc 1 n, ∫ t in (-x (2 * i))..(-x (2 * i - 1)), f t)
        < ∫ t in (-1 : ℝ)..1, f t := by
    linarith
  have hsum_even :
      ∑ i ∈ Finset.Icc 1 n,
        ∫ t in x (2 * i - 1)..x (2 * i),
          (putnam_2022_a6_evenPart P).eval t =
        ((∑ i ∈ Finset.Icc 1 n, ∫ t in x (2 * i - 1)..x (2 * i), f t) +
          (∑ i ∈ Finset.Icc 1 n, ∫ t in (-x (2 * i))..(-x (2 * i - 1)), f t)) / 2 := by
    calc
      ∑ i ∈ Finset.Icc 1 n,
        ∫ t in x (2 * i - 1)..x (2 * i),
          (putnam_2022_a6_evenPart P).eval t
          = ∑ i ∈ Finset.Icc 1 n,
              ((∫ t in x (2 * i - 1)..x (2 * i), f t) +
                (∫ t in (-x (2 * i))..(-x (2 * i - 1)), f t)) / 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            have hPint : IntervalIntegrable f volume (x (2 * i - 1)) (x (2 * i)) :=
              hcont.intervalIntegrable _ _
            have hNint :
                IntervalIntegrable (fun t => f (-t)) volume (x (2 * i - 1)) (x (2 * i)) :=
              (hcont.comp continuous_neg).intervalIntegrable _ _
            calc
              ∫ t in x (2 * i - 1)..x (2 * i), (putnam_2022_a6_evenPart P).eval t
                  = ∫ t in x (2 * i - 1)..x (2 * i), (f t + f (-t)) / 2 := by
                    apply intervalIntegral.integral_congr
                    intro t
                    simp [f, putnam_2022_a6_evenPart_eval_eq]
              _ = ((∫ t in x (2 * i - 1)..x (2 * i), f t) +
                    (∫ t in x (2 * i - 1)..x (2 * i), f (-t))) / 2 := by
                    rw [intervalIntegral.integral_div]
                    rw [intervalIntegral.integral_add hPint hNint]
              _ = ((∫ t in x (2 * i - 1)..x (2 * i), f t) +
                    (∫ t in (-x (2 * i))..(-x (2 * i - 1)), f t)) / 2 := by
                    rw [intervalIntegral.integral_comp_neg]
      _ = ((∑ i ∈ Finset.Icc 1 n, ∫ t in x (2 * i - 1)..x (2 * i), f t) +
          (∑ i ∈ Finset.Icc 1 n, ∫ t in (-x (2 * i))..(-x (2 * i - 1)), f t)) / 2 := by
            rw [← Finset.sum_add_distrib, Finset.sum_div]
  have h01_even :
      ∫ t in (0 : ℝ)..1, (putnam_2022_a6_evenPart P).eval t =
        (∫ t in (-1 : ℝ)..1, f t) / 2 := by
    have hP01 : IntervalIntegrable f volume (0 : ℝ) 1 := hcont.intervalIntegrable _ _
    have hN01 : IntervalIntegrable (fun t => f (-t)) volume (0 : ℝ) 1 :=
      (hcont.comp continuous_neg).intervalIntegrable _ _
    have hPm10 : IntervalIntegrable f volume (-1 : ℝ) 0 := hcont.intervalIntegrable _ _
    calc
      ∫ t in (0 : ℝ)..1, (putnam_2022_a6_evenPart P).eval t
          = ∫ t in (0 : ℝ)..1, (f t + f (-t)) / 2 := by
            apply intervalIntegral.integral_congr
            intro t
            simp [f, putnam_2022_a6_evenPart_eval_eq]
      _ = ((∫ t in (0 : ℝ)..1, f t) + (∫ t in (0 : ℝ)..1, f (-t))) / 2 := by
            rw [intervalIntegral.integral_div]
            rw [intervalIntegral.integral_add hP01 hN01]
      _ = ((∫ t in (0 : ℝ)..1, f t) + (∫ t in (-1 : ℝ)..0, f t)) / 2 := by
            rw [intervalIntegral.integral_comp_neg]
            norm_num
      _ = (∫ t in (-1 : ℝ)..1, f t) / 2 := by
            have hadd := intervalIntegral.integral_add_adjacent_intervals hPm10 hP01
            linarith
  rw [show putnam_2022_a6_endpointPoly n x = P by rfl]
  rw [hsum_even, h01_even]
  nlinarith [hsum_lt]

/--
Let $n$ be a positive integer. Determine, in terms of $n$, the largest integer $m$ with the following property: There exist real numbers $x_1,\dots,x_{2n}$ with $-1< x_1< x_2<\cdots< x_{2n}<1$ such that the sum of the lengths of the $n$ intervals $[x_1^{2k-1},x_2^{2k-1}],[x_3^{2k-1},x_4^{2k-1}],\dots,[x_{2n-1}^{2k-1},x_{2n}^{2k-1}]$ is equal to $1$ for all integers $k$ with $1 \leq k \leq m$.
-/
theorem putnam_2022_a6
    (n : ℕ) (hn : 0 < n) :
    IsGreatest
      {m : ℕ | ∃ x : ℕ → ℝ,
        StrictMono x ∧ -1 < x 1 ∧ x (2 * n) < 1 ∧
        ∀ k ∈ Icc 1 m, ∑ i ∈ Icc 1 n, ((x (2 * i) : ℝ) ^ (2 * k - 1) - (x (2 * i - 1)) ^ (2 * k - 1)) = 1}
    (putnam_2022_a6_solution n) :=
by
  dsimp [putnam_2022_a6_solution]
  refine ⟨?_, ?_⟩
  · refine ⟨putnam_2022_a6_witness n,
      putnam_2022_a6_witness_strictMono n hn,
      putnam_2022_a6_witness_one_gt_neg_one n hn,
      putnam_2022_a6_witness_last_lt_one n hn, ?_⟩
    intro k hk
    exact putnam_2022_a6_witness_moment n k hn hk
  · intro m hm
    rcases hm with ⟨x, hxmono, hxone, hxlast, hsum⟩
    by_contra hmnle
    have hmn : n < m := Nat.lt_of_not_ge hmnle
    let P : ℝ[X] := putnam_2022_a6_endpointPoly n x
    have hmom :
        ∀ r ≤ n,
          ∑ i ∈ Finset.Icc 1 n,
            (x (2 * i) ^ (2 * r + 1) - x (2 * i - 1) ^ (2 * r + 1)) = 1 := by
      intro r hr
      have hk : r + 1 ∈ Icc 1 m := by
        constructor <;> omega
      have h := hsum (r + 1) hk
      rw [show (Set.Icc 1 n).toFinset = Finset.Icc 1 n by
        ext i
        simp] at h
      have hexp : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
      simpa [hexp] using h
    have heq :
        ∑ i ∈ Finset.Icc 1 n,
            ∫ t in x (2 * i - 1)..x (2 * i),
              (putnam_2022_a6_evenPart P).eval t =
          ∫ t in (0 : ℝ)..1, (putnam_2022_a6_evenPart P).eval t := by
      simpa [P] using
        putnam_2022_a6_evenPart_moment_eq n
          (fun i => x (2 * i - 1)) (fun i => x (2 * i)) hmom P
          (by simpa [P] using putnam_2022_a6_endpointPoly_natDegree_le n x)
    have hlt :
        ∑ i ∈ Finset.Icc 1 n,
            ∫ t in x (2 * i - 1)..x (2 * i),
              (putnam_2022_a6_evenPart P).eval t
          < ∫ t in (0 : ℝ)..1, (putnam_2022_a6_evenPart P).eval t := by
      simpa [P] using
        putnam_2022_a6_endpoint_evenPart_integral_lt n hn x hxmono hxone hxlast
    linarith
