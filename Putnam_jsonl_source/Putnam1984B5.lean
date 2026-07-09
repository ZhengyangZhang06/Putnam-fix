import Mathlib

open Topology Filter Nat

private noncomputable def putnam_1984_b5_binaryMoment (n r : ℕ) : ℝ :=
  ∑ L ∈ List.fixedLengthDigits (by norm_num : 1 < (2 : ℕ)) n,
    (-(1 : ℝ)) ^ L.sum * (((Nat.ofDigits (2 : ℕ) L : ℕ) : ℝ) ^ r)

private lemma putnam_1984_b5_pow_sub_add_pow (r : ℕ) (x : ℝ) :
    x ^ r - (x + 1) ^ r = -∑ j ∈ Finset.range r, x ^ j * (r.choose j : ℝ) := by
  rw [add_pow, Finset.sum_range_succ]
  simp

private lemma putnam_1984_b5_binaryMoment_succ (n r : ℕ) :
    putnam_1984_b5_binaryMoment (n + 1) r =
      ∑ L ∈ List.fixedLengthDigits (by norm_num : 1 < (2 : ℕ)) n,
        (-(1 : ℝ)) ^ L.sum *
          (((2 : ℝ) * ((Nat.ofDigits (2 : ℕ) L : ℕ) : ℝ)) ^ r -
            (((1 : ℝ) + (2 : ℝ) * ((Nat.ofDigits (2 : ℕ) L : ℕ) : ℝ)) ^ r)) := by
  unfold putnam_1984_b5_binaryMoment
  rw [List.fixedLengthDigits_succ_eq_disjiUnion]
  rw [Finset.sum_disjiUnion]
  simp only [List.consFixedLengthDigits]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [Nat.ofDigits]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro L hL
  ring_nf

private lemma putnam_1984_b5_binaryMoment_succ_formula (n r : ℕ) :
    putnam_1984_b5_binaryMoment (n + 1) r =
      -∑ j ∈ Finset.range r,
        ((r.choose j : ℝ) * (2 : ℝ) ^ j) * putnam_1984_b5_binaryMoment n j := by
  rw [putnam_1984_b5_binaryMoment_succ]
  simp_rw [show ∀ (L : List ℕ),
      ((1 : ℝ) + (2 : ℝ) * ((Nat.ofDigits (2 : ℕ) L : ℕ) : ℝ)) =
        ((2 : ℝ) * ((Nat.ofDigits (2 : ℕ) L : ℕ) : ℝ)) + 1 by
    intro L
    ring]
  simp_rw [putnam_1984_b5_pow_sub_add_pow]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  unfold putnam_1984_b5_binaryMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  ring_nf

private lemma putnam_1984_b5_tri_succ (n : ℕ) :
    (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  cases n with
  | zero => simp
  | succ k =>
      rw [Nat.succ_sub_one]
      have hmul : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by
        ring
      rw [hmul]
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

private theorem putnam_1984_b5_binaryMoment_moments (n : ℕ) :
    (∀ r : ℕ, r < n → putnam_1984_b5_binaryMoment n r = 0) ∧
      putnam_1984_b5_binaryMoment n n =
        (-(1 : ℝ)) ^ n * (n.factorial : ℝ) * (2 : ℝ) ^ (n * (n - 1) / 2) := by
  induction n with
  | zero =>
      constructor
      · intro r hr
        exact (Nat.not_lt_zero r hr).elim
      · unfold putnam_1984_b5_binaryMoment
        simp
  | succ n ih =>
      rcases ih with ⟨ihzero, ihdiag⟩
      constructor
      · intro r hr
        rw [putnam_1984_b5_binaryMoment_succ_formula]
        apply neg_eq_zero.mpr
        apply Finset.sum_eq_zero
        intro j hj
        have hjr : j < r := Finset.mem_range.mp hj
        have hrle : r ≤ n := Nat.lt_succ_iff.mp hr
        have hjn : j < n := lt_of_lt_of_le hjr hrle
        rw [ihzero j hjn]
        ring
      · rw [putnam_1984_b5_binaryMoment_succ_formula, Finset.sum_range_succ]
        have hlow : ∑ j ∈ Finset.range n,
            ((Nat.choose (n + 1) j : ℝ) * (2 : ℝ) ^ j) *
              putnam_1984_b5_binaryMoment n j = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjn : j < n := Finset.mem_range.mp hj
          rw [ihzero j hjn]
          ring
        rw [hlow, zero_add, ihdiag]
        rw [Nat.choose_succ_self_right, Nat.factorial_succ]
        rw [show (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n by
          simpa using putnam_1984_b5_tri_succ n]
        rw [pow_add]
        rw [show (n + 1) * n.factorial = n * n.factorial + n.factorial by
          rw [Nat.succ_mul]]
        push_cast
        ring_nf

private lemma putnam_1984_b5_interval_to_range (m : ℕ) (d : ℕ → ℕ) :
    ((∑ k : Set.Icc 0 (2 ^ m - 1), (-(1 : ℤ)) ^ (d k) * (k : ℕ) ^ m : ℤ) : ℝ)
      = ∑ k ∈ Finset.range (2 ^ m), (-(1 : ℝ)) ^ (d k) * (k : ℝ) ^ m := by
  rw [Int.cast_sum]
  rw [← Finset.sum_subtype (s := Finset.range (2 ^ m))
    (p := fun x : ℕ => x ∈ Set.Icc 0 (2 ^ m - 1))
    (f := fun x : ℕ => (((-(1 : ℤ)) ^ (d x) * (x : ℕ) ^ m : ℤ) : ℝ))]
  · simp
  · intro x
    dsimp
    rw [Finset.mem_range, Set.mem_Icc]
    constructor
    · intro hx
      exact ⟨Nat.zero_le x, (Nat.lt_iff_le_pred (Nat.pow_pos (by norm_num : 0 < 2))).mp hx⟩
    · intro hx
      exact (Nat.lt_iff_le_pred (Nat.pow_pos (by norm_num : 0 < 2))).mpr hx.2

private lemma putnam_1984_b5_sumbits_sum (sumbits : List ℕ → ℕ)
    (hsumbits : ∀ bits : List ℕ, sumbits bits = ∑ i : Fin bits.length, bits[i]) :
    ∀ bits : List ℕ, sumbits bits = bits.sum := by
  intro bits
  rw [hsumbits bits]
  change (∑ i : Fin bits.length, bits.get i) = bits.sum
  rw [← List.sum_ofFn, List.ofFn_get]

private lemma putnam_1984_b5_range_to_lists (m : ℕ) (d : ℕ → ℕ) (sumbits : List ℕ → ℕ)
    (hsumbits : ∀ bits : List ℕ, sumbits bits = ∑ i : Fin bits.length, bits[i])
    (hd : ∀ k : ℕ, d k = sumbits (Nat.digits 2 k)) :
    ∑ k ∈ Finset.range (2 ^ m), (-(1 : ℝ)) ^ (d k) * (k : ℝ) ^ m =
      putnam_1984_b5_binaryMoment m m := by
  unfold putnam_1984_b5_binaryMoment
  let hb : 1 < 2 := by norm_num
  have hsumbits_sum : ∀ bits : List ℕ, sumbits bits = bits.sum :=
    putnam_1984_b5_sumbits_sum sumbits hsumbits
  rw [← Finset.sum_nbij (i := Nat.ofDigits (2 : ℕ))
    (s := List.fixedLengthDigits hb m) (t := Finset.range (2 ^ m))
    (f := fun L : List ℕ =>
      (-(1 : ℝ)) ^ L.sum * (((Nat.ofDigits (2 : ℕ) L : ℕ) : ℝ) ^ m))
    (g := fun k : ℕ => (-(1 : ℝ)) ^ (d k) * (k : ℝ) ^ m)
    (hi := (by exact (Nat.bijOn_ofDigits' hb m).1))
    (i_inj := (Nat.bijOn_ofDigits' hb m).2.1)
    (i_surj := (Nat.bijOn_ofDigits' hb m).2.2)]
  · intro L hL
    have hsumdigits : (Nat.digits 2 (Nat.ofDigits (2 : ℕ) L)).sum = L.sum := by
      exact Nat.sum_digits_ofDigits_eq_sum hb ((List.mem_fixedLengthDigits_iff hb).mp hL)
    rw [hd (Nat.ofDigits (2 : ℕ) L), hsumbits_sum, hsumdigits]

-- (2, (Polynomial.X * (Polynomial.X - 1)) / 2, Polynomial.X)
/--
For each nonnegative integer $k$, let $d(k)$ denote the number of $1$'s in the binary expansion of $k$ (for example, $d(0)=0$ and $d(5)=2$). Let $m$ be a positive integer. Express $\sum_{k=0}^{2^m-1} (-1)^{d(k)}k^m$ in the form $(-1)^ma^{f(m)}(g(m))!$, where $a$ is an integer and $f$ and $g$ are polynomials.
-/
theorem putnam_1984_b5
    (m : ℕ) (mpos : m > 0)
    (d : ℕ → ℕ)
    (sumbits : List ℕ → ℕ)
    (hsumbits : ∀ bits : List ℕ, sumbits bits = ∑ i : Fin bits.length, bits[i])
    (hd : ∀ k : ℕ, d k = sumbits (Nat.digits 2 k)) :
    let (a, f, g) := ((2, (Polynomial.X * (Polynomial.X - 1)) / 2, Polynomial.X) : ℤ × Polynomial ℝ × Polynomial ℕ );
    ∑ k : Set.Icc 0 (2 ^ m - 1), (-(1 : ℤ)) ^ (d k) * (k : ℕ) ^ m = (-1) ^ m * (a : ℝ) ^ (f.eval (m : ℝ)) * (g.eval m)! := by
  dsimp
  rw [putnam_1984_b5_interval_to_range m d]
  rw [putnam_1984_b5_range_to_lists m d sumbits hsumbits hd]
  rw [(putnam_1984_b5_binaryMoment_moments m).2]
  have hpoly : (((Polynomial.X * (Polynomial.X - 1)) / 2 : Polynomial ℝ).eval (m : ℝ)) =
      ((m * (m - 1) / 2 : ℕ) : ℝ) := by
    rw [show (((Polynomial.X * (Polynomial.X - 1)) / 2 : Polynomial ℝ).eval (m : ℝ)) =
        (m : ℝ) * ((m : ℝ) - 1) / 2 by
      rw [show ((Polynomial.X * (Polynomial.X - 1)) / 2 : Polynomial ℝ) =
          (Polynomial.X * (Polynomial.X - 1)) * Polynomial.C ((2 : ℝ)⁻¹) by
        rw [show (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) by
          exact (Polynomial.C_ofNat (R := ℝ) 2).symm, Polynomial.div_C]]
      simp [Polynomial.eval_mul, Polynomial.eval_sub]
      ring]
    rw [Nat.cast_div]
    · rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_iff.mpr mpos), Nat.cast_one]
      ring
    · rw [Nat.dvd_iff_mod_eq_zero]
      exact Nat.even_iff.mp (Nat.even_mul_pred_self m)
    · norm_num
  rw [hpoly, Real.rpow_natCast]
  simp
  ring
