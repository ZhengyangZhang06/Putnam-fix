import Mathlib

open Topology Filter Nat

noncomputable abbrev putnam_1984_b5_solution : ℤ × Polynomial ℝ × Polynomial ℕ :=
  (2,
    (Polynomial.X - 1) * Polynomial.X * Polynomial.C (1 / 2 : ℝ),
    Polynomial.X)

namespace Putnam1984B5

open Finset Polynomial

local notation "B" => (List.fixedLengthDigits (by norm_num : 1 < 2))

noncomputable def weightedDigitSum (n r : ℕ) : ℤ :=
  ∑ L ∈ B n, (-1 : ℤ) ^ L.sum * (Nat.ofDigits 2 L : ℤ) ^ r

lemma list_index_sum_eq_sum (L : List ℕ) :
    (∑ i : Fin L.length, L[i]) = L.sum := by
  simp

lemma digit_sum_of_ofDigits {n : ℕ} {L : List ℕ} (hL : L ∈ B n) :
    (Nat.digits 2 (Nat.ofDigits 2 L)).sum = L.sum := by
  exact Nat.sum_digits_ofDigits_eq_sum (by norm_num : 1 < 2)
    ((List.mem_fixedLengthDigits_iff (by norm_num : 1 < 2)).mp hL)

lemma weightedDigitSum_succ_test (n r : ℕ) :
    weightedDigitSum (n + 1) r =
      ∑ d ∈ Finset.range 2, ∑ L ∈ B n,
        (-1 : ℤ) ^ (d + L.sum) * (d + 2 * Nat.ofDigits 2 L : ℤ) ^ r := by
  classical
  unfold weightedDigitSum
  rw [List.fixedLengthDigits_succ_eq_disjiUnion]
  rw [Finset.sum_disjiUnion]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [List.consFixedLengthDigits]
  rw [Finset.sum_image]
  · simp [Nat.ofDigits]
  · intro L hL L' hL' h
    simpa using h

lemma weightedDigitSum_succ_pair (n r : ℕ) :
    weightedDigitSum (n + 1) r =
      ∑ L ∈ B n, (-1 : ℤ) ^ L.sum *
        ((2 * Nat.ofDigits 2 L : ℤ) ^ r - (1 + 2 * Nat.ofDigits 2 L : ℤ) ^ r) := by
  rw [weightedDigitSum_succ_test]
  norm_num [Finset.sum_range_succ]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro L hL
  simp [one_add, pow_succ]
  ring

lemma pow_sub_one_add_pow (x : ℤ) (r : ℕ) :
    x ^ r - (1 + x) ^ r = -∑ j ∈ Finset.range r, (r.choose j : ℤ) * x ^ j := by
  rw [add_comm 1 x, add_pow]
  rw [Finset.sum_range_succ]
  simp
  ring_nf

lemma weightedDigitSum_succ (n r : ℕ) :
    weightedDigitSum (n + 1) r =
      -∑ j ∈ Finset.range r, ((r.choose j : ℤ) * (2 : ℤ) ^ j) * weightedDigitSum n j := by
  rw [weightedDigitSum_succ_pair]
  simp_rw [pow_sub_one_add_pow]
  simp_rw [mul_neg, Finset.mul_sum]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j hj
  unfold weightedDigitSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro L hL
  rw [mul_pow]
  ring

lemma weightedDigitSum_eq_zero_of_lt {r n : ℕ} (h : r < n) :
    weightedDigitSum n r = 0 := by
  induction n generalizing r with
  | zero => omega
  | succ n ih =>
      rw [weightedDigitSum_succ]
      simp only [neg_eq_zero]
      exact Finset.sum_eq_zero fun j hj => by
        rw [ih (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.le_of_lt_succ h)), mul_zero]

lemma weightedDigitSum_self_sumRange (n : ℕ) :
    weightedDigitSum n n =
      (-1 : ℤ) ^ n * (n ! : ℤ) * (2 : ℤ) ^ (∑ i ∈ Finset.range n, i) := by
  induction n with
  | zero =>
      simp [weightedDigitSum]
  | succ n ih =>
      rw [weightedDigitSum_succ]
      rw [Finset.sum_eq_single_of_mem n (Finset.self_mem_range_succ n)]
      · rw [ih, Nat.choose_succ_self_right, Nat.factorial_succ, Finset.sum_range_succ, pow_add]
        simp [pow_succ]
        ring
      · intro j hj hjn
        have hjlt : j < n := by
          exact lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hjn
        rw [weightedDigitSum_eq_zero_of_lt hjlt, mul_zero]

lemma range_sum_eq_weightedDigitSum
    (m : ℕ) (d : ℕ → ℕ) (sumbits : List ℕ → ℕ)
    (hsumbits : ∀ bits : List ℕ, sumbits bits = ∑ i : Fin bits.length, bits[i])
    (hd : ∀ k : ℕ, d k = sumbits (Nat.digits 2 k)) :
    ∑ k ∈ Finset.range (2 ^ m), (-1 : ℤ) ^ (d k) * (k : ℤ) ^ m =
      weightedDigitSum m m := by
  classical
  unfold weightedDigitSum
  have hbij := Nat.bijOn_ofDigits' (by norm_num : 1 < 2) m
  refine (Finset.sum_nbij (Nat.ofDigits 2) (fun L hL => hbij.1 hL)
    hbij.2.1 hbij.2.2 ?_).symm
  intro L hL
  have hbits : d (Nat.ofDigits 2 L) = L.sum := by
    rw [hd, hsumbits, list_index_sum_eq_sum, digit_sum_of_ofDigits hL]
  simp [hbits]
  exact_mod_cast rfl

lemma interval_sum_eq_range_sum (m : ℕ) (d : ℕ → ℕ) :
    (∑ k : Set.Icc 0 (2 ^ m - 1),
        (-1 : ℤ) ^ (d (k : ℕ)) * ((k : ℕ) : ℤ) ^ m) =
      ∑ k ∈ Finset.range (2 ^ m), (-1 : ℤ) ^ (d k) * (k : ℤ) ^ m := by
  have hpow_ne : 2 ^ m ≠ 0 := by positivity
  let e : Set.Icc 0 (2 ^ m - 1) ≃ ((Finset.Icc 0 (2 ^ m - 1) : Finset ℕ) : Set ℕ) :=
    Equiv.subtypeEquivRight (by intro k; simp)
  calc
    (∑ k : Set.Icc 0 (2 ^ m - 1),
        (-1 : ℤ) ^ (d (k : ℕ)) * ((k : ℕ) : ℤ) ^ m)
        = ∑ k : ((Finset.Icc 0 (2 ^ m - 1) : Finset ℕ) : Set ℕ),
            (-1 : ℤ) ^ (d (k : ℕ)) * ((k : ℕ) : ℤ) ^ m := by
          refine Fintype.sum_equiv e _ _ ?_
          intro k
          rfl
    _ = ∑ k ∈ Finset.Icc 0 (2 ^ m - 1), (-1 : ℤ) ^ (d k) * (k : ℤ) ^ m := by
          exact Finset.sum_finset_coe
            (fun k : ℕ => (-1 : ℤ) ^ (d k) * (k : ℤ) ^ m)
            (Finset.Icc 0 (2 ^ m - 1))
    _ = ∑ k ∈ Finset.range (2 ^ m), (-1 : ℤ) ^ (d k) * (k : ℤ) ^ m := by
          rw [← Nat.range_eq_Icc_zero_sub_one (2 ^ m) hpow_ne]

lemma solutionPolynomial_eval (m : ℕ) (hm : 0 < m) :
    Polynomial.eval (m : ℝ)
      ((Polynomial.X - 1) * Polynomial.X * Polynomial.C (1 / 2 : ℝ)) =
      ((∑ i ∈ Finset.range m, i : ℕ) : ℝ) := by
  have hmul_nat := Finset.sum_range_id_mul_two m
  have hmul_real :
      ((∑ i ∈ Finset.range m, (i : ℝ)) * 2) =
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) hmul_nat
  have hpred : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hm)]
    norm_num
  rw [hpred] at hmul_real
  simp
  nlinarith

end Putnam1984B5

/--
For each nonnegative integer $k$, let $d(k)$ denote the number of $1$'s in the binary expansion of $k$ (for example, $d(0)=0$ and $d(5)=2$). Let $m$ be a positive integer. Express $\sum_{k=0}^{2^m-1} (-1)^{d(k)}k^m$ in the form $(-1)^ma^{f(m)}(g(m))!$, where $a$ is an integer and $f$ and $g$ are polynomials.
-/
theorem putnam_1984_b5
    (m : ℕ) (mpos : m > 0)
    (d : ℕ → ℕ)
    (sumbits : List ℕ → ℕ)
    (hsumbits : ∀ bits : List ℕ, sumbits bits = ∑ i : Fin bits.length, bits[i])
    (hd : ∀ k : ℕ, d k = sumbits (Nat.digits 2 k)) :
    let (a, f, g) := putnam_1984_b5_solution;
    ∑ k : Set.Icc 0 (2 ^ m - 1), (-(1 : ℤ)) ^ (d k) * (k : ℕ) ^ m = (-1) ^ m * (a : ℝ) ^ (f.eval (m : ℝ)) * (g.eval m)! :=
  by
    classical
    dsimp [putnam_1984_b5_solution]
    have hsum :
        (∑ k : Set.Icc 0 (2 ^ m - 1),
            (-1 : ℤ) ^ (d (k : ℕ)) * ((k : ℕ) : ℤ) ^ m) =
          (-1 : ℤ) ^ m * (m ! : ℤ) *
            (2 : ℤ) ^ (∑ i ∈ Finset.range m, i) := by
      calc
        (∑ k : Set.Icc 0 (2 ^ m - 1),
            (-1 : ℤ) ^ (d (k : ℕ)) * ((k : ℕ) : ℤ) ^ m)
            = ∑ k ∈ Finset.range (2 ^ m), (-1 : ℤ) ^ (d k) * (k : ℤ) ^ m := by
                exact Putnam1984B5.interval_sum_eq_range_sum m d
        _ = Putnam1984B5.weightedDigitSum m m := by
                exact Putnam1984B5.range_sum_eq_weightedDigitSum m d sumbits hsumbits hd
        _ = (-1 : ℤ) ^ m * (m ! : ℤ) *
              (2 : ℤ) ^ (∑ i ∈ Finset.range m, i) := by
                exact Putnam1984B5.weightedDigitSum_self_sumRange m
    rw [hsum]
    rw [Putnam1984B5.solutionPolynomial_eval m mpos, Real.rpow_natCast]
    simp
    ring
