import Mathlib

private def putnam_1979_a1_decomp : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | 1 => (1, 0, 0)
  | 2 => (0, 1, 0)
  | 3 => (0, 0, 1)
  | 4 => (0, 2, 0)
  | n + 5 =>
      let e := putnam_1979_a1_decomp (n + 2)
      (e.1, e.2.1, e.2.2 + 1)

private def putnam_1979_a1_ones (a : Multiset ℕ) : ℕ :=
  (a.map fun n => (putnam_1979_a1_decomp n).1).sum

private def putnam_1979_a1_twos (a : Multiset ℕ) : ℕ :=
  (a.map fun n => (putnam_1979_a1_decomp n).2.1).sum

private def putnam_1979_a1_threes (a : Multiset ℕ) : ℕ :=
  (a.map fun n => (putnam_1979_a1_decomp n).2.2).sum

private lemma putnam_1979_a1_decomp_sum (n : ℕ) :
    (putnam_1979_a1_decomp n).1 + 2 * (putnam_1979_a1_decomp n).2.1 +
      3 * (putnam_1979_a1_decomp n).2.2 = n := by
  fun_induction putnam_1979_a1_decomp n
  · norm_num [putnam_1979_a1_decomp]
  · norm_num [putnam_1979_a1_decomp]
  · norm_num [putnam_1979_a1_decomp]
  · norm_num [putnam_1979_a1_decomp]
  · norm_num [putnam_1979_a1_decomp]
  · rename_i n e ih
    subst e
    dsimp [putnam_1979_a1_decomp]
    omega

private lemma putnam_1979_a1_decomp_prod (n : ℕ) (hn : 0 < n) :
    n ≤ 2 ^ (putnam_1979_a1_decomp n).2.1 * 3 ^ (putnam_1979_a1_decomp n).2.2 := by
  fun_induction putnam_1979_a1_decomp n
  · omega
  · norm_num [putnam_1979_a1_decomp]
  · norm_num [putnam_1979_a1_decomp]
  · norm_num [putnam_1979_a1_decomp]
  · norm_num [putnam_1979_a1_decomp]
  · rename_i n e ih
    subst e
    dsimp [putnam_1979_a1_decomp]
    have ih' : n + 2 ≤ 2 ^ (putnam_1979_a1_decomp (n + 2)).2.1 *
        3 ^ (putnam_1979_a1_decomp (n + 2)).2.2 := ih (by omega)
    calc
      n + 5 ≤ 3 * (n + 2) := by nlinarith
      _ ≤ 3 * (2 ^ (putnam_1979_a1_decomp (n + 2)).2.1 *
          3 ^ (putnam_1979_a1_decomp (n + 2)).2.2) := Nat.mul_le_mul_left 3 ih'
      _ = 2 ^ (putnam_1979_a1_decomp (n + 2)).2.1 *
          3 ^ ((putnam_1979_a1_decomp (n + 2)).2.2 + 1) := by
        rw [pow_succ]
        ring

private lemma putnam_1979_a1_multiset_sum (a : Multiset ℕ) :
    putnam_1979_a1_ones a + 2 * putnam_1979_a1_twos a + 3 * putnam_1979_a1_threes a =
      a.sum := by
  induction a using Multiset.induction_on with
  | empty => simp [putnam_1979_a1_ones, putnam_1979_a1_twos, putnam_1979_a1_threes]
  | cons x s ih =>
      have hx := putnam_1979_a1_decomp_sum x
      simp only [putnam_1979_a1_ones, putnam_1979_a1_twos, putnam_1979_a1_threes,
        Multiset.map_cons, Multiset.sum_cons]
      change (putnam_1979_a1_decomp x).1 + putnam_1979_a1_ones s +
        2 * ((putnam_1979_a1_decomp x).2.1 + putnam_1979_a1_twos s) +
        3 * ((putnam_1979_a1_decomp x).2.2 + putnam_1979_a1_threes s) = x + s.sum
      omega

private lemma putnam_1979_a1_multiset_prod (a : Multiset ℕ) (hpos : ∀ i ∈ a, i > 0) :
    a.prod ≤ 2 ^ putnam_1979_a1_twos a * 3 ^ putnam_1979_a1_threes a := by
  induction a using Multiset.induction_on with
  | empty => simp [putnam_1979_a1_twos, putnam_1979_a1_threes]
  | cons x s ih =>
      have hxpos : x > 0 := hpos x (by simp)
      have hspos : ∀ i ∈ s, i > 0 := by
        intro i hi
        exact hpos i (by simp [hi])
      have hx := putnam_1979_a1_decomp_prod x hxpos
      have hs := ih hspos
      simp only [putnam_1979_a1_twos, putnam_1979_a1_threes, Multiset.map_cons,
        Multiset.sum_cons, Multiset.prod_cons]
      change x * s.prod ≤ 2 ^ ((putnam_1979_a1_decomp x).2.1 + putnam_1979_a1_twos s) *
        3 ^ ((putnam_1979_a1_decomp x).2.2 + putnam_1979_a1_threes s)
      calc
        x * s.prod ≤ (2 ^ (putnam_1979_a1_decomp x).2.1 *
            3 ^ (putnam_1979_a1_decomp x).2.2) *
            (2 ^ putnam_1979_a1_twos s * 3 ^ putnam_1979_a1_threes s) :=
          Nat.mul_le_mul hx hs
        _ = 2 ^ ((putnam_1979_a1_decomp x).2.1 + putnam_1979_a1_twos s) *
            3 ^ ((putnam_1979_a1_decomp x).2.2 + putnam_1979_a1_threes s) := by
          rw [pow_add, pow_add]
          ring

private lemma putnam_1979_a1_count_step (T H : ℕ) (hT : 3 ≤ T) :
    2 ^ T * 3 ^ H ≤ 2 ^ (T - 3) * 3 ^ (H + 2) := by
  have hExp : T = T - 3 + 3 := by omega
  have hPow : 2 ^ T = 2 ^ (T - 3 + 3) := congrArg (fun e => 2 ^ e) hExp
  calc
    2 ^ T * 3 ^ H = (2 ^ (T - 3) * 2 ^ 3) * 3 ^ H := by
      rw [hPow, pow_add]
    _ = 8 * (2 ^ (T - 3) * 3 ^ H) := by ring
    _ ≤ 9 * (2 ^ (T - 3) * 3 ^ H) := by
      exact Nat.mul_le_mul_right _ (by norm_num : 8 ≤ 9)
    _ = 2 ^ (T - 3) * 3 ^ (H + 2) := by
      rw [pow_add]
      norm_num
      ring

private lemma putnam_1979_a1_base0 (H : ℕ) (hH : H ≤ 659) :
    3 ^ H ≤ 2 * 3 ^ 659 := by
  have hpow : 3 ^ H ≤ 3 ^ 659 := Nat.pow_le_pow_right (by norm_num : 3 > 0) hH
  exact le_trans hpow (Nat.le_mul_of_pos_left (3 ^ 659) (by norm_num : 0 < 2))

private lemma putnam_1979_a1_base1 (H : ℕ) (hH : H ≤ 659) :
    2 * 3 ^ H ≤ 2 * 3 ^ 659 := by
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num : 3 > 0) hH)

private lemma putnam_1979_a1_base2 (H : ℕ) (hH : H ≤ 658) :
    4 * 3 ^ H ≤ 2 * 3 ^ 659 := by
  have hpow : 3 ^ H ≤ 3 ^ 658 := Nat.pow_le_pow_right (by norm_num : 3 > 0) hH
  calc
    4 * 3 ^ H ≤ 4 * 3 ^ 658 := Nat.mul_le_mul_left 4 hpow
    _ = 3 ^ 658 * 4 := by ring
    _ ≤ 3 ^ 658 * 6 := Nat.mul_le_mul_left (3 ^ 658) (by norm_num : 4 ≤ 6)
    _ = 2 * 3 ^ 659 := by
      rw [show 3 ^ 659 = 3 ^ 658 * 3 by
        rw [show 659 = 658 + 1 by norm_num, pow_succ]
      ]
      ring

private lemma putnam_1979_a1_count_bound :
    ∀ T H O : ℕ, O + 2 * T + 3 * H = 1979 → 2 ^ T * 3 ^ H ≤ 2 * 3 ^ 659 := by
  intro T
  induction T using Nat.strong_induction_on with
  | h T ih =>
      intro H O hsum
      by_cases hT : 3 ≤ T
      · have hsum' : O + 2 * (T - 3) + 3 * (H + 2) = 1979 := by omega
        exact le_trans (putnam_1979_a1_count_step T H hT)
          (ih (T - 3) (by omega) (H + 2) O hsum')
      · have hTle : T ≤ 2 := by omega
        interval_cases T
        · have hH : H ≤ 659 := by omega
          simpa using putnam_1979_a1_base0 H hH
        · have hH : H ≤ 659 := by omega
          simpa using putnam_1979_a1_base1 H hH
        · have hH : H ≤ 658 := by omega
          simpa using putnam_1979_a1_base2 H hH

-- Multiset.replicate 659 3 + {2}
/--
For which positive integers $n$ and $a_1, a_2, \dots, a_n$ with $\sum_{i = 1}^{n} a_i = 1979$ does $\prod_{i = 1}^{n} a_i$ attain the greatest value?
-/
theorem putnam_1979_a1
    (P : Multiset ℕ → Prop)
    (hP : ∀ a, P a ↔ Multiset.card a > 0 ∧ (∀ i ∈ a, i > 0) ∧ a.sum = 1979) :
    P ((Multiset.replicate 659 3 + {2}) : Multiset ℕ ) ∧ ∀ a : Multiset ℕ, P a → ((Multiset.replicate 659 3 + {2}) : Multiset ℕ ).prod ≥ a.prod := by
  constructor
  · rw [hP]
    constructor
    · rw [Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]
      norm_num
    constructor
    · intro i hi
      rw [Multiset.mem_add] at hi
      rcases hi with hi | hi
      · rw [Multiset.mem_replicate] at hi
        omega
      · rw [Multiset.mem_singleton] at hi
        omega
    · rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton]
      norm_num
  · intro a haP
    have ha := (hP a).mp haP
    have hpos : ∀ i ∈ a, i > 0 := ha.2.1
    have hsum : a.sum = 1979 := ha.2.2
    have hdecomp := putnam_1979_a1_multiset_sum a
    have hcounts : putnam_1979_a1_ones a + 2 * putnam_1979_a1_twos a +
        3 * putnam_1979_a1_threes a = 1979 := by
      omega
    have hprod := putnam_1979_a1_multiset_prod a hpos
    have hcount := putnam_1979_a1_count_bound (putnam_1979_a1_twos a)
      (putnam_1979_a1_threes a) (putnam_1979_a1_ones a) hcounts
    have hbound : a.prod ≤ 2 * 3 ^ 659 := le_trans hprod hcount
    calc
      a.prod ≤ 2 * 3 ^ 659 := hbound
      _ = ((Multiset.replicate 659 3 + {2}) : Multiset ℕ).prod := by
        rw [Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_singleton]
        ring
