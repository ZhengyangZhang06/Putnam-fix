import Mathlib

open Nat
open Finset

def num_ones : List ℕ → ℕ
| [] => (0 : ℕ)
| (h :: t) => if h = 1 then num_ones t + 1 else num_ones t

noncomputable def putnamA5Weight (k : ℕ) : ℂ :=
  (-2 : ℂ) ^ num_ones (digits 3 k)

noncomputable def putnamA5Coeff (j : ℕ) : ℂ :=
  (if j = 0 then (1 : ℂ) else 0) - 2 + (2 : ℂ) ^ j

noncomputable def putnamA5Sum (n m : ℕ) (z : ℂ) : ℂ :=
  ∑ k : Fin (3 ^ n), putnamA5Weight (k : ℕ) * (z + (k : ℕ)) ^ m

noncomputable def putnamA5Closed : ℕ → ℕ → ℂ → ℂ
| 0, m, z => z ^ m
| n + 1, m, z =>
    ∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : ℂ) * putnamA5Coeff j * (3 : ℂ) ^ (m - j) *
        putnamA5Closed n (m - j) (z / 3)

abbrev putnam_2023_a5_solution : Set ℂ :=
  {z : ℂ |
    (z + (((3 : ℂ) ^ 1010 - 1) / 2)) *
      ((z + (((3 : ℂ) ^ 1010 - 1) / 2)) ^ 2 +
        (((9 : ℂ) ^ 1010 - 1) / 16)) = 0}

lemma putnamA5Weight_three_mul (q : ℕ) : putnamA5Weight (3 * q) = putnamA5Weight q := by
  by_cases hq : q = 0
  · simp [putnamA5Weight, hq]
  · have hd : digits 3 (0 + 3 * q) = 0 :: digits 3 q :=
      Nat.digits_add 3 (by norm_num) 0 q (by norm_num) (Or.inr hq)
    rw [show 3 * q = 0 + 3 * q by omega]
    rw [putnamA5Weight, putnamA5Weight, hd]
    simp [num_ones]

lemma putnamA5Weight_three_mul_add_one (q : ℕ) :
    putnamA5Weight (3 * q + 1) = (-2 : ℂ) * putnamA5Weight q := by
  have hd : digits 3 (1 + 3 * q) = 1 :: digits 3 q :=
    Nat.digits_add 3 (by norm_num) 1 q (by norm_num) (Or.inl (by norm_num))
  rw [show 3 * q + 1 = 1 + 3 * q by omega]
  rw [putnamA5Weight, putnamA5Weight, hd]
  simp [num_ones, pow_succ]
  ring

lemma putnamA5Weight_three_mul_add_two (q : ℕ) :
    putnamA5Weight (3 * q + 2) = putnamA5Weight q := by
  have hd : digits 3 (2 + 3 * q) = 2 :: digits 3 q :=
    Nat.digits_add 3 (by norm_num) 2 q (by norm_num) (Or.inl (by norm_num))
  rw [show 3 * q + 2 = 2 + 3 * q by omega]
  rw [putnamA5Weight, putnamA5Weight, hd]
  simp [num_ones]

lemma putnamA5_choose_sum_if_zero (m : ℕ) (x : ℂ) :
    (∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : ℂ) * (if j = 0 then (1 : ℂ) else 0) * x ^ (m - j)) = x ^ m := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hne
    simp [hne]
  · intro h0
    simp at h0

lemma putnamA5_choose_sum_one (m : ℕ) (x : ℂ) :
    (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) * x ^ (m - j)) =
      (x + 1) ^ m := by
  calc
    (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) * x ^ (m - j))
        = ∑ j ∈ Finset.range (m + 1), (1 : ℂ) ^ j * ((Nat.choose m j : ℂ) * x ^ (m - j)) := by
            simp
    _ = (1 + x) ^ m := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (add_pow (1 : ℂ) x m).symm
    _ = (x + 1) ^ m := by ring

lemma putnamA5_choose_sum_two (m : ℕ) (x : ℂ) :
    (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) * (2 : ℂ) ^ j * x ^ (m - j)) =
      (x + 2) ^ m := by
  calc
    (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) * (2 : ℂ) ^ j * x ^ (m - j))
        = (2 + x) ^ m := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using (add_pow (2 : ℂ) x m).symm
    _ = (x + 2) ^ m := by ring

lemma putnamA5_secondDiff_expand (m : ℕ) (x : ℂ) :
    x ^ m - 2 * (x + 1) ^ m + (x + 2) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℂ) * putnamA5Coeff j * x ^ (m - j) := by
  symm
  unfold putnamA5Coeff
  calc
    (∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℂ) * ((if j = 0 then (1 : ℂ) else 0) - 2 + (2 : ℂ) ^ j) * x ^ (m - j))
        = (∑ j ∈ Finset.range (m + 1),
              (Nat.choose m j : ℂ) * (if j = 0 then (1 : ℂ) else 0) * x ^ (m - j))
          - 2 * (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) * x ^ (m - j))
          + (∑ j ∈ Finset.range (m + 1),
              (Nat.choose m j : ℂ) * (2 : ℂ) ^ j * x ^ (m - j)) := by
            rw [Finset.mul_sum]
            rw [← Finset.sum_sub_distrib]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
    _ = x ^ m - 2 * (x + 1) ^ m + (x + 2) ^ m := by
      rw [putnamA5_choose_sum_if_zero, putnamA5_choose_sum_one, putnamA5_choose_sum_two]

lemma putnamA5Sum_succ (n m : ℕ) (z : ℂ) :
    putnamA5Sum (n + 1) m z =
      ∑ q : Fin (3 ^ n), putnamA5Weight (q : ℕ) *
        ((z + (3 * (q : ℕ) : ℕ)) ^ m - 2 * (z + (3 * (q : ℕ) + 1 : ℕ)) ^ m +
          (z + (3 * (q : ℕ) + 2 : ℕ)) ^ m) := by
  classical
  unfold putnamA5Sum
  let e : Fin (3 ^ n) × Fin 3 ≃ Fin (3 ^ (n + 1)) :=
    finProdFinEquiv.trans (finCongr (by rw [pow_succ]))
  calc
    (∑ k : Fin (3 ^ (n + 1)), putnamA5Weight ↑k * (z + ↑↑k) ^ m)
        = ∑ p : Fin (3 ^ n) × Fin 3,
            putnamA5Weight (e p : ℕ) * (z + ((e p : Fin (3 ^ (n + 1))) : ℕ)) ^ m := by
            simpa [e] using
              (Equiv.sum_comp e
                (fun k : Fin (3 ^ (n + 1)) => putnamA5Weight (k : ℕ) * (z + (k : ℕ)) ^ m)).symm
    _ = ∑ q : Fin (3 ^ n), ∑ d : Fin 3,
          putnamA5Weight ((d : ℕ) + 3 * (q : ℕ)) *
            (z + ((d : ℕ) + 3 * (q : ℕ) : ℕ)) ^ m := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro _ _
            rfl
    _ = ∑ q : Fin (3 ^ n), putnamA5Weight (q : ℕ) *
        ((z + (3 * (q : ℕ) : ℕ)) ^ m - 2 * (z + (3 * (q : ℕ) + 1 : ℕ)) ^ m +
          (z + (3 * (q : ℕ) + 2 : ℕ)) ^ m) := by
            refine Finset.sum_congr rfl ?_
            intro q _
            rw [Fin.sum_univ_three]
            have h0 : putnamA5Weight (3 * (q : ℕ)) = putnamA5Weight (q : ℕ) := by
              exact putnamA5Weight_three_mul (q : ℕ)
            have h1 : putnamA5Weight (1 + 3 * (q : ℕ)) = (-2 : ℂ) * putnamA5Weight (q : ℕ) := by
              rw [show 1 + 3 * (q : ℕ) = 3 * (q : ℕ) + 1 by omega]
              exact putnamA5Weight_three_mul_add_one (q : ℕ)
            have h2 : putnamA5Weight (2 + 3 * (q : ℕ)) = putnamA5Weight (q : ℕ) := by
              rw [show 2 + 3 * (q : ℕ) = 3 * (q : ℕ) + 2 by omega]
              exact putnamA5Weight_three_mul_add_two (q : ℕ)
            norm_num
            rw [h0, h1, h2]
            ring_nf

lemma putnamA5Sum_succ_expand (n m : ℕ) (z : ℂ) :
    putnamA5Sum (n + 1) m z =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℂ) * putnamA5Coeff j * (3 : ℂ) ^ (m - j) *
          putnamA5Sum n (m - j) (z / 3) := by
  calc
    putnamA5Sum (n + 1) m z =
        ∑ q : Fin (3 ^ n), putnamA5Weight (q : ℕ) *
          (∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℂ) * putnamA5Coeff j *
              (z + ↑(3 * (q : ℕ) : ℕ)) ^ (m - j)) := by
          rw [putnamA5Sum_succ]
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [show z + ↑(3 * ↑q + 1 : ℕ) = (z + ↑(3 * ↑q : ℕ)) + 1 by norm_num; ring]
          rw [show z + ↑(3 * ↑q + 2 : ℕ) = (z + ↑(3 * ↑q : ℕ)) + 2 by norm_num; ring]
          rw [putnamA5_secondDiff_expand]
    _ = ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℂ) * putnamA5Coeff j * (3 : ℂ) ^ (m - j) *
          putnamA5Sum n (m - j) (z / 3) := by
          unfold putnamA5Sum
          simp_rw [mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro j _
          let A : ℂ := (Nat.choose m j : ℂ) * putnamA5Coeff j
          let B : ℂ := (3 : ℂ) ^ (m - j)
          change (∑ q : Fin (3 ^ n), putnamA5Weight (q : ℕ) *
              (A * (z + ↑(3 * (q : ℕ) : ℕ)) ^ (m - j))) =
            ∑ q : Fin (3 ^ n), A * B *
              (putnamA5Weight (q : ℕ) * (z / 3 + (q : ℂ)) ^ (m - j))
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [show (z + ↑(3 * ↑q : ℕ)) ^ (m - j) = B * (z / 3 + (q : ℂ)) ^ (m - j) by
            rw [show z + ↑(3 * ↑q : ℕ) = (3 : ℂ) * (z / 3 + (q : ℂ)) by norm_num; ring]
            rw [mul_pow]]
          ring

lemma putnamA5Sum_eq_closed (n m : ℕ) (z : ℂ) :
    putnamA5Sum n m z = putnamA5Closed n m z := by
  induction n generalizing m z with
  | zero =>
      unfold putnamA5Sum putnamA5Closed putnamA5Weight
      simp [num_ones]
  | succ n ih =>
      rw [putnamA5Sum_succ_expand]
      unfold putnamA5Closed
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ih]

noncomputable def putnamA5Center (n : ℕ) : ℂ :=
  ((3 : ℂ) ^ n - 1) / 2

noncomputable def putnamA5SqSum (n : ℕ) : ℂ :=
  ((9 : ℂ) ^ n - 1) / 4

noncomputable def putnamA5Scale (n t : ℕ) : ℂ :=
  ((Nat.factorial (2 * n + t) : ℂ) / (Nat.factorial t : ℂ)) *
    (3 : ℂ) ^ (n * (n - 1))

noncomputable def putnamA5LowPoly (n : ℕ) : ℕ → ℂ → ℂ
| 0, _ => 1
| 1, z => z + putnamA5Center n
| 2, z => (z + putnamA5Center n) ^ 2 + putnamA5SqSum n / 12
| 3, z => (z + putnamA5Center n) *
    ((z + putnamA5Center n) ^ 2 + putnamA5SqSum n / 4)
| _ + 4, _ => 0

@[simp] lemma putnamA5Coeff_zero : putnamA5Coeff 0 = 0 := by
  norm_num [putnamA5Coeff]

@[simp] lemma putnamA5Coeff_one : putnamA5Coeff 1 = 0 := by
  norm_num [putnamA5Coeff]

lemma putnamA5Center_succ (n : ℕ) :
    putnamA5Center (n + 1) = 3 * putnamA5Center n + 1 := by
  unfold putnamA5Center
  rw [pow_succ]
  ring

lemma putnamA5SqSum_succ (n : ℕ) :
    putnamA5SqSum (n + 1) = 9 * putnamA5SqSum n + 2 := by
  unfold putnamA5SqSum
  rw [pow_succ]
  ring

lemma putnamA5_choose_mul_factorial_desc (m j : ℕ) :
    (Nat.choose m j : ℂ) * (Nat.factorial j : ℂ) = (Nat.descFactorial m j : ℂ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  norm_cast
  ring

lemma putnamA5_factorial_desc_cast {m j : ℕ} (h : j ≤ m) :
    (Nat.factorial (m - j) : ℂ) * (Nat.descFactorial m j : ℂ) =
      (Nat.factorial m : ℂ) := by
  exact_mod_cast Nat.factorial_mul_descFactorial h

lemma putnamA5_pow_step (n r : ℕ) :
    (3 : ℂ) ^ (2 * n + r) * (3 : ℂ) ^ (n * (n - 1)) =
      (3 : ℂ) ^ ((n + 1) * n) * (3 : ℂ) ^ r := by
  rw [← pow_add, ← pow_add]
  congr 1
  cases n with
  | zero => norm_num
  | succ n =>
      simp
      ring

lemma putnamA5_scale_ratio (n t s : ℕ) (hs : s ≤ t) :
    (Nat.choose (2 * n + t + 2) (s + 2) : ℂ) * putnamA5Coeff (s + 2) *
        (3 : ℂ) ^ (2 * n + (t - s)) * putnamA5Scale n (t - s)
      = putnamA5Scale (n + 1) t *
          (putnamA5Coeff (s + 2) * (Nat.factorial t : ℂ) * (3 : ℂ) ^ (t - s) /
            ((Nat.factorial (s + 2) : ℂ) * (Nat.factorial (t - s) : ℂ))) := by
  unfold putnamA5Scale
  have hsub : 2 * n + t + 2 - (s + 2) = 2 * n + (t - s) := by omega
  have hle : s + 2 ≤ 2 * n + t + 2 := by omega
  have hchoose := putnamA5_choose_mul_factorial_desc (2 * n + t + 2) (s + 2)
  have hfac := putnamA5_factorial_desc_cast (m := 2 * n + t + 2) (j := s + 2) hle
  rw [hsub] at hfac
  have hp := putnamA5_pow_step n (t - s)
  have hfac' :
      (Nat.descFactorial (2 * n + t + 2) (s + 2) : ℂ) *
          (Nat.factorial (2 * n + (t - s)) : ℂ) =
        (Nat.factorial (2 * n + t + 2) : ℂ) := by
    rw [← hfac]
    ring
  have hchoose' :
      (Nat.choose (2 * n + t + 2) (s + 2) : ℂ) =
        (Nat.descFactorial (2 * n + t + 2) (s + 2) : ℂ) /
          (Nat.factorial (s + 2) : ℂ) := by
    have hne : (Nat.factorial (s + 2) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (s + 2)
    field_simp [hne]
    exact hchoose
  rw [hchoose']
  rw [show 2 * (n + 1) + t = 2 * n + t + 2 by omega]
  rw [show (n + 1) * (n + 1 - 1) = (n + 1) * n by simp]
  calc
    (↑((2 * n + t + 2).descFactorial (s + 2)) / ↑(s + 2)! *
        putnamA5Coeff (s + 2) * 3 ^ (2 * n + (t - s)) *
        (↑(2 * n + (t - s))! / ↑(t - s)! * 3 ^ (n * (n - 1))))
        = (putnamA5Coeff (s + 2) *
            ((Nat.descFactorial (2 * n + t + 2) (s + 2) : ℂ) *
              (Nat.factorial (2 * n + (t - s)) : ℂ)) *
            ((3 : ℂ) ^ (2 * n + (t - s)) * (3 : ℂ) ^ (n * (n - 1)))) /
            ((Nat.factorial (s + 2) : ℂ) * (Nat.factorial (t - s) : ℂ)) := by
          ring_nf
    _ = (putnamA5Coeff (s + 2) * (Nat.factorial (2 * n + t + 2) : ℂ) *
          ((3 : ℂ) ^ ((n + 1) * n) * (3 : ℂ) ^ (t - s))) /
            ((Nat.factorial (s + 2) : ℂ) * (Nat.factorial (t - s) : ℂ)) := by
          rw [hfac', hp]
    _ = (↑(2 * n + t + 2)! / ↑t ! * 3 ^ ((n + 1) * n)) *
          (putnamA5Coeff (s + 2) * ↑t ! * 3 ^ (t - s) /
            (↑(s + 2)! * ↑(t - s)!)) := by
          have hnet : (Nat.factorial t : ℂ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero t
          field_simp [hnet]

lemma putnamA5Closed_eq_zero_of_lt {n m : ℕ} (h : m < 2 * n) (z : ℂ) :
    putnamA5Closed n m z = 0 := by
  induction n generalizing m z with
  | zero =>
      omega
  | succ n ih =>
      unfold putnamA5Closed
      refine Finset.sum_eq_zero ?_
      intro j hj
      by_cases hle : j ≤ 1
      · have hj01 : j = 0 ∨ j = 1 := by omega
        rcases hj01 with rfl | rfl <;> simp
      · have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hlt : m - j < 2 * n := by omega
        rw [ih hlt]
        ring

lemma putnamA5Closed_succ_low_sum (n t : ℕ) (z : ℂ) :
    putnamA5Closed (n + 1) (2 * (n + 1) + t) z =
      ∑ j ∈ Finset.Icc 2 (t + 2),
        (Nat.choose (2 * (n + 1) + t) j : ℂ) * putnamA5Coeff j *
          (3 : ℂ) ^ (2 * (n + 1) + t - j) *
            putnamA5Closed n (2 * (n + 1) + t - j) (z / 3) := by
  change (∑ j ∈ Finset.range (2 * (n + 1) + t + 1),
      (Nat.choose (2 * (n + 1) + t) j : ℂ) * putnamA5Coeff j *
        (3 : ℂ) ^ (2 * (n + 1) + t - j) *
          putnamA5Closed n (2 * (n + 1) + t - j) (z / 3)) = _
  let f : ℕ → ℂ := fun j =>
    (Nat.choose (2 * (n + 1) + t) j : ℂ) * putnamA5Coeff j *
      (3 : ℂ) ^ (2 * (n + 1) + t - j) *
        putnamA5Closed n (2 * (n + 1) + t - j) (z / 3)
  change (∑ j ∈ Finset.range (2 * (n + 1) + t + 1), f j) =
    ∑ j ∈ Finset.Icc 2 (t + 2), f j
  exact (Finset.sum_subset
    (by
      intro j hj
      rw [Finset.mem_range]
      rw [Finset.mem_Icc] at hj
      omega)
    (by
      intro j hjrange hjnot
      by_cases hle : j ≤ 1
      · have hj01 : j = 0 ∨ j = 1 := by omega
        rcases hj01 with rfl | rfl <;> simp [f]
      · have hjgt : t + 2 < j := by
          have hnot' : ¬(2 ≤ j ∧ j ≤ t + 2) := by
            simpa [Finset.mem_Icc] using hjnot
          omega
        have hjle : j ≤ 2 * (n + 1) + t := Nat.le_of_lt_succ (Finset.mem_range.mp hjrange)
        have hlt : 2 * (n + 1) + t - j < 2 * n := by omega
        simp [f, putnamA5Closed_eq_zero_of_lt hlt])).symm

lemma putnamA5LowPoly_succ_zero (n : ℕ) (z : ℂ) :
    putnamA5LowPoly (n + 1) 0 z = putnamA5LowPoly n 0 (z / 3) := by
  norm_num [putnamA5LowPoly]

lemma putnamA5LowPoly_succ_one (n : ℕ) (z : ℂ) :
    putnamA5LowPoly (n + 1) 1 z =
      3 * putnamA5LowPoly n 1 (z / 3) + putnamA5LowPoly n 0 (z / 3) := by
  norm_num [putnamA5LowPoly, putnamA5Center_succ]
  ring

lemma putnamA5LowPoly_succ_two (n : ℕ) (z : ℂ) :
    putnamA5LowPoly (n + 1) 2 z =
      9 * putnamA5LowPoly n 2 (z / 3) +
        6 * putnamA5LowPoly n 1 (z / 3) + (7 / 6) * putnamA5LowPoly n 0 (z / 3) := by
  norm_num [putnamA5LowPoly, putnamA5Center_succ, putnamA5SqSum_succ]
  ring

lemma putnamA5LowPoly_succ_three (n : ℕ) (z : ℂ) :
    putnamA5LowPoly (n + 1) 3 z =
      27 * putnamA5LowPoly n 3 (z / 3) +
        27 * putnamA5LowPoly n 2 (z / 3) +
          (21 / 2) * putnamA5LowPoly n 1 (z / 3) +
            (3 / 2) * putnamA5LowPoly n 0 (z / 3) := by
  norm_num [putnamA5LowPoly, putnamA5Center_succ, putnamA5SqSum_succ]
  ring

lemma putnamA5_sum_Icc_2_2 {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ j ∈ Finset.Icc 2 2, f j) = f 2 := by
  simp

lemma putnamA5_sum_Icc_2_3 {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ j ∈ Finset.Icc 2 3, f j) = f 2 + f 3 := by
  rw [show 3 = 2 + 1 by norm_num]
  rw [Finset.sum_Icc_succ_top (by norm_num)]
  simp

lemma putnamA5_sum_Icc_2_4 {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ j ∈ Finset.Icc 2 4, f j) = f 2 + f 3 + f 4 := by
  rw [show 4 = 3 + 1 by norm_num]
  rw [Finset.sum_Icc_succ_top (by norm_num)]
  simp [putnamA5_sum_Icc_2_3, add_assoc]

lemma putnamA5_sum_Icc_2_5 {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ j ∈ Finset.Icc 2 5, f j) = f 2 + f 3 + f 4 + f 5 := by
  rw [show 5 = 4 + 1 by norm_num]
  rw [Finset.sum_Icc_succ_top (by norm_num)]
  simp [putnamA5_sum_Icc_2_4, add_assoc]

lemma putnamA5Closed_low (n t : ℕ) (ht : t ≤ 3) (z : ℂ) :
    putnamA5Closed n (2 * n + t) z =
      putnamA5Scale n t * putnamA5LowPoly n t z := by
  induction n generalizing t z with
  | zero =>
      interval_cases t
      all_goals
        simp [putnamA5Closed, putnamA5Scale, putnamA5LowPoly, putnamA5Center,
          putnamA5SqSum]
        try ring
  | succ n ih =>
      interval_cases t
      · rw [putnamA5Closed_succ_low_sum n 0 z]
        rw [putnamA5_sum_Icc_2_2]
        norm_num [putnamA5Coeff]
        rw [show 2 * (n + 1) - 2 = 2 * n + 0 by omega]
        rw [ih 0 (by norm_num) (z / 3)]
        have hratio := putnamA5_scale_ratio n 0 0 (by norm_num)
        norm_num [putnamA5Coeff] at hratio
        rw [putnamA5LowPoly_succ_zero]
        simpa [mul_assoc] using congrArg (fun c => c * putnamA5LowPoly n 0 (z / 3)) hratio
      · rw [putnamA5Closed_succ_low_sum n 1 z]
        rw [putnamA5_sum_Icc_2_3]
        norm_num [putnamA5Coeff]
        rw [show 2 * (n + 1) + 1 - 2 = 2 * n + 1 by omega]
        rw [show 2 * (n + 1) + 1 - 3 = 2 * n + 0 by omega]
        rw [ih 1 (by norm_num) (z / 3), ih 0 (by norm_num) (z / 3)]
        have h0 := putnamA5_scale_ratio n 1 0 (by norm_num)
        have h1 := putnamA5_scale_ratio n 1 1 (by norm_num)
        norm_num [putnamA5Coeff] at h0 h1
        rw [putnamA5LowPoly_succ_one]
        rw [show 2 * n + (1 - 0) = 2 * n + 1 by omega] at h0
        rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by omega]
        rw [show 2 * n + 0 = 2 * n by omega]
        have h0p :
            ↑((2 * n + 1 + 2).choose 2) * 2 * 3 ^ (2 * n + 1) *
                (putnamA5Scale n 1 * putnamA5LowPoly n 1 (z / 3)) =
              (putnamA5Scale (n + 1) 1 * 3) * putnamA5LowPoly n 1 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 1 (z / 3)) h0
        have h1p :
            ↑((2 * n + 1 + 2).choose 3) * 6 * 3 ^ (2 * n) *
                (putnamA5Scale n 0 * putnamA5LowPoly n 0 (z / 3)) =
              putnamA5Scale (n + 1) 1 * putnamA5LowPoly n 0 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 0 (z / 3)) h1
        calc
          (↑((2 * n + 1 + 2).choose 2) * 2 * 3 ^ (2 * n + 1) *
                (putnamA5Scale n 1 * putnamA5LowPoly n 1 (z / 3)) +
              ↑((2 * n + 1 + 2).choose 3) * 6 * 3 ^ (2 * n) *
                (putnamA5Scale n 0 * putnamA5LowPoly n 0 (z / 3)))
              = (putnamA5Scale (n + 1) 1 * 3) * putnamA5LowPoly n 1 (z / 3) +
                  putnamA5Scale (n + 1) 1 * putnamA5LowPoly n 0 (z / 3) := by
                rw [h0p, h1p]
          _ = putnamA5Scale (n + 1) 1 *
                (3 * putnamA5LowPoly n 1 (z / 3) + putnamA5LowPoly n 0 (z / 3)) := by
                ring
      · rw [putnamA5Closed_succ_low_sum n 2 z]
        rw [putnamA5_sum_Icc_2_4]
        norm_num [putnamA5Coeff]
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        rw [show 2 * n + 2 + 2 - 3 = 2 * n + 1 by omega]
        rw [show 2 * n + 2 + 2 - 4 = 2 * n + 0 by omega]
        rw [ih 2 (by norm_num) (z / 3), ih 1 (by norm_num) (z / 3),
          ih 0 (by norm_num) (z / 3)]
        have h0 := putnamA5_scale_ratio n 2 0 (by norm_num)
        have h1 := putnamA5_scale_ratio n 2 1 (by norm_num)
        have h2 := putnamA5_scale_ratio n 2 2 (by norm_num)
        norm_num [putnamA5Coeff] at h0 h1 h2
        rw [putnamA5LowPoly_succ_two]
        rw [show 2 * n + (2 - 0) = 2 * n + 2 by omega] at h0
        rw [show 2 * n + (2 - 1) = 2 * n + 1 by omega] at h1
        have h0p :
            ↑((2 * n + 2 + 2).choose 2) * 2 * 3 ^ (2 * n + 2) *
                (putnamA5Scale n 2 * putnamA5LowPoly n 2 (z / 3)) =
              (putnamA5Scale (n + 1) 2 * 9) * putnamA5LowPoly n 2 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 2 (z / 3)) h0
        have h1p :
            ↑((2 * n + 2 + 2).choose 3) * 6 * 3 ^ (2 * n + 1) *
                (putnamA5Scale n 1 * putnamA5LowPoly n 1 (z / 3)) =
              (putnamA5Scale (n + 1) 2 * 6) * putnamA5LowPoly n 1 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 1 (z / 3)) h1
        have h2p :
            ↑((2 * n + 2 + 2).choose 4) * 14 * 3 ^ (2 * n) *
                (putnamA5Scale n 0 * putnamA5LowPoly n 0 (z / 3)) =
              (putnamA5Scale (n + 1) 2 * (7 / 6)) * putnamA5LowPoly n 0 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 0 (z / 3)) h2
        calc
          (↑((2 * n + 2 + 2).choose 2) * 2 * 3 ^ (2 * n + 2) *
                (putnamA5Scale n 2 * putnamA5LowPoly n 2 (z / 3)) +
              ↑((2 * n + 2 + 2).choose 3) * 6 * 3 ^ (2 * n + 1) *
                (putnamA5Scale n 1 * putnamA5LowPoly n 1 (z / 3)) +
              ↑((2 * n + 2 + 2).choose 4) * 14 * 3 ^ (2 * n) *
                (putnamA5Scale n 0 * putnamA5LowPoly n 0 (z / 3)))
              = (putnamA5Scale (n + 1) 2 * 9) * putnamA5LowPoly n 2 (z / 3) +
                  (putnamA5Scale (n + 1) 2 * 6) * putnamA5LowPoly n 1 (z / 3) +
                    (putnamA5Scale (n + 1) 2 * (7 / 6)) *
                      putnamA5LowPoly n 0 (z / 3) := by
                rw [h0p, h1p, h2p]
          _ = putnamA5Scale (n + 1) 2 *
                (9 * putnamA5LowPoly n 2 (z / 3) +
                  6 * putnamA5LowPoly n 1 (z / 3) +
                    (7 / 6) * putnamA5LowPoly n 0 (z / 3)) := by
                ring
      · rw [putnamA5Closed_succ_low_sum n 3 z]
        rw [putnamA5_sum_Icc_2_5]
        norm_num [putnamA5Coeff]
        rw [show 2 * (n + 1) + 3 - 2 = 2 * n + 3 by omega]
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        rw [show 2 * n + 2 + 3 - 4 = 2 * n + 1 by omega]
        rw [show 2 * n + 2 + 3 - 5 = 2 * n + 0 by omega]
        rw [ih 3 (by norm_num) (z / 3), ih 2 (by norm_num) (z / 3),
          ih 1 (by norm_num) (z / 3), ih 0 (by norm_num) (z / 3)]
        have h0 := putnamA5_scale_ratio n 3 0 (by norm_num)
        have h1 := putnamA5_scale_ratio n 3 1 (by norm_num)
        have h2 := putnamA5_scale_ratio n 3 2 (by norm_num)
        have h3 := putnamA5_scale_ratio n 3 3 (by norm_num)
        norm_num [putnamA5Coeff] at h0 h1 h2 h3
        rw [putnamA5LowPoly_succ_three]
        rw [show 2 * n + 3 + 2 = 2 * n + 2 + 3 by omega] at h0 h1 h2 h3
        rw [show 2 * n + (3 - 0) = 2 * n + 3 by omega] at h0
        rw [show 2 * n + (3 - 1) = 2 * n + 2 by omega] at h1
        rw [show 2 * n + (3 - 2) = 2 * n + 1 by omega] at h2
        have h0p :
            ↑((2 * n + 2 + 3).choose 2) * 2 * 3 ^ (2 * n + 3) *
                (putnamA5Scale n 3 * putnamA5LowPoly n 3 (z / 3)) =
              (putnamA5Scale (n + 1) 3 * 27) * putnamA5LowPoly n 3 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 3 (z / 3)) h0
        have h1p :
            ↑((2 * n + 2 + 3).choose 3) * 6 * 3 ^ (2 * n + 2) *
                (putnamA5Scale n 2 * putnamA5LowPoly n 2 (z / 3)) =
              (putnamA5Scale (n + 1) 3 * 27) * putnamA5LowPoly n 2 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 2 (z / 3)) h1
        have h2p :
            ↑((2 * n + 2 + 3).choose 4) * 14 * 3 ^ (2 * n + 1) *
                (putnamA5Scale n 1 * putnamA5LowPoly n 1 (z / 3)) =
              (putnamA5Scale (n + 1) 3 * (21 / 2)) * putnamA5LowPoly n 1 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 1 (z / 3)) h2
        have h3p :
            ↑((2 * n + 2 + 3).choose 5) * 30 * 3 ^ (2 * n) *
                (putnamA5Scale n 0 * putnamA5LowPoly n 0 (z / 3)) =
              (putnamA5Scale (n + 1) 3 * (3 / 2)) * putnamA5LowPoly n 0 (z / 3) := by
          simpa [mul_assoc] using
            congrArg (fun c => c * putnamA5LowPoly n 0 (z / 3)) h3
        calc
          (↑((2 * n + 2 + 3).choose 2) * 2 * 3 ^ (2 * n + 3) *
                (putnamA5Scale n 3 * putnamA5LowPoly n 3 (z / 3)) +
              ↑((2 * n + 2 + 3).choose 3) * 6 * 3 ^ (2 * n + 2) *
                (putnamA5Scale n 2 * putnamA5LowPoly n 2 (z / 3)) +
              ↑((2 * n + 2 + 3).choose 4) * 14 * 3 ^ (2 * n + 1) *
                (putnamA5Scale n 1 * putnamA5LowPoly n 1 (z / 3)) +
              ↑((2 * n + 2 + 3).choose 5) * 30 * 3 ^ (2 * n) *
                (putnamA5Scale n 0 * putnamA5LowPoly n 0 (z / 3)))
              = (putnamA5Scale (n + 1) 3 * 27) * putnamA5LowPoly n 3 (z / 3) +
                  (putnamA5Scale (n + 1) 3 * 27) * putnamA5LowPoly n 2 (z / 3) +
                    (putnamA5Scale (n + 1) 3 * (21 / 2)) *
                      putnamA5LowPoly n 1 (z / 3) +
                        (putnamA5Scale (n + 1) 3 * (3 / 2)) *
                          putnamA5LowPoly n 0 (z / 3) := by
                rw [h0p, h1p, h2p, h3p]
          _ = putnamA5Scale (n + 1) 3 *
                (27 * putnamA5LowPoly n 3 (z / 3) +
                  27 * putnamA5LowPoly n 2 (z / 3) +
                    (21 / 2) * putnamA5LowPoly n 1 (z / 3) +
                      (3 / 2) * putnamA5LowPoly n 0 (z / 3)) := by
                ring

/--
For a nonnegative integer $k$, let $f(k)$ be the number of ones in the base 3 representation of $k$. Find all complex numbers $z$ such that \[ \sum_{k=0}^{3^{1010}-1} (-2)^{f(k)} (z+k)^{2023} = 0. \]
-/
theorem putnam_2023_a5
: {z : ℂ | ∑ k ∈ Finset.Icc 0 (3^1010 - 1), (-2)^(num_ones (digits 3 k)) * (z + k)^2023 = 0} = putnam_2023_a5_solution := by
  ext z
  change ((∑ k ∈ Finset.Icc 0 (3 ^ 1010 - 1),
      putnamA5Weight k * (z + (k : ℂ)) ^ 2023) = 0) ↔
        (z + (((3 : ℂ) ^ 1010 - 1) / 2)) *
          ((z + (((3 : ℂ) ^ 1010 - 1) / 2)) ^ 2 +
            (((9 : ℂ) ^ 1010 - 1) / 16)) = 0
  have hpow : (3 ^ 1010 : ℕ) ≠ 0 := by positivity
  rw [← Nat.range_eq_Icc_zero_sub_one (3 ^ 1010) hpow]
  rw [show (∑ k ∈ Finset.range (3 ^ 1010), putnamA5Weight k * (z + (k : ℂ)) ^ 2023) =
      putnamA5Sum 1010 2023 z by
    exact (Fin.sum_univ_eq_sum_range
      (fun k : ℕ => putnamA5Weight k * (z + (k : ℂ)) ^ 2023) (3 ^ 1010)).symm]
  rw [putnamA5Sum_eq_closed]
  rw [putnamA5Closed_low 1010 3 (by norm_num) z]
  have hscale : putnamA5Scale 1010 3 ≠ 0 := by
    unfold putnamA5Scale
    apply mul_ne_zero
    · apply div_ne_zero
      · exact_mod_cast Nat.factorial_ne_zero (2 * 1010 + 3)
      · exact_mod_cast Nat.factorial_ne_zero 3
    · exact pow_ne_zero _ (by norm_num : (3 : ℂ) ≠ 0)
  have hpoly :
      putnamA5LowPoly 1010 3 z =
        (z + (((3 : ℂ) ^ 1010 - 1) / 2)) *
          ((z + (((3 : ℂ) ^ 1010 - 1) / 2)) ^ 2 +
            (((9 : ℂ) ^ 1010 - 1) / 16)) := by
    change (z + putnamA5Center 1010) *
        ((z + putnamA5Center 1010) ^ 2 + putnamA5SqSum 1010 / 4) =
      (z + (((3 : ℂ) ^ 1010 - 1) / 2)) *
        ((z + (((3 : ℂ) ^ 1010 - 1) / 2)) ^ 2 +
          (((9 : ℂ) ^ 1010 - 1) / 16))
    unfold putnamA5Center putnamA5SqSum
    set A : ℂ := ((3 : ℂ) ^ 1010 - 1) / 2
    set B : ℂ := (9 : ℂ) ^ 1010 - 1
    change (z + A) * ((z + A) ^ 2 + B / 4 / 4) =
      (z + A) * ((z + A) ^ 2 + B / 16)
    congr 1
    congr 1
    rw [div_div]
    norm_num
  rw [hpoly]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hscale
  · intro h
    rw [h, mul_zero]
