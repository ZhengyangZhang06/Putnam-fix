import Mathlib

open Nat

def num_ones : List ℕ → ℕ
| [] => (0 : ℕ)
| (h :: t) => if h = 1 then num_ones t + 1 else num_ones t

namespace Putnam2023A5

open Finset

lemma num_ones_append (l₁ l₂ : List ℕ) :
    num_ones (l₁ ++ l₂) = num_ones l₁ + num_ones l₂ := by
  induction l₁ with
  | nil => simp [num_ones]
  | cons h t ih =>
      by_cases hh : h = 1
      · simp [num_ones, hh, ih]
        omega
      · simp [num_ones, hh, ih]

lemma num_ones_replicate_zero (n : ℕ) :
    num_ones (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [num_ones]
  | succ n ih => simp [List.replicate_succ, num_ones, ih]

noncomputable def ternaryDigits {n : ℕ} (f : Fin n → Fin 3) : List ℕ :=
  List.ofFn fun i => (f i : ℕ)

noncomputable def digitWeight (d : Fin 3) : ℂ :=
  if (d : ℕ) = 1 then (-2 : ℂ) else 1

noncomputable def ternaryWeight {n : ℕ} (f : Fin n → Fin 3) : ℂ :=
  (-2 : ℂ) ^ num_ones (ternaryDigits f)

noncomputable def ternaryValue {n : ℕ} (f : Fin n → Fin 3) : ℂ :=
  ∑ i : Fin n, ((f i : ℕ) : ℂ) * (3 : ℂ) ^ (i : ℕ)

noncomputable def digitMoment (e : ℕ) : ℂ :=
  ∑ d : Fin 3, digitWeight d * (((d : ℕ) : ℂ) ^ e)

noncomputable def funMoment (n e : ℕ) : ℂ :=
  ∑ f : Fin n → Fin 3, ternaryWeight f * (ternaryValue f) ^ e

noncomputable def shiftSum (n : ℕ) : ℂ :=
  ∑ i : Fin n, (3 : ℂ) ^ (i : ℕ)

noncomputable def shiftSqSum (n : ℕ) : ℂ :=
  ∑ i : Fin n, ((3 : ℂ) ^ (i : ℕ)) ^ 2

noncomputable def shiftSqProd (n : ℕ) : ℂ :=
  ∏ i : Fin n, ((3 : ℂ) ^ (i : ℕ)) ^ 2

lemma ternaryDigits_snoc {n : ℕ} (f : Fin n → Fin 3) (d : Fin 3) :
    ternaryDigits (Fin.snoc f d) = ternaryDigits f ++ [(d : ℕ)] := by
  rw [ternaryDigits, ternaryDigits, List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

lemma num_ones_ternaryDigits_snoc {n : ℕ} (f : Fin n → Fin 3) (d : Fin 3) :
    num_ones (ternaryDigits (Fin.snoc f d)) =
      num_ones (ternaryDigits f) + if (d : ℕ) = 1 then 1 else 0 := by
  rw [ternaryDigits_snoc, num_ones_append]
  by_cases hd : (d : ℕ) = 1 <;> simp [num_ones, hd]

lemma ternaryWeight_snoc {n : ℕ} (f : Fin n → Fin 3) (d : Fin 3) :
    ternaryWeight (Fin.snoc f d) = ternaryWeight f * digitWeight d := by
  rw [ternaryWeight, ternaryWeight, digitWeight, num_ones_ternaryDigits_snoc]
  by_cases hd : (d : ℕ) = 1
  · simp [hd, pow_succ, mul_comm]
  · simp [hd]

lemma ternaryValue_snoc {n : ℕ} (f : Fin n → Fin 3) (d : Fin 3) :
    ternaryValue (Fin.snoc f d) =
      ternaryValue f + ((d : ℕ) : ℂ) * (3 : ℂ) ^ n := by
  rw [ternaryValue, ternaryValue, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma shiftSum_succ (n : ℕ) :
    shiftSum (n + 1) = shiftSum n + (3 : ℂ) ^ n := by
  rw [shiftSum, shiftSum, Fin.sum_univ_castSucc]
  simp

lemma shiftSqSum_succ (n : ℕ) :
    shiftSqSum (n + 1) = shiftSqSum n + ((3 : ℂ) ^ n) ^ 2 := by
  rw [shiftSqSum, shiftSqSum, Fin.sum_univ_castSucc]
  simp

lemma shiftSqProd_succ (n : ℕ) :
    shiftSqProd (n + 1) = shiftSqProd n * ((3 : ℂ) ^ n) ^ 2 := by
  rw [shiftSqProd, shiftSqProd, Fin.prod_univ_castSucc]
  simp

lemma digitMoment_zero : digitMoment 0 = 0 := by
  norm_num [digitMoment, digitWeight, Fin.sum_univ_three]

lemma digitMoment_one : digitMoment 1 = 0 := by
  norm_num [digitMoment, digitWeight, Fin.sum_univ_three]

lemma digitMoment_two : digitMoment 2 = 2 := by
  norm_num [digitMoment, digitWeight, Fin.sum_univ_three]

lemma digitMoment_three : digitMoment 3 = 6 := by
  norm_num [digitMoment, digitWeight, Fin.sum_univ_three]

lemma digitMoment_four : digitMoment 4 = 14 := by
  norm_num [digitMoment, digitWeight, Fin.sum_univ_three]

lemma digitMoment_five : digitMoment 5 = 30 := by
  norm_num [digitMoment, digitWeight, Fin.sum_univ_three]

lemma digitMoment_eq_zero_of_lt_two {e : ℕ} (he : e < 2) : digitMoment e = 0 := by
  interval_cases e <;> simp [digitMoment_zero, digitMoment_one]

lemma cast_choose_mul_factorial_mul_factorial (j e : ℕ) (he : e ≤ j) :
    ((j.choose e : ℂ) * (e.factorial : ℂ) * ((j - e).factorial : ℂ) =
      (j.factorial : ℂ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial (n := j) (k := e) he
  have hcast :
      (((j.choose e * e.factorial * (j - e).factorial : ℕ) : ℂ) =
        (j.factorial : ℂ)) := by
    exact_mod_cast hnat
  simpa [Nat.cast_mul, mul_assoc] using hcast

lemma cast_choose_add_mul_factorial (m t : ℕ) :
    (((m + t).choose m : ℂ) * (m.factorial : ℂ) * (t.factorial : ℂ) =
      ((m + t).factorial : ℂ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial (n := m + t) (k := m)
    (by omega : m ≤ m + t)
  have hcast :
      ((((m + t).choose m * m.factorial * ((m + t - m).factorial) : ℕ) : ℂ) =
        ((m + t).factorial : ℂ)) := by
    exact_mod_cast hnat
  simpa [Nat.add_sub_cancel_left, Nat.cast_mul, mul_assoc] using hcast

lemma sum_fintype_fintype_range_comm {α β M : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid M] (N : ℕ) (F : α → β → ℕ → M) :
    (∑ a : α, ∑ b : β, ∑ i ∈ Finset.range N, F a b i) =
      ∑ i ∈ Finset.range N, ∑ a : α, ∑ b : β, F a b i := by
  simpa [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (Finset.univ : Finset (α × β)))
      (t := Finset.range N) (f := fun p i => F p.1 p.2 i))

lemma funMoment_succ (n j : ℕ) :
    funMoment (n + 1) j =
      ∑ e ∈ Finset.range (j + 1),
        (j.choose e : ℂ) * funMoment n e *
          ((3 : ℂ) ^ n) ^ (j - e) * digitMoment (j - e) := by
  classical
  unfold funMoment
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 3))]
  change (∑ p : Fin 3 × (Fin n → Fin 3),
      ternaryWeight (Fin.snoc p.2 p.1) * ternaryValue (Fin.snoc p.2 p.1) ^ j) =
    ∑ e ∈ Finset.range (j + 1),
      (j.choose e : ℂ) * (∑ f : Fin n → Fin 3, ternaryWeight f * ternaryValue f ^ e) *
        ((3 : ℂ) ^ n) ^ (j - e) * digitMoment (j - e)
  rw [Fintype.sum_prod_type]
  simp_rw [ternaryWeight_snoc, ternaryValue_snoc, add_pow]
  simp_rw [Finset.mul_sum]
  rw [sum_fintype_fintype_range_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_comm]
  simp_rw [mul_pow]
  simp only [digitMoment]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  ring

lemma funMoment_eq_zero_of_lt :
    ∀ {n e : ℕ}, e < 2 * n → funMoment n e = 0 := by
  intro n
  induction n with
  | zero =>
      intro e he
      omega
  | succ n ih =>
      intro e he
      rw [funMoment_succ]
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hrn : r < 2 * n
      · rw [ih hrn]
        ring
      · have hre : r ≤ e := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
        have ht : e - r < 2 := by omega
        rw [digitMoment_eq_zero_of_lt_two ht]
        ring

lemma funMoment_two_mul (n : ℕ) :
    funMoment n (2 * n) = ((2 * n).factorial : ℂ) * shiftSqProd n := by
  induction n with
  | zero =>
      simp [funMoment, ternaryValue, ternaryWeight, ternaryDigits, shiftSqProd, num_ones]
  | succ n ih =>
      change funMoment (n + 1) (2 * n + 2) =
        (((2 * n + 2).factorial : ℂ) * shiftSqProd (n + 1))
      rw [funMoment_succ]
      change (∑ e ∈ Finset.range (2 * n + 3),
          (↑((2 * n + 2).choose e) * funMoment n e) *
            (3 ^ n) ^ (2 * n + 2 - e) * digitMoment (2 * n + 2 - e)) =
        ((2 * n + 2).factorial : ℂ) * shiftSqProd (n + 1)
      conv_lhs => rw [Finset.sum_range_add (n := 2 * n) (m := 3)]
      have hfirst :
          (∑ e ∈ Finset.range (2 * n),
            (↑((2 * n + 2).choose e) * funMoment n e) *
              (3 ^ n) ^ (2 * n + 2 - e) * digitMoment (2 * n + 2 - e)) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        rw [funMoment_eq_zero_of_lt (Finset.mem_range.mp he)]
        ring
      rw [hfirst, zero_add]
      rw [shiftSqProd_succ]
      simp [Finset.sum_range_succ, ih, digitMoment_two, digitMoment_one, digitMoment_zero]
      have hchoose :
          (((2 * n + 2).choose (2 * n) : ℂ) * ((2 * n).factorial : ℂ) * 2 =
            ((2 * n + 2).factorial : ℂ)) := by
        simpa using cast_choose_add_mul_factorial (2 * n) 2
      rw [← hchoose]
      ring

lemma funMoment_two_mul_add_one (n : ℕ) :
    funMoment n (2 * n + 1) =
      ((2 * n + 1).factorial : ℂ) * shiftSqProd n * shiftSum n := by
  induction n with
  | zero =>
      simp [funMoment, ternaryValue, ternaryWeight, ternaryDigits, shiftSqProd, shiftSum,
        num_ones]
  | succ n ih =>
      change funMoment (n + 1) (2 * n + 3) =
        ((2 * n + 3).factorial : ℂ) * shiftSqProd (n + 1) * shiftSum (n + 1)
      rw [funMoment_succ]
      change (∑ e ∈ Finset.range (2 * n + 4),
          (↑((2 * n + 3).choose e) * funMoment n e) *
            (3 ^ n) ^ (2 * n + 3 - e) * digitMoment (2 * n + 3 - e)) =
        ((2 * n + 3).factorial : ℂ) * shiftSqProd (n + 1) * shiftSum (n + 1)
      conv_lhs => rw [Finset.sum_range_add (n := 2 * n) (m := 4)]
      have hfirst :
          (∑ e ∈ Finset.range (2 * n),
            (↑((2 * n + 3).choose e) * funMoment n e) *
              (3 ^ n) ^ (2 * n + 3 - e) * digitMoment (2 * n + 3 - e)) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        rw [funMoment_eq_zero_of_lt (Finset.mem_range.mp he)]
        ring
      rw [hfirst, zero_add]
      rw [shiftSqProd_succ, shiftSum_succ]
      simp [Finset.sum_range_succ, funMoment_two_mul, ih, digitMoment_three,
        digitMoment_two, digitMoment_one, digitMoment_zero]
      have hchoose0 :
          (((2 * n + 3).choose (2 * n) : ℂ) * ((2 * n).factorial : ℂ) * 6 =
            ((2 * n + 3).factorial : ℂ)) := by
        simpa using cast_choose_add_mul_factorial (2 * n) 3
      have hchoose1 :
          (((2 * n + 3).choose (2 * n + 1) : ℂ) *
              ((2 * n + 1).factorial : ℂ) * 2 =
            ((2 * n + 3).factorial : ℂ)) := by
        simpa using cast_choose_add_mul_factorial (2 * n + 1) 2
      have h0 :
          ↑((2 * n + 3).choose (2 * n)) *
              (↑(2 * n)! * shiftSqProd n) * (3 ^ n) ^ 3 * 6 =
            ↑(2 * n + 3)! * shiftSqProd n * (3 ^ n) ^ 3 := by
        rw [← hchoose0]
        ring
      have h1 :
          ↑((2 * n + 3).choose (2 * n + 1)) *
              (↑(2 * n + 1)! * shiftSqProd n * shiftSum n) * (3 ^ n) ^ 2 * 2 =
            ↑(2 * n + 3)! * shiftSqProd n * shiftSum n * (3 ^ n) ^ 2 := by
        rw [← hchoose1]
        ring
      rw [h0, h1]
      ring

lemma funMoment_two_mul_add_two (n : ℕ) :
    funMoment n (2 * n + 2) =
      ((2 * n + 2).factorial : ℂ) * shiftSqProd n *
        (shiftSum n ^ 2 / 2 + shiftSqSum n / 12) := by
  induction n with
  | zero =>
      simp [funMoment, ternaryValue, ternaryWeight, ternaryDigits, shiftSqProd, shiftSum,
        shiftSqSum, num_ones]
  | succ n ih =>
      change funMoment (n + 1) (2 * n + 4) =
        ((2 * n + 4).factorial : ℂ) * shiftSqProd (n + 1) *
          (shiftSum (n + 1) ^ 2 / 2 + shiftSqSum (n + 1) / 12)
      rw [funMoment_succ]
      change (∑ e ∈ Finset.range (2 * n + 5),
          (↑((2 * n + 4).choose e) * funMoment n e) *
            (3 ^ n) ^ (2 * n + 4 - e) * digitMoment (2 * n + 4 - e)) =
        ((2 * n + 4).factorial : ℂ) * shiftSqProd (n + 1) *
          (shiftSum (n + 1) ^ 2 / 2 + shiftSqSum (n + 1) / 12)
      conv_lhs => rw [Finset.sum_range_add (n := 2 * n) (m := 5)]
      have hfirst :
          (∑ e ∈ Finset.range (2 * n),
            (↑((2 * n + 4).choose e) * funMoment n e) *
              (3 ^ n) ^ (2 * n + 4 - e) * digitMoment (2 * n + 4 - e)) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        rw [funMoment_eq_zero_of_lt (Finset.mem_range.mp he)]
        ring
      rw [hfirst, zero_add]
      rw [shiftSqProd_succ, shiftSum_succ, shiftSqSum_succ]
      simp [Finset.sum_range_succ, funMoment_two_mul, funMoment_two_mul_add_one, ih,
        digitMoment_four, digitMoment_three, digitMoment_two, digitMoment_one, digitMoment_zero]
      have hcoef0 :
          (((2 * n + 4).choose (2 * n) : ℂ) * ((2 * n).factorial : ℂ) * 14 =
            ((2 * n + 4).factorial : ℂ) * (7 / 12 : ℂ)) := by
        have h := cast_choose_add_mul_factorial (2 * n) 4
        norm_num at h
        calc
          ((↑((2 * n + 4).choose (2 * n)) : ℂ) * ↑(2 * n)! * 14)
              = (↑((2 * n + 4).choose (2 * n)) * ↑(2 * n)! * 24) * (7 / 12 : ℂ) := by
                ring
          _ = ↑(2 * n + 4)! * (7 / 12 : ℂ) := by rw [h]
      have hcoef1 :
          (((2 * n + 4).choose (2 * n + 1) : ℂ) *
              ((2 * n + 1).factorial : ℂ) * 6 =
            ((2 * n + 4).factorial : ℂ)) := by
        simpa using cast_choose_add_mul_factorial (2 * n + 1) 3
      have hcoef2 :
          (((2 * n + 4).choose (2 * n + 2) : ℂ) *
              ((2 * n + 2).factorial : ℂ) * 2 =
            ((2 * n + 4).factorial : ℂ)) := by
        simpa using cast_choose_add_mul_factorial (2 * n + 2) 2
      have h0 :
          ↑((2 * n + 4).choose (2 * n)) *
              (↑(2 * n)! * shiftSqProd n) * (3 ^ n) ^ 4 * 14 =
            ↑(2 * n + 4)! * shiftSqProd n * (3 ^ n) ^ 4 * (7 / 12 : ℂ) := by
        calc
          ↑((2 * n + 4).choose (2 * n)) *
              (↑(2 * n)! * shiftSqProd n) * (3 ^ n) ^ 4 * 14
              = (↑((2 * n + 4).choose (2 * n)) * ↑(2 * n)! * 14) *
                  shiftSqProd n * (3 ^ n) ^ 4 := by ring
          _ = (↑(2 * n + 4)! * (7 / 12 : ℂ)) * shiftSqProd n * (3 ^ n) ^ 4 := by
                rw [hcoef0]
          _ = ↑(2 * n + 4)! * shiftSqProd n * (3 ^ n) ^ 4 * (7 / 12 : ℂ) := by
                ring
      have h1 :
          ↑((2 * n + 4).choose (2 * n + 1)) *
              (↑(2 * n + 1)! * shiftSqProd n * shiftSum n) * (3 ^ n) ^ 3 * 6 =
            ↑(2 * n + 4)! * shiftSqProd n * shiftSum n * (3 ^ n) ^ 3 := by
        calc
          ↑((2 * n + 4).choose (2 * n + 1)) *
              (↑(2 * n + 1)! * shiftSqProd n * shiftSum n) * (3 ^ n) ^ 3 * 6
              = (↑((2 * n + 4).choose (2 * n + 1)) * ↑(2 * n + 1)! * 6) *
                  shiftSqProd n * shiftSum n * (3 ^ n) ^ 3 := by ring
          _ = ↑(2 * n + 4)! * shiftSqProd n * shiftSum n * (3 ^ n) ^ 3 := by
                rw [hcoef1]
      have h2 :
          ↑((2 * n + 4).choose (2 * n + 2)) *
              (↑(2 * n + 2)! * shiftSqProd n *
                (shiftSum n ^ 2 / 2 + shiftSqSum n / 12)) * (3 ^ n) ^ 2 * 2 =
            ↑(2 * n + 4)! * shiftSqProd n *
              (shiftSum n ^ 2 / 2 + shiftSqSum n / 12) * (3 ^ n) ^ 2 := by
        calc
          ↑((2 * n + 4).choose (2 * n + 2)) *
              (↑(2 * n + 2)! * shiftSqProd n *
                (shiftSum n ^ 2 / 2 + shiftSqSum n / 12)) * (3 ^ n) ^ 2 * 2
              = (↑((2 * n + 4).choose (2 * n + 2)) * ↑(2 * n + 2)! * 2) *
                  shiftSqProd n * (shiftSum n ^ 2 / 2 + shiftSqSum n / 12) *
                    (3 ^ n) ^ 2 := by ring
          _ = ↑(2 * n + 4)! * shiftSqProd n *
              (shiftSum n ^ 2 / 2 + shiftSqSum n / 12) * (3 ^ n) ^ 2 := by
                rw [hcoef2]
      rw [h0, h1, h2]
      ring

lemma funMoment_two_mul_add_three (n : ℕ) :
    funMoment n (2 * n + 3) =
      ((2 * n + 3).factorial : ℂ) * shiftSqProd n *
        (shiftSum n ^ 3 / 6 + shiftSum n * shiftSqSum n / 12) := by
  induction n with
  | zero =>
      simp [funMoment, ternaryValue, ternaryWeight, ternaryDigits, shiftSqProd, shiftSum,
        shiftSqSum, num_ones]
  | succ n ih =>
      change funMoment (n + 1) (2 * n + 5) =
        ((2 * n + 5).factorial : ℂ) * shiftSqProd (n + 1) *
          (shiftSum (n + 1) ^ 3 / 6 + shiftSum (n + 1) * shiftSqSum (n + 1) / 12)
      rw [funMoment_succ]
      change (∑ e ∈ Finset.range (2 * n + 6),
          (↑((2 * n + 5).choose e) * funMoment n e) *
            (3 ^ n) ^ (2 * n + 5 - e) * digitMoment (2 * n + 5 - e)) =
        ((2 * n + 5).factorial : ℂ) * shiftSqProd (n + 1) *
          (shiftSum (n + 1) ^ 3 / 6 + shiftSum (n + 1) * shiftSqSum (n + 1) / 12)
      conv_lhs => rw [Finset.sum_range_add (n := 2 * n) (m := 6)]
      have hfirst :
          (∑ e ∈ Finset.range (2 * n),
            (↑((2 * n + 5).choose e) * funMoment n e) *
              (3 ^ n) ^ (2 * n + 5 - e) * digitMoment (2 * n + 5 - e)) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        rw [funMoment_eq_zero_of_lt (Finset.mem_range.mp he)]
        ring
      rw [hfirst, zero_add]
      rw [shiftSqProd_succ, shiftSum_succ, shiftSqSum_succ]
      simp [Finset.sum_range_succ, funMoment_two_mul, funMoment_two_mul_add_one,
        funMoment_two_mul_add_two, ih, digitMoment_five, digitMoment_four,
        digitMoment_three, digitMoment_two, digitMoment_one, digitMoment_zero]
      have hcoef0 :
          (((2 * n + 5).choose (2 * n) : ℂ) * ((2 * n).factorial : ℂ) * 30 =
            ((2 * n + 5).factorial : ℂ) * (1 / 4 : ℂ)) := by
        have h := cast_choose_add_mul_factorial (2 * n) 5
        norm_num at h
        calc
          ((↑((2 * n + 5).choose (2 * n)) : ℂ) * ↑(2 * n)! * 30)
              = (↑((2 * n + 5).choose (2 * n)) * ↑(2 * n)! * 120) * (1 / 4 : ℂ) := by
                ring
          _ = ↑(2 * n + 5)! * (1 / 4 : ℂ) := by rw [h]
      have hcoef1 :
          (((2 * n + 5).choose (2 * n + 1) : ℂ) *
              ((2 * n + 1).factorial : ℂ) * 14 =
            ((2 * n + 5).factorial : ℂ) * (7 / 12 : ℂ)) := by
        have h := cast_choose_add_mul_factorial (2 * n + 1) 4
        norm_num at h
        calc
          ((↑((2 * n + 5).choose (2 * n + 1)) : ℂ) * ↑(2 * n + 1)! * 14)
              = (↑((2 * n + 5).choose (2 * n + 1)) * ↑(2 * n + 1)! * 24) *
                  (7 / 12 : ℂ) := by ring
          _ = ↑(2 * n + 5)! * (7 / 12 : ℂ) := by rw [h]
      have hcoef2 :
          (((2 * n + 5).choose (2 * n + 2) : ℂ) *
              ((2 * n + 2).factorial : ℂ) * 6 =
            ((2 * n + 5).factorial : ℂ)) := by
        simpa using cast_choose_add_mul_factorial (2 * n + 2) 3
      have hcoef3 :
          (((2 * n + 5).choose (2 * n + 3) : ℂ) *
              ((2 * n + 3).factorial : ℂ) * 2 =
            ((2 * n + 5).factorial : ℂ)) := by
        simpa using cast_choose_add_mul_factorial (2 * n + 3) 2
      have h0 :
          ↑((2 * n + 5).choose (2 * n)) *
              (↑(2 * n)! * shiftSqProd n) * (3 ^ n) ^ 5 * 30 =
            ↑(2 * n + 5)! * shiftSqProd n * (3 ^ n) ^ 5 * (1 / 4 : ℂ) := by
        calc
          ↑((2 * n + 5).choose (2 * n)) *
              (↑(2 * n)! * shiftSqProd n) * (3 ^ n) ^ 5 * 30
              = (↑((2 * n + 5).choose (2 * n)) * ↑(2 * n)! * 30) *
                  shiftSqProd n * (3 ^ n) ^ 5 := by ring
          _ = (↑(2 * n + 5)! * (1 / 4 : ℂ)) * shiftSqProd n * (3 ^ n) ^ 5 := by
                rw [hcoef0]
          _ = ↑(2 * n + 5)! * shiftSqProd n * (3 ^ n) ^ 5 * (1 / 4 : ℂ) := by
                ring
      have h1 :
          ↑((2 * n + 5).choose (2 * n + 1)) *
              (↑(2 * n + 1)! * shiftSqProd n * shiftSum n) * (3 ^ n) ^ 4 * 14 =
            ↑(2 * n + 5)! * shiftSqProd n * shiftSum n * (3 ^ n) ^ 4 *
              (7 / 12 : ℂ) := by
        calc
          ↑((2 * n + 5).choose (2 * n + 1)) *
              (↑(2 * n + 1)! * shiftSqProd n * shiftSum n) * (3 ^ n) ^ 4 * 14
              = (↑((2 * n + 5).choose (2 * n + 1)) * ↑(2 * n + 1)! * 14) *
                  shiftSqProd n * shiftSum n * (3 ^ n) ^ 4 := by ring
          _ = (↑(2 * n + 5)! * (7 / 12 : ℂ)) * shiftSqProd n * shiftSum n *
                (3 ^ n) ^ 4 := by rw [hcoef1]
          _ = ↑(2 * n + 5)! * shiftSqProd n * shiftSum n * (3 ^ n) ^ 4 *
                (7 / 12 : ℂ) := by ring
      have h2 :
          ↑((2 * n + 5).choose (2 * n + 2)) *
              (↑(2 * n + 2)! * shiftSqProd n *
                (shiftSum n ^ 2 / 2 + shiftSqSum n / 12)) * (3 ^ n) ^ 3 * 6 =
            ↑(2 * n + 5)! * shiftSqProd n *
              (shiftSum n ^ 2 / 2 + shiftSqSum n / 12) * (3 ^ n) ^ 3 := by
        calc
          ↑((2 * n + 5).choose (2 * n + 2)) *
              (↑(2 * n + 2)! * shiftSqProd n *
                (shiftSum n ^ 2 / 2 + shiftSqSum n / 12)) * (3 ^ n) ^ 3 * 6
              = (↑((2 * n + 5).choose (2 * n + 2)) * ↑(2 * n + 2)! * 6) *
                  shiftSqProd n * (shiftSum n ^ 2 / 2 + shiftSqSum n / 12) *
                    (3 ^ n) ^ 3 := by ring
          _ = ↑(2 * n + 5)! * shiftSqProd n *
              (shiftSum n ^ 2 / 2 + shiftSqSum n / 12) * (3 ^ n) ^ 3 := by
                rw [hcoef2]
      have h3 :
          ↑((2 * n + 5).choose (2 * n + 3)) *
              (↑(2 * n + 3)! * shiftSqProd n *
                (shiftSum n ^ 3 / 6 + shiftSum n * shiftSqSum n / 12)) *
                (3 ^ n) ^ 2 * 2 =
            ↑(2 * n + 5)! * shiftSqProd n *
              (shiftSum n ^ 3 / 6 + shiftSum n * shiftSqSum n / 12) *
                (3 ^ n) ^ 2 := by
        calc
          ↑((2 * n + 5).choose (2 * n + 3)) *
              (↑(2 * n + 3)! * shiftSqProd n *
                (shiftSum n ^ 3 / 6 + shiftSum n * shiftSqSum n / 12)) *
                (3 ^ n) ^ 2 * 2
              = (↑((2 * n + 5).choose (2 * n + 3)) * ↑(2 * n + 3)! * 2) *
                  shiftSqProd n *
                    (shiftSum n ^ 3 / 6 + shiftSum n * shiftSqSum n / 12) *
                      (3 ^ n) ^ 2 := by ring
          _ = ↑(2 * n + 5)! * shiftSqProd n *
              (shiftSum n ^ 3 / 6 + shiftSum n * shiftSqSum n / 12) *
                (3 ^ n) ^ 2 := by
                rw [hcoef3]
      rw [h0, h1, h2, h3]
      ring

lemma ofDigits_ternaryDigits {n : ℕ} (f : Fin n → Fin 3) :
    Nat.ofDigits 3 (ternaryDigits f) = (finFunctionFinEquiv f : ℕ) := by
  rw [Nat.ofDigits_eq_sum_mapIdx, finFunctionFinEquiv_apply]
  rw [List.mapIdx_eq_ofFn, List.sum_ofFn]
  simp [ternaryDigits]
  refine Fintype.sum_equiv (finCongr (by simp)) _ _ ?_
  intro i
  simp
  congr

lemma natCast_finFunctionFinEquiv {n : ℕ} (f : Fin n → Fin 3) :
    (((finFunctionFinEquiv f : Fin (3 ^ n)) : ℕ) : ℂ) = ternaryValue f := by
  rw [finFunctionFinEquiv_apply, ternaryValue]
  norm_cast

lemma ternaryDigits_mem_fixedLength {n : ℕ} (f : Fin n → Fin 3) :
    ternaryDigits f ∈ {L : List ℕ | L.length = n ∧ ∀ x ∈ L, x < 3} := by
  simp [ternaryDigits]

lemma num_ones_digits_finFunction {n : ℕ} (f : Fin n → Fin 3) :
    num_ones (Nat.digits 3 ((finFunctionFinEquiv f : Fin (3 ^ n)) : ℕ)) =
      num_ones (ternaryDigits f) := by
  have h :
      Nat.digitsAppend 3 n ((finFunctionFinEquiv f : Fin (3 ^ n)) : ℕ) =
        ternaryDigits f := by
    rw [← ofDigits_ternaryDigits f]
    exact (Nat.setInvOn_digitsAppend_ofDigits (b := 3) (by norm_num) n).1
      (ternaryDigits_mem_fixedLength f)
  rw [← h]
  simp [Nat.digitsAppend, num_ones_append, num_ones_replicate_zero]

lemma original_range_sum_eq_fun (n m : ℕ) (z : ℂ) :
    (∑ k ∈ Finset.range (3 ^ n),
      (-2 : ℂ) ^ (num_ones (Nat.digits 3 k)) * (z + k) ^ m) =
      ∑ f : Fin n → Fin 3, ternaryWeight f * (z + ternaryValue f) ^ m := by
  rw [Finset.sum_range]
  rw [← Equiv.sum_comp (finFunctionFinEquiv (m := 3) (n := n))]
  apply Finset.sum_congr rfl
  intro f hf
  rw [num_ones_digits_finFunction, natCast_finFunctionFinEquiv]
  rfl

lemma sum_fintype_range_comm {α M : Type*} [Fintype α] [AddCommMonoid M]
    (N : ℕ) (F : α → ℕ → M) :
    (∑ a : α, ∑ i ∈ Finset.range N, F a i) =
      ∑ i ∈ Finset.range N, ∑ a : α, F a i := by
  simpa using
    (Finset.sum_comm (s := (Finset.univ : Finset α))
      (t := Finset.range N) (f := fun a i => F a i))

lemma fun_sum_pow_eq_moments (n m : ℕ) (z : ℂ) :
    (∑ f : Fin n → Fin 3, ternaryWeight f * (z + ternaryValue f) ^ m) =
      ∑ e ∈ Finset.range (m + 1),
        (m.choose e : ℂ) * funMoment n e * z ^ (m - e) := by
  simp_rw [add_comm z, add_pow]
  simp_rw [Finset.mul_sum]
  rw [sum_fintype_range_comm]
  apply Finset.sum_congr rfl
  intro e he
  unfold funMoment
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  ring

lemma fun_sum_2023_cubic (z : ℂ) :
    (∑ f : Fin 1010 → Fin 3, ternaryWeight f * (z + ternaryValue f) ^ 2023) =
      (Nat.factorial 2023 : ℂ) * shiftSqProd 1010 *
        (z ^ 3 / 6 + shiftSum 1010 * z ^ 2 / 2 +
          (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
          (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12)) := by
  rw [fun_sum_pow_eq_moments]
  change (∑ e ∈ Finset.range 2024,
      (↑(Nat.choose 2023 e) * funMoment 1010 e) * z ^ (2023 - e)) =
    (Nat.factorial 2023 : ℂ) * shiftSqProd 1010 *
      (z ^ 3 / 6 + shiftSum 1010 * z ^ 2 / 2 +
        (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
        (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12))
  conv_lhs => rw [Finset.sum_range_add (n := 2020) (m := 4)]
  have hfirst :
      (∑ e ∈ Finset.range 2020,
        (↑(Nat.choose 2023 e) * funMoment 1010 e) * z ^ (2023 - e)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [funMoment_eq_zero_of_lt (n := 1010) (Finset.mem_range.mp he)]
    ring
  rw [hfirst, zero_add]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  have hidx0 : 2020 + 0 = 2020 := by norm_num
  have hidx1 : 2020 + 1 = 2021 := by norm_num
  have hidx2 : 2020 + 2 = 2022 := by norm_num
  have hidx3 : 2020 + 3 = 2023 := by norm_num
  have hexp0 : 2023 - (2020 + 0) = 3 := by norm_num
  have hexp1 : 2023 - (2020 + 1) = 2 := by norm_num
  have hexp2 : 2023 - (2020 + 2) = 1 := by norm_num
  have hexp3 : 2023 - (2020 + 3) = 0 := by norm_num
  rw [hidx0, hidx1, hidx2, hidx3, hexp0, hexp1, hexp2, hexp3]
  simp only [zero_add, pow_one, pow_zero, mul_one]
  change
      (Nat.choose 2023 2020 : ℂ) * funMoment 1010 2020 * z ^ 3 +
          (Nat.choose 2023 2021 : ℂ) * funMoment 1010 2021 * z ^ 2 +
        (Nat.choose 2023 2022 : ℂ) * funMoment 1010 2022 * z +
      (Nat.choose 2023 2023 : ℂ) * funMoment 1010 2023 =
    (Nat.factorial 2023 : ℂ) * shiftSqProd 1010 *
      (z ^ 3 / 6 + shiftSum 1010 * z ^ 2 / 2 +
        (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
        (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12))
  rw [funMoment_two_mul, funMoment_two_mul_add_one, funMoment_two_mul_add_two,
    funMoment_two_mul_add_three]
  have hfac0 : 2 * 1010 = 2020 := by norm_num
  have hfac1 : 2 * 1010 + 1 = 2021 := by norm_num
  have hfac2 : 2 * 1010 + 2 = 2022 := by norm_num
  have hfac3 : 2 * 1010 + 3 = 2023 := by norm_num
  rw [hfac0, hfac1, hfac2, hfac3]
  have hcoef0 :
      ((Nat.choose 2023 2020 : ℂ) * (Nat.factorial 2020 : ℂ) =
        (Nat.factorial 2023 : ℂ) / 6) := by
    have h := cast_choose_add_mul_factorial 2020 3
    have hadd : 2020 + 3 = 2023 := by norm_num
    rw [hadd] at h
    have hsmall : ((Nat.factorial 3 : ℕ) : ℂ) = 6 := by norm_num
    rw [hsmall] at h
    calc
      (Nat.choose 2023 2020 : ℂ) * (Nat.factorial 2020 : ℂ)
          = ((Nat.choose 2023 2020 : ℂ) * (Nat.factorial 2020 : ℂ) * 6) / 6 := by ring
      _ = (Nat.factorial 2023 : ℂ) / 6 := by rw [h]
  have hcoef1 :
      ((Nat.choose 2023 2021 : ℂ) * (Nat.factorial 2021 : ℂ) =
        (Nat.factorial 2023 : ℂ) / 2) := by
    have h := cast_choose_add_mul_factorial 2021 2
    have hadd : 2021 + 2 = 2023 := by norm_num
    rw [hadd] at h
    have hsmall : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num
    rw [hsmall] at h
    calc
      (Nat.choose 2023 2021 : ℂ) * (Nat.factorial 2021 : ℂ)
          = ((Nat.choose 2023 2021 : ℂ) * (Nat.factorial 2021 : ℂ) * 2) / 2 := by ring
      _ = (Nat.factorial 2023 : ℂ) / 2 := by rw [h]
  have hcoef2 :
      ((Nat.choose 2023 2022 : ℂ) * (Nat.factorial 2022 : ℂ) =
        (Nat.factorial 2023 : ℂ)) := by
    have h := cast_choose_add_mul_factorial 2022 1
    have hadd : 2022 + 1 = 2023 := by norm_num
    rw [hadd] at h
    have hsmall : ((Nat.factorial 1 : ℕ) : ℂ) = 1 := by norm_num
    rw [hsmall, mul_one] at h
    exact h
  have hcoef3 :
      ((Nat.choose 2023 2023 : ℂ) * (Nat.factorial 2023 : ℂ) =
        (Nat.factorial 2023 : ℂ)) := by
    rw [Nat.choose_self]
    ring
  calc
    _ =
        ((Nat.choose 2023 2020 : ℂ) * (Nat.factorial 2020 : ℂ)) *
            shiftSqProd 1010 * z ^ 3 +
          ((Nat.choose 2023 2021 : ℂ) * (Nat.factorial 2021 : ℂ)) *
              shiftSqProd 1010 * shiftSum 1010 * z ^ 2 +
        ((Nat.choose 2023 2022 : ℂ) * (Nat.factorial 2022 : ℂ)) *
            shiftSqProd 1010 *
              (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
          ((Nat.choose 2023 2023 : ℂ) * (Nat.factorial 2023 : ℂ)) *
            shiftSqProd 1010 *
              (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12) := by
        ring
    _ = (Nat.factorial 2023 : ℂ) * shiftSqProd 1010 *
        (z ^ 3 / 6 + shiftSum 1010 * z ^ 2 / 2 +
          (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
          (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12)) := by
        rw [hcoef0, hcoef1, hcoef2, hcoef3]
        ring

lemma shiftSum_eq_geom (n : ℕ) :
    shiftSum n = ((3 : ℂ) ^ n - 1) / 2 := by
  unfold shiftSum
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (3 : ℂ) ^ i) n]
  rw [geom_sum_eq (by norm_num : (3 : ℂ) ≠ 1) n]
  norm_num

lemma shiftSqSum_eq_geom (n : ℕ) :
    shiftSqSum n = ((9 : ℂ) ^ n - 1) / 8 := by
  unfold shiftSqSum
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((3 : ℂ) ^ i) ^ 2) n]
  have hpow : ∀ i : ℕ, ((3 : ℂ) ^ i) ^ 2 = (9 : ℂ) ^ i := by
    intro i
    calc
      ((3 : ℂ) ^ i) ^ 2 = ((3 : ℂ) ^ 2) ^ i := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = (9 : ℂ) ^ i := by norm_num
  simp_rw [hpow]
  rw [geom_sum_eq (by norm_num : (9 : ℂ) ≠ 1) n]
  norm_num

lemma shiftSqProd_ne_zero (n : ℕ) : shiftSqProd n ≠ 0 := by
  unfold shiftSqProd
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => ((3 : ℂ) ^ i) ^ 2) n]
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  exact pow_ne_zero 2 (pow_ne_zero i (by norm_num : (3 : ℂ) ≠ 0))

lemma cubic_core_factor (z s q : ℂ) :
    z ^ 3 / 6 + s * z ^ 2 / 2 + (s ^ 2 / 2 + q / 12) * z +
        (s ^ 3 / 6 + s * q / 12) =
      (z + s) * ((z + s) ^ 2 + q / 2) / 6 := by
  ring

lemma sqrt_offset_sq :
    (((Real.sqrt ((9 : ℝ) ^ 1010 - 1) : ℂ) * Complex.I / 4) ^ 2) =
      -(((9 : ℂ) ^ 1010 - 1) / 16) := by
  have hnonneg : 0 ≤ (9 : ℝ) ^ 1010 - 1 := by
    have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ 1010 := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)
    exact sub_nonneg.mpr hpow
  have hsqrtR : Real.sqrt ((9 : ℝ) ^ 1010 - 1) ^ 2 = ((9 : ℝ) ^ 1010 - 1) :=
    Real.sq_sqrt hnonneg
  have hsqrt : ((Real.sqrt ((9 : ℝ) ^ 1010 - 1) : ℂ) ^ 2) =
      (((9 : ℝ) ^ 1010 - 1 : ℝ) : ℂ) := by
    exact_mod_cast hsqrtR
  rw [div_pow, mul_pow, hsqrt, Complex.I_sq]
  have hcast : (((9 : ℝ) ^ 1010 - 1 : ℝ) : ℂ) = (9 : ℂ) ^ 1010 - 1 := by
    norm_num
  rw [hcast]
  have htmp (X : ℂ) : X * (-1) / (4 : ℂ) ^ 2 = -(X / 16) := by
    norm_num
    ring
  exact htmp ((9 : ℂ) ^ 1010 - 1)

lemma centered_cubic_roots (C B : ℂ) :
    {z : ℂ | (z - C) * ((z - C) ^ 2 - B ^ 2) = 0} =
      ({C, C + B, C - B} : Set ℂ) := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hlin | hquad
    · left
      calc
        z = (z - C) + C := by ring
        _ = C := by rw [hlin]; ring
    · have hfact : (z - C - B) * (z - C + B) = 0 := by
        have hfac : (z - C) ^ 2 - B ^ 2 = (z - C - B) * (z - C + B) := by
          ring
        rwa [hfac] at hquad
      rcases mul_eq_zero.mp hfact with hminus | hplus
      · right; left
        calc
          z = (z - C - B) + C + B := by ring
          _ = C + B := by rw [hminus]; ring
      · right; right
        calc
          z = (z - C + B) + C - B := by ring
          _ = C - B := by rw [hplus]; ring
  · intro hz
    rcases hz with hz | hz | hz
    · rw [hz]
      ring
    · rw [hz]
      ring
    · rw [hz]
      ring

lemma original_sum_2023_cubic (z : ℂ) :
    (∑ k ∈ Finset.Icc 0 (3 ^ 1010 - 1),
      (-2 : ℂ) ^ (num_ones (Nat.digits 3 k)) * (z + k) ^ 2023) =
      (Nat.factorial 2023 : ℂ) * shiftSqProd 1010 *
        (z ^ 3 / 6 + shiftSum 1010 * z ^ 2 / 2 +
          (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
          (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12)) := by
  have hpowne : (3 ^ 1010 : ℕ) ≠ 0 := by
    exact pow_ne_zero 1010 (by norm_num : (3 : ℕ) ≠ 0)
  have hrange : Finset.Icc 0 (3 ^ 1010 - 1) = Finset.range (3 ^ 1010) :=
    (Nat.range_eq_Icc_zero_sub_one (3 ^ 1010) hpowne).symm
  rw [hrange]
  rw [original_range_sum_eq_fun 1010 2023 z]
  exact fun_sum_2023_cubic z

lemma final_cubic_zero_set :
    {z : ℂ |
      (Nat.factorial 2023 : ℂ) * shiftSqProd 1010 *
        (z ^ 3 / 6 + shiftSum 1010 * z ^ 2 / 2 +
          (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
          (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12)) = 0} =
      (({-(3^1010 - 1)/2,
        -(3^1010 - 1)/2 + Real.sqrt (9^1010 - 1) * Complex.I/4,
        -(3^1010 - 1)/2 - Real.sqrt (9^1010 - 1) * Complex.I/4}) : Set ℂ) := by
  let C : ℂ := -((3 : ℂ) ^ 1010 - 1) / 2
  let B : ℂ := (Real.sqrt ((9 : ℝ) ^ 1010 - 1) : ℂ) * Complex.I / 4
  have hsumC : shiftSum 1010 = -C := by
    dsimp [C]
    rw [shiftSum_eq_geom]
    have htmp (X : ℂ) : (X - 1) / 2 = -(-(X - 1) / 2) := by
      ring
    exact htmp ((3 : ℂ) ^ 1010)
  have hqB : shiftSqSum 1010 / 2 = -B ^ 2 := by
    dsimp [B]
    rw [shiftSqSum_eq_geom, sqrt_offset_sq]
    have htmp (X : ℂ) : ((X - 1) / 8) / 2 = -(-((X - 1) / 16)) := by
      ring
    exact htmp ((9 : ℂ) ^ 1010)
  have hpoly : ∀ z : ℂ,
      z ^ 3 / 6 + shiftSum 1010 * z ^ 2 / 2 +
          (shiftSum 1010 ^ 2 / 2 + shiftSqSum 1010 / 12) * z +
          (shiftSum 1010 ^ 3 / 6 + shiftSum 1010 * shiftSqSum 1010 / 12) =
        (z - C) * ((z - C) ^ 2 - B ^ 2) / 6 := by
    intro z
    rw [cubic_core_factor, hsumC, hqB]
    have htmp (w c b : ℂ) :
        (w + -c) * ((w + -c) ^ 2 + -b ^ 2) / 6 =
          (w - c) * ((w - c) ^ 2 - b ^ 2) / 6 := by
      ring
    exact htmp z C B
  have hscale : (Nat.factorial 2023 : ℂ) * shiftSqProd 1010 ≠ 0 := by
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 2023))
      (shiftSqProd_ne_zero 1010)
  ext z
  rw [Set.mem_setOf_eq, hpoly z]
  have hiff :
      ((Nat.factorial 2023 : ℂ) * shiftSqProd 1010 *
            ((z - C) * ((z - C) ^ 2 - B ^ 2) / 6) = 0) ↔
        (z - C) * ((z - C) ^ 2 - B ^ 2) = 0 := by
    constructor
    · intro hz
      have hdiv : (z - C) * ((z - C) ^ 2 - B ^ 2) / 6 = 0 :=
        eq_zero_of_ne_zero_of_mul_left_eq_zero hscale hz
      rcases div_eq_zero_iff.mp hdiv with hnum | hsix
      · exact hnum
      · norm_num at hsix
    · intro hz
      rw [hz]
      ring
  rw [hiff]
  exact Set.ext_iff.mp (centered_cubic_roots C B) z

end Putnam2023A5
-- {-(3^1010 - 1)/2, -(3^1010 - 1)/2 + Real.sqrt (9^1010 - 1) * Complex.I/4, -(3^1010 - 1)/2 - Real.sqrt (9^1010 - 1) * Complex.I/4}
/--
For a nonnegative integer $k$, let $f(k)$ be the number of ones in the base 3 representation of $k$. Find all complex numbers $z$ such that \[ \sum_{k=0}^{3^{1010}-1} (-2)^{f(k)} (z+k)^{2023} = 0. \]
-/
theorem putnam_2023_a5
: {z : ℂ | ∑ k ∈ Finset.Icc 0 (3^1010 - 1), (-2)^(num_ones (digits 3 k)) * (z + k)^2023 = 0} = (({-(3^1010 - 1)/2, -(3^1010 - 1)/2 + Real.sqrt (9^1010 - 1) * Complex.I/4, -(3^1010 - 1)/2 - Real.sqrt (9^1010 - 1) * Complex.I/4}) : Set ℂ ) := by
  rw [show
      {z : ℂ |
        ∑ k ∈ Finset.Icc 0 (3^1010 - 1),
            (-2) ^ (num_ones (digits 3 k)) * (z + k)^2023 = 0} =
        {z : ℂ |
          (Nat.factorial 2023 : ℂ) * Putnam2023A5.shiftSqProd 1010 *
            (z ^ 3 / 6 + Putnam2023A5.shiftSum 1010 * z ^ 2 / 2 +
              (Putnam2023A5.shiftSum 1010 ^ 2 / 2 + Putnam2023A5.shiftSqSum 1010 / 12) * z +
              (Putnam2023A5.shiftSum 1010 ^ 3 / 6 +
                Putnam2023A5.shiftSum 1010 * Putnam2023A5.shiftSqSum 1010 / 12)) = 0} by
      ext z
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
      rw [Putnam2023A5.original_sum_2023_cubic z]]
  exact Putnam2023A5.final_cubic_zero_set
