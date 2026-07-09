import Mathlib

open Metric Set EuclideanGeometry

lemma putnam_1970_a3_digit_eq_mod (n i : ℕ) :
    (Nat.digits 10 n)[i]! = n / 10 ^ i % 10 := by
  simpa using (Nat.getD_digits n i (b := 10) (by norm_num : 2 ≤ 10))

lemma putnam_1970_a3_mod_1000_eq_digits3 (a : ℕ) :
    a % 1000 = a % 10 + 10 * (a / 10 % 10) + 100 * (a / 100 % 10) := by
  omega

lemma putnam_1970_a3_mod_10000_eq_digits4 (a : ℕ) :
    a % 10000 =
      a % 10 + 10 * (a / 10 % 10) + 100 * (a / 100 % 10) + 1000 * (a / 1000 % 10) := by
  omega

lemma putnam_1970_a3_no_square_four_digits (n d : ℕ)
    (hd : d < 10) (hpos : d ≠ 0) (hmod : n ^ 2 % 10000 = 1111 * d) : False := by
  have h80 : n ^ 2 % 80 = (1111 * d) % 80 := by omega
  rw [Nat.pow_mod] at h80
  have hres : n % 80 < 80 := Nat.mod_lt n (by norm_num)
  interval_cases d
  · contradiction
  all_goals
    interval_cases r : n % 80 <;> norm_num at h80

lemma putnam_1970_a3_no_small_square_three_digits (n d : ℕ)
    (hd : d < 10) (hpos : d ≠ 0) (hmod : n ^ 2 % 1000 = 111 * d)
    (hlt : n ^ 2 < 1444) : False := by
  have hn : n ≤ 37 := by nlinarith
  interval_cases n
  all_goals interval_cases d
  all_goals omega

lemma putnam_1970_a3_run_length_1444 (L : ℕ → ℕ)
    (hL : ∀ n : ℕ, L n ≤ (Nat.digits 10 n).length ∧
      (∀ k : ℕ, k < L n → (Nat.digits 10 n)[k]! = (Nat.digits 10 n)[0]!) ∧
      (L n ≠ (Nat.digits 10 n).length → (Nat.digits 10 n)[L n]! ≠ (Nat.digits 10 n)[0]!)) :
    L 1444 = 3 := by
  have h := hL 1444
  norm_num [Nat.digits_add_two_add_one] at h
  have hle : L 1444 ≤ 4 := by omega
  interval_cases hval : L 1444
  · have hb := h.2.2 (by omega)
    norm_num [hval] at hb
  · have hb := h.2.2 (by omega)
    norm_num [hval] at hb
  · have hb := h.2.2 (by omega)
    norm_num [hval] at hb
  · rfl
  · have hb := h.2.1 3 (by omega)
    norm_num [hval] at hb

lemma putnam_1970_a3_square_run_le_three (L : ℕ → ℕ)
    (hL : ∀ n : ℕ, L n ≤ (Nat.digits 10 n).length ∧
      (∀ k : ℕ, k < L n → (Nat.digits 10 n)[k]! = (Nat.digits 10 n)[0]!) ∧
      (L n ≠ (Nat.digits 10 n).length → (Nat.digits 10 n)[L n]! ≠ (Nat.digits 10 n)[0]!))
    (n : ℕ) (hfirst : (Nat.digits 10 (n ^ 2))[0]! ≠ 0) :
    L (n ^ 2) ≤ 3 := by
  by_contra hle
  have hge : 4 ≤ L (n ^ 2) := by omega
  let d := (Nat.digits 10 (n ^ 2))[0]!
  have hpos : d ≠ 0 := by simpa [d] using hfirst
  have hd : d < 10 := by
    dsimp [d]
    rw [putnam_1970_a3_digit_eq_mod (n ^ 2) 0]
    norm_num
    exact Nat.mod_lt (n ^ 2) (by norm_num)
  have hsame := (hL (n ^ 2)).2.1
  have h0 : n ^ 2 % 10 = d := by
    dsimp [d]
    rw [putnam_1970_a3_digit_eq_mod (n ^ 2) 0]
    norm_num
  have h1 : n ^ 2 / 10 % 10 = d := by
    calc
      n ^ 2 / 10 % 10 = (Nat.digits 10 (n ^ 2))[1]! := by
        simpa using (putnam_1970_a3_digit_eq_mod (n ^ 2) 1).symm
      _ = d := hsame 1 (by omega)
  have h2 : n ^ 2 / 100 % 10 = d := by
    calc
      n ^ 2 / 100 % 10 = (Nat.digits 10 (n ^ 2))[2]! := by
        simpa using (putnam_1970_a3_digit_eq_mod (n ^ 2) 2).symm
      _ = d := hsame 2 (by omega)
  have h3 : n ^ 2 / 1000 % 10 = d := by
    calc
      n ^ 2 / 1000 % 10 = (Nat.digits 10 (n ^ 2))[3]! := by
        simpa using (putnam_1970_a3_digit_eq_mod (n ^ 2) 3).symm
      _ = d := hsame 3 (by omega)
  have hmod : n ^ 2 % 10000 = 1111 * d := by
    rw [putnam_1970_a3_mod_10000_eq_digits4 (n ^ 2)]
    omega
  exact putnam_1970_a3_no_square_four_digits n d hd hpos hmod

lemma putnam_1970_a3_square_run_three_ge (L : ℕ → ℕ)
    (hL : ∀ n : ℕ, L n ≤ (Nat.digits 10 n).length ∧
      (∀ k : ℕ, k < L n → (Nat.digits 10 n)[k]! = (Nat.digits 10 n)[0]!) ∧
      (L n ≠ (Nat.digits 10 n).length → (Nat.digits 10 n)[L n]! ≠ (Nat.digits 10 n)[0]!))
    (n : ℕ) (h : (Nat.digits 10 (n ^ 2))[0]! ≠ 0 ∧ L (n ^ 2) = 3) :
    n ^ 2 ≥ 1444 := by
  by_contra hge
  have hlt : n ^ 2 < 1444 := by omega
  let d := (Nat.digits 10 (n ^ 2))[0]!
  have hpos : d ≠ 0 := by simpa [d] using h.1
  have hd : d < 10 := by
    dsimp [d]
    rw [putnam_1970_a3_digit_eq_mod (n ^ 2) 0]
    norm_num
    exact Nat.mod_lt (n ^ 2) (by norm_num)
  have hsame := (hL (n ^ 2)).2.1
  have hgeL : 3 ≤ L (n ^ 2) := by omega
  have h0 : n ^ 2 % 10 = d := by
    dsimp [d]
    rw [putnam_1970_a3_digit_eq_mod (n ^ 2) 0]
    norm_num
  have h1 : n ^ 2 / 10 % 10 = d := by
    calc
      n ^ 2 / 10 % 10 = (Nat.digits 10 (n ^ 2))[1]! := by
        simpa using (putnam_1970_a3_digit_eq_mod (n ^ 2) 1).symm
      _ = d := hsame 1 (by omega)
  have h2 : n ^ 2 / 100 % 10 = d := by
    calc
      n ^ 2 / 100 % 10 = (Nat.digits 10 (n ^ 2))[2]! := by
        simpa using (putnam_1970_a3_digit_eq_mod (n ^ 2) 2).symm
      _ = d := hsame 2 (by omega)
  have hmod : n ^ 2 % 1000 = 111 * d := by
    rw [putnam_1970_a3_mod_1000_eq_digits3 (n ^ 2)]
    omega
  exact putnam_1970_a3_no_small_square_three_digits n d hd hpos hmod hlt

-- (3, 1444)
/--
Find the length of the longest possible sequence of equal nonzero digits (in base 10) in which a perfect square can terminate. Also, find the smallest square that attains this length.
-/
theorem putnam_1970_a3
(L : ℕ → ℕ)
(hL : ∀ n : ℕ, L n ≤ (Nat.digits 10 n).length ∧
(∀ k : ℕ, k < L n → (Nat.digits 10 n)[k]! = (Nat.digits 10 n)[0]!) ∧
(L n ≠ (Nat.digits 10 n).length → (Nat.digits 10 n)[L n]! ≠ (Nat.digits 10 n)[0]!))
: (∃ n : ℕ, (Nat.digits 10 (n^2))[0]! ≠ 0 ∧ L (n^2) = ((3, 1444) : ℕ × ℕ ).1) ∧
(∀ n : ℕ, (Nat.digits 10 (n^2))[0]! ≠ 0 → L (n^2) ≤ ((3, 1444) : ℕ × ℕ ).1) ∧
(∃ m : ℕ, m^2 = ((3, 1444) : ℕ × ℕ ).2) ∧
L (((3, 1444) : ℕ × ℕ ).2) = ((3, 1444) : ℕ × ℕ ).1 ∧
(Nat.digits 10 ((3, 1444) : ℕ × ℕ ).2)[0]! ≠ 0 ∧
∀ n : ℕ, (Nat.digits 10 (n^2))[0]! ≠ 0 ∧ L (n^2) = ((3, 1444) : ℕ × ℕ ).1 → n^2 ≥ ((3, 1444) : ℕ × ℕ ).2 := by
  have h1444 : L 1444 = 3 := putnam_1970_a3_run_length_1444 L hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨38, ?_, ?_⟩
    · norm_num [Nat.digits_add_two_add_one]
    · norm_num
      exact h1444
  · intro n hn
    simpa using putnam_1970_a3_square_run_le_three L hL n hn
  · refine ⟨38, by norm_num⟩
  · simpa using h1444
  · norm_num [Nat.digits_add_two_add_one]
  · intro n hn
    have hn' : (Nat.digits 10 (n ^ 2))[0]! ≠ 0 ∧ L (n ^ 2) = 3 := by
      simpa using hn
    simpa using putnam_1970_a3_square_run_three_ge L hL n hn'
