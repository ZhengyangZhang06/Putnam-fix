import Mathlib

open Metric Set EuclideanGeometry

abbrev putnam_1970_a3_solution : ℕ × ℕ := (3, 1444)

lemma putnam_1970_a3_digit_eq (n i : ℕ) :
    (Nat.digits 10 n)[i]! = n / 10 ^ i % 10 := by
  rw [show (Nat.digits 10 n)[i]! = (Nat.digits 10 n).getD i 0 by
    simp [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]]
  exact Nat.getD_digits n i (by norm_num)

lemma putnam_1970_a3_mod1000_of_digits (x d : ℕ)
    (h0 : x % 10 = d) (h1 : x / 10 % 10 = d) (h2 : x / 100 % 10 = d) :
    x % 1000 = 111 * d := by
  have hx : x % 1000 =
      x % 10 + 10 * ((x / 10) % 10) + 100 * ((x / 100) % 10) := by
    clear h0 h1 h2 d
    omega
  rw [h0, h1, h2] at hx
  omega

lemma putnam_1970_a3_mod10000_of_digits (x d : ℕ)
    (h0 : x % 10 = d) (h1 : x / 10 % 10 = d)
    (h2 : x / 100 % 10 = d) (h3 : x / 1000 % 10 = d) :
    x % 10000 = 1111 * d := by
  have hx : x % 10000 =
      x % 10 + 10 * ((x / 10) % 10) +
        100 * ((x / 100) % 10) + 1000 * ((x / 1000) % 10) := by
    clear h0 h1 h2 h3 d
    omega
  rw [h0, h1, h2, h3] at hx
  omega

lemma putnam_1970_a3_mod80_of_mod10000 {x y : ℕ} (h : x % 10000 = y) :
    x % 80 = y % 80 := by
  have hc := congrArg (fun t : ℕ => t % 80) h
  dsimp at hc
  have hreduce : x % 10000 % 80 = x % 80 := by omega
  rwa [hreduce] at hc

lemma putnam_1970_a3_square_mod80_ne (n d : ℕ) (hd0 : d ≠ 0) (hdlt : d < 10) :
    n ^ 2 % 80 ≠ (1111 * d) % 80 := by
  let r : Fin 80 := ⟨n % 80, Nat.mod_lt n (by norm_num)⟩
  let e : Fin 10 := ⟨d, hdlt⟩
  have hfinite :
      ∀ r : Fin 80, ∀ d : Fin 10, d.val ≠ 0 →
        r.val ^ 2 % 80 ≠ (1111 * d.val) % 80 := by
    decide
  have hr : n ^ 2 % 80 = r.val ^ 2 % 80 := by
    simpa [r] using Nat.pow_mod n 2 80
  simpa [r, e, hr] using hfinite r e hd0

lemma putnam_1970_a3_small_square_mod1000_ne (n d : ℕ)
    (hn : n < 38) (hd0 : d ≠ 0) (hdlt : d < 10) :
    n ^ 2 % 1000 ≠ (111 * d) % 1000 := by
  let r : Fin 38 := ⟨n, hn⟩
  let e : Fin 10 := ⟨d, hdlt⟩
  have hfinite :
      ∀ r : Fin 38, ∀ d : Fin 10, d.val ≠ 0 →
        r.val ^ 2 % 1000 ≠ (111 * d.val) % 1000 := by
    decide
  simpa [r, e] using hfinite r e hd0

/--
Find the length of the longest possible sequence of equal nonzero digits (in base 10) in which a perfect square can terminate. Also, find the smallest square that attains this length.
-/
theorem putnam_1970_a3
(L : ℕ → ℕ)
(hL : ∀ n : ℕ, L n ≤ (Nat.digits 10 n).length ∧
(∀ k : ℕ, k < L n → (Nat.digits 10 n)[k]! = (Nat.digits 10 n)[0]!) ∧
(L n ≠ (Nat.digits 10 n).length → (Nat.digits 10 n)[L n]! ≠ (Nat.digits 10 n)[0]!))
: (∃ n : ℕ, (Nat.digits 10 (n^2))[0]! ≠ 0 ∧ L (n^2) = putnam_1970_a3_solution.1) ∧
(∀ n : ℕ, (Nat.digits 10 (n^2))[0]! ≠ 0 → L (n^2) ≤ putnam_1970_a3_solution.1) ∧
(∃ m : ℕ, m^2 = putnam_1970_a3_solution.2) ∧
L (putnam_1970_a3_solution.2) = putnam_1970_a3_solution.1 ∧
(Nat.digits 10 putnam_1970_a3_solution.2)[0]! ≠ 0 ∧
∀ n : ℕ, (Nat.digits 10 (n^2))[0]! ≠ 0 ∧ L (n^2) = putnam_1970_a3_solution.1 → n^2 ≥ putnam_1970_a3_solution.2 :=
by
  have h1444 : L 1444 = 3 := by
    have hle : L 1444 ≤ 4 := by
      simpa [Nat.digits, Nat.digitsAux] using (hL 1444).1
    interval_cases h : L 1444
    · have hne : L 1444 ≠ (Nat.digits 10 1444).length := by
        norm_num [h, Nat.digits, Nat.digitsAux]
      have hc := (hL 1444).2.2 hne
      norm_num [h, Nat.digits, Nat.digitsAux] at hc
    · have hne : L 1444 ≠ (Nat.digits 10 1444).length := by
        norm_num [h, Nat.digits, Nat.digitsAux]
      have hc := (hL 1444).2.2 hne
      norm_num [h, Nat.digits, Nat.digitsAux] at hc
    · have hne : L 1444 ≠ (Nat.digits 10 1444).length := by
        norm_num [h, Nat.digits, Nat.digitsAux]
      have hc := (hL 1444).2.2 hne
      norm_num [h, Nat.digits, Nat.digitsAux] at hc
    · rfl
    · have hc := (hL 1444).2.1 3 (by omega)
      norm_num [h, Nat.digits, Nat.digitsAux] at hc
  have hupper :
      ∀ n : ℕ, (Nat.digits 10 (n ^ 2))[0]! ≠ 0 → L (n ^ 2) ≤ 3 := by
    intro n hunit
    by_contra hle
    have h4 : 4 ≤ L (n ^ 2) := by omega
    let x := n ^ 2
    let d := (Nat.digits 10 x)[0]!
    have hd0 : d ≠ 0 := by
      simpa [x, d] using hunit
    have h0 : x % 10 = d := by
      simpa [d] using (putnam_1970_a3_digit_eq x 0).symm
    have hdlt : d < 10 := by
      rw [← h0]
      exact Nat.mod_lt x (by norm_num)
    have h1 : x / 10 % 10 = d := by
      rw [← show (Nat.digits 10 x)[1]! = x / 10 % 10 by
        simpa using putnam_1970_a3_digit_eq x 1]
      exact (hL x).2.1 1 (by
        have : 4 ≤ L x := by simpa [x] using h4
        omega)
    have h2 : x / 100 % 10 = d := by
      rw [← show (Nat.digits 10 x)[2]! = x / 100 % 10 by
        simpa using putnam_1970_a3_digit_eq x 2]
      exact (hL x).2.1 2 (by
        have : 4 ≤ L x := by simpa [x] using h4
        omega)
    have h3 : x / 1000 % 10 = d := by
      rw [← show (Nat.digits 10 x)[3]! = x / 1000 % 10 by
        simpa using putnam_1970_a3_digit_eq x 3]
      exact (hL x).2.1 3 (by simpa [x] using h4)
    have hxmod : x % 10000 = 1111 * d :=
      putnam_1970_a3_mod10000_of_digits x d h0 h1 h2 h3
    have hmod80 : n ^ 2 % 80 = (1111 * d) % 80 := by
      simpa [x] using putnam_1970_a3_mod80_of_mod10000 hxmod
    exact (putnam_1970_a3_square_mod80_ne n d hd0 hdlt) hmod80
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨38, ?_, ?_⟩
    · norm_num [Nat.digits, Nat.digitsAux]
    · simpa [putnam_1970_a3_solution] using h1444
  · simpa [putnam_1970_a3_solution] using hupper
  · refine ⟨38, ?_⟩
    norm_num [putnam_1970_a3_solution]
  · simpa [putnam_1970_a3_solution] using h1444
  · norm_num [putnam_1970_a3_solution, Nat.digits, Nat.digitsAux]
  · intro n hn
    by_contra hge
    have hsmall : n ^ 2 < 1444 := by
      simpa [putnam_1970_a3_solution] using (not_le.mp hge)
    have hnlt : n < 38 := by
      nlinarith [sq_nonneg (n - 38 : ℤ)]
    let x := n ^ 2
    let d := (Nat.digits 10 x)[0]!
    have hd0 : d ≠ 0 := by
      simpa [x, d] using hn.1
    have h0 : x % 10 = d := by
      simpa [d] using (putnam_1970_a3_digit_eq x 0).symm
    have hdlt : d < 10 := by
      rw [← h0]
      exact Nat.mod_lt x (by norm_num)
    have h1 : x / 10 % 10 = d := by
      rw [← show (Nat.digits 10 x)[1]! = x / 10 % 10 by
        simpa using putnam_1970_a3_digit_eq x 1]
      exact (hL x).2.1 1 (by
        have hrun : L x = 3 := by
          simpa [putnam_1970_a3_solution, x] using hn.2
        omega)
    have h2 : x / 100 % 10 = d := by
      rw [← show (Nat.digits 10 x)[2]! = x / 100 % 10 by
        simpa using putnam_1970_a3_digit_eq x 2]
      exact (hL x).2.1 2 (by
        have hrun : L x = 3 := by
          simpa [putnam_1970_a3_solution, x] using hn.2
        omega)
    have hxmod : x % 1000 = 111 * d :=
      putnam_1970_a3_mod1000_of_digits x d h0 h1 h2
    have hmod1000 : n ^ 2 % 1000 = (111 * d) % 1000 := by
      simpa [x] using congrArg (fun t : ℕ => t % 1000) hxmod
    exact (putnam_1970_a3_small_square_mod1000_ne n d hnlt hd0 hdlt) hmod1000
