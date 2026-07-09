import Mathlib

open Set Filter Topology Real

abbrev putnam_1985_a4_solution : Set (Fin 100) :=
  {k : Fin 100 | ∃ n : ℕ, n ∈ Set.Ico (87 : ℕ) 88 ∧ k = (Fin.ofNat 100 n : Fin 100)}

/--
Define a sequence $\{a_i\}$ by $a_1=3$ and $a_{i+1}=3^{a_i}$ for $i \geq 1$. Which integers between $00$ and $99$ inclusive occur as the last two digits in the decimal expansion of infinitely many $a_i$?
-/
theorem putnam_1985_a4
    (a : ℕ → ℕ)
    (ha1 : a 1 = 3)
    (ha : ∀ i ≥ 1, a (i + 1) = 3 ^ a i) :
    {k : Fin 100 | ∀ N : ℕ, ∃ i ≥ N, a i % 100 = k} = putnam_1985_a4_solution :=
  by
  have pow_mod100_of_mod20_eq_seven :
      ∀ n : ℕ, n % 20 = 7 → 3 ^ n % 100 = 87 := by
    intro n hn
    have hz : ((3 : ZMod 100) ^ n) = 87 := by
      have hn' : n = 20 * (n / 20) + 7 := by
        calc
          n = 20 * (n / 20) + n % 20 := (Nat.div_add_mod n 20).symm
          _ = 20 * (n / 20) + 7 := by rw [hn]
      rw [hn', pow_add, pow_mul]
      have h20 : ((3 : ZMod 100) ^ 20) = 1 := by
        change ((3 ^ 20 : ℕ) : ZMod 100) = ((1 : ℕ) : ZMod 100)
        rw [ZMod.natCast_eq_natCast_iff']
        norm_num
      rw [h20, one_pow, one_mul]
      change ((3 ^ 7 : ℕ) : ZMod 100) = ((87 : ℕ) : ZMod 100)
      rw [ZMod.natCast_eq_natCast_iff']
      norm_num
    have hz' : ((3 ^ n : ℕ) : ZMod 100) = ((87 : ℕ) : ZMod 100) := by
      simpa [Nat.cast_pow] using hz
    exact (ZMod.natCast_eq_natCast_iff' (3 ^ n) 87 100).1 hz'
  have mod20_of_mod100_eq87 : ∀ n : ℕ, n % 100 = 87 → n % 20 = 7 := by
    intro n hn
    have h100 : n ≡ 87 [MOD 100] := by
      simp [Nat.ModEq, hn]
    have h20 : n ≡ 87 [MOD 20] := h100.of_dvd (by norm_num)
    simpa [Nat.ModEq] using h20
  have ha2 : a 2 = 27 := by
    rw [ha 1 (by norm_num), ha1]
    norm_num
  have ha3mod : a 3 % 100 = 87 := by
    rw [ha 2 (by norm_num), ha2]
    norm_num
  have htail : ∀ i : ℕ, 3 ≤ i → a i % 100 = 87 := by
    intro i hi
    refine Nat.le_induction ha3mod ?_ i hi
    intro n hn ih
    have hn1 : 1 ≤ n := by omega
    rw [ha n hn1]
    exact pow_mod100_of_mod20_eq_seven (a n) (mod20_of_mod100_eq87 (a n) ih)
  ext k
  constructor
  · intro hk
    rcases hk 3 with ⟨i, hi, hki⟩
    have hi87 : a i % 100 = 87 := htail i hi
    rw [hi87] at hki
    have hkval : (k : ℕ) = 87 := hki.symm
    refine ⟨87, by simp, ?_⟩
    apply Fin.ext
    rw [hkval]
    norm_num [Fin.ofNat]
  · intro hk
    rcases hk with ⟨n, hn, hnk⟩
    have hn87 : n = 87 := by
      rcases hn with ⟨hlo, hhi⟩
      omega
    have hkval : (k : ℕ) = 87 := by
      rw [hnk, hn87]
      norm_num [Fin.ofNat]
    intro N
    refine ⟨max N 3, le_max_left N 3, ?_⟩
    have hi3 : 3 ≤ max N 3 := le_max_right N 3
    rw [htail (max N 3) hi3]
    rw [hkval]
