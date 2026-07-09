import Mathlib

open Set Filter Topology Real

-- {87}
/--
Define a sequence $\{a_i\}$ by $a_1=3$ and $a_{i+1}=3^{a_i}$ for $i \geq 1$. Which integers between $00$ and $99$ inclusive occur as the last two digits in the decimal expansion of infinitely many $a_i$?
-/
theorem putnam_1985_a4
    (a : ℕ → ℕ)
    (ha1 : a 1 = 3)
    (ha : ∀ i ≥ 1, a (i + 1) = 3 ^ a i) :
    {k : Fin 100 | ∀ N : ℕ, ∃ i ≥ N, a i % 100 = k} = (({87}) : Set (Fin 100) ) := by
  have pow3_mod20_of_mod20_eq7 : ∀ n : ℕ, n % 20 = 7 → 3 ^ n % 20 = 7 := by
    intro n hn
    have hn4 : n % 4 = 3 := by
      have hmod20 : n ≡ 7 [MOD 20] := by simpa [Nat.ModEq] using hn
      have h := Nat.ModEq.of_dvd (by norm_num : 4 ∣ 20) hmod20
      simpa [Nat.ModEq] using h
    calc
      3 ^ n % 20 = 3 ^ (n % 4 + 4 * (n / 4)) % 20 := by rw [Nat.mod_add_div n 4]
      _ = (3 ^ (n % 4) * (3 ^ 4) ^ (n / 4)) % 20 := by rw [pow_add, pow_mul]
      _ = (3 ^ 3 * (3 ^ 4) ^ (n / 4)) % 20 := by rw [hn4]
      _ = 7 := by
        have hcycle : (3 ^ 4) ^ (n / 4) ≡ 1 [MOD 20] := by
          have : 3 ^ 4 ≡ 1 [MOD 20] := by norm_num [Nat.ModEq]
          simpa using Nat.ModEq.pow (n / 4) this
        have hhead : 3 ^ 3 ≡ 7 [MOD 20] := by norm_num [Nat.ModEq]
        have hmul := Nat.ModEq.mul hhead hcycle
        simpa [Nat.ModEq] using hmul
  have pow3_mod100_of_mod20_eq7 : ∀ n : ℕ, n % 20 = 7 → 3 ^ n % 100 = 87 := by
    intro n hn
    calc
      3 ^ n % 100 = 3 ^ (n % 20 + 20 * (n / 20)) % 100 := by rw [Nat.mod_add_div n 20]
      _ = (3 ^ (n % 20) * (3 ^ 20) ^ (n / 20)) % 100 := by rw [pow_add, pow_mul]
      _ = (3 ^ 7 * (3 ^ 20) ^ (n / 20)) % 100 := by rw [hn]
      _ = 87 := by
        have hcycle : (3 ^ 20) ^ (n / 20) ≡ 1 [MOD 100] := by
          have : 3 ^ 20 ≡ 1 [MOD 100] := by norm_num [Nat.ModEq]
          simpa using Nat.ModEq.pow (n / 20) this
        have hhead : 3 ^ 7 ≡ 87 [MOD 100] := by norm_num [Nat.ModEq]
        have hmul := Nat.ModEq.mul hhead hcycle
        simpa [Nat.ModEq] using hmul
  have hmod20 : ∀ j : ℕ, a (2 + j) % 20 = 7 := by
    intro j
    induction j with
    | zero =>
        have hrec := ha 1 (by norm_num)
        have h2 : a 2 = 3 ^ 3 := by simpa [ha1] using hrec
        rw [h2]
        norm_num
    | succ j ih =>
        have hrec := ha (2 + j) (by omega)
        have hrec' : a (2 + (j + 1)) = 3 ^ a (2 + j) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec
        rw [hrec']
        exact pow3_mod20_of_mod20_eq7 (a (2 + j)) ih
  have heventual : ∀ i : ℕ, i ≥ 3 → a i % 100 = 87 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hrec := ha (2 + j) (by omega)
    have hrec' : a (3 + j) = 3 ^ a (2 + j) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec
    rw [hrec']
    exact pow3_mod100_of_mod20_eq7 (a (2 + j)) (hmod20 j)
  ext k
  constructor
  · intro hk
    rcases hk 3 with ⟨i, hi, hik⟩
    have hkval : (k : ℕ) = 87 := hik.symm.trans (heventual i hi)
    have hkfin : k = (87 : Fin 100) := by
      apply Fin.ext
      simpa using hkval
    simpa using hkfin
  · intro hk
    have hkfin : k = (87 : Fin 100) := by simpa using hk
    subst k
    intro N
    refine ⟨max N 3, ?_, ?_⟩
    · exact le_max_left N 3
    · simpa using heventual (max N 3) (le_max_right N 3)
