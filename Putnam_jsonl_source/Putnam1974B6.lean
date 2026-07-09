import Mathlib

open Set Nat Polynomial Filter Topology

private def modClassCount {α : Type*} (s : Finset α) (r : ℕ) : ℕ :=
  (s.powerset.filter fun t => t.card ≡ r [MOD 3]).card

private def stepTriple : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | (a, b, c) => (a + c, b + a, c + b)

private def tripleCount : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | n + 1 => stepTriple (tripleCount n)

private lemma mod_shift0 (n : ℕ) : n + 1 ≡ 0 [MOD 3] ↔ n ≡ 2 [MOD 3] := by
  change ((n + 1) % 3 = 0) ↔ (n % 3 = 2)
  have hn := Nat.mod_lt n (by norm_num : 0 < 3)
  have hn1 := Nat.mod_lt (n + 1) (by norm_num : 0 < 3)
  have hdiv := Nat.div_add_mod n 3
  have hdiv1 := Nat.div_add_mod (n + 1) 3
  omega

private lemma mod_shift1 (n : ℕ) : n + 1 ≡ 1 [MOD 3] ↔ n ≡ 0 [MOD 3] := by
  change ((n + 1) % 3 = 1) ↔ (n % 3 = 0)
  have hn := Nat.mod_lt n (by norm_num : 0 < 3)
  have hn1 := Nat.mod_lt (n + 1) (by norm_num : 0 < 3)
  have hdiv := Nat.div_add_mod n 3
  have hdiv1 := Nat.div_add_mod (n + 1) 3
  omega

private lemma mod_shift2 (n : ℕ) : n + 1 ≡ 2 [MOD 3] ↔ n ≡ 1 [MOD 3] := by
  change ((n + 1) % 3 = 2) ↔ (n % 3 = 1)
  have hn := Nat.mod_lt n (by norm_num : 0 < 3)
  have hn1 := Nat.mod_lt (n + 1) (by norm_num : 0 < 3)
  have hdiv := Nat.div_add_mod n 3
  have hdiv1 := Nat.div_add_mod (n + 1) 3
  omega

private lemma insert_count_aux {α : Type*} [DecidableEq α] {a : α} {s : Finset α}
    (ha : a ∉ s) (r pred : ℕ)
    (hshift : ∀ n : ℕ, n + 1 ≡ r [MOD 3] ↔ n ≡ pred [MOD 3]) :
    modClassCount (insert a s) r = modClassCount s r + modClassCount s pred := by
  unfold modClassCount
  rw [Finset.powerset_insert s a, Finset.filter_union]
  have hdisj : Disjoint (s.powerset.filter fun t => t.card ≡ r [MOD 3])
      ((s.powerset.image (insert a)).filter fun t => t.card ≡ r [MOD 3]) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image] at ht hti
    rcases ht with ⟨hts, _⟩
    rcases hti with ⟨⟨u, _hu, rfl⟩, _⟩
    exact (Finset.notMem_mono hts ha) (Finset.mem_insert_self a u)
  rw [Finset.card_union_of_disjoint hdisj]
  congr 1
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  · congr 1
    ext t
    simp only [Finset.mem_filter]
    constructor
    · intro ht
      exact ⟨ht.1, by
        have hat : a ∉ t := Finset.notMem_mono (Finset.mem_powerset.mp ht.1) ha
        rw [Finset.card_insert_of_notMem hat] at ht
        exact (hshift t.card).mp ht.2⟩
    · intro ht
      exact ⟨ht.1, by
        have hat : a ∉ t := Finset.notMem_mono (Finset.mem_powerset.mp ht.1) ha
        rw [Finset.card_insert_of_notMem hat]
        exact (hshift t.card).mpr ht.2⟩
  · intro u hu v hv h
    have hau : a ∉ u := Finset.notMem_mono
      (Finset.mem_powerset.1 (Finset.mem_filter.1 hu).1) ha
    have hav : a ∉ v := Finset.notMem_mono
      (Finset.mem_powerset.1 (Finset.mem_filter.1 hv).1) ha
    have h' := congrArg (fun z : Finset α => z.erase a) h
    simpa [Finset.erase_insert hau, Finset.erase_insert hav] using h'

private lemma insert_count0 {α : Type*} [DecidableEq α] {a : α} {s : Finset α}
    (ha : a ∉ s) :
    modClassCount (insert a s) 0 = modClassCount s 0 + modClassCount s 2 :=
  insert_count_aux ha 0 2 mod_shift0

private lemma insert_count1 {α : Type*} [DecidableEq α] {a : α} {s : Finset α}
    (ha : a ∉ s) :
    modClassCount (insert a s) 1 = modClassCount s 1 + modClassCount s 0 :=
  insert_count_aux ha 1 0 mod_shift1

private lemma insert_count2 {α : Type*} [DecidableEq α] {a : α} {s : Finset α}
    (ha : a ∉ s) :
    modClassCount (insert a s) 2 = modClassCount s 2 + modClassCount s 1 :=
  insert_count_aux ha 2 1 mod_shift2

private lemma modClassCount_eq_triple {α : Type*} [DecidableEq α] (s : Finset α) :
    (modClassCount s 0, modClassCount s 1, modClassCount s 2) = tripleCount s.card := by
  induction s using Finset.induction_on with
  | empty =>
      unfold modClassCount tripleCount
      rw [Finset.powerset_empty]
      repeat rw [Finset.filter_singleton]
      norm_num [Nat.ModEq]
  | insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha]
      simp only [tripleCount]
      rw [insert_count0 ha, insert_count1 ha, insert_count2 ha]
      simpa [stepTriple] using congrArg stepTriple ih

private lemma tripleCount_six_step (n q : ℕ) (h : tripleCount n = (q, q, q + 1)) :
    tripleCount (n + 6) = (64 * q + 21, 64 * q + 21, 64 * q + 22) := by
  rw [show n + 6 = ((((((n + 1) + 1) + 1) + 1) + 1) + 1) by omega]
  simp [tripleCount, h, stepTriple]
  omega

private lemma tripleCount_six_mul_add_four (m : ℕ) :
    ∃ q : ℕ, tripleCount (6 * m + 4) = (q, q, q + 1) ∧
      2 ^ (6 * m + 4) = 3 * q + 1 := by
  induction m with
  | zero =>
      refine ⟨5, ?_, ?_⟩ <;> norm_num [tripleCount, stepTriple]
  | succ m ih =>
      rcases ih with ⟨q, hq, hpow⟩
      refine ⟨64 * q + 21, ?_, ?_⟩
      · rw [show 6 * (m + 1) + 4 = (6 * m + 4) + 6 by omega]
        simpa using tripleCount_six_step (6 * m + 4) q hq
      · rw [show 6 * (m + 1) + 4 = (6 * m + 4) + 6 by omega]
        rw [pow_add, hpow]
        norm_num
        omega

private lemma ncard_modClass {α : Type*} (s : Finset α) (r : ℕ) :
    ({S | S ⊆ s ∧ S.card ≡ r [MOD 3]} : Set (Finset α)).ncard =
      modClassCount s r := by
  unfold modClassCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext S
  simp

-- ((2^1000 - 1)/3, (2^1000 - 1)/3, 1 + (2^1000 - 1)/3)
/--
For a set with $1000$ elements, how many subsets are there whose candinality is respectively $\equiv 0 \bmod 3, \equiv 1 \bmod 3, \equiv 2 \bmod 3$?
-/
theorem putnam_1974_b6
(n : ℤ)
(hn : n = 1000)
(count0 count1 count2 : ℕ)
(hcount0 : count0 = {S | S ⊆ Finset.Icc 1 n ∧ S.card ≡ 0 [MOD 3]}.ncard)
(hcount1 : count1 = {S | S ⊆ Finset.Icc 1 n ∧ S.card ≡ 1 [MOD 3]}.ncard)
(hcount2 : count2 = {S | S ⊆ Finset.Icc 1 n ∧ S.card ≡ 2 [MOD 3]}.ncard)
: (count0, count1, count2) = (((2^1000 - 1)/3, (2^1000 - 1)/3, 1 + (2^1000 - 1)/3) : (ℕ × ℕ × ℕ) ) := by
  subst n
  let s : Finset ℤ := Finset.Icc 1 (1000 : ℤ)
  have hsCard : s.card = 1000 := by
    change (Finset.Icc (1 : ℤ) 1000).card = 1000
    rw [Int.card_Icc]
    exact Int.toNat_natCast 1000
  have hcounts : (count0, count1, count2) =
      (modClassCount s 0, modClassCount s 1, modClassCount s 2) := by
    rw [hcount0, hcount1, hcount2]
    simp [s, ncard_modClass]
  have htriple : (modClassCount s 0, modClassCount s 1, modClassCount s 2) =
      tripleCount 1000 := by
    simpa [hsCard] using modClassCount_eq_triple s
  rcases tripleCount_six_mul_add_four 166 with ⟨q, hq, hpow⟩
  have hq1000 : tripleCount 1000 = (q, q, q + 1) := by
    simpa using hq
  have hpow1000 : 2 ^ 1000 = 3 * q + 1 := by
    rw [show (1000 : ℕ) = 6 * 166 + 4 by norm_num]
    exact hpow
  have hqdiv : q = (2 ^ 1000 - 1) / 3 := by
    rw [hpow1000]
    rw [Nat.add_sub_cancel]
    rw [Nat.mul_div_right]
    norm_num
  calc
    (count0, count1, count2) =
        (modClassCount s 0, modClassCount s 1, modClassCount s 2) := hcounts
    _ = tripleCount 1000 := htriple
    _ = (q, q, q + 1) := hq1000
    _ = (((2 ^ 1000 - 1) / 3, (2 ^ 1000 - 1) / 3,
          1 + (2 ^ 1000 - 1) / 3) : ℕ × ℕ × ℕ) := by
        rw [hqdiv]
        rw [Nat.add_comm]
