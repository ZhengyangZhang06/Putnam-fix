import Mathlib

open Topology MvPolynomial Filter Set

abbrev putnam_2009_a5_solution : Prop := False

open scoped BigOperators

namespace Putnam2009A5

lemma gcd_two_pow (a j : ℕ) : Nat.gcd (2 ^ a) (2 ^ j) = 2 ^ min a j := by
  by_cases h : a ≤ j
  · rw [Nat.min_eq_left h, Nat.gcd_eq_left_iff_dvd]
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).2 h
  · have hj : j ≤ a := le_of_not_ge h
    rw [Nat.min_eq_right hj, Nat.gcd_eq_right_iff_dvd]
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).2 hj

lemma card_cyclic_two_pow_pow_eq_one (a j : ℕ) :
    Fintype.card {x : Multiplicative (ZMod (2 ^ a)) // x ^ (2 ^ j) = 1} =
      2 ^ min a j := by
  rw [← Nat.card_eq_fintype_card]
  calc
    Nat.card {x : Multiplicative (ZMod (2 ^ a)) // x ^ (2 ^ j) = 1}
        = Nat.gcd (2 ^ a) (2 ^ j) := by
          simpa [powMonoidHom] using
            (IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod (2 ^ a))) (2 ^ j))
    _ = 2 ^ min a j := gcd_two_pow a j

noncomputable def piPowEqOneEquiv {ι : Type*} [Fintype ι] {M : ι → Type*}
    [(i : ι) → Monoid (M i)] (d : ℕ) :
    {x : ((i : ι) → M i) // x ^ d = 1} ≃ ((i : ι) → {y : M i // y ^ d = 1}) where
  toFun x i := ⟨x.1 i, by
    have hx := congr_fun x.2 i
    simpa [Pi.pow_apply] using hx⟩
  invFun y := ⟨fun i => (y i).1, by
    ext i
    simpa [Pi.pow_apply] using (y i).2⟩
  left_inv x := by
    ext i
    rfl
  right_inv y := by
    ext i
    rfl

lemma card_pi_two_pow_pow_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (j : ℕ) :
    Fintype.card
        {x : ((i : ι) → Multiplicative (ZMod (2 ^ a i))) // x ^ (2 ^ j) = 1} =
      2 ^ (∑ i, min (a i) j) := by
  calc
    Fintype.card
        {x : ((i : ι) → Multiplicative (ZMod (2 ^ a i))) // x ^ (2 ^ j) = 1}
        = Fintype.card
            ((i : ι) → {y : Multiplicative (ZMod (2 ^ a i)) // y ^ (2 ^ j) = 1}) := by
          exact Fintype.card_congr
            (piPowEqOneEquiv (M := fun i => Multiplicative (ZMod (2 ^ a i))) (2 ^ j))
    _ = ∏ i, Fintype.card {y : Multiplicative (ZMod (2 ^ a i)) // y ^ (2 ^ j) = 1} :=
          Fintype.card_pi
    _ = ∏ i, 2 ^ min (a i) j := by
          exact Finset.prod_congr rfl
            (by intro i _; exact card_cyclic_two_pow_pow_eq_one (a i) j)
    _ = 2 ^ (∑ i, min (a i) j) := by
          rw [Finset.prod_pow_eq_pow_sum]

lemma card_pi_multiplicative_zmod_two_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) :
    Fintype.card ((i : ι) → Multiplicative (ZMod (2 ^ a i))) = 2 ^ (∑ i, a i) := by
  calc
    Fintype.card ((i : ι) → Multiplicative (ZMod (2 ^ a i)))
        = ∏ i, Fintype.card (Multiplicative (ZMod (2 ^ a i))) := Fintype.card_pi
    _ = ∏ i, 2 ^ a i := by
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [Fintype.card_multiplicative, ZMod.card]
    _ = 2 ^ (∑ i, a i) := by
        rw [Finset.prod_pow_eq_pow_sum]

lemma sum_range_indicator_lt {k N : ℕ} (hk : k ≤ N) :
    (∑ j ∈ Finset.range N, if j < k then 1 else 0) = k := by
  rw [Finset.sum_boole]
  have hfilter : ({j ∈ Finset.range N | j < k}) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.card_range]
  rfl

lemma order_factorization_two_eq_sum_not_pow {H : Type*} [Group H] [Fintype H]
    [DecidableEq H] {N : ℕ} (hcard : Fintype.card H = 2 ^ N) (x : H) :
    (orderOf x).factorization 2 =
      ∑ j ∈ Finset.range N, if x ^ (2 ^ j) = 1 then 0 else 1 := by
  have hdvd : orderOf x ∣ 2 ^ N := by
    simpa [hcard] using (orderOf_dvd_card (G := H) (x := x))
  obtain ⟨k, hkN, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk, Nat.factorization_pow_self Nat.prime_two]
  rw [← sum_range_indicator_lt hkN]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases hkj : j < k
  · have hpow_ne : x ^ (2 ^ j) ≠ 1 := by
      intro hx
      have hdiv : orderOf x ∣ 2 ^ j := (orderOf_dvd_iff_pow_eq_one).2 hx
      rw [hk] at hdiv
      have : k ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hdiv
      omega
    simp [hkj, hpow_ne]
  · have hjk : k ≤ j := le_of_not_gt hkj
    have hdiv : orderOf x ∣ 2 ^ j := by
      rw [hk]
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).2 hjk
    have hpow : x ^ (2 ^ j) = 1 := (orderOf_dvd_iff_pow_eq_one).1 hdiv
    simp [hkj, hpow]

lemma sum_not_indicator_card {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ x : α, if p x then 0 else 1) =
      Fintype.card α - Fintype.card {x : α // p x} := by
  rw [show (∑ x : α, if p x then 0 else 1) =
      ∑ x : α, if ¬ p x then 1 else 0 by
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases hp : p x <;> simp [hp]]
  rw [Finset.sum_boole]
  rw [Fintype.card_subtype]
  change (Finset.filter (fun x : α => ¬ p x) Finset.univ).card =
    Fintype.card α - (Finset.filter p Finset.univ).card
  change (Finset.filter (fun x : α => ¬ p x) Finset.univ).card =
    (Finset.univ : Finset α).card - (Finset.filter p Finset.univ).card
  exact Nat.eq_sub_of_add_eq'
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) p)

lemma sum_factorization_two_eq_sum_layers {H : Type*} [Group H] [Fintype H]
    [DecidableEq H] {N : ℕ} (hcard : Fintype.card H = 2 ^ N) :
    (∑ x : H, (orderOf x).factorization 2) =
      ∑ j ∈ Finset.range N,
        (Fintype.card H - Fintype.card {x : H // x ^ (2 ^ j) = 1}) := by
  calc
    (∑ x : H, (orderOf x).factorization 2)
        = ∑ x : H, ∑ j ∈ Finset.range N, if x ^ (2 ^ j) = 1 then 0 else 1 := by
          exact Finset.sum_congr rfl
            (by intro x _; exact order_factorization_two_eq_sum_not_pow hcard x)
    _ = ∑ j ∈ Finset.range N, ∑ x : H, if x ^ (2 ^ j) = 1 then 0 else 1 := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range N,
        (Fintype.card H - Fintype.card {x : H // x ^ (2 ^ j) = 1}) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact sum_not_indicator_card (fun x : H => x ^ (2 ^ j) = 1)

lemma sum_factorization_pi_two_pow_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) :
    (∑ x : ((i : ι) → Multiplicative (ZMod (2 ^ a i))), (orderOf x).factorization 2) =
      ∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j)) := by
  let H := ((i : ι) → Multiplicative (ZMod (2 ^ a i)))
  have hcard : Fintype.card H = 2 ^ (∑ i, a i) := card_pi_multiplicative_zmod_two_pow a
  calc
    (∑ x : H, (orderOf x).factorization 2) =
        ∑ j ∈ Finset.range (∑ i, a i),
          (Fintype.card H - Fintype.card {x : H // x ^ (2 ^ j) = 1}) :=
          sum_factorization_two_eq_sum_layers hcard
    _ = ∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hcard, card_pi_two_pow_pow_eq_one]

lemma modeq_16_mul_add (m r : ℕ) : 16 * m + r ≡ r [MOD 16] := by
  rw [Nat.modEq_iff_dvd]
  use -(m : ℤ)
  omega

lemma modeq_16_mul (m : ℕ) : 16 * m ≡ 0 [MOD 16] := by
  simpa using modeq_16_mul_add m 0

lemma pow_two_modeq_zero_of_ge_four {n : ℕ} (hn : 4 ≤ n) : 2 ^ n ≡ 0 [MOD 16] := by
  have hn' : n = 4 + (n - 4) := by omega
  rw [hn', pow_add]
  norm_num
  exact modeq_16_mul _

lemma term_modeq_zero_of_ge_four {N b : ℕ} (hN : 4 ≤ N) (hbN : b ≤ N)
    (hb : 4 ≤ b) :
    2 ^ N - 2 ^ b ≡ 0 [MOD 16] := by
  exact Nat.ModEq.sub (Nat.pow_le_pow_right (by norm_num : 0 < 2) hbN) (by rfl)
    (pow_two_modeq_zero_of_ge_four hN) (pow_two_modeq_zero_of_ge_four hb)

lemma term_modeq_15 {N : ℕ} (hN : 4 ≤ N) : 2 ^ N - 1 ≡ 15 [MOD 16] := by
  have hN' : N = 4 + (N - 4) := by omega
  rw [hN', pow_add]
  norm_num
  have hq : 0 < 2 ^ (N - 4) := pow_pos (by norm_num) _
  have hterm : 16 * 2 ^ (N - 4) - 1 = 16 * (2 ^ (N - 4) - 1) + 15 := by omega
  rw [hterm]
  exact modeq_16_mul_add _ _

lemma term_modeq_14 {N : ℕ} (hN : 4 ≤ N) : 2 ^ N - 2 ≡ 14 [MOD 16] := by
  have hN' : N = 4 + (N - 4) := by omega
  rw [hN', pow_add]
  norm_num
  have hq : 0 < 2 ^ (N - 4) := pow_pos (by norm_num) _
  have hterm : 16 * 2 ^ (N - 4) - 2 = 16 * (2 ^ (N - 4) - 1) + 14 := by omega
  rw [hterm]
  exact modeq_16_mul_add _ _

lemma term_modeq_12 {N : ℕ} (hN : 4 ≤ N) : 2 ^ N - 4 ≡ 12 [MOD 16] := by
  have hN' : N = 4 + (N - 4) := by omega
  rw [hN', pow_add]
  norm_num
  have hq : 0 < 2 ^ (N - 4) := pow_pos (by norm_num) _
  have hterm : 16 * 2 ^ (N - 4) - 4 = 16 * (2 ^ (N - 4) - 1) + 12 := by omega
  rw [hterm]
  exact modeq_16_mul_add _ _

lemma term_modeq_8 {N : ℕ} (hN : 4 ≤ N) : 2 ^ N - 8 ≡ 8 [MOD 16] := by
  have hN' : N = 4 + (N - 4) := by omega
  rw [hN', pow_add]
  norm_num
  have hq : 0 < 2 ^ (N - 4) := pow_pos (by norm_num) _
  have hterm : 16 * 2 ^ (N - 4) - 8 = 16 * (2 ^ (N - 4) - 1) + 8 := by omega
  rw [hterm]
  exact modeq_16_mul_add _ _

lemma sum_min_le_sum {ι : Type*} [Fintype ι] (a : ι → ℕ) (j : ℕ) :
    (∑ i, min (a i) j) ≤ ∑ i, a i := by
  exact Finset.sum_le_sum (by intro i _; exact min_le_left _ _)

lemma sum_min_one_eq_card {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hpos : ∀ i, 0 < a i) :
    (∑ i, min (a i) 1) = Fintype.card ι := by
  calc
    (∑ i, min (a i) 1) = ∑ _i : ι, 1 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact Nat.min_eq_right (hpos i)
    _ = Fintype.card ι := by simp

lemma sum_min_ge_card_of_pos_j {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hpos : ∀ i, 0 < a i) {j : ℕ} (hj : 1 ≤ j) :
    Fintype.card ι ≤ ∑ i, min (a i) j := by
  calc
    Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, min (a i) j := by
      exact Finset.sum_le_sum (by intro i _; exact le_min (hpos i) hj)

lemma sum_min_eq_min_sum_of_card_one {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcard : Fintype.card ι = 1) (j : ℕ) :
    (∑ i, min (a i) j) = min (∑ i, a i) j := by
  letI : Unique ι := (Fintype.card_eq_one_iff_nonempty_unique.mp hcard).some
  simp

lemma sum_min_two_ge_three_of_card_two {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (hpos : ∀ i, 0 < a i) (hcard : Fintype.card ι = 2)
    (hN : 4 ≤ ∑ i, a i) :
    3 ≤ ∑ i, min (a i) 2 := by
  let e : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  have hsum_a : (∑ i, a i) = ∑ k : Fin 2, a (e.symm k) := by
    rw [← Equiv.sum_comp e.symm (fun i => a i)]
  have hsum_min : (∑ i, min (a i) 2) = ∑ k : Fin 2, min (a (e.symm k)) 2 := by
    rw [← Equiv.sum_comp e.symm (fun i => min (a i) 2)]
  rw [hsum_min]
  rw [hsum_a] at hN
  rw [Fin.sum_univ_two] at hN ⊢
  have h0 := hpos (e.symm 0)
  have h1 := hpos (e.symm 1)
  omega

lemma sum_min_three_ge_four_of_card_two {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (hpos : ∀ i, 0 < a i) (hcard : Fintype.card ι = 2)
    (hN : 4 ≤ ∑ i, a i) :
    4 ≤ ∑ i, min (a i) 3 := by
  let e : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  have hsum_a : (∑ i, a i) = ∑ k : Fin 2, a (e.symm k) := by
    rw [← Equiv.sum_comp e.symm (fun i => a i)]
  have hsum_min : (∑ i, min (a i) 3) = ∑ k : Fin 2, min (a (e.symm k)) 3 := by
    rw [← Equiv.sum_comp e.symm (fun i => min (a i) 3)]
  rw [hsum_min]
  rw [hsum_a] at hN
  rw [Fin.sum_univ_two] at hN ⊢
  have h0 := hpos (e.symm 0)
  have h1 := hpos (e.symm 1)
  omega

lemma sum_min_two_ge_four_of_card_three {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (hpos : ∀ i, 0 < a i) (hcard : Fintype.card ι = 3)
    (hN : 4 ≤ ∑ i, a i) :
    4 ≤ ∑ i, min (a i) 2 := by
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  have hsum_a : (∑ i, a i) = ∑ k : Fin 3, a (e.symm k) := by
    rw [← Equiv.sum_comp e.symm (fun i => a i)]
  have hsum_min : (∑ i, min (a i) 2) = ∑ k : Fin 3, min (a (e.symm k)) 2 := by
    rw [← Equiv.sum_comp e.symm (fun i => min (a i) 2)]
  rw [hsum_min]
  rw [hsum_a] at hN
  rw [Fin.sum_univ_three] at hN ⊢
  have h0 := hpos (e.symm 0)
  have h1 := hpos (e.symm 1)
  have h2 := hpos (e.symm 2)
  omega

lemma residue_sum_two (N : ℕ) (hN : 4 ≤ N) (c : ℕ) :
    (∑ j ∈ Finset.range N, (if j = 0 then 15 else if j = 1 then c else 0)) =
      15 + c := by
  have hsplit :
      (fun j : ℕ => (if j = 0 then 15 else if j = 1 then c else 0 : ℕ)) =
        (fun j => (if 0 = j then 15 else 0) + (if 1 = j then c else 0)) := by
    funext j
    by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp [h0, h1, eq_comm]
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  simp [h0, h1]

lemma residue_sum_three (N : ℕ) (hN : 4 ≤ N) (c d : ℕ) :
    (∑ j ∈ Finset.range N,
        (if j = 0 then 15 else if j = 1 then c else if j = 2 then d else 0)) =
      15 + c + d := by
  have hsplit :
      (fun j : ℕ => (if j = 0 then 15 else if j = 1 then c else if j = 2 then d else 0 : ℕ)) =
        (fun j => (if 0 = j then 15 else 0) +
          (if 1 = j then c else 0) + (if 2 = j then d else 0)) := by
    funext j
    by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> by_cases h2 : j = 2 <;>
      simp [h0, h1, h2, eq_comm]
  rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq, Finset.sum_ite_eq]
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  have h2 : 2 < N := by omega
  simp [h0, h1, h2]

lemma residue_sum_four (N : ℕ) (hN : 4 ≤ N) :
    (∑ j ∈ Finset.range N,
        (if j = 0 then 15 else if j = 1 then 14 else if j = 2 then 12 else
          if j = 3 then 8 else 0)) = 49 := by
  have hsplit :
      (fun j : ℕ =>
        (if j = 0 then 15 else if j = 1 then 14 else if j = 2 then 12 else
          if j = 3 then 8 else 0 : ℕ)) =
        (fun j => (if 0 = j then 15 else 0) + (if 1 = j then 14 else 0) +
          (if 2 = j then 12 else 0) + (if 3 = j then 8 else 0)) := by
    funext j
    by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> by_cases h2 : j = 2 <;>
      by_cases h3 : j = 3 <;> simp [h0, h1, h2, h3, eq_comm]
  rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq, Finset.sum_ite_eq, Finset.sum_ite_eq]
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  have h2 : 2 < N := by omega
  have h3 : 3 < N := by omega
  simp [h0, h1, h2, h3]

lemma expression_modeq_card_one {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hN : 4 ≤ ∑ i, a i) (hr : Fintype.card ι = 1) :
    (∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 1 [MOD 16] := by
  let N := ∑ i, a i
  let b := fun j => ∑ i, min (a i) j
  have hb : ∀ j, b j = min N j := by
    intro j
    simpa [N, b] using sum_min_eq_min_sum_of_card_one a hr j
  have hmodeq :
      (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡
        ∑ j ∈ Finset.range N,
          (if j = 0 then 15 else if j = 1 then 14 else if j = 2 then 12 else
            if j = 3 then 8 else 0) [MOD 16] := by
    apply Nat.ModEq.sum
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simpa [b, hb] using (term_modeq_15 (N := N) hN)
    · by_cases hj1 : j = 1
      · subst j
        have hb1 : b 1 = 1 := by
          rw [hb]
          exact Nat.min_eq_right (by omega)
        simp [hb1]
        exact term_modeq_14 hN
      · by_cases hj2 : j = 2
        · subst j
          have hb2 : b 2 = 2 := by
            rw [hb]
            exact Nat.min_eq_right (by omega)
          simp [hb2]
          exact term_modeq_12 hN
        · by_cases hj3 : j = 3
          · subst j
            have hb3 : b 3 = 3 := by
              rw [hb]
              exact Nat.min_eq_right (by omega)
            simp [hb3]
            exact term_modeq_8 hN
          · have hjge4 : 4 ≤ j := by omega
            have hb4 : 4 ≤ b j := by
              rw [hb]
              exact le_min (by omega) hjge4
            have hbN : b j ≤ N := sum_min_le_sum a j
            simp [hj0, hj1, hj2, hj3]
            exact term_modeq_zero_of_ge_four hN hbN hb4
  have hmodeq49 : (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡ 49 [MOD 16] := by
    simpa [residue_sum_four N hN] using hmodeq
  have h491 : (49 : ℕ) ≡ 1 [MOD 16] := by norm_num [Nat.ModEq]
  simpa [N, b] using hmodeq49.trans h491

lemma expression_modeq_card_two {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hpos : ∀ i, 0 < a i) (hN : 4 ≤ ∑ i, a i) (hr : Fintype.card ι = 2) :
    ((∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 11 [MOD 16]) ∨
      ((∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 3 [MOD 16]) := by
  let N := ∑ i, a i
  let b := fun j => ∑ i, min (a i) j
  have hb2ge : 3 ≤ b 2 := by
    simpa [b] using sum_min_two_ge_three_of_card_two a hpos hr hN
  have hb3ge : 4 ≤ b 3 := by
    simpa [b] using sum_min_three_ge_four_of_card_two a hpos hr hN
  by_cases hb2eq : b 2 = 3
  · right
    have hmodeq :
        (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡
          ∑ j ∈ Finset.range N,
            (if j = 0 then 15 else if j = 1 then 12 else if j = 2 then 8 else 0)
          [MOD 16] := by
      apply Nat.ModEq.sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simpa [b] using (term_modeq_15 (N := N) hN)
      · by_cases hj1 : j = 1
        · subst j
          have hb1 : b 1 = 2 := by simpa [b, hr] using sum_min_one_eq_card a hpos
          simp [hb1]
          exact term_modeq_12 hN
        · by_cases hj2 : j = 2
          · subst j
            simp [hb2eq]
            exact term_modeq_8 hN
          · have hjge3 : 3 ≤ j := by omega
            have hb4 : 4 ≤ b j := by
              calc
                4 ≤ b 3 := hb3ge
                _ ≤ b j := by
                  exact Finset.sum_le_sum (by intro i _; exact min_le_min_left (a i) hjge3)
            have hbN : b j ≤ N := sum_min_le_sum a j
            simp [hj0, hj1, hj2]
            exact term_modeq_zero_of_ge_four hN hbN hb4
    have hmodeq35 : (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡ 35 [MOD 16] := by
      simpa [residue_sum_three N hN 12 8] using hmodeq
    have h353 : (35 : ℕ) ≡ 3 [MOD 16] := by norm_num [Nat.ModEq]
    simpa [N, b] using hmodeq35.trans h353
  · left
    have hb2ge4 : 4 ≤ b 2 := by omega
    have hmodeq :
        (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡
          ∑ j ∈ Finset.range N, (if j = 0 then 15 else if j = 1 then 12 else 0)
          [MOD 16] := by
      apply Nat.ModEq.sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simpa [b] using (term_modeq_15 (N := N) hN)
      · by_cases hj1 : j = 1
        · subst j
          have hb1 : b 1 = 2 := by simpa [b, hr] using sum_min_one_eq_card a hpos
          simp [hb1]
          exact term_modeq_12 hN
        · have hjge2 : 2 ≤ j := by omega
          have hb4 : 4 ≤ b j := by
            calc
              4 ≤ b 2 := hb2ge4
              _ ≤ b j := by
                exact Finset.sum_le_sum (by intro i _; exact min_le_min_left (a i) hjge2)
          have hbN : b j ≤ N := sum_min_le_sum a j
          simp [hj0, hj1]
          exact term_modeq_zero_of_ge_four hN hbN hb4
    have hmodeq27 : (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡ 27 [MOD 16] := by
      simpa [residue_sum_two N hN 12] using hmodeq
    have h2711 : (27 : ℕ) ≡ 11 [MOD 16] := by norm_num [Nat.ModEq]
    simpa [N, b] using hmodeq27.trans h2711

lemma expression_modeq_card_three {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hpos : ∀ i, 0 < a i) (hN : 4 ≤ ∑ i, a i) (hr : Fintype.card ι = 3) :
    (∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 7 [MOD 16] := by
  let N := ∑ i, a i
  let b := fun j => ∑ i, min (a i) j
  have hb2 : 4 ≤ b 2 := by
    simpa [b] using sum_min_two_ge_four_of_card_three a hpos hr hN
  have hmodeq :
      (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡
        ∑ j ∈ Finset.range N, (if j = 0 then 15 else if j = 1 then 8 else 0)
        [MOD 16] := by
    apply Nat.ModEq.sum
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simpa [b] using (term_modeq_15 (N := N) hN)
    · by_cases hj1 : j = 1
      · subst j
        have hb1 : b 1 = 3 := by simpa [b, hr] using sum_min_one_eq_card a hpos
        simp [hb1]
        exact term_modeq_8 hN
      · have hjge2 : 2 ≤ j := by omega
        have hb4 : 4 ≤ b j := by
          calc
            4 ≤ b 2 := hb2
            _ ≤ b j := by
              exact Finset.sum_le_sum (by intro i _; exact min_le_min_left (a i) hjge2)
        have hbN : b j ≤ N := sum_min_le_sum a j
        simp [hj0, hj1]
        exact term_modeq_zero_of_ge_four hN hbN hb4
  have hmodeq23 : (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡ 23 [MOD 16] := by
    simpa [residue_sum_two N hN 8] using hmodeq
  have h237 : (23 : ℕ) ≡ 7 [MOD 16] := by norm_num [Nat.ModEq]
  simpa [N, b] using hmodeq23.trans h237

lemma expression_modeq_card_ge_four {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hpos : ∀ i, 0 < a i) (hN : 4 ≤ ∑ i, a i) (hr : 4 ≤ Fintype.card ι) :
    (∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 15 [MOD 16] := by
  let N := ∑ i, a i
  let b := fun j => ∑ i, min (a i) j
  have hmodeq :
      (∑ j ∈ Finset.range N, (2 ^ N - 2 ^ (b j))) ≡
        ∑ j ∈ Finset.range N, (if j = 0 then 15 else 0) [MOD 16] := by
    apply Nat.ModEq.sum
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simpa [b] using (term_modeq_15 (N := N) hN)
    · have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
      have hb4 : 4 ≤ b j := le_trans hr (sum_min_ge_card_of_pos_j a hpos hjpos)
      have hbN : b j ≤ N := sum_min_le_sum a j
      simp [hj0]
      exact term_modeq_zero_of_ge_four hN hbN hb4
  have hsum : (∑ j ∈ Finset.range N, (if j = 0 then 15 else 0)) = 15 := by
    refine Finset.sum_eq_single_of_mem 0 ?_ ?_
    · simp [N]
      omega
    · intro j _ hj0
      simp [hj0]
  simpa [N, b, hsum] using hmodeq

lemma expression_modeq_possible {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hpos : ∀ i, 0 < a i) (hN : 4 ≤ ∑ i, a i) :
    ((∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 1 [MOD 16]) ∨
    ((∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 3 [MOD 16]) ∨
    ((∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 7 [MOD 16]) ∨
    ((∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 11 [MOD 16]) ∨
    ((∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))) ≡ 15 [MOD 16]) := by
  by_cases h1 : Fintype.card ι = 1
  · exact Or.inl (expression_modeq_card_one a hN h1)
  · by_cases h2 : Fintype.card ι = 2
    · rcases expression_modeq_card_two a hpos hN h2 with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inl h)
    · by_cases h3 : Fintype.card ι = 3
      · exact Or.inr (Or.inr (Or.inl (expression_modeq_card_three a hpos hN h3)))
      · have hrpos : 0 < Fintype.card ι := by
          rw [Fintype.card_pos_iff]
          by_contra hne
          haveI : IsEmpty ι := not_nonempty_iff.mp hne
          simp at hN
        have hr4 : 4 ≤ Fintype.card ι := by omega
        exact Or.inr (Or.inr (Or.inr (Or.inr (expression_modeq_card_ge_four a hpos hN hr4))))

end Putnam2009A5

/--
Is there a finite abelian group $G$ such that the product of the orders of all its elements is 2^{2009}?
-/
theorem putnam_2009_a5
: (∃ (G : Type*) (_ : CommGroup G) (_ : Fintype G), ∏ g : G, orderOf g = 2^2009) ↔ putnam_2009_a5_solution :=
by
  classical
  unfold putnam_2009_a5_solution
  constructor
  · rintro ⟨G, hcomm, hfintype, hprod⟩
    letI : CommGroup G := hcomm
    letI : Fintype G := hfintype
    haveI : Finite G := Finite.of_fintype G
    obtain ⟨ι, hι, n, hn_gt, ⟨e⟩⟩ :=
      CommGroup.equiv_prod_multiplicative_zmod_of_finite G
    letI : Fintype ι := hι
    haveI : ∀ i : ι, NeZero (n i) := fun i =>
      ⟨ne_of_gt (lt_trans Nat.zero_lt_one (hn_gt i))⟩
    let H := ((i : ι) → Multiplicative (ZMod (n i)))
    have hprodH : (∏ x : H, orderOf x) = 2 ^ 2009 := by
      calc
        (∏ x : H, orderOf x) = ∏ g : G, orderOf g := by
          exact (Fintype.prod_equiv e.toEquiv (fun g : G => orderOf g)
            (fun x : H => orderOf x) (fun g => (e.orderOf_eq g).symm)).symm
        _ = 2 ^ 2009 := hprod
    have hn_pow : ∀ i : ι, ∃ a ≤ 2009, n i = 2 ^ a := by
      intro i
      let xi : H := Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i)))
      have horder_xi : orderOf xi = n i := by
        rw [show xi = Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i))) from rfl]
        rw [orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
      have hdiv_prod : n i ∣ ∏ x : H, orderOf x := by
        rw [← horder_xi]
        exact Finset.dvd_prod_of_mem (fun x : H => orderOf x) (Finset.mem_univ xi)
      have hdiv_pow : n i ∣ 2 ^ 2009 := by
        simpa [hprodH] using hdiv_prod
      exact (Nat.dvd_prime_pow Nat.prime_two).1 hdiv_pow
    choose a ha_le hn_eq using hn_pow
    have ha_pos : ∀ i : ι, 0 < a i := by
      intro i
      by_contra h
      have hai : a i = 0 := Nat.eq_zero_of_not_pos h
      have : ¬(1 < n i) := by
        rw [hn_eq i, hai]
        norm_num
      exact this (hn_gt i)
    have hn_fun : n = fun i : ι => 2 ^ a i := funext hn_eq
    subst n
    let H₂ := ((i : ι) → Multiplicative (ZMod (2 ^ a i)))
    have hprodH₂ : (∏ x : H₂, orderOf x) = 2 ^ 2009 := by
      simpa [H, H₂] using hprodH
    have hfac : (∑ x : H₂, (orderOf x).factorization 2) = 2009 := by
      have hfacprod :=
        Nat.factorization_prod_apply
          (p := 2) (S := (Finset.univ : Finset H₂)) (g := fun x : H₂ => orderOf x)
          (by intro x _; exact (orderOf_pos x).ne')
      have hleft : ((∏ x : H₂, orderOf x).factorization 2) = 2009 := by
        rw [hprodH₂, Nat.factorization_pow_self Nat.prime_two]
      simpa [hfacprod] using hleft
    have hsum_formula := Putnam2009A5.sum_factorization_pi_two_pow_eq a
    let E :=
      ∑ j ∈ Finset.range (∑ i, a i),
        (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j))
    have hE : E = 2009 := by
      simpa [E] using hsum_formula.symm.trans hfac
    by_cases hN : 4 ≤ ∑ i, a i
    · rcases Putnam2009A5.expression_modeq_possible a ha_pos hN with hmod | hmod | hmod | hmod | hmod
      · have : (2009 : ℕ) ≡ 1 [MOD 16] := by simpa [E, hE] using hmod
        norm_num [Nat.ModEq] at this
      · have : (2009 : ℕ) ≡ 3 [MOD 16] := by simpa [E, hE] using hmod
        norm_num [Nat.ModEq] at this
      · have : (2009 : ℕ) ≡ 7 [MOD 16] := by simpa [E, hE] using hmod
        norm_num [Nat.ModEq] at this
      · have : (2009 : ℕ) ≡ 11 [MOD 16] := by simpa [E, hE] using hmod
        norm_num [Nat.ModEq] at this
      · have : (2009 : ℕ) ≡ 15 [MOD 16] := by simpa [E, hE] using hmod
        norm_num [Nat.ModEq] at this
    · have hNle : (∑ i, a i) ≤ 3 := by omega
      have hEle : E ≤ (∑ i, a i) * 2 ^ (∑ i, a i) := by
        dsimp [E]
        calc
          (∑ j ∈ Finset.range (∑ i, a i),
            (2 ^ (∑ i, a i) - 2 ^ (∑ i, min (a i) j)))
              ≤ ∑ j ∈ Finset.range (∑ i, a i), 2 ^ (∑ i, a i) := by
                exact Finset.sum_le_sum (by intro j _; exact Nat.sub_le _ _)
          _ = (∑ i, a i) * 2 ^ (∑ i, a i) := by
                simp
      interval_cases (∑ i, a i) <;> norm_num at hEle <;> omega
  · intro h
    exact False.elim h
