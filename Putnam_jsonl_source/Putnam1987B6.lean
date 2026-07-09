import Mathlib

open MvPolynomial Real Nat Filter Topology

/--
Let $F$ be the field of $p^2$ elements, where $p$ is an odd prime. Suppose $S$ is a set of $(p^2-1)/2$ distinct nonzero elements of $F$ with the property that for each $a\neq 0$ in $F$, exactly one of $a$ and $-a$ is in $S$. Let $N$ be the number of elements in the intersection $S \cap \{2a: a \in S\}$. Prove that $N$ is even.
-/
theorem putnam_1987_b6
    (p : ℕ)
    (F : Type*) [Field F] [Fintype F]
    (S : Set F)
    (hp : Odd p ∧ Nat.Prime p)
    (Fcard : Fintype.card F = p ^ 2)
    (Snz : ∀ x ∈ S, x ≠ 0)
    (Scard : S.ncard = ((p : ℤ) ^ 2 - 1) / 2)
    (hS : ∀ a : F, a ≠ 0 → Xor' (a ∈ S) (-a ∈ S)) :
    (Even ((S ∩ {x | ∃ a ∈ S, x = 2 * a}).ncard)) := by
  classical
  have hSfin : S.Finite := Set.finite_univ.subset (by intro x hx; trivial)
  let s : Finset F := hSfin.toFinset
  have hs_mem : ∀ x : F, x ∈ s ↔ x ∈ S := by
    intro x
    dsimp [s]
    rw [Set.Finite.mem_toFinset]
  have hs_card : s.card = S.ncard := by
    dsimp [s]
    rw [Set.ncard_eq_toFinset_card S hSfin]
  have hneg_one_ne : (-1 : F) ≠ 1 := by
    intro hneg
    have hx := hS 1 one_ne_zero
    have hneg1 : -(1 : F) = 1 := by simpa using hneg
    rw [hneg1] at hx
    unfold Xor' at hx
    tauto
  have htwo_ne_zero : (2 : F) ≠ 0 := by
    intro h2
    have h11 : (1 : F) + 1 = 0 := by
      simpa [one_add_one_eq_two] using h2
    exact hneg_one_ne (neg_eq_of_add_eq_zero_right h11)
  let t : Finset F := s.image (fun x : F => (2 : F) * x)
  have ht_mem_set : ∀ x : F, x ∈ t ↔ ∃ a ∈ S, x = (2 : F) * a := by
    intro x
    dsimp [t]
    constructor
    · intro hx
      rcases (Finset.mem_image.mp hx) with ⟨a, ha, hax⟩
      exact ⟨a, (hs_mem a).mp ha, hax.symm⟩
    · rintro ⟨a, haS, rfl⟩
      exact Finset.mem_image.mpr ⟨a, (hs_mem a).mpr haS, rfl⟩
  have ht_mem_inv : ∀ x : F, x ∈ t ↔ (2 : F)⁻¹ * x ∈ S := by
    intro x
    rw [ht_mem_set x]
    constructor
    · rintro ⟨a, haS, rfl⟩
      convert haS using 1
      field_simp [htwo_ne_zero]
    · intro hx
      refine ⟨(2 : F)⁻¹ * x, hx, ?_⟩
      field_simp [htwo_ne_zero]
  have hT : ∀ a : F, a ≠ 0 → Xor' (a ∈ t) (-a ∈ t) := by
    intro a ha0
    rw [ht_mem_inv a, ht_mem_inv (-a)]
    have hb0 : (2 : F)⁻¹ * a ≠ 0 := by
      intro hb
      have : a = 0 := by
        calc
          a = (2 : F) * ((2 : F)⁻¹ * a) := by field_simp [htwo_ne_zero]
          _ = 0 := by rw [hb, mul_zero]
      exact ha0 this
    simpa [mul_neg] using hS ((2 : F)⁻¹ * a) hb0
  have ht_nz : ∀ x ∈ t, x ≠ 0 := by
    intro x hx hx0
    have hbS : (2 : F)⁻¹ * x ∈ S := (ht_mem_inv x).mp hx
    exact Snz ((2 : F)⁻¹ * x) hbS (by rw [hx0, mul_zero])
  have hprod_t_double :
      (∏ x ∈ t, x) = (2 : F) ^ s.card * ∏ x ∈ s, x := by
    dsimp [t]
    calc
      (∏ x ∈ s.image (fun x : F => (2 : F) * x), x) = ∏ x ∈ s, (2 : F) * x := by
        rw [Finset.prod_image]
        intro x hx y hy hxy
        exact mul_left_cancel₀ htwo_ne_zero hxy
      _ = (2 : F) ^ s.card * ∏ x ∈ s, x := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const]
  have hprod_t_sign :
      (∏ x ∈ t, x) =
        (-1 : F) ^ (s.card - ({x ∈ s | x ∈ t}.card)) * ∏ x ∈ s, x := by
    have hmap_mem : ∀ x, x ∈ s → (if x ∈ t then x else -x) ∈ t := by
      intro x hx
      by_cases hxt : x ∈ t
      · simp [hxt]
      · have hxS : x ∈ S := (hs_mem x).mp hx
        have hx0 : x ≠ 0 := Snz x hxS
        have hxT := hT x hx0
        unfold Xor' at hxT
        rcases hxT with ⟨hxin, _⟩ | ⟨hneg, _⟩
        · exact (hxt hxin).elim
        · simpa [hxt] using hneg
    have hmap_inj :
        ∀ x (hx : x ∈ s) y (hy : y ∈ s),
          (if x ∈ t then x else -x) = (if y ∈ t then y else -y) → x = y := by
      intro x hx y hy hxy
      have hxS : x ∈ S := (hs_mem x).mp hx
      have hyS : y ∈ S := (hs_mem y).mp hy
      have hx0 : x ≠ 0 := Snz x hxS
      have hy0 : y ≠ 0 := Snz y hyS
      by_cases hxt : x ∈ t <;> by_cases hyt : y ∈ t <;> simp [hxt, hyt] at hxy
      · exact hxy
      · exfalso
        have hneg_y_S : -y ∈ S := by simpa [hxy] using hxS
        have hyxor := hS y hy0
        unfold Xor' at hyxor
        rcases hyxor with ⟨_, hnot⟩ | ⟨_, hnot⟩
        · exact hnot hneg_y_S
        · exact hnot hyS
      · exfalso
        have hneg_x_S : -x ∈ S := by simpa [← hxy] using hyS
        have hxxor := hS x hx0
        unfold Xor' at hxxor
        rcases hxxor with ⟨_, hnot⟩ | ⟨_, hnot⟩
        · exact hnot hneg_x_S
        · exact hnot hxS
      · exact hxy
    have hmap_surj : ∀ z ∈ t, ∃ x, ∃ hx : x ∈ s, (if x ∈ t then x else -x) = z := by
      intro z hz
      by_cases hzS : z ∈ S
      · refine ⟨z, (hs_mem z).mpr hzS, ?_⟩
        simp [hz]
      · have hz0 : z ≠ 0 := ht_nz z hz
        have hzx := hS z hz0
        unfold Xor' at hzx
        have hnegzS : -z ∈ S := by
          rcases hzx with ⟨hzSin, _⟩ | ⟨hneg, _⟩
          · exact (hzS hzSin).elim
          · exact hneg
        refine ⟨-z, (hs_mem (-z)).mpr hnegzS, ?_⟩
        have hnegz_not_t : -z ∉ t := by
          intro hzneg
          have hzTx := hT z hz0
          unfold Xor' at hzTx
          rcases hzTx with ⟨_, hnot⟩ | ⟨_, hnot⟩
          · exact hnot hzneg
          · exact hnot hz
        simp [hnegz_not_t]
    have hbij :
        (∏ x ∈ s, (if x ∈ t then x else -x)) = ∏ x ∈ t, x := by
      refine Finset.prod_bij (fun x hx => if x ∈ t then x else -x) ?_ ?_ ?_ ?_
      · exact hmap_mem
      · exact hmap_inj
      · exact hmap_surj
      · intro x hx
        rfl
    have hsplit :
        (∏ x ∈ s, (if x ∈ t then x else -x)) =
          (∏ x ∈ s, if x ∈ t then (1 : F) else -1) * ∏ x ∈ s, x := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro x hx
      by_cases hxt : x ∈ t <;> simp [hxt]
    have hsign :
        (∏ x ∈ s, if x ∈ t then (1 : F) else -1) =
          (-1 : F) ^ (s.card - ({x ∈ s | x ∈ t}.card)) := by
      have hprod : (∏ x ∈ s, if x ∈ t then (1 : F) else -1) =
          (-1 : F) ^ ({x ∈ s | ¬ x ∈ t}.card) := by
        rw [Finset.prod_ite]
        simp [Finset.prod_const]
      have hcardnot : ({x ∈ s | ¬ x ∈ t}.card) =
          s.card - ({x ∈ s | x ∈ t}.card) := by
        have h := Finset.card_filter_add_card_filter_not (s := s) (p := fun x => x ∈ t)
        omega
      rw [hprod, hcardnot]
    rw [← hbij, hsplit, hsign]
  have hP_ne_zero : (∏ x ∈ s, x) ≠ (0 : F) := by
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    exact Snz x ((hs_mem x).mp hx)
  have hdiv_scard : (p - 1) ∣ s.card := by
    rw [hs_card]
    rcases hp.1 with ⟨k, rfl⟩
    have hcalc :
        (((((2 * k + 1 : ℕ) : ℤ) ^ 2 - 1) / 2) : ℤ) =
          2 * (k : ℤ) * ((k : ℤ) + 1) := by
      apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
      norm_num
      ring
    have hnz : (S.ncard : ℤ) = 2 * (k : ℤ) * ((k : ℤ) + 1) := by
      rw [Scard, hcalc]
    have hn : S.ncard = 2 * k * (k + 1) := by
      have hnz' : (S.ncard : ℤ) = ((2 * k * (k + 1) : ℕ) : ℤ) := by
        rw [hnz]
        norm_num
      exact_mod_cast hnz'
    rw [hn]
    use k + 1
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hsub]
  have hEven_scard : Even s.card := by
    rw [hs_card]
    rcases hp.1 with ⟨k, rfl⟩
    have hcalc :
        (((((2 * k + 1 : ℕ) : ℤ) ^ 2 - 1) / 2) : ℤ) =
          2 * (k : ℤ) * ((k : ℤ) + 1) := by
      apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
      norm_num
      ring
    have hnz : (S.ncard : ℤ) = 2 * (k : ℤ) * ((k : ℤ) + 1) := by
      rw [Scard, hcalc]
    have hn : S.ncard = 2 * k * (k + 1) := by
      have hnz' : (S.ncard : ℤ) = ((2 * k * (k + 1) : ℕ) : ℤ) := by
        rw [hnz]
        norm_num
      exact_mod_cast hnz'
    rw [hn]
    rw [mul_assoc]
    exact even_two.mul_right (k * (k + 1))
  have htwo_pow_pminus : (2 : F) ^ (p - 1) = 1 := by
    haveI : Fact p.Prime := ⟨hp.2⟩
    haveI : CharP F p := charP_of_card_eq_prime_pow (R := F) (p := p) (f := 2) Fcard
    have hcop : Nat.Coprime 2 p := by
      rw [Nat.coprime_primes Nat.prime_two hp.2]
      intro h
      subst p
      norm_num at hp
    have hmod : 2 ^ (p - 1) ≡ 1 [MOD p] :=
      Nat.ModEq.pow_card_sub_one_eq_one hp.2 hcop
    have hcast := (CharP.natCast_eq_natCast F p).2 hmod
    simpa [Nat.cast_pow] using hcast
  have htwo_pow_scard : (2 : F) ^ s.card = 1 := by
    rcases hdiv_scard with ⟨c, hc⟩
    rw [hc, pow_mul, htwo_pow_pminus, one_pow]
  let n : ℕ := ({x ∈ s | x ∈ t}.card)
  have hpow_sign : (2 : F) ^ s.card = (-1 : F) ^ (s.card - n) := by
    dsimp [n]
    exact mul_right_cancel₀ hP_ne_zero (hprod_t_double.symm.trans hprod_t_sign)
  have hsign_one : (-1 : F) ^ (s.card - n) = 1 := by
    rw [← hpow_sign, htwo_pow_scard]
  have hEven_diff : Even (s.card - n) := by
    by_contra hEven
    have hOdd : Odd (s.card - n) := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨m, hm⟩
    rw [hm] at hsign_one
    have : (-1 : F) = 1 := by
      simpa [pow_succ, pow_mul] using hsign_one
    exact hneg_one_ne this
  have hEven_n : Even n := by
    have hnle : n ≤ s.card := by
      dsimp [n]
      exact Finset.card_filter_le _ _
    rcases hEven_scard with ⟨a, ha⟩
    rcases hEven_diff with ⟨b, hb⟩
    use a - b
    omega
  have htarget_card : (S ∩ {x | ∃ a ∈ S, x = (2 : F) * a}).ncard = n := by
    let U : Set F := S ∩ {x | ∃ a ∈ S, x = (2 : F) * a}
    have hUfin : U.Finite := Set.finite_univ.subset (by intro x hx; trivial)
    have hfin_eq : hUfin.toFinset = {x ∈ s | x ∈ t} := by
      ext x
      rw [Set.Finite.mem_toFinset, Finset.mem_filter, hs_mem x, ht_mem_set x]
      rfl
    dsimp [n]
    rw [Set.ncard_eq_toFinset_card U hUfin, hfin_eq]
  rw [htarget_card]
  exact hEven_n
