import Mathlib

open Topology MvPolynomial Filter Set

private theorem coord_kernel_card_even
    {n a m : ℕ} (ha : 0 < a) (hm : 0 < m) (hn : n = 2 ^ a) :
    2 ∣ Nat.card {y : Multiplicative (ZMod n) // y ^ (2 ^ m) = 1} := by
  have hnpos : 0 < n := by rw [hn]; exact Nat.pow_pos (by norm_num : 0 < 2)
  haveI : NeZero n := ⟨hnpos.ne'⟩
  haveI : Finite (Multiplicative (ZMod n)) := Finite.of_fintype _
  let C := {y : Multiplicative (ZMod n) // y ^ (2 ^ m) = 1}
  let K := (powMonoidHom (2 ^ m) : Multiplicative (ZMod n) →* Multiplicative (ZMod n)).ker
  let e : C ≃ K :=
    { toFun := fun y => ⟨y.1, by
        change y.1 ^ (2 ^ m) = 1
        exact y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := by intro y; ext; rfl
      right_inv := by intro y; ext; rfl }
  have hcardC : Nat.card C = Nat.gcd n (2 ^ m) := by
    calc
      Nat.card C = Nat.card K := Nat.card_congr e
      _ = Nat.gcd (Nat.card (Multiplicative (ZMod n))) (2 ^ m) := by
        simpa [K] using (IsCyclic.card_powMonoidHom_ker (Multiplicative (ZMod n)) (2 ^ m))
      _ = Nat.gcd n (2 ^ m) := by
        have hcard : Nat.card (Multiplicative (ZMod n)) = n := by
          calc
            Nat.card (Multiplicative (ZMod n)) = Nat.card (ZMod n) := Nat.card_congr Multiplicative.toAdd
            _ = n := by rw [Nat.card_eq_fintype_card, ZMod.card]
        rw [hcard]
  rw [hcardC, hn]
  exact Nat.dvd_gcd (dvd_pow_self 2 ha.ne') (dvd_pow_self 2 hm.ne')

private theorem pi_pow_kernel_card_dvd_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n a : ι → ℕ) (ha_pos : ∀ i, 0 < a i) (hn : ∀ i, n i = 2 ^ a i)
    (hcard : 2 ≤ Fintype.card ι) {m : ℕ} (hm : 0 < m) :
    4 ∣ Nat.card {x : ((i : ι) → Multiplicative (ZMod (n i))) // x ^ (2 ^ m) = 1} := by
  let H := (i : ι) → Multiplicative (ZMod (n i))
  let C : ι → Type _ := fun i => {y : Multiplicative (ZMod (n i)) // y ^ (2 ^ m) = 1}
  let e : {x : H // x ^ (2 ^ m) = 1} ≃ ((i : ι) → C i) :=
    { toFun := fun x i => ⟨x.1 i, by
        have hx := congrFun x.2 i
        simpa [H] using hx⟩
      invFun := fun y => ⟨fun i => (y i).1, by
        ext i
        exact (y i).2⟩
      left_inv := by
        intro x
        ext i
        rfl
      right_inv := by
        intro y
        ext i
        rfl }
  have hcardprod : Nat.card {x : H // x ^ (2 ^ m) = 1} = ∏ i, Nat.card (C i) := by
    rw [Nat.card_congr e, Nat.card_pi]
  have hcoord_even : ∀ i, 2 ∣ Nat.card (C i) := by
    intro i
    exact coord_kernel_card_even (n := n i) (a := a i) (m := m) (ha_pos i) hm (hn i)
  classical
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card ι)
  have hrest_even : 2 ∣ ∏ k ∈ (Finset.univ.erase i), Nat.card (C k) := by
    have hjmem : j ∈ (Finset.univ.erase i) := by
      simp [hij.symm]
    exact (hcoord_even j).trans (Finset.dvd_prod_of_mem (fun k => Nat.card (C k)) hjmem)
  have htwo_two : 4 ∣ Nat.card (C i) * (∏ k ∈ (Finset.univ.erase i), Nat.card (C k)) := by
    obtain ⟨u, hu⟩ := hcoord_even i
    obtain ⟨v, hv⟩ := hrest_even
    rw [hu, hv]
    use u * v
    ring
  rw [hcardprod]
  have hsplit : (∏ k, Nat.card (C k)) = Nat.card (C i) * ∏ k ∈ (Finset.univ.erase i), Nat.card (C k) := by
    have h := Finset.prod_erase_mul (Finset.univ : Finset ι) (fun k => Nat.card (C k)) (Finset.mem_univ i)
    simpa [mul_comm] using h.symm
  rw [hsplit]
  exact htwo_two

private theorem cyclic_two_power_product_ne
    (H : Type*) [CommGroup H] [Fintype H] [IsCyclic H] {a : ℕ}
    (hcard : Fintype.card H = 2 ^ a) :
    (∏ h : H, orderOf h) ≠ 2 ^ 2009 := by
  intro hprod
  have hS : (∑ h : H, (orderOf h).factorization 2) = 2009 := by
    have hfac := congrArg (fun n : ℕ => n.factorization 2) hprod
    change (∏ h : H, orderOf h).factorization 2 = (2 ^ 2009).factorization 2 at hfac
    rw [Nat.factorization_prod_apply (S := (Finset.univ : Finset H)) (g := fun h : H => orderOf h)
      (by intro h hh; exact (orderOf_pos h).ne')] at hfac
    have hpowfac : (2 ^ 2009).factorization 2 = 2009 := Nat.factorization_pow_self Nat.prime_two
    rw [hpowfac] at hfac
    exact hfac
  rcases a.eq_zero_or_pos with rfl | ha
  · have : (∑ h : H, (orderOf h).factorization 2) = 0 := by
      have hcard1 : Fintype.card H = 1 := by simpa using hcard
      haveI : Unique H := (Fintype.card_eq_one_iff_nonempty_unique.mp hcard1).some
      have horder : orderOf (default : H) = 1 := by
        rw [orderOf_eq_one_iff]
        exact Subsingleton.elim _ _
      simp [horder]
    omega
  · let M : Finset H := Finset.univ.filter fun h : H => orderOf h = 2 ^ a
    have hMcard : M.card = 2 ^ (a - 1) := by
      have hdvd : 2 ^ a ∣ Fintype.card H := by rw [hcard]
      calc
        M.card = Nat.totient (2 ^ a) := by
          simpa [M] using (IsCyclic.card_orderOf_eq_totient (α := H) (d := 2 ^ a) hdvd)
        _ = 2 ^ (a - 1) := by
          simpa using (Nat.totient_prime_pow Nat.prime_two (n := a) ha)
    have hle_not (x : H) (hx : x ∈ (Finset.univ.filter fun h : H => ¬ orderOf h = 2 ^ a)) :
        (orderOf x).factorization 2 ≤ a - 1 := by
      have hxne : orderOf x ≠ 2 ^ a := by simpa using (Finset.mem_filter.mp hx).2
      have hdvd : orderOf x ∣ 2 ^ a := by
        simpa [hcard] using (orderOf_dvd_card (x := x))
      obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hk_lt : k < a := by
        exact lt_of_le_of_ne hk_le (fun hka => hxne (by rw [hk_eq, hka]))
      rw [hk_eq, Nat.factorization_pow_self Nat.prime_two]
      exact Nat.le_sub_one_of_lt hk_lt
    have hsum_le : (∑ h : H, (orderOf h).factorization 2) ≤
        M.card * a + ((Finset.univ.filter fun h : H => ¬ orderOf h = 2 ^ a).card) * (a - 1) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset H))
        (p := fun h : H => orderOf h = 2 ^ a) (f := fun h : H => (orderOf h).factorization 2)]
      apply add_le_add
      · rw [Finset.sum_const_nat]
        intro x hx
        have hxeq : orderOf x = 2 ^ a := by simpa [M] using (Finset.mem_filter.mp hx).2
        rw [hxeq, Nat.factorization_pow_self Nat.prime_two]
      · exact Finset.sum_le_card_nsmul _ _ _ hle_not
    have hnotcard : (Finset.univ.filter fun h : H => ¬ orderOf h = 2 ^ a).card = 2 ^ (a - 1) := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset H))
        (p := fun h : H => orderOf h = 2 ^ a)
      have hsplit' : M.card + (Finset.univ.filter fun h : H => ¬ orderOf h = 2 ^ a).card =
          (Finset.univ : Finset H).card := by
        simpa [M] using hsplit
      have huniv : (Finset.univ : Finset H).card = 2 ^ a := by simpa using hcard
      have hpow : 2 ^ a = 2 ^ (a - 1) + 2 ^ (a - 1) := by
        cases a with
        | zero => cases ha
        | succ b =>
            rw [show b + 1 - 1 = b by omega]
            rw [pow_succ]
            omega
      omega
    by_cases ha8 : a ≤ 8
    · have hupper : (∑ h : H, (orderOf h).factorization 2) ≤ 1920 := by
        have : M.card * a + ((Finset.univ.filter fun h : H => ¬ orderOf h = 2 ^ a).card) * (a - 1) ≤ 1920 := by
          rw [hMcard, hnotcard]
          interval_cases a <;> norm_num
        exact hsum_le.trans this
      omega
    · have ha9 : 9 ≤ a := by omega
      have hlower : 2304 ≤ (∑ h : H, (orderOf h).factorization 2) := by
        have hmax_le_sum : M.card * a ≤ (∑ h : H, (orderOf h).factorization 2) := by
          calc
            M.card * a = ∑ h ∈ M, (orderOf h).factorization 2 := by
              symm
              rw [Finset.sum_const_nat]
              intro x hx
              have hxeq : orderOf x = 2 ^ a := by simpa [M] using (Finset.mem_filter.mp hx).2
              rw [hxeq, Nat.factorization_pow_self Nat.prime_two]
            _ ≤ ∑ h : H, (orderOf h).factorization 2 := by
              exact Finset.sum_le_sum_of_subset (by intro x hx; exact Finset.mem_univ x)
        have hnum : 2304 ≤ M.card * a := by
          rw [hMcard]
          have hp : 2 ^ 8 ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
          nlinarith
        exact hnum.trans hmax_le_sum
      omega

private theorem pi_two_power_product_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n a : ι → ℕ) [∀ i, NeZero (n i)]
    (ha_pos : ∀ i, 0 < a i) (hn : ∀ i, n i = 2 ^ a i)
    (hcard : 2 ≤ Fintype.card ι) :
    (∏ x : ((i : ι) → Multiplicative (ZMod (n i))), orderOf x) ≠ 2 ^ 2009 := by
  intro hprod
  let H := (i : ι) → Multiplicative (ZMod (n i))
  let v : H → ℕ := fun x => (orderOf x).factorization 2
  have hS : (∑ x : H, v x) = 2009 := by
    have hfac := congrArg (fun n : ℕ => n.factorization 2) hprod
    change (∏ x : H, orderOf x).factorization 2 = (2 ^ 2009).factorization 2 at hfac
    rw [Nat.factorization_prod_apply (S := (Finset.univ : Finset H)) (g := fun x : H => orderOf x)
      (by intro x hx; exact (orderOf_pos x).ne')] at hfac
    have hpowfac : (2 ^ 2009).factorization 2 = 2009 := Nat.factorization_pow_self Nat.prime_two
    rw [hpowfac] at hfac
    exact hfac
  have horder_pow : ∀ x : H, ∃ k ≤ 2009, orderOf x = 2 ^ k := by
    intro x
    have hdvd : orderOf x ∣ 2 ^ 2009 := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem (fun y : H => orderOf y) (Finset.mem_univ x)
    exact (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hv_range : ∀ x ∈ (Finset.univ : Finset H), v x ∈ Finset.range 2010 := by
    intro x hx
    obtain ⟨k, hk_le, hk_eq⟩ := horder_pow x
    have hv_eq : v x = k := by
      change (orderOf x).factorization 2 = k
      rw [hk_eq, Nat.factorization_pow_self Nat.prime_two]
    rw [hv_eq]
    exact Finset.mem_range.mpr (by omega)
  let L : ℕ → ℕ := fun k => (Finset.univ.filter fun x : H => v x = k).card
  let B : ℕ → ℕ := fun k => (Finset.univ.filter fun x : H => v x ≤ k).card
  have hpow_iff (x : H) (m : ℕ) : v x ≤ m ↔ x ^ (2 ^ m) = 1 := by
    obtain ⟨k, hk_le, hk_eq⟩ := horder_pow x
    change (orderOf x).factorization 2 ≤ m ↔ x ^ (2 ^ m) = 1
    rw [hk_eq, Nat.factorization_pow_self Nat.prime_two]
    constructor
    · intro hkm
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hk_eq]; exact pow_dvd_pow 2 hkm)
    · intro hx
      have hdvd : 2 ^ k ∣ 2 ^ m := by
        rw [← hk_eq]
        exact orderOf_dvd_of_pow_eq_one hx
      obtain ⟨l, hlm, hl_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hkl : k = l := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hl_eq
      omega
  have hB_kernel (m : ℕ) : B m = Nat.card {x : H // x ^ (2 ^ m) = 1} := by
    have hfilter : B m = Nat.card {x : H // v x ≤ m} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hfilter]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1, (hpow_iff x.1 m).1 x.2⟩
        invFun := fun x => ⟨x.1, (hpow_iff x.1 m).2 x.2⟩
        left_inv := by intro x; ext; rfl
        right_inv := by intro x; ext; rfl }
  have hB4 (m : ℕ) (hm : 0 < m) : 4 ∣ B m := by
    rw [hB_kernel m]
    exact pi_pow_kernel_card_dvd_four n a ha_pos hn hcard hm
  have hB0 : B 0 = 1 := by
    rw [hB_kernel 0]
    haveI : Unique {x : H // x ^ (2 ^ 0) = 1} := by
      refine ⟨⟨1, by simp⟩, ?_⟩
      intro x
      apply Subtype.ext
      simpa using x.2
    exact Nat.card_unique
  have hlayer (k : ℕ) (hk : 0 < k) : L k + B (k - 1) = B k := by
    classical
    let s := (Finset.univ.filter fun x : H => v x ≤ k)
    have hsplit := Finset.card_filter_add_card_filter_not (s := s) (p := fun x : H => v x ≤ k - 1)
    have hfirst : s.filter (fun x : H => v x ≤ k - 1) = Finset.univ.filter fun x : H => v x ≤ k - 1 := by
      ext x
      simp [s]
      omega
    have hsecond : s.filter (fun x : H => ¬ v x ≤ k - 1) = Finset.univ.filter fun x : H => v x = k := by
      ext x
      simp [s]
      omega
    rw [hfirst, hsecond] at hsplit
    simpa [L, B, s, add_comm] using hsplit
  have hL1_mod : L 1 % 4 = 3 := by
    have hrel := hlayer 1 (by norm_num)
    have hb1 := hB4 1 (by norm_num)
    obtain ⟨u, hu⟩ := hb1
    have h : L 1 + 1 = 4 * u := by
      calc
        L 1 + 1 = B 1 := by simpa [hB0] using hrel
        _ = 4 * u := hu
    omega
  have hL4 (k : ℕ) (hk : 2 ≤ k) : 4 ∣ L k := by
    have hrel := hlayer k (by omega)
    have hb := hB4 k (by omega)
    have hbp := hB4 (k - 1) (by omega)
    obtain ⟨u, hu⟩ := hb
    obtain ⟨w, hw⟩ := hbp
    use u - w
    omega
  have hfiber_sum : (∑ k ∈ Finset.range 2010, L k * k) = ∑ x : H, v x := by
    classical
    have hfiber := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset H))
      (t := Finset.range 2010) (g := v) hv_range (fun k : ℕ => k)
    rw [← hfiber]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_const_nat]
    intro x hx
    rfl
  have hsum_eq : (∑ k ∈ Finset.range 2010, L k * k) = 2009 := by
    rw [hfiber_sum, hS]
  have hrest4 : (4 : ℕ) ∣ (∑ k ∈ Finset.erase (Finset.range 2010) 1, L k * k) := by
    apply Finset.dvd_sum
    intro k hk
    have hk_ne : k ≠ 1 := by
      exact (Finset.mem_erase.mp hk).1
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hk2 : 2 ≤ k := by omega
      exact dvd_mul_of_dvd_left (hL4 k hk2) k
  have hsum_mod : (∑ k ∈ Finset.range 2010, L k * k) % 4 = 3 := by
    have hmem : 1 ∈ Finset.range 2010 := by simp
    have hsplit := Finset.sum_erase_add (s := Finset.range 2010) (a := 1) (f := fun k => L k * k) hmem
    rw [← hsplit]
    obtain ⟨q, hq⟩ := hrest4
    rw [hq]
    simp
    omega
  have hbad : 2009 % 4 = 3 := by
    rw [← hsum_eq]
    exact hsum_mod
  norm_num at hbad

-- False
/--
Is there a finite abelian group $G$ such that the product of the orders of all its elements is 2^{2009}?
-/
theorem putnam_2009_a5
: (∃ (G : Type*) (_ : CommGroup G) (_ : Fintype G), ∏ g : G, orderOf g = 2^2009) ↔ ((False) : Prop ) := by
  constructor
  · rintro ⟨G, hG, hF, hprod⟩
    letI : CommGroup G := hG
    letI : Fintype G := hF
    haveI : Finite G := Finite.of_fintype G
    classical
    obtain ⟨ι, hι, n, hn_gt, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
    letI : Fintype ι := hι
    letI : DecidableEq ι := Classical.decEq ι
    have hn_pos : ∀ i, 0 < n i := by
      intro i
      have h := hn_gt i
      omega
    haveI : (i : ι) → NeZero (n i) := fun i => ⟨(hn_pos i).ne'⟩
    let H := (i : ι) → Multiplicative (ZMod (n i))
    have hprodH : ∏ h : H, orderOf h = 2 ^ 2009 := by
      rw [← hprod]
      exact (Fintype.prod_equiv e.toEquiv (fun g : G => orderOf g) (fun h : H => orderOf h)
        (by intro g; exact (e.orderOf_eq g).symm)).symm
    have hn_dvd : ∀ i, n i ∣ 2 ^ 2009 := by
      intro i
      let x : H := Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i)))
      have hx : orderOf x = n i := by
        rw [orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
      rw [← hprodH, ← hx]
      exact Finset.dvd_prod_of_mem (fun h : H => orderOf h) (Finset.mem_univ x)
    have hn_pow : ∀ i, ∃ a ≤ 2009, n i = 2 ^ a := by
      intro i
      exact (Nat.dvd_prime_pow Nat.prime_two).1 (hn_dvd i)
    choose a ha_le ha_eq using hn_pow
    have ha_pos : ∀ i, 0 < a i := by
      intro i
      by_contra h
      have hai0 : a i = 0 := Nat.eq_zero_of_not_pos h
      have hni : n i = 1 := by
        rw [ha_eq i, hai0]
        norm_num
      have hgt := hn_gt i
      omega
    by_cases hcard0 : Fintype.card ι = 0
    · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard0
      have hprod_one : (∏ h : H, orderOf h) = 1 := by
        rw [Fintype.prod_unique]
        rw [orderOf_eq_one_iff]
        ext i
        exact isEmptyElim i
      rw [hprod_one] at hprodH
      have h2dvd : 2 ∣ 2 ^ 2009 := dvd_pow_self 2 (by norm_num : 2009 ≠ 0)
      rw [← hprodH] at h2dvd
      norm_num at h2dvd
    · by_cases hcard1 : Fintype.card ι = 1
      · rcases Fintype.card_eq_one_iff_nonempty_unique.mp hcard1 with ⟨huniq⟩
        letI : Unique ι := huniq
        haveI : IsCyclic H := by
          let epi := MulEquiv.piUnique (fun i : ι => Multiplicative (ZMod (n i)))
          exact epi.isCyclic.2 inferInstance
        have hcardH : Fintype.card H = 2 ^ a default := by
          let epi := MulEquiv.piUnique (fun i : ι => Multiplicative (ZMod (n i)))
          calc
            Fintype.card H = Fintype.card (Multiplicative (ZMod (n default))) := Fintype.card_congr epi.toEquiv
            _ = Fintype.card (ZMod (n default)) := Fintype.card_multiplicative (ZMod (n default))
            _ = n default := ZMod.card (n default)
            _ = 2 ^ a default := ha_eq default
        exact (cyclic_two_power_product_ne H hcardH) hprodH
      · have hcard2 : 2 ≤ Fintype.card ι := by omega
        exact (pi_two_power_product_ne n a ha_pos ha_eq hcard2) hprodH
  · intro h
    exact False.elim h
