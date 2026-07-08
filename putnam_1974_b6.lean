import Mathlib

open Set Nat Polynomial Filter Topology

abbrev putnam_1974_b6_solution : (ℕ × ℕ × ℕ) :=
  (2 * ((2 ^ 999 - 2) / 3) + 1,
    2 * ((2 ^ 999 - 2) / 3) + 1,
    2 * ((2 ^ 999 - 2) / 3) + 2)

set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option exponentiation.threshold 1001

private def putnam_1974_b6_residueCount {α : Type*} (r : ℕ) (s : Finset α) : ℕ :=
  (s.powerset.filter fun t => t.card ≡ r [MOD 3]).card

private lemma putnam_1974_b6_ncard_setOf_subsets_card_modEq {α : Type*}
    [DecidableEq α] (s : Finset α) (r : ℕ) :
    {S | S ⊆ s ∧ S.card ≡ r [MOD 3]}.ncard = putnam_1974_b6_residueCount r s := by
  let A : Set (Finset α) := {S | S ⊆ s ∧ S.card ≡ r [MOD 3]}
  have hfin : A.Finite := by
    refine s.powerset.finite_toSet.subset ?_
    intro S hS
    exact Finset.mem_powerset.mpr hS.1
  rw [Set.ncard_eq_toFinset_card A hfin]
  have hto : hfin.toFinset = s.powerset.filter (fun t => t.card ≡ r [MOD 3]) := by
    ext S
    simp [A]
  rw [hto]
  rfl

private lemma putnam_1974_b6_residueCount_eq_sum_choose_filter {α : Type*}
    [DecidableEq α] (s : Finset α) (r : ℕ) :
    putnam_1974_b6_residueCount r s =
      ∑ k ∈ (Finset.range (s.card + 1)).filter (fun k => k ≡ r [MOD 3]),
        Nat.choose s.card k := by
  have hpair : ((Finset.range (s.card + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k => (s.powersetCard k).filter fun t => t.card ≡ r [MOD 3]) := by
    intro i _hi j _hj hij
    exact (s.pairwise_disjoint_powersetCard hij).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc
    putnam_1974_b6_residueCount r s
        = (((Finset.range (s.card + 1)).biUnion fun k => s.powersetCard k).filter
            fun t => t.card ≡ r [MOD 3]).card := by
            rw [putnam_1974_b6_residueCount, Finset.powerset_card_biUnion]
    _ = ((Finset.range (s.card + 1)).biUnion
            fun k => (s.powersetCard k).filter fun t => t.card ≡ r [MOD 3]).card := by
            rw [Finset.filter_biUnion]
    _ = ∑ k ∈ Finset.range (s.card + 1),
          ((s.powersetCard k).filter fun t => t.card ≡ r [MOD 3]).card := by
            rw [Finset.card_biUnion hpair]
    _ = ∑ k ∈ Finset.range (s.card + 1),
          if k ≡ r [MOD 3] then Nat.choose s.card k else 0 := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            by_cases hkr : k ≡ r [MOD 3]
            · have hfilter :
                  (s.powersetCard k).filter (fun t => t.card ≡ r [MOD 3]) =
                    s.powersetCard k := by
                ext t
                by_cases ht : t ∈ s.powersetCard k
                · have htc : t.card = k := (Finset.mem_powersetCard.mp ht).2
                  simp [ht, htc, hkr]
                · simp [ht]
              simp [hfilter, hkr]
            · have hfilter :
                  (s.powersetCard k).filter (fun t => t.card ≡ r [MOD 3]) = ∅ := by
                ext t
                by_cases ht : t ∈ s.powersetCard k
                · have htc : t.card = k := (Finset.mem_powersetCard.mp ht).2
                  have htmod : ¬t.card ≡ r [MOD 3] := by
                    simpa [htc] using hkr
                  simp [ht, htmod]
                · simp [ht]
              simp [hfilter, hkr]
    _ = ∑ k ∈ (Finset.range (s.card + 1)).filter (fun k => k ≡ r [MOD 3]),
          Nat.choose s.card k := by
            rw [Finset.sum_filter]

private lemma putnam_1974_b6_mod_succ_pred (n r : ℕ) :
    (n + 1 ≡ r [MOD 3]) ↔ (n ≡ (r + 2) % 3 [MOD 3]) := by
  simp [Nat.ModEq]
  omega

private lemma putnam_1974_b6_residueCount_empty_zero {α : Type*} [DecidableEq α] :
    putnam_1974_b6_residueCount 0 (∅ : Finset α) = 1 := by
  rw [putnam_1974_b6_residueCount, Finset.powerset_empty]
  have hfilter :
      (({∅} : Finset (Finset α)).filter fun t => t.card ≡ 0 [MOD 3]) = {∅} := by
    ext t
    by_cases ht : t = ∅ <;> simp [ht, Nat.ModEq]
  simp [hfilter]

private lemma putnam_1974_b6_residueCount_empty_one {α : Type*} [DecidableEq α] :
    putnam_1974_b6_residueCount 1 (∅ : Finset α) = 0 := by
  rw [putnam_1974_b6_residueCount, Finset.powerset_empty]
  have hfilter :
      (({∅} : Finset (Finset α)).filter fun t => t.card ≡ 1 [MOD 3]) = ∅ := by
    ext t
    by_cases ht : t = ∅ <;> simp [ht, Nat.ModEq]
  simp [hfilter]

private lemma putnam_1974_b6_residueCount_empty_two {α : Type*} [DecidableEq α] :
    putnam_1974_b6_residueCount 2 (∅ : Finset α) = 0 := by
  rw [putnam_1974_b6_residueCount, Finset.powerset_empty]
  have hfilter :
      (({∅} : Finset (Finset α)).filter fun t => t.card ≡ 2 [MOD 3]) = ∅ := by
    ext t
    by_cases ht : t = ∅ <;> simp [ht, Nat.ModEq]
  simp [hfilter]

private lemma putnam_1974_b6_residueCount_insert {α : Type*} [DecidableEq α]
    {a : α} {s : Finset α} (ha : a ∉ s) (r : ℕ) :
    putnam_1974_b6_residueCount r (insert a s) =
      putnam_1974_b6_residueCount r s + putnam_1974_b6_residueCount ((r + 2) % 3) s := by
  rw [putnam_1974_b6_residueCount, Finset.powerset_insert, Finset.filter_union]
  have hdisj : Disjoint
      (s.powerset.filter fun t => t.card ≡ r [MOD 3])
      ((s.powerset.image (insert a)).filter fun t => t.card ≡ r [MOD 3]) := by
    rw [Finset.disjoint_left]
    intro t htleft htright
    rcases Finset.mem_filter.mp htleft with ⟨htpow, _⟩
    rcases Finset.mem_filter.mp htright with ⟨htimg, _⟩
    rcases Finset.mem_image.mp htimg with ⟨u, _hupow, rfl⟩
    exact ha ((Finset.mem_powerset.mp htpow) (Finset.mem_insert_self a u))
  rw [Finset.card_union_of_disjoint hdisj]
  congr 1
  rw [Finset.filter_image]
  have hfilter :
      s.powerset.filter (fun t => (insert a t).card ≡ r [MOD 3]) =
        s.powerset.filter (fun t => t.card ≡ (r + 2) % 3 [MOD 3]) := by
    ext t
    by_cases htpow : t ∈ s.powerset
    · have hnot : a ∉ t := fun hat => ha ((Finset.mem_powerset.mp htpow) hat)
      simp [htpow, Finset.card_insert_of_notMem hnot, putnam_1974_b6_mod_succ_pred]
    · simp [htpow]
  rw [hfilter]
  apply Finset.card_image_of_injOn
  intro u hu v hv huv
  have hupow : u ∈ s.powerset := (Finset.mem_filter.mp hu).1
  have hvpow : v ∈ s.powerset := (Finset.mem_filter.mp hv).1
  have hnu : a ∉ u := fun hau => ha ((Finset.mem_powerset.mp hupow) hau)
  have hnv : a ∉ v := fun hav => ha ((Finset.mem_powerset.mp hvpow) hav)
  have := congrArg (fun t : Finset α => t.erase a) huv
  simpa [Finset.erase_insert hnu, Finset.erase_insert hnv] using this

private def putnam_1974_b6_countTriple : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | n + 1 =>
      let t := putnam_1974_b6_countTriple n
      (t.1 + t.2.2, t.2.1 + t.1, t.2.2 + t.2.1)

private lemma putnam_1974_b6_residueCount_eq_countTriple {α : Type*}
    [DecidableEq α] (s : Finset α) :
    (putnam_1974_b6_residueCount 0 s,
      putnam_1974_b6_residueCount 1 s,
      putnam_1974_b6_residueCount 2 s) =
      putnam_1974_b6_countTriple s.card := by
  induction s using Finset.induction_on with
  | empty =>
      simp [putnam_1974_b6_countTriple, putnam_1974_b6_residueCount_empty_zero,
        putnam_1974_b6_residueCount_empty_one, putnam_1974_b6_residueCount_empty_two]
  | insert a s ha ih =>
      have ih0 :
          putnam_1974_b6_residueCount 0 s =
            (putnam_1974_b6_countTriple s.card).1 := congrArg Prod.fst ih
      have ih1 :
          putnam_1974_b6_residueCount 1 s =
            (putnam_1974_b6_countTriple s.card).2.1 := congrArg (fun t => t.2.1) ih
      have ih2 :
          putnam_1974_b6_residueCount 2 s =
            (putnam_1974_b6_countTriple s.card).2.2 := congrArg (fun t => t.2.2) ih
      rw [Finset.card_insert_of_notMem ha, putnam_1974_b6_countTriple]
      simp [putnam_1974_b6_residueCount_insert ha, ih0, ih1, ih2, Nat.add_comm]

private lemma putnam_1974_b6_countTriple_1000 :
    putnam_1974_b6_countTriple 1000 = putnam_1974_b6_solution := by
  unfold putnam_1974_b6_solution
  norm_num [putnam_1974_b6_countTriple]

private lemma putnam_1974_b6_filter_range_modEq_zero :
    ((Finset.range 1001).filter fun k => k ≡ 0 [MOD 3]) =
      (Finset.range 334).image fun i => 3 * i := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkrange, hmod⟩
    rcases Nat.modEq_zero_iff_dvd.mp hmod with ⟨i, rfl⟩
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    have hlt : 3 * i < 1001 := by simpa using hkrange
    simp
    omega
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · have hlt : i < 334 := by simpa using hi
      simp
      omega
    · exact (dvd_mul_right 3 i).modEq_zero_nat

private lemma putnam_1974_b6_filter_range_modEq_one :
    ((Finset.range 1001).filter fun k => k ≡ 1 [MOD 3]) =
      (Finset.range 334).image fun i => 3 * i + 1 := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkrange, hmod⟩
    refine Finset.mem_image.mpr ⟨k / 3, ?_, ?_⟩
    · have hlt : k < 1001 := by simpa using hkrange
      have hmod' : k % 3 = 1 := by simpa [Nat.ModEq] using hmod
      have hdecomp := Nat.div_add_mod k 3
      simp
      omega
    · have hmod' : k % 3 = 1 := by simpa [Nat.ModEq] using hmod
      have hdecomp := Nat.div_add_mod k 3
      omega
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · have hlt : i < 334 := by simpa using hi
      simp
      omega
    · exact Nat.ModEq.modulus_mul_add

private lemma putnam_1974_b6_filter_range_modEq_two :
    ((Finset.range 1001).filter fun k => k ≡ 2 [MOD 3]) =
      (Finset.range 333).image fun i => 3 * i + 2 := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkrange, hmod⟩
    refine Finset.mem_image.mpr ⟨k / 3, ?_, ?_⟩
    · have hlt : k < 1001 := by simpa using hkrange
      have hmod' : k % 3 = 2 := by simpa [Nat.ModEq] using hmod
      have hdecomp := Nat.div_add_mod k 3
      simp
      omega
    · have hmod' : k % 3 = 2 := by simpa [Nat.ModEq] using hmod
      have hdecomp := Nat.div_add_mod k 3
      omega
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · have hlt : i < 333 := by simpa using hi
      simp
      omega
    · exact Nat.ModEq.modulus_mul_add

private lemma putnam_1974_b6_sum_choose_filter_zero :
    (∑ k ∈ ((Finset.range 1001).filter fun k => k ≡ 0 [MOD 3]), Nat.choose 1000 k) =
      ∑ i ∈ Finset.range 334, Nat.choose 1000 (3 * i) := by
  rw [putnam_1974_b6_filter_range_modEq_zero]
  exact Finset.sum_image (by
    intro i _hi j _hj hij
    have hij' : 3 * i = 3 * j := by simpa using hij
    omega)

private lemma putnam_1974_b6_sum_choose_filter_one :
    (∑ k ∈ ((Finset.range 1001).filter fun k => k ≡ 1 [MOD 3]), Nat.choose 1000 k) =
      ∑ i ∈ Finset.range 334, Nat.choose 1000 (3 * i + 1) := by
  rw [putnam_1974_b6_filter_range_modEq_one]
  exact Finset.sum_image (by
    intro i _hi j _hj hij
    have hij' : 3 * i + 1 = 3 * j + 1 := by simpa using hij
    omega)

private lemma putnam_1974_b6_sum_choose_filter_two :
    (∑ k ∈ ((Finset.range 1001).filter fun k => k ≡ 2 [MOD 3]), Nat.choose 1000 k) =
      ∑ i ∈ Finset.range 333, Nat.choose 1000 (3 * i + 2) := by
  rw [putnam_1974_b6_filter_range_modEq_two]
  exact Finset.sum_image (by
    intro i _hi j _hj hij
    have hij' : 3 * i + 2 = 3 * j + 2 := by simpa using hij
    omega)

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
: (count0, count1, count2) = putnam_1974_b6_solution :=
by
  subst n
  rw [putnam_1974_b6_ncard_setOf_subsets_card_modEq] at hcount0
  rw [putnam_1974_b6_ncard_setOf_subsets_card_modEq] at hcount1
  rw [putnam_1974_b6_ncard_setOf_subsets_card_modEq] at hcount2
  rw [hcount0, hcount1, hcount2]
  have hcard : (Finset.Icc (1 : ℤ) (1000 : ℤ)).card = 1000 := by
    rw [Int.card_Icc]
    norm_num [Int.toNat]
  rw [putnam_1974_b6_residueCount_eq_countTriple, hcard, putnam_1974_b6_countTriple_1000]
