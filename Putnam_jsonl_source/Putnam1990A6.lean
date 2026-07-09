import Mathlib

open Filter Topology Nat

set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false

private lemma putnam_1990_a6_card_large (k : ℕ) (hk : k ≤ 10) :
    ((Finset.univ : Finset (Set.Icc (1:ℕ) 10)).filter
      (fun x : Set.Icc (1:ℕ) 10 => k < (x : ℕ))).card = 10 - k := by
  rw [← Fintype.card_subtype (fun x : Set.Icc (1:ℕ) 10 => k < (x : ℕ))]
  let e : {x : Set.Icc (1:ℕ) 10 // k < (x : ℕ)} ≃ Set.Icc (k+1) 10 :=
  { toFun := fun x : {x : Set.Icc (1:ℕ) 10 // k < (x : ℕ)} => (⟨(x.1 : ℕ), by
      constructor
      · exact Nat.succ_le_of_lt x.2
      · exact x.1.2.2⟩ : Set.Icc (k+1) 10)
    invFun := fun y : Set.Icc (k+1) 10 => (⟨⟨(y : ℕ), by
      constructor
      · change 1 ≤ (y : ℕ)
        have hy1 := y.2.1
        omega
      · exact y.2.2⟩, by
        change k < (y : ℕ)
        have hy1 := y.2.1
        omega⟩ : {x : Set.Icc (1:ℕ) 10 // k < (x : ℕ)})
    left_inv := by
      intro x
      ext
      rfl
    right_inv := by
      intro y
      ext
      rfl }
  rw [Fintype.card_congr e]
  rw [Fintype.card_ofFinset (Finset.Icc (k+1) 10)]
  rw [Nat.card_Icc]
  omega

private lemma putnam_1990_a6_card_subsets_large (k m : ℕ) (hk : k ≤ 10) :
    ((Finset.univ : Finset (Finset (Set.Icc (1:ℕ) 10))).filter
      (fun S => S.card = m ∧ ∀ s : Set.Icc (1:ℕ) 10, s ∈ S → k < (s : ℕ))).card =
    Nat.choose (10 - k) m := by
  let L : Finset (Set.Icc (1:ℕ) 10) :=
    (Finset.univ : Finset (Set.Icc (1:ℕ) 10)).filter
      (fun x : Set.Icc (1:ℕ) 10 => k < (x : ℕ))
  have hset : ((Finset.univ : Finset (Finset (Set.Icc (1:ℕ) 10))).filter
      (fun S => S.card = m ∧ ∀ s : Set.Icc (1:ℕ) 10, s ∈ S → k < (s : ℕ))) =
      Finset.powersetCard m L := by
    ext S
    simp [L, Finset.mem_powersetCard, Finset.subset_iff, and_comm]
  rw [hset, Finset.card_powersetCard]
  rw [putnam_1990_a6_card_large k hk]

-- 17711
/--
If $X$ is a finite set, let $|X|$ denote the number of elements in $X$. Call an ordered pair $(S,T)$ of subsets of $\{1,2,\dots,n\}$ \emph{admissible} if $s>|T|$ for each $s \in S$, and $t>|S|$ for each $t \in T$. How many admissible ordered pairs of subsets of $\{1,2,\dots,10\}$ are there? Prove your answer.
-/
theorem putnam_1990_a6 :
    ((Finset.univ : Finset <| Finset (Set.Icc 1 10) × Finset (Set.Icc 1 10)).filter
      fun ⟨S, T⟩ ↦ (∀ s ∈ S, T.card < s) ∧ (∀ t ∈ T, S.card < t)).card =
    ((17711) : ℕ ) := by
  let ι := Set.Icc (1:ℕ) 10
  let A : Finset (Finset ι × Finset ι) :=
    ((Finset.univ : Finset <| Finset ι × Finset ι).filter
      fun ⟨S, T⟩ ↦ (∀ s ∈ S, T.card < s) ∧ (∀ t ∈ T, S.card < t))
  let B : Finset (ℕ × ℕ) := Finset.range 11 ×ˢ Finset.range 11
  change A.card = 17711
  have hcardι : Fintype.card ι = 10 := by
    norm_num [ι, Set.Icc]
  have hmaps : Set.MapsTo (fun ST : Finset ι × Finset ι => (ST.1.card, ST.2.card)) ↑A ↑B := by
    intro ST hST
    change (ST.1.card, ST.2.card) ∈ (Finset.range 11 ×ˢ Finset.range 11)
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    constructor
    · exact Nat.lt_succ_of_le (by simpa [hcardι] using Finset.card_le_univ ST.1)
    · exact Nat.lt_succ_of_le (by simpa [hcardι] using Finset.card_le_univ ST.2)
  calc
    A.card = ∑ ab ∈ B, (A.filter fun ST => (ST.1.card, ST.2.card) = ab).card := by
      exact Finset.card_eq_sum_card_fiberwise
        (f := fun ST : Finset ι × Finset ι => (ST.1.card, ST.2.card)) hmaps
    _ = ∑ ab ∈ B, Nat.choose (10 - ab.2) ab.1 * Nat.choose (10 - ab.1) ab.2 := by
      apply Finset.sum_congr rfl
      intro ab hab
      have ha : ab.1 ≤ 10 := by
        have h := (Finset.mem_product.mp hab).1
        rw [Finset.mem_range] at h
        omega
      have hb : ab.2 ≤ 10 := by
        have h := (Finset.mem_product.mp hab).2
        rw [Finset.mem_range] at h
        omega
      have hset : A.filter (fun ST => (ST.1.card, ST.2.card) = ab) =
          (((Finset.univ : Finset (Finset ι)).filter
            (fun S => S.card = ab.1 ∧ ∀ s : ι, s ∈ S → ab.2 < (s : ℕ))) ×ˢ
          ((Finset.univ : Finset (Finset ι)).filter
            (fun T => T.card = ab.2 ∧ ∀ t : ι, t ∈ T → ab.1 < (t : ℕ)))) := by
        ext ST
        rcases ST with ⟨S, T⟩
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
        constructor
        · intro h
          rcases h with ⟨hcond, hcard⟩
          rcases hcond with ⟨hS, hT⟩
          have hScard : S.card = ab.1 := congr_arg Prod.fst hcard
          have hTcard : T.card = ab.2 := congr_arg Prod.snd hcard
          exact ⟨⟨hScard, by
            intro s hs
            simpa [← hTcard] using hS s hs⟩,
            ⟨hTcard, by
              intro t ht
              simpa [← hScard] using hT t ht⟩⟩
        · intro h
          rcases h with ⟨hSinfo, hTinfo⟩
          rcases hSinfo with ⟨hScard, hS⟩
          rcases hTinfo with ⟨hTcard, hT⟩
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro s hs
            simpa [hTcard] using hS s hs
          · intro t ht
            simpa [hScard] using hT t ht
          · ext <;> assumption
      rw [hset, Finset.card_product]
      rw [putnam_1990_a6_card_subsets_large ab.2 ab.1 hb]
      rw [putnam_1990_a6_card_subsets_large ab.1 ab.2 ha]
    _ = 17711 := by
      norm_num [B, Finset.sum_product, Finset.sum_range_succ, Nat.choose]
