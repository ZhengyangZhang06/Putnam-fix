import Mathlib

set_option maxRecDepth 10000

open Filter Topology Nat

abbrev putnam_1990_a6_solution : ℕ := 17711

private abbrev putnam_1990_a6_alpha := Set.Icc (1 : ℕ) 10

private def putnam_1990_a6_above (k : ℕ) : Finset putnam_1990_a6_alpha :=
  (Finset.univ.filter fun x : putnam_1990_a6_alpha => k < (x : ℕ))

private lemma putnam_1990_a6_card_above (k : ℕ) (hk : k ∈ Finset.range 11) :
    (putnam_1990_a6_above k).card = 10 - k := by
  simp only [Finset.mem_range] at hk
  unfold putnam_1990_a6_above
  interval_cases k <;> decide

private lemma putnam_1990_a6_fiber_eq (a b : ℕ) :
    (((Finset.univ : Finset <| Finset putnam_1990_a6_alpha × Finset putnam_1990_a6_alpha).filter
      fun ⟨S, T⟩ ↦ (∀ s ∈ S, T.card < (s : ℕ)) ∧ (∀ t ∈ T, S.card < (t : ℕ))).filter
        fun p ↦ (p.1.card, p.2.card) = (a, b)) =
    ((putnam_1990_a6_above b).powersetCard a) ×ˢ
      ((putnam_1990_a6_above a).powersetCard b) := by
  ext p
  rcases p with ⟨S, T⟩
  constructor
  · intro hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hP, hpair⟩
    have hS : S.card = a := by simpa using congrArg Prod.fst hpair
    have hT : T.card = b := by simpa using congrArg Prod.snd hpair
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, hS⟩, Finset.mem_powersetCard.mpr ⟨?_, hT⟩⟩
    · intro s hs
      have hs' : b < (s : ℕ) := by simpa [hT] using hP.1 s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs'⟩
    · intro t ht
      have ht' : a < (t : ℕ) := by simpa [hS] using hP.2 t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht'⟩
  · intro hp
    have hSmem : S ∈ (putnam_1990_a6_above b).powersetCard a := (Finset.mem_product.mp hp).1
    have hTmem : T ∈ (putnam_1990_a6_above a).powersetCard b := (Finset.mem_product.mp hp).2
    rcases Finset.mem_powersetCard.mp hSmem with ⟨hSsub, hScard⟩
    rcases Finset.mem_powersetCard.mp hTmem with ⟨hTsub, hTcard⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s hs
      have hsabove := hSsub hs
      have hslt : b < (s : ℕ) := (Finset.mem_filter.mp hsabove).2
      simpa [hTcard] using hslt
    · intro t ht
      have htabove := hTsub ht
      have htlt : a < (t : ℕ) := (Finset.mem_filter.mp htabove).2
      simpa [hScard] using htlt
    · exact Prod.ext hScard hTcard

private lemma putnam_1990_a6_fiber_card (a b : ℕ) (ha : a ∈ Finset.range 11)
    (hb : b ∈ Finset.range 11) :
    (((Finset.univ : Finset <| Finset putnam_1990_a6_alpha × Finset putnam_1990_a6_alpha).filter
      fun ⟨S, T⟩ ↦ (∀ s ∈ S, T.card < (s : ℕ)) ∧ (∀ t ∈ T, S.card < (t : ℕ))).filter
        fun p ↦ (p.1.card, p.2.card) = (a, b)).card =
      Nat.choose (10 - b) a * Nat.choose (10 - a) b := by
  rw [putnam_1990_a6_fiber_eq a b]
  rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    putnam_1990_a6_card_above b hb, putnam_1990_a6_card_above a ha]

/--
If $X$ is a finite set, let $|X|$ denote the number of elements in $X$. Call an ordered pair $(S,T)$ of subsets of $\{1,2,\dots,n\}$ \emph{admissible} if $s>|T|$ for each $s \in S$, and $t>|S|$ for each $t \in T$. How many admissible ordered pairs of subsets of $\{1,2,\dots,10\}$ are there? Prove your answer.
-/
theorem putnam_1990_a6 :
    ((Finset.univ : Finset <| Finset (Set.Icc 1 10) × Finset (Set.Icc 1 10)).filter
      fun ⟨S, T⟩ ↦ (∀ s ∈ S, T.card < s) ∧ (∀ t ∈ T, S.card < t)).card =
    putnam_1990_a6_solution :=
  by
  let A : Finset (Finset putnam_1990_a6_alpha × Finset putnam_1990_a6_alpha) :=
    (Finset.univ.filter
      fun ⟨S, T⟩ ↦ (∀ s ∈ S, T.card < (s : ℕ)) ∧ (∀ t ∈ T, S.card < (t : ℕ)))
  let R : Finset (ℕ × ℕ) := (Finset.range 11) ×ˢ (Finset.range 11)
  change A.card = putnam_1990_a6_solution
  have hmaps : (A : Set (Finset putnam_1990_a6_alpha × Finset putnam_1990_a6_alpha)).MapsTo
      (fun p ↦ (p.1.card, p.2.card)) (R : Set (ℕ × ℕ)) := by
    intro p hp
    change (p.1.card, p.2.card) ∈ R
    unfold R
    apply Finset.mem_product.mpr
    constructor
    · rw [Finset.mem_range]
      have hle : p.1.card ≤ 10 := by
        have := p.1.card_le_univ
        norm_num [Fintype.card_Icc, Nat.card_Icc] at this ⊢
        exact this
      omega
    · rw [Finset.mem_range]
      have hle : p.2.card ≤ 10 := by
        have := p.2.card_le_univ
        norm_num [Fintype.card_Icc, Nat.card_Icc] at this ⊢
        exact this
      omega
  calc
    A.card = ∑ ab ∈ R, ((A.filter fun p ↦ (p.1.card, p.2.card) = ab).card) := by
      exact Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ a ∈ Finset.range 11, ∑ b ∈ Finset.range 11,
        Nat.choose (10 - b) a * Nat.choose (10 - a) b := by
      unfold R
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simpa [A] using putnam_1990_a6_fiber_card a b ha hb
    _ = putnam_1990_a6_solution := by
      norm_num [Finset.sum_range_succ, Nat.choose, putnam_1990_a6_solution]
