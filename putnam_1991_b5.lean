import Mathlib

open Filter Topology

abbrev putnam_1991_b5_solution : ℕ → ℕ :=
  fun p => ⌊(((p + 3 : ℕ) : ℚ) / 4)⌋₊

private lemma card_sq_eq_of_isSquare {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {a : F} (ha : IsSquare a) :
    Fintype.card {x : F // x ^ 2 = a} = if a = 0 then 1 else 2 := by
  by_cases h0 : a = 0
  · subst a
    have h : (({x : F | x ^ 2 = (0 : F)}.toFinset.card : ℤ) = 1) := by
      simpa using (quadraticChar_card_sqrts (F := F) hF (0 : F))
    rw [if_pos rfl]
    change Fintype.card (↑({x : F | x ^ 2 = (0 : F)} : Set F)) = 1
    rw [← Set.toFinset_card ({x : F | x ^ 2 = (0 : F)})]
    exact_mod_cast h
  · have hχ : quadraticChar F a = 1 := (quadraticChar_one_iff_isSquare (F := F) h0).2 ha
    have h : (({x : F | x ^ 2 = a}.toFinset.card : ℤ) = 2) := by
      simpa [hχ] using (quadraticChar_card_sqrts (F := F) hF a)
    rw [if_neg h0]
    change Fintype.card (↑({x : F | x ^ 2 = a} : Set F)) = 2
    rw [← Set.toFinset_card ({x : F | x ^ 2 = a})]
    exact_mod_cast h

private noncomputable def hyperbolaEquivUnits {F : Type*} [Field F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    {xy : F × F // xy.1 ^ 2 = xy.2 ^ 2 + 1} ≃ Fˣ := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  refine
  { toFun := fun w => Units.mk0 (w.1.1 - w.1.2) ?_
    invFun := fun u =>
      ⟨(((u : F) + (u : F)⁻¹) / 2, ((u : F)⁻¹ - (u : F)) / 2), by
        field_simp [h2, Units.ne_zero u]
        ring_nf⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro hsub
    have hxy : w.1.1 ^ 2 = w.1.2 ^ 2 + 1 := w.2
    have hxyeq : w.1.1 = w.1.2 := sub_eq_zero.mp hsub
    have hsame : w.1.2 ^ 2 = w.1.2 ^ 2 + 1 := by simpa [hxyeq] using hxy
    have hzero : (1 : F) = 0 := by
      have h0 : (w.1.2 ^ 2 + 1) - w.1.2 ^ 2 = 0 := by rw [← hsame, sub_self]
      ring_nf at h0
      simpa using h0
    exact one_ne_zero hzero
  · intro w
    have hprod : (w.1.1 - w.1.2) * (w.1.1 + w.1.2) = 1 := by
      have hxy : w.1.1 ^ 2 = w.1.2 ^ 2 + 1 := w.2
      calc
        (w.1.1 - w.1.2) * (w.1.1 + w.1.2) = w.1.1 ^ 2 - w.1.2 ^ 2 := by ring
        _ = 1 := by rw [hxy]; ring
    have hinv : (w.1.1 - w.1.2)⁻¹ = w.1.1 + w.1.2 :=
      inv_eq_of_mul_eq_one_right hprod
    ext <;> dsimp only <;> simp only [Units.val_mk0]
    · rw [hinv]
      field_simp [h2]
      ring
    · rw [hinv]
      field_simp [h2]
      ring
  · intro u
    ext
    dsimp only
    simp only [Units.val_mk0]
    field_simp [h2, Units.ne_zero u]
    ring

private noncomputable def pairSigmaEquiv {F : Type*} [Field F] [DecidableEq F] :
    {xy : F × F // xy.1 ^ 2 = xy.2 ^ 2 + 1} ≃
      (Σ z : {z : F | (∃ x : F, z = x ^ 2) ∧ (∃ y : F, z = y ^ 2 + 1)},
        ({x : F // x ^ 2 = z.1} × {y : F // y ^ 2 = z.1 - 1})) := by
  classical
  refine
  { toFun := fun w =>
      ⟨⟨w.1.1 ^ 2, by
          constructor
          · exact ⟨w.1.1, rfl⟩
          · exact ⟨w.1.2, w.2⟩⟩,
        (⟨w.1.1, rfl⟩, ⟨w.1.2, by
          change w.1.2 ^ 2 = w.1.1 ^ 2 - 1
          rw [w.2]
          ring⟩)⟩
    invFun := fun s =>
      ⟨(s.2.1.1, s.2.2.1), by
        rw [s.2.1.2, s.2.2.2]
        ring⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro w
    rfl
  · intro s
    cases s with
    | mk z roots =>
      cases z with
      | mk zv hzmem =>
        cases roots with
        | mk x y =>
          cases x with
          | mk xv hx =>
            cases y with
            | mk yv hy =>
              dsimp at hx hy ⊢
              subst zv
              simp

/--
Let $p$ be an odd prime and let $\mathbb{Z}_p$ denote (the field of) integers modulo $p$. How many elements are in the set $\{x^2:x \in \mathbb{Z}_p\} \cap \{y^2+1:y \in \mathbb{Z}_p\}$?
-/
theorem putnam_1991_b5
(p : ℕ)
(podd : Odd p)
(pprime : Prime p)
: ({z : ZMod p | ∃ x : ZMod p, z = x ^ 2} ∩ {z : ZMod p | ∃ y : ZMod p, z = y ^ 2 + 1}).encard = putnam_1991_b5_solution p :=
by
  classical
  have hpNat : p.Prime := Nat.prime_iff.mpr pprime
  letI : Fact p.Prime := ⟨hpNat⟩
  letI : NeZero p := ⟨hpNat.ne_zero⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    have hpne2 : p ≠ 2 := by
      rintro rfl
      norm_num at podd
    rw [ringChar.eq (ZMod p) p]
    exact hpne2
  let A : Set (ZMod p) :=
    {z : ZMod p | (∃ x : ZMod p, z = x ^ 2) ∧ (∃ y : ZMod p, z = y ^ 2 + 1)}
  have hAset :
      ({z : ZMod p | ∃ x : ZMod p, z = x ^ 2} ∩
          {z : ZMod p | ∃ y : ZMod p, z = y ^ 2 + 1}) = A := by
    ext z
    rfl
  rw [hAset]
  let P : Type := {xy : ZMod p × ZMod p // xy.1 ^ 2 = xy.2 ^ 2 + 1}
  let g : A → ℕ := fun z =>
    (if (z.1 : ZMod p) = 0 then 1 else 2) * (if (z.1 : ZMod p) = 1 then 1 else 2)
  let d0 : A → ℕ := fun z => if (z.1 : ZMod p) = 0 then 1 else 0
  let d1 : A → ℕ := fun z => if (z.1 : ZMod p) = 1 then 1 else 0
  have hPairCard : Fintype.card P = p - 1 := by
    dsimp [P]
    calc
      Fintype.card {xy : ZMod p × ZMod p // xy.1 ^ 2 = xy.2 ^ 2 + 1}
          = Fintype.card (ZMod p)ˣ :=
            Fintype.card_congr (hyperbolaEquivUnits (F := ZMod p) hchar)
      _ = p - 1 := ZMod.card_units p
  have hsqA (z : A) : IsSquare (z.1 : ZMod p) := by
    rcases z.2.1 with ⟨x, hx⟩
    exact ⟨x, by rw [hx]; ring⟩
  have hsqAm1 (z : A) : IsSquare ((z.1 : ZMod p) - 1) := by
    rcases z.2.2 with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [hy]
    ring
  have hRX (z : A) :
      Fintype.card {x : ZMod p // x ^ 2 = z.1} =
        if (z.1 : ZMod p) = 0 then 1 else 2 :=
    card_sq_eq_of_isSquare (F := ZMod p) hchar (hsqA z)
  have hRY (z : A) :
      Fintype.card {y : ZMod p // y ^ 2 = (z.1 : ZMod p) - 1} =
        if (z.1 : ZMod p) = 1 then 1 else 2 := by
    rw [card_sq_eq_of_isSquare (F := ZMod p) hchar (hsqAm1 z)]
    by_cases hz1 : (z.1 : ZMod p) = 1
    · simp [hz1]
    · have hzsub : (z.1 : ZMod p) - 1 ≠ 0 := by
        intro h
        exact hz1 (sub_eq_zero.mp h)
      simp [hz1, hzsub]
  have hPairSum : Fintype.card P = ∑ z : A, g z := by
    dsimp [P]
    calc
      Fintype.card {xy : ZMod p × ZMod p // xy.1 ^ 2 = xy.2 ^ 2 + 1}
          = Fintype.card
              (Σ z : A,
                ({x : ZMod p // x ^ 2 = z.1} ×
                  {y : ZMod p // y ^ 2 = (z.1 : ZMod p) - 1})) :=
            Fintype.card_congr (pairSigmaEquiv (F := ZMod p))
      _ = ∑ z : A,
            Fintype.card
              ({x : ZMod p // x ^ 2 = z.1} ×
                {y : ZMod p // y ^ 2 = (z.1 : ZMod p) - 1}) := by
            rw [Fintype.card_sigma]
      _ = ∑ z : A, g z := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [Fintype.card_prod, hRX z, hRY z]
  have hpoint (z : A) : g z + 2 * d0 z + 2 * d1 z = 4 := by
    by_cases hz0 : (z.1 : ZMod p) = 0
    · have hz1 : ¬ (z.1 : ZMod p) = 1 := by
        intro h
        exact zero_ne_one (hz0.symm.trans h)
      simp [g, d0, d1, hz0]
    · by_cases hz1 : (z.1 : ZMod p) = 1
      · simp [g, d0, d1, hz1]
      · simp [g, d0, d1, hz0, hz1]
  have hcorr :
      (∑ z : A, g z) + 2 * (∑ z : A, d0 z) + 2 * (∑ z : A, d1 z) =
        4 * Fintype.card A := by
    calc
      (∑ z : A, g z) + 2 * (∑ z : A, d0 z) + 2 * (∑ z : A, d1 z)
          = ∑ z : A, (g z + 2 * d0 z + 2 * d1 z) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
      _ = ∑ z : A, 4 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hpoint z
      _ = 4 * Fintype.card A := by
            simp [Finset.sum_const, mul_comm]
  have hOneMem : (1 : ZMod p) ∈ A := by
    constructor
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  let oneA : A := ⟨1, hOneMem⟩
  have hd1 : ∑ z : A, d1 z = 1 := by
    rw [Fintype.sum_eq_single oneA]
    · simp [d1, oneA]
    · intro z hz
      have hzv : ¬ (z.1 : ZMod p) = 1 := by
        intro h
        apply hz
        ext
        exact h
      simp [d1, hzv]
  have hzero_square : (0 : ZMod p) ∈ A ↔ IsSquare (-1 : ZMod p) := by
    constructor
    · intro h0A
      rcases h0A.2 with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [eq_comm, eq_neg_iff_add_eq_zero]
      simpa [pow_two, add_comm] using hy.symm
    · rintro ⟨y, hy⟩
      constructor
      · exact ⟨0, by simp⟩
      · refine ⟨y, ?_⟩
        rw [pow_two, ← hy]
        ring
  have hsquare_mod : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 := by
    simpa [ZMod.card p] using (FiniteField.isSquare_neg_one_iff (F := ZMod p))
  have hpmod13 : p % 4 = 1 ∨ p % 4 = 3 := by
    have hpoddmod : p % 2 = 1 := Nat.odd_iff.mp podd
    omega
  by_cases hzero : (0 : ZMod p) ∈ A
  · let zeroA : A := ⟨0, hzero⟩
    have hd0 : ∑ z : A, d0 z = 1 := by
      rw [Fintype.sum_eq_single zeroA]
      · simp [d0, zeroA]
      · intro z hz
        have hzv : ¬ (z.1 : ZMod p) = 0 := by
          intro h
          apply hz
          ext
          exact h
        simp [d0, hzv]
    have hsumg : ∑ z : A, g z = p - 1 := by
      rw [← hPairSum, hPairCard]
    have h4 : p - 1 + 4 = 4 * Fintype.card A := by
      simpa [hsumg, hd0, hd1, add_assoc] using hcorr
    have hN : Fintype.card A = (p + 3) / 4 := by
      have hp1 : 1 ≤ p := hpNat.one_lt.le
      omega
    have hmod1 : p % 4 = 1 := by
      have hnot3 : p % 4 ≠ 3 := hsquare_mod.mp (hzero_square.mp hzero)
      omega
    have hsol : (p + 3) / 4 = ⌊(((p + 3 : ℕ) : ℚ) / 4)⌋₊ := by
      change (p + 3) / 4 = ⌊(((p + 3 : ℕ) : ℚ) / ((4 : ℕ) : ℚ))⌋₊
      rw [Rat.natFloor_natCast_div_natCast]
    rw [← Set.coe_fintypeCard A]
    simp only [putnam_1991_b5_solution]
    rw [hN]
    exact_mod_cast hsol
  · have hd0 : ∑ z : A, d0 z = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have hzv : ¬ (z.1 : ZMod p) = 0 := by
        intro h
        apply hzero
        simpa [A, h] using z.2
      simp [d0, hzv]
    have hsumg : ∑ z : A, g z = p - 1 := by
      rw [← hPairSum, hPairCard]
    have h4 : p - 1 + 2 = 4 * Fintype.card A := by
      simpa [hsumg, hd0, hd1, add_assoc] using hcorr
    have hN : Fintype.card A = (p + 1) / 4 := by
      have hp1 : 1 ≤ p := hpNat.one_lt.le
      omega
    have hmod3 : p % 4 = 3 := by
      cases hpmod13 with
      | inl h1 =>
        have hnot3 : p % 4 ≠ 3 := by omega
        exact (hzero (hzero_square.mpr (hsquare_mod.mpr hnot3))).elim
      | inr h3 => exact h3
    have hsol : (p + 1) / 4 = ⌊(((p + 3 : ℕ) : ℚ) / 4)⌋₊ := by
      change (p + 1) / 4 = ⌊(((p + 3 : ℕ) : ℚ) / ((4 : ℕ) : ℚ))⌋₊
      rw [Rat.natFloor_natCast_div_natCast]
      omega
    rw [← Set.coe_fintypeCard A]
    simp only [putnam_1991_b5_solution]
    rw [hN]
    exact_mod_cast hsol
