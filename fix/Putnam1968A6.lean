import Mathlib

open Finset Polynomial

private lemma putnam_1968_a6_esymm_card_eq_prod {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm s.card = s.prod := by
  rw [Multiset.esymm]
  have hpc : s.powersetCard s.card = {s} := by
    have hcard : (s.powersetCard s.card).card = 1 := by
      rw [Multiset.card_powersetCard, Nat.choose_self]
    obtain ⟨t, ht⟩ := Multiset.card_eq_one.mp hcard
    have hs_mem : s ∈ s.powersetCard s.card := by
      rw [Multiset.mem_powersetCard]
      exact ⟨le_rfl, rfl⟩
    rw [ht, Multiset.mem_singleton] at hs_mem
    rw [ht, hs_mem]
  rw [hpc]
  simp

private lemma putnam_1968_a6_sum_sq_eq (s : Multiset ℂ) :
    (s.map fun z => z ^ 2).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_eq_empty]
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one,
        Function.comp_apply, pow_two]
      rw [Multiset.sum_map_mul_left (a := a) (s := s) (f := fun x : ℂ => x)]
      rw [Multiset.map_id']
      ring

private lemma putnam_1968_a6_prod_sq_eq (s : Multiset ℂ) :
    (s.map fun z => z ^ 2).prod = s.prod ^ 2 := by
  calc
    (s.map fun z => z ^ 2).prod = (s.map fun z => z * z).prod := by
      simp [pow_two]
    _ = (s.map (fun z => z)).prod * (s.map (fun z => z)).prod := by
      rw [Multiset.prod_map_mul]
    _ = s.prod ^ 2 := by simp [pow_two]

private lemma putnam_1968_a6_real_sq_sum (s : Multiset ℂ) (hreal : ∀ z ∈ s, z.im = 0) :
    ((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ) = (s.map (fun z => z ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a.im = 0 := hreal a (by simp)
      have hs : ∀ z ∈ s, z.im = 0 := by
        intro z hz
        exact hreal z (by simp [hz])
      have hae : ((a.re ^ 2 : ℝ) : ℂ) = a ^ 2 := by
        apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, ha]
      simp [hae, ih hs]

private lemma putnam_1968_a6_real_sq_prod (s : Multiset ℂ) (hreal : ∀ z ∈ s, z.im = 0) :
    ((s.map (fun z => (z.re ^ 2 : ℝ))).prod : ℂ) = (s.map (fun z => z ^ 2)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a.im = 0 := hreal a (by simp)
      have hs : ∀ z ∈ s, z.im = 0 := by
        intro z hz
        exact hreal z (by simp [hz])
      have hae : ((a.re ^ 2 : ℝ) : ℂ) = a ^ 2 := by
        apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, ha]
      simp [hae, ih hs]

private lemma putnam_1968_a6_card_le_three {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hy_nonneg : ∀ i, 0 ≤ y i)
    (hy_prod : ∏ i, y i = 1) (hy_sum : ∑ i, y i ≤ 3) : Fintype.card ι ≤ 3 := by
  by_cases hι : Fintype.card ι = 0
  · omega
  have hpos_nat : 0 < Fintype.card ι := Nat.pos_of_ne_zero hι
  have hpos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hpos_nat
  have hweight_pos : 0 < ∑ i : ι, (1 : ℝ) := by
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hpos
  have hamgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset ι)
      (fun _ : ι => (1 : ℝ)) y (by intro i hi; norm_num)
      hweight_pos (by intro i hi; exact hy_nonneg i)
  have hone : (1 : ℝ) ≤ (∑ i, y i) / (Fintype.card ι : ℝ) := by
    convert hamgm using 1
    · simp [hy_prod, Finset.card_univ]
    · simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard_real : (Fintype.card ι : ℝ) ≤ ∑ i, y i := by
    have := (le_div_iff₀ hpos).mp hone
    simpa using this
  have hcard_le_three_real : (Fintype.card ι : ℝ) ≤ 3 := hcard_real.trans hy_sum
  exact_mod_cast hcard_le_three_real

private lemma putnam_1968_a6_all_eq_one_of_card_three {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 3) (y : ι → ℝ) (hy_nonneg : ∀ i, 0 ≤ y i)
    (hy_prod : ∏ i, y i = 1) (hy_sum : ∑ i, y i = 3) : ∀ i, y i = 1 := by
  have hwpos : ∀ i ∈ (Finset.univ : Finset ι), 0 < (fun _ : ι => (1 / 3 : ℝ)) i := by
    intro i hi
    norm_num
  have hwsum : ∑ i : ι, (1 / 3 : ℝ) = 1 := by
    simp [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  have hz : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ y i := by
    intro i hi
    exact hy_nonneg i
  have hgeom : (∏ i : ι, y i ^ (1 / 3 : ℝ)) = 1 := by
    rw [Real.finset_prod_rpow (Finset.univ : Finset ι) y (fun i hi => hy_nonneg i) (1 / 3 : ℝ)]
    rw [hy_prod]
    norm_num [Real.one_rpow]
  have harith : (∑ i : ι, (1 / 3 : ℝ) * y i) = 1 := by
    rw [← Finset.mul_sum]
    rw [hy_sum]
    norm_num
  have heq : (∏ i : ι, y i ^ (fun _ : ι => (1 / 3 : ℝ)) i) =
      (∑ i : ι, (fun _ : ι => (1 / 3 : ℝ)) i * y i) := by
    rw [hgeom, harith]
  have hall := (Real.geom_mean_eq_arith_mean_weighted_iff' (Finset.univ : Finset ι)
      (fun _ : ι => (1 / 3 : ℝ)) y hwpos hwsum hz).mp (by simpa using heq)
  intro j
  have hj := hall j (by simp)
  have htarget : y j = ∑ i : ι, (1 / 3 : ℝ) * y i := by simpa using hj
  rw [harith] at htarget
  exact htarget

private lemma putnam_1968_a6_degree_le_three {P : ℂ[X]}
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.natDegree ≤ 3 := by
  by_contra hnot
  have hn4 : 4 ≤ P.natDegree := by omega
  let s : Multiset ℂ := P.roots
  have hs_card : s.card = P.natDegree := by
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hs_real : ∀ z ∈ s, z.im = 0 := by
    intro z hz
    rcases hreal z (Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hz)) with ⟨r, hr⟩
    rw [← hr]
    simp
  have hlead := hcoeff P.natDegree (by constructor <;> omega)
  have hc1 := hcoeff (P.natDegree - 1) (by constructor <;> omega)
  have hc2 := hcoeff (P.natDegree - 2) (by constructor <;> omega)
  have hc0 := hcoeff 0 (by constructor <;> omega)
  have hv1 : P.coeff (P.natDegree - 1) = P.leadingCoeff * (-1) ^ 1 * P.roots.esymm 1 := by
    have hv := Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := P.natDegree - 1) (by omega)
    simpa [show P.natDegree - (P.natDegree - 1) = 1 by omega] using hv
  have hv2 : P.coeff (P.natDegree - 2) = P.leadingCoeff * (-1) ^ 2 * P.roots.esymm 2 := by
    have hv := Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := P.natDegree - 2) (by omega)
    simpa [show P.natDegree - (P.natDegree - 2) = 2 by omega] using hv
  have hv0 : P.coeff 0 = P.leadingCoeff * (-1) ^ P.natDegree * P.roots.esymm P.natDegree := by
    simpa using Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := 0) (Nat.zero_le _)
  have he1pm : P.roots.esymm 1 = (1 : ℂ) ∨ P.roots.esymm 1 = (-1 : ℂ) := by
    rcases hlead with hL | hL
    · rcases hc1 with hC | hC
      · have hv : P.roots.esymm 1 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using (congrArg Neg.neg hv1).symm
        exact Or.inr hv
      · have hv : P.roots.esymm 1 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using (congrArg Neg.neg hv1).symm
        exact Or.inl hv
    · rcases hc1 with hC | hC
      · have hv : P.roots.esymm 1 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using hv1.symm
        exact Or.inl hv
      · have hv : P.roots.esymm 1 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using hv1.symm
        exact Or.inr hv
  have he1sq : (P.roots.esymm 1) ^ 2 = (1 : ℂ) := by
    rcases he1pm with h | h <;> simp [h]
  have he2pm : P.roots.esymm 2 = (1 : ℂ) ∨ P.roots.esymm 2 = (-1 : ℂ) := by
    rcases hlead with hL | hL
    · rcases hc2 with hC | hC
      · have hv : P.roots.esymm 2 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using hv2.symm
        exact Or.inl hv
      · have hv : P.roots.esymm 2 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using hv2.symm
        exact Or.inr hv
    · rcases hc2 with hC | hC
      · have hv : P.roots.esymm 2 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using (congrArg Neg.neg hv2).symm
        exact Or.inr hv
      · have hv : P.roots.esymm 2 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using (congrArg Neg.neg hv2).symm
        exact Or.inl hv
  have hprod_sq : P.roots.prod ^ 2 = (1 : ℂ) := by
    have hen : P.roots.esymm P.natDegree = P.roots.prod := by
      rw [← hs_card]
      exact putnam_1968_a6_esymm_card_eq_prod P.roots
    have hsignsq : ((-1 : ℂ) ^ P.natDegree) ^ 2 = 1 := by
      rw [← pow_mul]
      have : (-1 : ℂ) ^ 2 = 1 := by norm_num
      rw [show P.natDegree * 2 = 2 * P.natDegree by omega, pow_mul, this, one_pow]
    let A : ℂ := (-1 : ℂ) ^ P.natDegree
    have hA_sq : A ^ 2 = 1 := hsignsq
    have hAprod_sq : (A * P.roots.prod) ^ 2 = 1 := by
      rcases hlead with hL | hL
      · rcases hc0 with hC | hC
        · have hAprod : A * P.roots.prod = 1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using hv0.symm
          rw [hAprod]; norm_num
        · have hAprod : A * P.roots.prod = -1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using hv0.symm
          rw [hAprod]; norm_num
      · rcases hc0 with hC | hC
        · have hAprod : A * P.roots.prod = -1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using (congrArg Neg.neg hv0).symm
          rw [hAprod]; norm_num
        · have hAprod : A * P.roots.prod = 1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using (congrArg Neg.neg hv0).symm
          rw [hAprod]; norm_num
    calc
      P.roots.prod ^ 2 = A ^ 2 * P.roots.prod ^ 2 := by rw [hA_sq]; ring
      _ = (A * P.roots.prod) ^ 2 := by ring
      _ = 1 := hAprod_sq
  have hsum_complex : (s.map fun z => z ^ 2).sum = (P.roots.esymm 1) ^ 2 - 2 * P.roots.esymm 2 := by
    rw [putnam_1968_a6_sum_sq_eq]
    have he1 : P.roots.esymm 1 = P.roots.sum := by
      simp [Multiset.esymm, Multiset.powersetCard_one]
    rw [he1]
  have hsum_le : (s.map (fun z => (z.re ^ 2 : ℝ))).sum ≤ 3 := by
    rcases he2pm with he2 | he2
    · have hcast : (((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ)) = (-1 : ℂ) := by
        calc
          ((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ) = (s.map fun z => z ^ 2).sum :=
            putnam_1968_a6_real_sq_sum s hs_real
          _ = (P.roots.esymm 1) ^ 2 - 2 * P.roots.esymm 2 := hsum_complex
          _ = -1 := by rw [he1sq, he2]; norm_num
      have hreal_sum : (s.map (fun z => (z.re ^ 2 : ℝ))).sum = (-1 : ℝ) :=
        Complex.ofReal_inj.mp (by simpa using hcast)
      linarith
    · have hcast : (((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ)) = (3 : ℂ) := by
        calc
          ((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ) = (s.map fun z => z ^ 2).sum :=
            putnam_1968_a6_real_sq_sum s hs_real
          _ = (P.roots.esymm 1) ^ 2 - 2 * P.roots.esymm 2 := hsum_complex
          _ = 3 := by rw [he1sq, he2]; norm_num
      have hreal_sum : (s.map (fun z => (z.re ^ 2 : ℝ))).sum = (3 : ℝ) :=
        Complex.ofReal_inj.mp (by simpa using hcast)
      linarith
  have hprod_real : (s.map (fun z => (z.re ^ 2 : ℝ))).prod = (1 : ℝ) := by
    have hcast : ((s.map (fun z => (z.re ^ 2 : ℝ))).prod : ℂ) = (1 : ℂ) := by
      calc
        ((s.map (fun z => (z.re ^ 2 : ℝ))).prod : ℂ) = (s.map fun z => z ^ 2).prod :=
          putnam_1968_a6_real_sq_prod s hs_real
        _ = s.prod ^ 2 := putnam_1968_a6_prod_sq_eq s
        _ = 1 := hprod_sq
    exact Complex.ofReal_inj.mp (by simpa using hcast)
  have hprod_type : (∏ x : s, ((x : ℂ).re ^ 2 : ℝ)) = 1 := by
    calc
      (∏ x : s, ((x : ℂ).re ^ 2 : ℝ)) = (s.map (fun z => (z.re ^ 2 : ℝ))).prod := by
        rw [← Multiset.map_univ s (fun z => (z.re ^ 2 : ℝ))]
        rfl
      _ = 1 := hprod_real
  have hsum_type : (∑ x : s, ((x : ℂ).re ^ 2 : ℝ)) ≤ 3 := by
    calc
      (∑ x : s, ((x : ℂ).re ^ 2 : ℝ)) = (s.map (fun z => (z.re ^ 2 : ℝ))).sum := by
        rw [← Multiset.map_univ s (fun z => (z.re ^ 2 : ℝ))]
        rfl
      _ ≤ 3 := hsum_le
  have hcard3 : Fintype.card s ≤ 3 :=
    putnam_1968_a6_card_le_three (fun x : s => ((x : ℂ).re ^ 2 : ℝ))
      (fun x => sq_nonneg _) hprod_type hsum_type
  have : P.natDegree ≤ 3 := by
    rw [← hs_card, ← Multiset.card_coe]
    exact hcard3
  exact hnot this

private lemma putnam_1968_a6_real_sq_sum_nonneg (s : Multiset ℂ) :
    0 ≤ (s.map (fun z => (z.re ^ 2 : ℝ))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp [add_nonneg (sq_nonneg a.re) ih]

private lemma putnam_1968_a6_esymm_two_eq_neg_one {P : ℂ[X]}
    (hdeg : 2 ≤ P.natDegree)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.roots.esymm 2 = (-1 : ℂ) := by
  let s : Multiset ℂ := P.roots
  have hs_real : ∀ z ∈ s, z.im = 0 := by
    intro z hz
    rcases hreal z (Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hz)) with ⟨r, hr⟩
    rw [← hr]
    simp
  have hlead := hcoeff P.natDegree (by constructor <;> omega)
  have hc1 := hcoeff (P.natDegree - 1) (by constructor <;> omega)
  have hc2 := hcoeff (P.natDegree - 2) (by constructor <;> omega)
  have hv1 : P.coeff (P.natDegree - 1) = P.leadingCoeff * (-1) ^ 1 * P.roots.esymm 1 := by
    have hv := Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := P.natDegree - 1) (by omega)
    simpa [show P.natDegree - (P.natDegree - 1) = 1 by omega] using hv
  have hv2 : P.coeff (P.natDegree - 2) = P.leadingCoeff * (-1) ^ 2 * P.roots.esymm 2 := by
    have hv := Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := P.natDegree - 2) (by omega)
    simpa [show P.natDegree - (P.natDegree - 2) = 2 by omega] using hv
  have he1pm : P.roots.esymm 1 = (1 : ℂ) ∨ P.roots.esymm 1 = (-1 : ℂ) := by
    rcases hlead with hL | hL
    · rcases hc1 with hC | hC
      · have hv : P.roots.esymm 1 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using (congrArg Neg.neg hv1).symm
        exact Or.inr hv
      · have hv : P.roots.esymm 1 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using (congrArg Neg.neg hv1).symm
        exact Or.inl hv
    · rcases hc1 with hC | hC
      · have hv : P.roots.esymm 1 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using hv1.symm
        exact Or.inl hv
      · have hv : P.roots.esymm 1 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using hv1.symm
        exact Or.inr hv
  have he1sq : (P.roots.esymm 1) ^ 2 = (1 : ℂ) := by
    rcases he1pm with h | h <;> simp [h]
  have he2pm : P.roots.esymm 2 = (1 : ℂ) ∨ P.roots.esymm 2 = (-1 : ℂ) := by
    rcases hlead with hL | hL
    · rcases hc2 with hC | hC
      · have hv : P.roots.esymm 2 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using hv2.symm
        exact Or.inl hv
      · have hv : P.roots.esymm 2 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using hv2.symm
        exact Or.inr hv
    · rcases hc2 with hC | hC
      · have hv : P.roots.esymm 2 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using (congrArg Neg.neg hv2).symm
        exact Or.inr hv
      · have hv : P.roots.esymm 2 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv2
          simpa using (congrArg Neg.neg hv2).symm
        exact Or.inl hv
  rcases he2pm with he2 | he2
  · exfalso
    have hsum_complex : (s.map fun z => z ^ 2).sum = (P.roots.esymm 1) ^ 2 - 2 * P.roots.esymm 2 := by
      rw [putnam_1968_a6_sum_sq_eq]
      have he1 : P.roots.esymm 1 = P.roots.sum := by
        simp [Multiset.esymm, Multiset.powersetCard_one]
      rw [he1]
    have hcast : (((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ)) = (-1 : ℂ) := by
      calc
        ((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ) = (s.map fun z => z ^ 2).sum :=
          putnam_1968_a6_real_sq_sum s hs_real
        _ = (P.roots.esymm 1) ^ 2 - 2 * P.roots.esymm 2 := hsum_complex
        _ = -1 := by rw [he1sq, he2]; norm_num
    have hreal_sum : (s.map (fun z => (z.re ^ 2 : ℝ))).sum = (-1 : ℝ) :=
      Complex.ofReal_inj.mp (by simpa using hcast)
    have hnonneg := putnam_1968_a6_real_sq_sum_nonneg s
    linarith
  · exact he2

private lemma putnam_1968_a6_roots_sq_eq_one_of_natDegree_three {P : ℂ[X]}
    (hn : P.natDegree = 3)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    ∀ z ∈ P.roots, z ^ 2 = (1 : ℂ) := by
  let s : Multiset ℂ := P.roots
  have hs_card : s.card = P.natDegree := by
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hs_card_three : s.card = 3 := by
    rw [hs_card, hn]
  have hs_real : ∀ z ∈ s, z.im = 0 := by
    intro z hz
    rcases hreal z (Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hz)) with ⟨r, hr⟩
    rw [← hr]
    simp
  have hlead := hcoeff P.natDegree (by constructor <;> omega)
  have hc1 := hcoeff (P.natDegree - 1) (by constructor <;> omega)
  have hc0 := hcoeff 0 (by constructor <;> omega)
  have hv1 : P.coeff (P.natDegree - 1) = P.leadingCoeff * (-1) ^ 1 * P.roots.esymm 1 := by
    have hv := Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := P.natDegree - 1) (by omega)
    simpa [show P.natDegree - (P.natDegree - 1) = 1 by omega] using hv
  have hv0 : P.coeff 0 = P.leadingCoeff * (-1) ^ P.natDegree * P.roots.esymm P.natDegree := by
    simpa using Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := 0) (Nat.zero_le _)
  have he1pm : P.roots.esymm 1 = (1 : ℂ) ∨ P.roots.esymm 1 = (-1 : ℂ) := by
    rcases hlead with hL | hL
    · rcases hc1 with hC | hC
      · have hv : P.roots.esymm 1 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using (congrArg Neg.neg hv1).symm
        exact Or.inr hv
      · have hv : P.roots.esymm 1 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using (congrArg Neg.neg hv1).symm
        exact Or.inl hv
    · rcases hc1 with hC | hC
      · have hv : P.roots.esymm 1 = 1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using hv1.symm
        exact Or.inl hv
      · have hv : P.roots.esymm 1 = -1 := by
          simp [Polynomial.leadingCoeff, hL, hC] at hv1
          simpa using hv1.symm
        exact Or.inr hv
  have he1sq : (P.roots.esymm 1) ^ 2 = (1 : ℂ) := by
    rcases he1pm with h | h <;> simp [h]
  have he2 : P.roots.esymm 2 = (-1 : ℂ) :=
    putnam_1968_a6_esymm_two_eq_neg_one (P := P) (by omega) hcoeff hreal
  have hprod_sq : P.roots.prod ^ 2 = (1 : ℂ) := by
    have hen : P.roots.esymm P.natDegree = P.roots.prod := by
      rw [← hs_card]
      exact putnam_1968_a6_esymm_card_eq_prod P.roots
    have hsignsq : ((-1 : ℂ) ^ P.natDegree) ^ 2 = 1 := by
      rw [← pow_mul]
      have : (-1 : ℂ) ^ 2 = 1 := by norm_num
      rw [show P.natDegree * 2 = 2 * P.natDegree by omega, pow_mul, this, one_pow]
    let A : ℂ := (-1 : ℂ) ^ P.natDegree
    have hA_sq : A ^ 2 = 1 := hsignsq
    have hAprod_sq : (A * P.roots.prod) ^ 2 = 1 := by
      rcases hlead with hL | hL
      · rcases hc0 with hC | hC
        · have hAprod : A * P.roots.prod = 1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using hv0.symm
          rw [hAprod]; norm_num
        · have hAprod : A * P.roots.prod = -1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using hv0.symm
          rw [hAprod]; norm_num
      · rcases hc0 with hC | hC
        · have hAprod : A * P.roots.prod = -1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using (congrArg Neg.neg hv0).symm
          rw [hAprod]; norm_num
        · have hAprod : A * P.roots.prod = 1 := by
            simp [Polynomial.leadingCoeff, hL, hC, hen] at hv0
            simpa using (congrArg Neg.neg hv0).symm
          rw [hAprod]; norm_num
    calc
      P.roots.prod ^ 2 = A ^ 2 * P.roots.prod ^ 2 := by rw [hA_sq]; ring
      _ = (A * P.roots.prod) ^ 2 := by ring
      _ = 1 := hAprod_sq
  have hsum_complex : (s.map fun z => z ^ 2).sum = (P.roots.esymm 1) ^ 2 - 2 * P.roots.esymm 2 := by
    rw [putnam_1968_a6_sum_sq_eq]
    have he1 : P.roots.esymm 1 = P.roots.sum := by
      simp [Multiset.esymm, Multiset.powersetCard_one]
    rw [he1]
  have hsum_real : (s.map (fun z => (z.re ^ 2 : ℝ))).sum = (3 : ℝ) := by
    have hcast : (((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ)) = (3 : ℂ) := by
      calc
        ((s.map (fun z => (z.re ^ 2 : ℝ))).sum : ℂ) = (s.map fun z => z ^ 2).sum :=
          putnam_1968_a6_real_sq_sum s hs_real
        _ = (P.roots.esymm 1) ^ 2 - 2 * P.roots.esymm 2 := hsum_complex
        _ = 3 := by rw [he1sq, he2]; norm_num
    exact Complex.ofReal_inj.mp (by simpa using hcast)
  have hprod_real : (s.map (fun z => (z.re ^ 2 : ℝ))).prod = (1 : ℝ) := by
    have hcast : ((s.map (fun z => (z.re ^ 2 : ℝ))).prod : ℂ) = (1 : ℂ) := by
      calc
        ((s.map (fun z => (z.re ^ 2 : ℝ))).prod : ℂ) = (s.map fun z => z ^ 2).prod :=
          putnam_1968_a6_real_sq_prod s hs_real
        _ = s.prod ^ 2 := putnam_1968_a6_prod_sq_eq s
        _ = 1 := hprod_sq
    exact Complex.ofReal_inj.mp (by simpa using hcast)
  have hprod_type : (∏ x : s, ((x : ℂ).re ^ 2 : ℝ)) = 1 := by
    calc
      (∏ x : s, ((x : ℂ).re ^ 2 : ℝ)) = (s.map (fun z => (z.re ^ 2 : ℝ))).prod := by
        rw [← Multiset.map_univ s (fun z => (z.re ^ 2 : ℝ))]
        rfl
      _ = 1 := hprod_real
  have hsum_type : (∑ x : s, ((x : ℂ).re ^ 2 : ℝ)) = 3 := by
    calc
      (∑ x : s, ((x : ℂ).re ^ 2 : ℝ)) = (s.map (fun z => (z.re ^ 2 : ℝ))).sum := by
        rw [← Multiset.map_univ s (fun z => (z.re ^ 2 : ℝ))]
        rfl
      _ = 3 := hsum_real
  have hcard_type : Fintype.card s = 3 := by
    simpa using hs_card_three
  have hall := putnam_1968_a6_all_eq_one_of_card_three hcard_type
    (fun x : s => ((x : ℂ).re ^ 2 : ℝ)) (fun x => sq_nonneg _) hprod_type hsum_type
  intro z hz
  have hzmem : z ∈ s := by simpa only [s] using hz
  have hzreal : z.im = 0 := hs_real z hzmem
  have hzsq : ((z.re ^ 2 : ℝ) : ℂ) = z ^ 2 := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, hzreal]
  calc
    z ^ 2 = ((z.re ^ 2 : ℝ) : ℂ) := hzsq.symm
    _ = 1 := by
      have hzcount : 0 < Multiset.count z s := Multiset.count_pos.mpr hzmem
      let hzsub : s := s.mkToType z ⟨0, hzcount⟩
      have hzone : z.re ^ 2 = (1 : ℝ) := by
        have hzone_sub := hall hzsub
        change hzsub.fst.re ^ 2 = (1 : ℝ) at hzone_sub
        dsimp [hzsub, Multiset.mkToType] at hzone_sub
        exact hzone_sub
      rw [hzone]
      norm_num

private lemma putnam_1968_a6_cubic_coeff_relations {P : ℂ[X]}
    (hn : P.natDegree = 3)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.coeff 1 = -P.coeff 3 ∧ P.coeff 0 = -P.coeff 2 := by
  have hs_card : P.roots.card = P.natDegree := by
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hs_card_three : P.roots.card = 3 := by
    rw [hs_card, hn]
  have hsq := putnam_1968_a6_roots_sq_eq_one_of_natDegree_three (P := P) hn hcoeff hreal
  have he2 : P.roots.esymm 2 = (-1 : ℂ) :=
    putnam_1968_a6_esymm_two_eq_neg_one (P := P) (by omega) hcoeff hreal
  have hv2 : P.coeff 1 = P.leadingCoeff * (-1) ^ 2 * P.roots.esymm 2 := by
    have hv := Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := 1) (by omega)
    simpa [hn] using hv
  have hcoeff1 : P.coeff 1 = -P.coeff 3 := by
    calc
      P.coeff 1 = P.leadingCoeff * (-1 : ℂ) := by
        simpa [he2] using hv2
      _ = -P.coeff 3 := by
        simp [Polynomial.leadingCoeff, hn]
  rcases Multiset.card_eq_three.mp hs_card_three with ⟨x, y, z, hxyz⟩
  have hx2 : x ^ 2 = (1 : ℂ) := hsq x (by rw [hxyz]; simp)
  have hy2 : y ^ 2 = (1 : ℂ) := hsq y (by rw [hxyz]; simp)
  have hz2 : z ^ 2 = (1 : ℂ) := hsq z (by rw [hxyz]; simp)
  have he2xyz : x * y + x * z + y * z = (-1 : ℂ) := by
    have h := he2
    rw [hxyz] at h
    have h' : x * z + (y * z + x * y) = (-1 : ℂ) := by
      simpa [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one] using h
    calc
      x * y + x * z + y * z = x * z + (y * z + x * y) := by ring
      _ = -1 := h'
  have he3neg1xyz : x * y * z = -(x + y + z) := by
    have hxpm : x = (1 : ℂ) ∨ x = -1 := sq_eq_one_iff.mp hx2
    have hypm : y = (1 : ℂ) ∨ y = -1 := sq_eq_one_iff.mp hy2
    have hzpm : z = (1 : ℂ) ∨ z = -1 := sq_eq_one_iff.mp hz2
    rcases hxpm with rfl | rfl
    · rcases hypm with rfl | rfl
      · rcases hzpm with rfl | rfl
        · norm_num at he2xyz
        · norm_num
      · rcases hzpm with rfl | rfl <;> norm_num
    · rcases hypm with rfl | rfl
      · rcases hzpm with rfl | rfl <;> norm_num
      · rcases hzpm with rfl | rfl
        · norm_num
        · norm_num at he2xyz
  have he1xyz : P.roots.esymm 1 = x + y + z := by
    rw [hxyz]
    simp [Multiset.esymm, Multiset.powersetCard_one]
    ring
  have he3xyz : P.roots.esymm 3 = x * y * z := by
    rw [hxyz]
    simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
    ring_nf
  have he3neg1 : P.roots.esymm 3 = -P.roots.esymm 1 := by
    rw [he3xyz, he1xyz, he3neg1xyz]
  have hv0 : P.coeff 0 = P.leadingCoeff * (-1) ^ P.natDegree * P.roots.esymm P.natDegree := by
    simpa using Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := 0) (Nat.zero_le _)
  have hv1 : P.coeff 2 = P.leadingCoeff * (-1) ^ 1 * P.roots.esymm 1 := by
    have hv := Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := 2) (by omega)
    simpa [hn] using hv
  have hcoeff0 : P.coeff 0 = -P.coeff 2 := by
    calc
      P.coeff 0 = -P.leadingCoeff * P.roots.esymm 3 := by
        have hv0' : P.coeff 0 = P.leadingCoeff * (-1 : ℂ) ^ 3 * P.roots.esymm 3 := by
          simpa [hn] using hv0
        calc
          P.coeff 0 = P.leadingCoeff * (-1 : ℂ) ^ 3 * P.roots.esymm 3 := hv0'
          _ = -P.leadingCoeff * P.roots.esymm 3 := by ring
      _ = P.leadingCoeff * P.roots.esymm 1 := by
        rw [he3neg1]
        ring
      _ = -P.coeff 2 := by
        rw [hv1]
        ring
  exact ⟨hcoeff1, hcoeff0⟩

private lemma putnam_1968_a6_quadratic_coeff_relation {P : ℂ[X]}
    (hn : P.natDegree = 2)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.coeff 0 = -P.coeff 2 := by
  have he2 : P.roots.esymm 2 = (-1 : ℂ) :=
    putnam_1968_a6_esymm_two_eq_neg_one (P := P) (by omega) hcoeff hreal
  have hv0 : P.coeff 0 = P.leadingCoeff * (-1) ^ P.natDegree * P.roots.esymm P.natDegree := by
    simpa using Polynomial.coeff_eq_esymm_roots_of_splits (p := P) (IsAlgClosed.splits P)
      (k := 0) (Nat.zero_le _)
  calc
    P.coeff 0 = P.leadingCoeff * P.roots.esymm 2 := by
      simpa [hn] using hv0
    _ = -P.coeff 2 := by
      simp [Polynomial.leadingCoeff, hn, he2]

private lemma putnam_1968_a6_eq_linear {P : ℂ[X]} (hn : P.natDegree = 1) :
    P = C (P.coeff 1) * X + C (P.coeff 0) := by
  rw [Polynomial.as_sum_range P]
  rw [hn]
  norm_num [Finset.sum_range_succ, Polynomial.monomial_zero_left,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

private lemma putnam_1968_a6_eq_quadratic {P : ℂ[X]} (hn : P.natDegree = 2) :
    P = C (P.coeff 2) * X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) := by
  rw [Polynomial.as_sum_range P]
  rw [hn]
  norm_num [Finset.sum_range_succ, Polynomial.monomial_zero_left,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

private lemma putnam_1968_a6_eq_cubic {P : ℂ[X]} (hn : P.natDegree = 3) :
    P = C (P.coeff 3) * X ^ 3 + C (P.coeff 2) * X ^ 2 + C (P.coeff 1) * X +
      C (P.coeff 0) := by
  rw [Polynomial.as_sum_range P]
  rw [hn]
  norm_num [Finset.sum_range_succ, Polynomial.monomial_zero_left,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

private def putnam_1968_a6_roots_real (P : ℂ[X]) : Prop :=
  ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z

private lemma putnam_1968_a6_roots_real_neg {P : ℂ[X]}
    (hP : putnam_1968_a6_roots_real P) : putnam_1968_a6_roots_real (-P) := by
  intro z hz
  exact hP z (by simpa using hz)

private lemma putnam_1968_a6_roots_real_X_sub_one :
    putnam_1968_a6_roots_real (X - 1 : ℂ[X]) := by
  intro z hz
  refine ⟨1, ?_⟩
  have h : z - 1 = 0 := by simpa using hz
  simpa using (sub_eq_zero.mp h).symm

private lemma putnam_1968_a6_roots_real_X_add_one :
    putnam_1968_a6_roots_real (X + 1 : ℂ[X]) := by
  intro z hz
  refine ⟨-1, ?_⟩
  have h : z + 1 = 0 := by simpa using hz
  simpa using (eq_neg_of_add_eq_zero_left h).symm

private lemma putnam_1968_a6_roots_real_quad_add :
    putnam_1968_a6_roots_real (X ^ 2 + X - 1 : ℂ[X]) := by
  intro z hz
  have hpoly : z ^ 2 + z - 1 = 0 := by simpa using hz
  have hsq : (2 * z + 1) ^ 2 = (5 : ℂ) := by
    calc
      (2 * z + 1) ^ 2 = 4 * (z ^ 2 + z - 1) + 5 := by ring
      _ = 5 := by rw [hpoly]; norm_num
  have hsqrt : ((Real.sqrt 5 : ℂ) ^ 2) = (5 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt]
    · norm_num
    · norm_num
  have heq : 2 * z + 1 = (Real.sqrt 5 : ℂ) ∨ 2 * z + 1 = -(Real.sqrt 5 : ℂ) := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hsqrt.symm)
  rcases heq with h | h
  · refine ⟨(Real.sqrt 5 - 1) / 2, ?_⟩
    have hz1 : z = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
      calc
        z = (2 * z + 1 - 1) / 2 := by ring
        _ = (((Real.sqrt 5 : ℂ) - 1) / 2) := by rw [h]
    rw [hz1]
    norm_num
  · refine ⟨(-Real.sqrt 5 - 1) / 2, ?_⟩
    have hz1 : z = (-(Real.sqrt 5 : ℂ) - 1) / 2 := by
      calc
        z = (2 * z + 1 - 1) / 2 := by ring
        _ = ((-(Real.sqrt 5 : ℂ) - 1) / 2) := by rw [h]
    rw [hz1]
    norm_num

private lemma putnam_1968_a6_roots_real_quad_sub :
    putnam_1968_a6_roots_real (X ^ 2 - X - 1 : ℂ[X]) := by
  intro z hz
  have hpoly : z ^ 2 - z - 1 = 0 := by simpa using hz
  have hsq : (2 * z - 1) ^ 2 = (5 : ℂ) := by
    calc
      (2 * z - 1) ^ 2 = 4 * (z ^ 2 - z - 1) + 5 := by ring
      _ = 5 := by rw [hpoly]; norm_num
  have hsqrt : ((Real.sqrt 5 : ℂ) ^ 2) = (5 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt]
    · norm_num
    · norm_num
  have heq : 2 * z - 1 = (Real.sqrt 5 : ℂ) ∨ 2 * z - 1 = -(Real.sqrt 5 : ℂ) := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hsqrt.symm)
  rcases heq with h | h
  · refine ⟨(Real.sqrt 5 + 1) / 2, ?_⟩
    have hz1 : z = ((Real.sqrt 5 : ℂ) + 1) / 2 := by
      calc
        z = (2 * z - 1 + 1) / 2 := by ring
        _ = (((Real.sqrt 5 : ℂ) + 1) / 2) := by rw [h]
    rw [hz1]
    norm_num
  · refine ⟨(-Real.sqrt 5 + 1) / 2, ?_⟩
    have hz1 : z = (-(Real.sqrt 5 : ℂ) + 1) / 2 := by
      calc
        z = (2 * z - 1 + 1) / 2 := by ring
        _ = ((-(Real.sqrt 5 : ℂ) + 1) / 2) := by rw [h]
    rw [hz1]
    norm_num

private lemma putnam_1968_a6_roots_real_cubic_add :
    putnam_1968_a6_roots_real (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) := by
  intro z hz
  have hpoly : z ^ 3 + z ^ 2 - z - 1 = 0 := by simpa using hz
  have hfac : (z + 1) ^ 2 * (z - 1) = 0 := by
    calc
      (z + 1) ^ 2 * (z - 1) = z ^ 3 + z ^ 2 - z - 1 := by ring
      _ = 0 := hpoly
  have hzcase : z + 1 = 0 ∨ z - 1 = 0 := by
    have hm := mul_eq_zero.mp hfac
    rcases hm with hsq | hm
    · exact Or.inl (sq_eq_zero_iff.mp hsq)
    · exact Or.inr hm
  rcases hzcase with h | h
  · refine ⟨-1, ?_⟩
    simpa using (eq_neg_of_add_eq_zero_left h).symm
  · refine ⟨1, ?_⟩
    simpa using (sub_eq_zero.mp h).symm

private lemma putnam_1968_a6_roots_real_cubic_sub :
    putnam_1968_a6_roots_real (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) := by
  intro z hz
  have hpoly : z ^ 3 - z ^ 2 - z + 1 = 0 := by simpa using hz
  have hfac : (z - 1) ^ 2 * (z + 1) = 0 := by
    calc
      (z - 1) ^ 2 * (z + 1) = z ^ 3 - z ^ 2 - z + 1 := by ring
      _ = 0 := hpoly
  have hzcase : z - 1 = 0 ∨ z + 1 = 0 := by
    have hm := mul_eq_zero.mp hfac
    rcases hm with hsq | hm
    · exact Or.inl (sq_eq_zero_iff.mp hsq)
    · exact Or.inr hm
  rcases hzcase with h | h
  · refine ⟨1, ?_⟩
    simpa using (sub_eq_zero.mp h).symm
  · refine ⟨-1, ?_⟩
    simpa using (eq_neg_of_add_eq_zero_left h).symm

private lemma putnam_1968_a6_candidate_mem {P : ℂ[X]} {n : ℕ}
    (hn : P.natDegree = n) (hnpos : 1 ≤ n)
    (hcoeff : ∀ k ∈ Set.Icc 0 n, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : putnam_1968_a6_roots_real P) :
    P ∈ {P : ℂ[X] | P.natDegree ≥ 1 ∧
      (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
      ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  refine ⟨?_, ?_, hreal⟩
  · rw [hn]
    exact hnpos
  · intro k hk
    rw [hn] at hk
    exact hcoeff k hk

private lemma putnam_1968_a6_mem_X_sub_one :
    (X - 1 : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_neg_X_sub_one :
    (-(X - 1) : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_X_add_one :
    (X + 1 : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_neg_X_add_one :
    (-(X + 1) : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_quad_add :
    (X ^ 2 + X - 1 : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_neg_quad_add :
    (-(X ^ 2 + X - 1) : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_quad_sub :
    (X ^ 2 - X - 1 : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_neg_quad_sub :
    (-(X ^ 2 - X - 1) : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_cubic_add :
    (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_neg_cubic_add :
    (-(X ^ 3 + X ^ 2 - X - 1) : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_cubic_sub :
    (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

private lemma putnam_1968_a6_mem_neg_cubic_sub :
    (-(X ^ 3 - X ^ 2 - X + 1) : ℂ[X]) ∈ (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X]) := by
  simp

-- {X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}
/--
Find all polynomials of the form $\sum_{0}^{n} a_{i} x^{n-i}$ with $n \ge 1$ and $a_i = \pm 1$ for all $0 \le i \le n$ whose roots are all real.
-/
theorem putnam_1968_a6
: {P : ℂ[X] | P.natDegree ≥ 1 ∧ (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} = (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1), X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X] ) := by
  ext P
  constructor
  · intro hP
    rcases hP with ⟨hdeg, hcoeff, hreal⟩
    have hle : P.natDegree ≤ 3 := putnam_1968_a6_degree_le_three hcoeff hreal
    have hcases : P.natDegree = 1 ∨ P.natDegree = 2 ∨ P.natDegree = 3 := by omega
    rcases hcases with hn | hn | hn
    · have hc0 := hcoeff 0 (by rw [hn]; constructor <;> norm_num)
      have hc1 := hcoeff 1 (by rw [hn]; constructor <;> norm_num)
      rcases hc1 with hc1 | hc1
      · rcases hc0 with hc0 | hc0
        · have hPeq : P = X + 1 := by
            calc
              P = C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_linear hn
              _ = X + 1 := by rw [hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_X_add_one
        · have hPeq : P = X - 1 := by
            calc
              P = C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_linear hn
              _ = X - 1 := by rw [hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_X_sub_one
      · rcases hc0 with hc0 | hc0
        · have hPeq : P = -(X - 1) := by
            calc
              P = C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_linear hn
              _ = -(X - 1) := by rw [hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_neg_X_sub_one
        · have hPeq : P = -(X + 1) := by
            calc
              P = C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_linear hn
              _ = -(X + 1) := by rw [hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_neg_X_add_one
    · have hrel := putnam_1968_a6_quadratic_coeff_relation hn hcoeff hreal
      have hc1 := hcoeff 1 (by rw [hn]; constructor <;> norm_num)
      have hc2 := hcoeff 2 (by rw [hn]; constructor <;> norm_num)
      rcases hc2 with hc2 | hc2
      · have hc0 : P.coeff 0 = (-1 : ℂ) := by rw [hrel, hc2] <;> norm_num
        rcases hc1 with hc1 | hc1
        · have hPeq : P = X ^ 2 + X - 1 := by
            calc
              P = C (P.coeff 2) * X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_quadratic hn
              _ = X ^ 2 + X - 1 := by rw [hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_quad_add
        · have hPeq : P = X ^ 2 - X - 1 := by
            calc
              P = C (P.coeff 2) * X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_quadratic hn
              _ = X ^ 2 - X - 1 := by rw [hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_quad_sub
      · have hc0 : P.coeff 0 = (1 : ℂ) := by rw [hrel, hc2] <;> norm_num
        rcases hc1 with hc1 | hc1
        · have hPeq : P = -(X ^ 2 - X - 1) := by
            calc
              P = C (P.coeff 2) * X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_quadratic hn
              _ = -(X ^ 2 - X - 1) := by rw [hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_neg_quad_sub
        · have hPeq : P = -(X ^ 2 + X - 1) := by
            calc
              P = C (P.coeff 2) * X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_quadratic hn
              _ = -(X ^ 2 + X - 1) := by rw [hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_neg_quad_add
    · have hrels := putnam_1968_a6_cubic_coeff_relations hn hcoeff hreal
      have hc2 := hcoeff 2 (by rw [hn]; constructor <;> norm_num)
      have hc3 := hcoeff 3 (by rw [hn]; constructor <;> norm_num)
      rcases hc3 with hc3 | hc3
      · have hc1 : P.coeff 1 = (-1 : ℂ) := by rw [hrels.1, hc3] <;> norm_num
        rcases hc2 with hc2 | hc2
        · have hc0 : P.coeff 0 = (-1 : ℂ) := by rw [hrels.2, hc2] <;> norm_num
          have hPeq : P = X ^ 3 + X ^ 2 - X - 1 := by
            calc
              P = C (P.coeff 3) * X ^ 3 + C (P.coeff 2) * X ^ 2 +
                    C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_cubic hn
              _ = X ^ 3 + X ^ 2 - X - 1 := by
                rw [hc3, hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_cubic_add
        · have hc0 : P.coeff 0 = (1 : ℂ) := by rw [hrels.2, hc2] <;> norm_num
          have hPeq : P = X ^ 3 - X ^ 2 - X + 1 := by
            calc
              P = C (P.coeff 3) * X ^ 3 + C (P.coeff 2) * X ^ 2 +
                    C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_cubic hn
              _ = X ^ 3 - X ^ 2 - X + 1 := by
                rw [hc3, hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_cubic_sub
      · have hc1 : P.coeff 1 = (1 : ℂ) := by rw [hrels.1, hc3] <;> norm_num
        rcases hc2 with hc2 | hc2
        · have hc0 : P.coeff 0 = (-1 : ℂ) := by rw [hrels.2, hc2] <;> norm_num
          have hPeq : P = -(X ^ 3 - X ^ 2 - X + 1) := by
            calc
              P = C (P.coeff 3) * X ^ 3 + C (P.coeff 2) * X ^ 2 +
                    C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_cubic hn
              _ = -(X ^ 3 - X ^ 2 - X + 1) := by
                rw [hc3, hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_neg_cubic_sub
        · have hc0 : P.coeff 0 = (1 : ℂ) := by rw [hrels.2, hc2] <;> norm_num
          have hPeq : P = -(X ^ 3 + X ^ 2 - X - 1) := by
            calc
              P = C (P.coeff 3) * X ^ 3 + C (P.coeff 2) * X ^ 2 +
                    C (P.coeff 1) * X + C (P.coeff 0) :=
                putnam_1968_a6_eq_cubic hn
              _ = -(X ^ 3 + X ^ 2 - X - 1) := by
                rw [hc3, hc2, hc1, hc0]; norm_num <;> ring
          rw [hPeq]
          exact putnam_1968_a6_mem_neg_cubic_add
  · intro hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply putnam_1968_a6_candidate_mem (n := 1)
      · compute_degree!
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · exact putnam_1968_a6_roots_real_X_sub_one
    · apply putnam_1968_a6_candidate_mem (n := 1)
      · compute_degree! <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · exact putnam_1968_a6_roots_real_neg putnam_1968_a6_roots_real_X_sub_one
    · apply putnam_1968_a6_candidate_mem (n := 1)
      · compute_degree!
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · exact putnam_1968_a6_roots_real_X_add_one
    · apply putnam_1968_a6_candidate_mem (n := 1)
      · compute_degree! <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · exact putnam_1968_a6_roots_real_neg putnam_1968_a6_roots_real_X_add_one
    · apply putnam_1968_a6_candidate_mem (n := 2)
      · compute_degree!
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_quad_add
    · apply putnam_1968_a6_candidate_mem (n := 2)
      · compute_degree! <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_neg putnam_1968_a6_roots_real_quad_add
    · apply putnam_1968_a6_candidate_mem (n := 2)
      · compute_degree!
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_quad_sub
    · apply putnam_1968_a6_candidate_mem (n := 2)
      · compute_degree! <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_neg putnam_1968_a6_roots_real_quad_sub
    · apply putnam_1968_a6_candidate_mem (n := 3)
      · compute_degree!
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_cubic_add
    · apply putnam_1968_a6_candidate_mem (n := 3)
      · compute_degree! <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_neg putnam_1968_a6_roots_real_cubic_add
    · apply putnam_1968_a6_candidate_mem (n := 3)
      · compute_degree!
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_cubic_sub
    · apply putnam_1968_a6_candidate_mem (n := 3)
      · compute_degree! <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
      · norm_num
      · intro k hk
        norm_num [Set.mem_Icc] at hk
        interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]
      · exact putnam_1968_a6_roots_real_neg putnam_1968_a6_roots_real_cubic_sub
