import Mathlib

open Finset Polynomial

private abbrev Good (P : ℂ[X]) : Prop :=
  P.natDegree ≥ 1 ∧
    (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
    ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z

private noncomputable abbrev answerFinset : Finset ℂ[X] :=
  {X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1),
    X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1,
    -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}

private noncomputable abbrev answerSet : Set ℂ[X] :=
  (({X - 1, -(X - 1), X + 1, -(X + 1), X^2 + X - 1, -(X^2 + X - 1),
    X^2 - X - 1, -(X^2 - X - 1), X^3 + X^2 - X - 1,
    -(X^3 + X^2 - X - 1), X^3 - X^2 - X + 1, -(X^3 - X^2 - X + 1)}) : Set ℂ[X])

private lemma mem_answer_X_sub_one : (X - 1 : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_neg_X_sub_one : (-(X - 1) : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_X_add_one : (X + 1 : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_neg_X_add_one : (-(X + 1) : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_X_sq_add_X_sub_one : (X ^ 2 + X - 1 : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_neg_X_sq_add_X_sub_one :
    (-(X ^ 2 + X - 1) : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_X_sq_sub_X_sub_one : (X ^ 2 - X - 1 : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_neg_X_sq_sub_X_sub_one :
    (-(X ^ 2 - X - 1) : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_cubic_add : (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_neg_cubic_add : (-(X ^ 3 + X ^ 2 - X - 1) : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_cubic_sub : (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answer_neg_cubic_sub : (-(X ^ 3 - X ^ 2 - X + 1) : ℂ[X]) ∈ answerFinset := by
  simp [answerFinset]

private lemma mem_answerSet_X_sub_one : (X - 1 : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_neg_X_sub_one : (-(X - 1) : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_X_add_one : (X + 1 : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_neg_X_add_one : (-(X + 1) : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_X_sq_add_X_sub_one : (X ^ 2 + X - 1 : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_neg_X_sq_add_X_sub_one :
    (-(X ^ 2 + X - 1) : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_X_sq_sub_X_sub_one : (X ^ 2 - X - 1 : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_neg_X_sq_sub_X_sub_one :
    (-(X ^ 2 - X - 1) : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_cubic_add : (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_neg_cubic_add : (-(X ^ 3 + X ^ 2 - X - 1) : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_cubic_sub : (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

private lemma mem_answerSet_neg_cubic_sub : (-(X ^ 3 - X ^ 2 - X + 1) : ℂ[X]) ∈ answerSet := by
  simp [answerSet]

namespace Multiset

private lemma esymm_cons_two [CommRing R] (a : R) (s : Multiset R) :
    (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
  rw [Multiset.esymm, Multiset.powersetCard_cons]
  simp [Multiset.esymm, Multiset.powersetCard_one, add_comm]
  simpa using (Multiset.sum_map_mul_left (s := s) (a := a) (f := fun x : R => x))

private lemma sum_map_sq_eq_sum_sq_sub_two_esymm_two [CommRing R] (s : Multiset R) :
    (s.map (fun x => x ^ 2)).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | cons a s ih =>
      rw [esymm_cons_two, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, ih]
      ring

end Multiset

private lemma neg_one_pow_sq (n : ℕ) : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul]
  have : n * 2 = 2 * n := by omega
  rw [this, pow_mul]
  norm_num

private lemma roots_sum_sq_eq (P : ℂ[X]) (hmonic : P.Monic) (hdeg : 2 ≤ P.natDegree) :
    (P.roots.map (fun z => z ^ 2)).sum =
      P.coeff (P.natDegree - 1) ^ 2 - 2 * P.coeff (P.natDegree - 2) := by
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = P.natDegree := hsplit.natDegree_eq_card_roots.symm
  have hpos : 0 < P.natDegree := lt_of_lt_of_le (by norm_num) hdeg
  have hsum : P.roots.sum = -P.coeff (P.natDegree - 1) := by
    have hnext := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hmonic
    rw [Polynomial.nextCoeff_of_natDegree_pos hpos] at hnext
    have hneg := congrArg Neg.neg hnext
    simpa [eq_comm] using hneg
  have hsub2 : P.natDegree - (P.natDegree - 2) = 2 := by omega
  have he2coeff := Polynomial.coeff_eq_esymm_roots_of_card (p := P) hcard
      (k := P.natDegree - 2) (by omega)
  have he2 : P.roots.esymm 2 = P.coeff (P.natDegree - 2) := by
    rw [he2coeff, hmonic, hsub2]
    norm_num
  rw [Multiset.sum_map_sq_eq_sum_sq_sub_two_esymm_two, hsum, he2]
  ring

private lemma roots_re_sq_sum_eq (P : ℂ[X]) (hmonic : P.Monic)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    (∑ x : P.roots, ((x : ℂ).re) ^ 2) = ((P.roots.map (fun z => z ^ 2)).sum).re := by
  have him (x : P.roots) : (x : ℂ).im = 0 := by
    have hxroot : P.eval (x : ℂ) = 0 := by
      exact (Polynomial.mem_roots hmonic.ne_zero).mp (Multiset.coe_mem (x := x))
    rcases hreal (x : ℂ) hxroot with ⟨r, hr⟩
    rw [← hr]
    simp
  have hcomplex : (∑ x : P.roots, ((x : ℂ) ^ 2)) = (P.roots.map (fun z => z ^ 2)).sum := by
    rw [Finset.sum_eq_multiset_sum]
    exact congr_arg Multiset.sum (Multiset.map_univ P.roots (fun z => z ^ 2))
  rw [← hcomplex]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [pow_two]
  simp [Complex.mul_re, him x, sq]

private lemma roots_re_sq_prod_eq_one (P : ℂ[X]) (hmonic : P.Monic)
    (hcoeff0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    (∏ x : P.roots, ((x : ℂ).re) ^ 2) = 1 := by
  have him (x : P.roots) : (x : ℂ).im = 0 := by
    have hxroot : P.eval (x : ℂ) = 0 := by
      exact (Polynomial.mem_roots hmonic.ne_zero).mp (Multiset.coe_mem (x := x))
    rcases hreal (x : ℂ) hxroot with ⟨r, hr⟩
    rw [← hr]
    simp
  have hprod_roots_sq : P.roots.prod ^ 2 = 1 := by
    have hsplit : P.Splits := IsAlgClosed.splits P
    have hconst := hsplit.coeff_zero_eq_prod_roots_of_monic hmonic
    rcases hcoeff0 with h0 | h0
    · rw [h0] at hconst
      have hsq := congrArg (fun z : ℂ => z ^ 2) hconst
      simpa [mul_pow, neg_one_pow_sq] using hsq.symm
    · rw [h0] at hconst
      have hsq := congrArg (fun z : ℂ => z ^ 2) hconst
      simpa [mul_pow, neg_one_pow_sq] using hsq.symm
  apply Complex.ofReal_injective
  calc
    ((∏ x : P.roots, ((x : ℂ).re) ^ 2 : ℝ) : ℂ)
        = ∏ x : P.roots, ((x : ℂ) ^ 2) := by
          rw [Complex.ofReal_prod]
          apply Finset.prod_congr rfl
          intro x hx
          apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, him x]
    _ = (P.roots.map (fun z => z ^ 2)).prod := by
          rw [Finset.prod_eq_multiset_prod]
          exact congr_arg Multiset.prod (Multiset.map_univ P.roots (fun z => z ^ 2))
    _ = P.roots.prod ^ 2 := by
          simpa using (Multiset.prod_map_pow (m := P.roots) (f := fun z : ℂ => z) (n := 2))
    _ = (1 : ℂ) := hprod_roots_sq
    _ = ((1 : ℝ) : ℂ) := by norm_num

private lemma card_le_sum_of_prod_eq_one {ι : Type*} [Fintype ι] (y : ι → ℝ)
    (hcardpos : 0 < Fintype.card ι) (hy : ∀ i, 0 ≤ y i)
    (hprod : ∏ i, y i = 1) :
    (Fintype.card ι : ℝ) ≤ ∑ i, y i := by
  have hamgm := Real.geom_mean_le_arith_mean (s := (Finset.univ : Finset ι))
      (w := fun _ : ι => (1 : ℝ)) (z := y)
      (by intro i hi; norm_num)
      (by simpa using (show (0 : ℝ) < (Fintype.card ι : ℝ) by exact_mod_cast hcardpos))
      (by intro i hi; exact hy i)
  have h1 : (1 : ℝ) ≤ (∑ i, y i) / (Fintype.card ι : ℝ) := by
    simpa [hprod] using hamgm
  have hcardposR : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcardpos
  rwa [le_div_iff₀ hcardposR, one_mul] at h1

private lemma monic_natDegree_le_three (P : ℂ[X]) (hdeg1 : 1 ≤ P.natDegree) (hmonic : P.Monic)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.natDegree ≤ 3 := by
  by_cases hdeg2 : 2 ≤ P.natDegree
  · let S : ℝ := ∑ x : P.roots, ((x : ℂ).re) ^ 2
    have hcoeff0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1 := hcoeff 0 (by simp)
    have hcoeff1 : P.coeff (P.natDegree - 1) = 1 ∨ P.coeff (P.natDegree - 1) = -1 :=
      hcoeff (P.natDegree - 1) (by constructor <;> omega)
    have hcoeff2 : P.coeff (P.natDegree - 2) = 1 ∨ P.coeff (P.natDegree - 2) = -1 :=
      hcoeff (P.natDegree - 2) (by constructor <;> omega)
    have hSle : S ≤ 3 := by
      have hS : S = (P.coeff (P.natDegree - 1) ^ 2 - 2 * P.coeff (P.natDegree - 2)).re := by
        change (∑ x : P.roots, ((x : ℂ).re) ^ 2) = _
        rw [roots_re_sq_sum_eq P hmonic hreal, roots_sum_sq_eq P hmonic hdeg2]
      rw [hS]
      rcases hcoeff1 with h1 | h1 <;> rcases hcoeff2 with h2 | h2 <;>
        simp [h1, h2] <;> norm_num
    have hprod : (∏ x : P.roots, ((x : ℂ).re) ^ 2) = 1 :=
      roots_re_sq_prod_eq_one P hmonic hcoeff0 hreal
    have hcardpos : 0 < Fintype.card P.roots := by
      rw [Multiset.card_coe, ← (IsAlgClosed.splits P).natDegree_eq_card_roots]
      exact hdeg1
    have hcard_le : (Fintype.card P.roots : ℝ) ≤ S :=
      card_le_sum_of_prod_eq_one (fun x : P.roots => ((x : ℂ).re) ^ 2) hcardpos
        (fun x => sq_nonneg _) hprod
    have hcard_eq : Fintype.card P.roots = P.natDegree := by
      rw [Multiset.card_coe, ← (IsAlgClosed.splits P).natDegree_eq_card_roots]
    have hnreal : (P.natDegree : ℝ) ≤ 3 := by
      rw [← hcard_eq]
      exact hcard_le.trans hSle
    exact_mod_cast hnreal
  · omega

private lemma prod_mul_sum_eq_esymm_two_of_card_three_of_sq_one {s : Multiset ℂ}
    (hcard : s.card = 3) (hsq : ∀ z ∈ s, z ^ 2 = 1) :
    s.prod * s.sum = s.esymm 2 := by
  rcases Multiset.card_eq_three.mp hcard with ⟨x, y, z, rfl⟩
  have hx : x ^ 2 = 1 := hsq x (by simp)
  have hy : y ^ 2 = 1 := hsq y (by simp)
  have hz : z ^ 2 = 1 := hsq z (by simp)
  simp [Multiset.esymm, Multiset.powersetCard_one]
  calc
    x * (y * z) * (x + (y + z)) = x ^ 2 * y * z + x * y ^ 2 * z + x * y * z ^ 2 := by ring
    _ = x * z + (y * z + x * y) := by rw [hx, hy, hz]; ring

private lemma roots_re_sq_eq_one_of_cubic (P : ℂ[X]) (hn : P.natDegree = 3) (hmonic : P.Monic)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    ∀ x : P.roots, ((x : ℂ).re) ^ 2 = 1 := by
  let S : ℝ := ∑ x : P.roots, ((x : ℂ).re) ^ 2
  have hcoeff0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1 := hcoeff 0 (by simp)
  have hcoeff1 : P.coeff (P.natDegree - 1) = 1 ∨ P.coeff (P.natDegree - 1) = -1 :=
    hcoeff (P.natDegree - 1) (by constructor <;> omega)
  have hcoeff2 : P.coeff (P.natDegree - 2) = 1 ∨ P.coeff (P.natDegree - 2) = -1 :=
    hcoeff (P.natDegree - 2) (by constructor <;> omega)
  have hSle : S ≤ 3 := by
    have hS : S = (P.coeff (P.natDegree - 1) ^ 2 - 2 * P.coeff (P.natDegree - 2)).re := by
      change (∑ x : P.roots, ((x : ℂ).re) ^ 2) = _
      rw [roots_re_sq_sum_eq P hmonic hreal, roots_sum_sq_eq P hmonic (by rw [hn]; norm_num)]
    rw [hS]
    rcases hcoeff1 with h1 | h1 <;> rcases hcoeff2 with h2 | h2 <;>
      simp [h1, h2] <;> norm_num
  have hprod : (∏ x : P.roots, ((x : ℂ).re) ^ 2) = 1 :=
    roots_re_sq_prod_eq_one P hmonic hcoeff0 hreal
  have hcardpos : 0 < Fintype.card P.roots := by
    rw [Multiset.card_coe, ← (IsAlgClosed.splits P).natDegree_eq_card_roots, hn]
    norm_num
  have hcard_le : (Fintype.card P.roots : ℝ) ≤ S :=
    card_le_sum_of_prod_eq_one (fun x : P.roots => ((x : ℂ).re) ^ 2) hcardpos
      (fun x => sq_nonneg _) hprod
  have hcard : Fintype.card P.roots = 3 := by
    rw [Multiset.card_coe, ← (IsAlgClosed.splits P).natDegree_eq_card_roots, hn]
  have hSge : (3 : ℝ) ≤ S := by
    simpa [hcard] using hcard_le
  have hS : S = 3 := le_antisymm hSle hSge
  let y : P.roots → ℝ := fun x => ((x : ℂ).re) ^ 2
  have hy : ∀ x : P.roots, 0 ≤ y x := fun x => sq_nonneg _
  have heqgm : (∏ x : P.roots, y x ^ ((1 : ℝ) / 3)) =
      ∑ x : P.roots, ((1 : ℝ) / 3) * y x := by
    have hleft : (∏ x : P.roots, y x ^ ((1 : ℝ) / 3)) = 1 := by
      rw [Real.finset_prod_rpow]
      · rw [hprod]
        norm_num
      · intro x hx
        exact hy x
    have hright : (∑ x : P.roots, ((1 : ℝ) / 3) * y x) = 1 := by
      rw [← Finset.mul_sum]
      change ((1 : ℝ) / 3) * S = 1
      rw [hS]
      norm_num
    rw [hleft, hright]
  have hall := (Real.geom_mean_eq_arith_mean_weighted_iff' (s := (Finset.univ : Finset P.roots))
      (w := fun _ : P.roots => (1 : ℝ) / 3) (z := y)
      (by intro i hi; norm_num)
      (by rw [Finset.sum_const, Finset.card_univ, hcard]; norm_num)
      (by intro i hi; exact hy i)).mp heqgm
  intro x
  have hx := hall x (by simp)
  dsimp [y] at hx ⊢
  rw [hx]
  rw [← Finset.mul_sum]
  change ((1 : ℝ) / 3) * S = 1
  rw [hS]
  norm_num

private lemma cubic_coeff1_eq_neg_one (P : ℂ[X]) (hn : P.natDegree = 3) (hmonic : P.Monic)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z)
    (hall : ∀ x : P.roots, ((x : ℂ).re) ^ 2 = 1) :
    P.coeff 1 = -1 := by
  have hcoeff2 : P.coeff 2 = 1 ∨ P.coeff 2 = -1 :=
    hcoeff 2 (by rw [hn]; norm_num [Set.mem_Icc])
  have hS : (∑ x : P.roots, ((x : ℂ).re) ^ 2) = 3 := by
    calc
      (∑ x : P.roots, ((x : ℂ).re) ^ 2) = ∑ x : P.roots, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hall x]
      _ = (Fintype.card P.roots : ℝ) := by simp
      _ = 3 := by
        rw [Multiset.card_coe, ← (IsAlgClosed.splits P).natDegree_eq_card_roots, hn]
        norm_num
  have hSexpr : (3 : ℝ) = (P.coeff 2 ^ 2 - 2 * P.coeff 1).re := by
    rw [← hS, roots_re_sq_sum_eq P hmonic hreal]
    have hsq := roots_sum_sq_eq P hmonic (by rw [hn]; norm_num)
    simpa [hn] using congrArg Complex.re hsq
  have hcoeff1 : P.coeff 1 = 1 ∨ P.coeff 1 = -1 :=
    hcoeff 1 (by rw [hn]; norm_num [Set.mem_Icc])
  rcases hcoeff2 with h2 | h2 <;> rcases hcoeff1 with h1 | h1
  · norm_num [h1, h2] at hSexpr
  · exact h1
  · norm_num [h1, h2] at hSexpr
  · exact h1

private lemma cubic_coeff0_eq_neg_coeff2 (P : ℂ[X]) (hn : P.natDegree = 3) (hmonic : P.Monic)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z)
    (hall : ∀ x : P.roots, ((x : ℂ).re) ^ 2 = 1) :
    P.coeff 0 = -P.coeff 2 := by
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = 3 := by
    rw [← hn]
    exact hsplit.natDegree_eq_card_roots.symm
  have hcoeff2 : P.coeff 2 = 1 ∨ P.coeff 2 = -1 :=
    hcoeff 2 (by rw [hn]; norm_num [Set.mem_Icc])
  have hcoeff1val : P.coeff 1 = -1 :=
    cubic_coeff1_eq_neg_one P hn hmonic hcoeff hreal hall
  have hsumCoeff : P.roots.sum = -P.coeff 2 := by
    have hnext := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hmonic
    have hpos : 0 < P.natDegree := by rw [hn]; norm_num
    rw [Polynomial.nextCoeff_of_natDegree_pos hpos, hn] at hnext
    have hneg := congrArg Neg.neg hnext
    simpa [eq_comm] using hneg
  have he2 : P.roots.esymm 2 = -1 := by
    have hcard' : P.roots.card = P.natDegree := hsplit.natDegree_eq_card_roots.symm
    have hv := Polynomial.coeff_eq_esymm_roots_of_card (p := P) hcard' (k := 1)
      (by rw [hn]; norm_num)
    rw [hn, hmonic] at hv
    norm_num at hv
    simpa [hcoeff1val] using hv.symm
  have hroot_sq : ∀ z ∈ P.roots, z ^ 2 = 1 := by
    intro z hzmem
    have hzroot : P.eval z = 0 := (Polynomial.mem_roots hmonic.ne_zero).mp hzmem
    rcases hreal z hzroot with ⟨r, hr⟩
    have hcount : 0 < P.roots.count z := Multiset.count_pos.mpr hzmem
    let x : P.roots := ⟨z, ⟨0, hcount⟩⟩
    have hre : z.re ^ 2 = 1 := by simpa [x] using hall x
    have him : z.im = 0 := by rw [← hr]; simp
    apply Complex.ext
    · rw [pow_two]
      simp [Complex.mul_re, him]
      simpa [sq] using hre
    · simp [pow_two, Complex.mul_im, him]
  have hprod_sum : P.roots.prod * P.roots.sum = -1 := by
    rw [prod_mul_sum_eq_esymm_two_of_card_three_of_sq_one hcard hroot_sq, he2]
  have hsum_sq : P.roots.sum ^ 2 = 1 := by
    rw [hsumCoeff]
    rcases hcoeff2 with h2 | h2 <;> simp [h2]
  have hprod_eq : P.roots.prod = -P.roots.sum := by
    calc
      P.roots.prod = P.roots.prod * 1 := by ring
      _ = P.roots.prod * (P.roots.sum ^ 2) := by rw [hsum_sq]
      _ = (P.roots.prod * P.roots.sum) * P.roots.sum := by ring
      _ = (-1) * P.roots.sum := by rw [hprod_sum]
      _ = -P.roots.sum := by ring
  have hconst := hsplit.coeff_zero_eq_prod_roots_of_monic hmonic
  rw [hn] at hconst
  norm_num at hconst
  rw [hconst, hprod_eq, hsumCoeff]
  ring

private lemma roots_real_X_sq_add_X_sub_one :
    ∀ z : ℂ, (X ^ 2 + X - 1 : ℂ[X]).eval z = 0 → ∃ r : ℝ, r = z := by
  intro z hz
  have hq : (1 : ℂ) * (z * z) + (1 : ℂ) * z + (-1 : ℂ) = 0 := by
    simpa [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, pow_two] using hz
  have hdisc : discrim (1 : ℂ) (1 : ℂ) (-1 : ℂ) =
      ((Real.sqrt 5 : ℝ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
    rw [discrim]
    norm_num
    rw [← Complex.ofReal_mul]
    norm_num [sq, Real.sq_sqrt]
  have hz' := (quadratic_eq_zero_iff (a := (1 : ℂ)) (b := (1 : ℂ)) (c := (-1 : ℂ))
    one_ne_zero hdisc z).mp hq
  rcases hz' with hz' | hz'
  · refine ⟨(-1 + Real.sqrt 5) / 2, ?_⟩
    rw [hz']
    norm_num
  · refine ⟨(-1 - Real.sqrt 5) / 2, ?_⟩
    rw [hz']
    norm_num

private lemma roots_real_X_sq_sub_X_sub_one :
    ∀ z : ℂ, (X ^ 2 - X - 1 : ℂ[X]).eval z = 0 → ∃ r : ℝ, r = z := by
  intro z hz
  have hq : (1 : ℂ) * (z * z) + (-1 : ℂ) * z + (-1 : ℂ) = 0 := by
    simpa [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, pow_two] using hz
  have hdisc : discrim (1 : ℂ) (-1 : ℂ) (-1 : ℂ) =
      ((Real.sqrt 5 : ℝ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
    rw [discrim]
    norm_num
    rw [← Complex.ofReal_mul]
    norm_num [sq, Real.sq_sqrt]
  have hz' := (quadratic_eq_zero_iff (a := (1 : ℂ)) (b := (-1 : ℂ)) (c := (-1 : ℂ))
    one_ne_zero hdisc z).mp hq
  rcases hz' with hz' | hz'
  · refine ⟨(1 + Real.sqrt 5) / 2, ?_⟩
    rw [hz']
    norm_num
  · refine ⟨(1 - Real.sqrt 5) / 2, ?_⟩
    rw [hz']
    norm_num

private lemma roots_real_cubic_add :
    ∀ z : ℂ, (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]).eval z = 0 → ∃ r : ℝ, r = z := by
  intro z hz
  have hpoly : z ^ 3 + z ^ 2 - z - 1 = 0 := by
    simpa [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C] using hz
  have hfactor : (z + 1) ^ 2 * (z - 1) = 0 := by
    calc
      (z + 1) ^ 2 * (z - 1) = z ^ 3 + z ^ 2 - z - 1 := by ring
      _ = 0 := hpoly
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · have hzadd : z + 1 = 0 := eq_zero_of_pow_eq_zero hleft
    refine ⟨-1, ?_⟩
    have hz' : z = -1 := by
      rw [← sub_eq_zero]
      simpa [sub_eq_add_neg] using hzadd
    rw [hz']
    norm_num
  · refine ⟨1, ?_⟩
    have hz' : z = 1 := sub_eq_zero.mp hright
    rw [hz']
    norm_num

private lemma roots_real_cubic_sub :
    ∀ z : ℂ, (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]).eval z = 0 → ∃ r : ℝ, r = z := by
  intro z hz
  have hpoly : z ^ 3 - z ^ 2 - z + 1 = 0 := by
    simpa [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C] using hz
  have hfactor : (z - 1) ^ 2 * (z + 1) = 0 := by
    calc
      (z - 1) ^ 2 * (z + 1) = z ^ 3 - z ^ 2 - z + 1 := by ring
      _ = 0 := hpoly
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · refine ⟨1, ?_⟩
    have hzsub : z - 1 = 0 := eq_zero_of_pow_eq_zero hleft
    have hz' : z = 1 := sub_eq_zero.mp hzsub
    rw [hz']
    norm_num
  · refine ⟨-1, ?_⟩
    have hz' : z = -1 := by
      rw [← sub_eq_zero]
      simpa [sub_eq_add_neg] using hright
    rw [hz']
    norm_num

private lemma good_neg {P : ℂ[X]} (h : Good P) : Good (-P) := by
  rcases h with ⟨hdeg, hcoeff, hreal⟩
  refine ⟨by simpa using hdeg, ?_, ?_⟩
  · intro k hk
    have hk' : k ∈ Set.Icc 0 P.natDegree := by
      simpa [Polynomial.natDegree_neg] using hk
    have hc := hcoeff k hk'
    rw [coeff_neg]
    rcases hc with hc | hc <;> simp [hc]
  · intro z hz
    apply hreal z
    simpa using hz

private lemma good_X_sub_one : Good (X - 1 : ℂ[X]) := by
  refine ⟨?_, ?_, ?_⟩
  · have hn : (X - 1 : ℂ[X]).natDegree = 1 := by compute_degree!
    rw [hn]
  · intro k hk
    have hn : (X - 1 : ℂ[X]).natDegree = 1 := by compute_degree!
    have hkcases : k = 0 ∨ k = 1 := by
      rw [hn] at hk
      simp only [Set.mem_Icc] at hk
      omega
    rcases hkcases with rfl | rfl <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
  · intro z hz
    refine ⟨1, ?_⟩
    have hz' : z = 1 := by
      apply sub_eq_zero.mp
      simpa [eval_sub, eval_X, eval_one] using hz
    rw [hz']
    norm_num

private lemma good_X_add_one : Good (X + 1 : ℂ[X]) := by
  refine ⟨?_, ?_, ?_⟩
  · have hn : (X + 1 : ℂ[X]).natDegree = 1 := by compute_degree!
    rw [hn]
  · intro k hk
    have hn : (X + 1 : ℂ[X]).natDegree = 1 := by compute_degree!
    have hkcases : k = 0 ∨ k = 1 := by
      rw [hn] at hk
      simp only [Set.mem_Icc] at hk
      omega
    rcases hkcases with rfl | rfl <;> simp [Polynomial.coeff_X, Polynomial.coeff_one]
  · intro z hz
    refine ⟨-1, ?_⟩
    have hz' : z = -1 := by
      rw [← sub_eq_zero]
      simpa [sub_eq_add_neg, eval_add, eval_X, eval_one] using hz
    rw [hz']
    norm_num

private lemma good_X_sq_add_X_sub_one : Good (X ^ 2 + X - 1 : ℂ[X]) := by
  refine ⟨?_, ?_, roots_real_X_sq_add_X_sub_one⟩
  · have hn : (X ^ 2 + X - 1 : ℂ[X]).natDegree = 2 := by compute_degree!
    rw [hn]
    norm_num
  intro k hk
  have hn : (X ^ 2 + X - 1 : ℂ[X]).natDegree = 2 := by compute_degree!
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by
    rw [hn] at hk
    simp only [Set.mem_Icc] at hk
    omega
  rcases hkcases with rfl | rfl | rfl <;>
    simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]

private lemma good_X_sq_sub_X_sub_one : Good (X ^ 2 - X - 1 : ℂ[X]) := by
  refine ⟨?_, ?_, roots_real_X_sq_sub_X_sub_one⟩
  · have hn : (X ^ 2 - X - 1 : ℂ[X]).natDegree = 2 := by compute_degree!
    rw [hn]
    norm_num
  intro k hk
  have hn : (X ^ 2 - X - 1 : ℂ[X]).natDegree = 2 := by compute_degree!
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by
    rw [hn] at hk
    simp only [Set.mem_Icc] at hk
    omega
  rcases hkcases with rfl | rfl | rfl <;>
    simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]

private lemma good_cubic_add : Good (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) := by
  refine ⟨?_, ?_, roots_real_cubic_add⟩
  · have hn : (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]).natDegree = 3 := by compute_degree!
    rw [hn]
    norm_num
  intro k hk
  have hn : (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]).natDegree = 3 := by compute_degree!
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    rw [hn] at hk
    simp only [Set.mem_Icc] at hk
    omega
  rcases hkcases with rfl | rfl | rfl | rfl <;>
    simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]

private lemma good_cubic_sub : Good (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) := by
  refine ⟨?_, ?_, roots_real_cubic_sub⟩
  · have hn : (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]).natDegree = 3 := by compute_degree!
    rw [hn]
    norm_num
  intro k hk
  have hn : (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]).natDegree = 3 := by compute_degree!
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    rw [hn] at hk
    simp only [Set.mem_Icc] at hk
    omega
  rcases hkcases with rfl | rfl | rfl | rfl <;>
    simp [Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_X_pow]

private lemma monic_cases (P : ℂ[X]) (hdeg1 : 1 ≤ P.natDegree) (hmonic : P.Monic)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hreal : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P = (X - 1 : ℂ[X]) ∨
    P = (X + 1 : ℂ[X]) ∨
    P = (X ^ 2 + X - 1 : ℂ[X]) ∨
    P = (X ^ 2 - X - 1 : ℂ[X]) ∨
    P = (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) ∨
    P = (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) := by
  have hle : P.natDegree ≤ 3 := monic_natDegree_le_three P hdeg1 hmonic hcoeff hreal
  have hcases : P.natDegree = 1 ∨ P.natDegree = 2 ∨ P.natDegree = 3 := by omega
  rcases hcases with hn | hn | hn
  · have hP : P = X + C (P.coeff 0) := hmonic.eq_X_add_C hn
    have hcoeff0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1 := hcoeff 0 (by simp)
    rcases hcoeff0 with h0 | h0
    · right
      left
      rw [hP, h0]
      simp
    · left
      rw [hP, h0]
      simp
      ring_nf
  · have hcoeff2 : P.coeff 2 = 1 := by
      rw [← hn]
      change P.leadingCoeff = 1
      exact hmonic
    have hcoeff1 : P.coeff 1 = 1 ∨ P.coeff 1 = -1 :=
      hcoeff 1 (by rw [hn]; norm_num [Set.mem_Icc])
    have hcoeff0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1 :=
      hcoeff 0 (by simp)
    have hsum_nonneg : 0 ≤ (P.coeff 1 ^ 2 - 2 * P.coeff 0).re := by
      have hS : (∑ x : P.roots, ((x : ℂ).re) ^ 2) =
          (P.coeff 1 ^ 2 - 2 * P.coeff 0).re := by
        rw [roots_re_sq_sum_eq P hmonic hreal]
        have hsq := roots_sum_sq_eq P hmonic (by rw [hn])
        simpa [hn] using congrArg Complex.re hsq
      rw [← hS]
      exact Finset.sum_nonneg (by intro x hx; exact sq_nonneg _)
    have hcoeff0val : P.coeff 0 = -1 := by
      rcases hcoeff0 with h0 | h0
      · rcases hcoeff1 with h1 | h1 <;> norm_num [h0, h1] at hsum_nonneg
      · exact h0
    have hdeg : P.degree ≤ (2 : WithBot ℕ) := by
      exact degree_le_of_natDegree_le (by rw [hn])
    have hP : P = C (P.coeff 2) * X ^ 2 + C (P.coeff 1) * X + C (P.coeff 0) :=
      Polynomial.eq_quadratic_of_degree_le_two hdeg
    rcases hcoeff1 with h1 | h1
    · right
      right
      left
      rw [hP, hcoeff2, h1, hcoeff0val]
      simp
      ring_nf
    · right
      right
      right
      left
      rw [hP, hcoeff2, h1, hcoeff0val]
      simp
      ring_nf
  · have hcoeff3 : P.coeff 3 = 1 := by
      rw [← hn]
      change P.leadingCoeff = 1
      exact hmonic
    have hcoeff2 : P.coeff 2 = 1 ∨ P.coeff 2 = -1 :=
      hcoeff 2 (by rw [hn]; norm_num [Set.mem_Icc])
    have hall := roots_re_sq_eq_one_of_cubic P hn hmonic hcoeff hreal
    have hcoeff1 : P.coeff 1 = -1 :=
      cubic_coeff1_eq_neg_one P hn hmonic hcoeff hreal hall
    have hcoeff0rel : P.coeff 0 = -P.coeff 2 :=
      cubic_coeff0_eq_neg_coeff2 P hn hmonic hcoeff hreal hall
    have hP : P = C (P.coeff 3) * X ^ 3 + C (P.coeff 2) * X ^ 2 +
        C (P.coeff 1) * X + C (P.coeff 0) := by
      rw [P.as_sum_range_C_mul_X_pow, hn]
      norm_num [Finset.sum_range_succ]
      abel
    rcases hcoeff2 with h2 | h2
    · have hcoeff0 : P.coeff 0 = -1 := by rw [hcoeff0rel, h2]
      right
      right
      right
      right
      left
      rw [hP, hcoeff3, h2, hcoeff1, hcoeff0]
      simp
      ring_nf
    · have hcoeff0 : P.coeff 0 = 1 := by rw [hcoeff0rel, h2]; norm_num
      right
      right
      right
      right
      right
      rw [hP, hcoeff3, h2, hcoeff1, hcoeff0]
      simp
      ring_nf

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
    have hgood : Good P := by simpa [Good] using hP
    rcases hgood with ⟨hdeg, hcoeff, hreal⟩
    have hlc : P.leadingCoeff = 1 ∨ P.leadingCoeff = -1 := by
      have := hcoeff P.natDegree (by simp [Set.mem_Icc])
      change P.coeff P.natDegree = 1 ∨ P.coeff P.natDegree = -1
      exact this
    rcases hlc with hlc | hlc
    · have hmonic : P.Monic := by
        change P.leadingCoeff = 1
        exact hlc
      have hcases := monic_cases P hdeg hmonic hcoeff hreal
      rcases hcases with h | h | h | h | h | h
      · rw [h]
        exact mem_answerSet_X_sub_one
      · rw [h]
        exact mem_answerSet_X_add_one
      · rw [h]
        exact mem_answerSet_X_sq_add_X_sub_one
      · rw [h]
        exact mem_answerSet_X_sq_sub_X_sub_one
      · rw [h]
        exact mem_answerSet_cubic_add
      · rw [h]
        exact mem_answerSet_cubic_sub
    · have hgoodNeg : Good (-P) := good_neg ⟨hdeg, hcoeff, hreal⟩
      rcases hgoodNeg with ⟨hdegN, hcoeffN, hrealN⟩
      have hmonicNeg : (-P).Monic := by
        change (-P).leadingCoeff = 1
        rw [Polynomial.leadingCoeff_neg, hlc]
        norm_num
      have hcases := monic_cases (-P) hdegN hmonicNeg hcoeffN hrealN
      rcases hcases with h | h | h | h | h | h
      · have hp : P = -(X - 1 : ℂ[X]) := by simpa using congrArg Neg.neg h
        rw [hp]
        exact mem_answerSet_neg_X_sub_one
      · have hp : P = -(X + 1 : ℂ[X]) := by simpa using congrArg Neg.neg h
        rw [hp]
        exact mem_answerSet_neg_X_add_one
      · have hp : P = -(X ^ 2 + X - 1 : ℂ[X]) := by simpa using congrArg Neg.neg h
        rw [hp]
        exact mem_answerSet_neg_X_sq_add_X_sub_one
      · have hp : P = -(X ^ 2 - X - 1 : ℂ[X]) := by simpa using congrArg Neg.neg h
        rw [hp]
        exact mem_answerSet_neg_X_sq_sub_X_sub_one
      · have hp : P = -(X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) := by simpa using congrArg Neg.neg h
        rw [hp]
        exact mem_answerSet_neg_cubic_add
      · have hp : P = -(X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) := by simpa using congrArg Neg.neg h
        rw [hp]
        exact mem_answerSet_neg_cubic_sub
  · intro hP
    have hPfin : P ∈ answerSet := by simpa [answerSet] using hP
    simp [answerSet] at hPfin
    rcases hPfin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [Good] using good_X_sub_one
    · simpa [Good] using good_neg good_X_sub_one
    · simpa [Good] using good_X_add_one
    · simpa [Good] using good_neg good_X_add_one
    · simpa [Good] using good_X_sq_add_X_sub_one
    · simpa [Good] using good_neg good_X_sq_add_X_sub_one
    · simpa [Good] using good_X_sq_sub_X_sub_one
    · simpa [Good] using good_neg good_X_sq_sub_X_sub_one
    · simpa [Good] using good_cubic_add
    · simpa [Good] using good_neg good_cubic_add
    · simpa [Good] using good_cubic_sub
    · simpa [Good] using good_neg good_cubic_sub
