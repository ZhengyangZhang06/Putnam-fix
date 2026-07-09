import Mathlib

open Set Filter Topology Real Polynomial Function

abbrev putnam_1985_b1_solution : Fin 5 → ℤ := ![0, -2, 2, -1, 1]

private lemma putnam_1985_b1_solution_injective : Function.Injective putnam_1985_b1_solution := by
  decide

private lemma putnam_1985_b1_solution_poly :
    (∏ i : Fin 5, ((X : Polynomial ℝ) - putnam_1985_b1_solution i)) =
      (X ^ 5 - 5 * X ^ 3 + 4 * X : Polynomial ℝ) := by
  simp [Fin.prod_univ_five, putnam_1985_b1_solution, Matrix.cons_val_zero]
  ring_nf

private lemma putnam_1985_b1_solution_count :
    ({j ∈ Finset.range ((∏ i : Fin 5, ((X : Polynomial ℝ) - putnam_1985_b1_solution i)).natDegree + 1) |
      (∏ i : Fin 5, ((X : Polynomial ℝ) - putnam_1985_b1_solution i)).coeff j ≠ 0}.card) = 3 := by
  rw [putnam_1985_b1_solution_poly]
  have hdeg : (X ^ 5 - 5 * X ^ 3 + 4 * X : Polynomial ℝ).natDegree = 5 := by
    compute_degree!
  rw [hdeg]
  have hset :
      ({j ∈ Finset.range (5 + 1) | (X ^ 5 - 5 * X ^ 3 + 4 * X : Polynomial ℝ).coeff j ≠ 0}) =
        ({1, 3, 5} : Finset ℕ) := by
    ext j
    constructor
    · intro h
      simp only [Finset.mem_filter, Finset.mem_range] at h
      have hj : j < 6 := by omega
      interval_cases j
      · exfalso
        norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_X] at h
      · norm_num
      · exfalso
        norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_X] at h
      · norm_num
      · exfalso
        norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_X] at h
      · norm_num
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl <;>
        norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_X]
  rw [hset]
  norm_num

private lemma putnam_1985_b1_coeff_filter_card_ge_three {q : Polynomial ℝ} {a b c : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (har : a < q.natDegree + 1) (hbr : b < q.natDegree + 1) (hcr : c < q.natDegree + 1)
    (ha : q.coeff a ≠ 0) (hb : q.coeff b ≠ 0) (hc : q.coeff c ≠ 0) :
    3 ≤ ({j ∈ Finset.range (q.natDegree + 1) | q.coeff j ≠ 0}.card) := by
  have hsubset : ({a, b, c} : Finset ℕ) ⊆
      {j ∈ Finset.range (q.natDegree + 1) | q.coeff j ≠ 0} := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · simp [har, ha]
    · simp [hbr, hb]
    · simp [hcr, hc]
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    simp [hab, hac, hbc]
  rw [← hcard]
  exact Finset.card_le_card hsubset

private lemma putnam_1985_b1_prod_natDegree_five (m : Fin 5 → ℤ) :
    (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).natDegree = 5 := by
  rw [show (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)) =
      ∏ i : Fin 5, ((X : Polynomial ℝ) - C ((m i : ℝ))) by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Polynomial.C_eq_intCast]]
  simpa using (Polynomial.natDegree_finset_prod_X_sub_C_eq_card
    (s := (Finset.univ : Finset (Fin 5))) (f := fun i => (m i : ℝ)) (R := ℝ))

private lemma putnam_1985_b1_prod_coeff_five_ne_zero (m : Fin 5 → ℤ) :
    (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff 5 ≠ 0 := by
  have hcoeff := Multiset.prod_X_sub_C_coeff
    (((Finset.univ : Finset (Fin 5)).val.map (fun i => (m i : ℝ))) : Multiset ℝ)
    (k := 5) (by simp)
  have hcoeff' : (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff 5 = (1 : ℝ) := by
    simpa [Finset.prod, Multiset.map_map, Function.comp_def, Polynomial.C_eq_intCast,
      Multiset.esymm] using hcoeff
  rw [hcoeff']
  norm_num

private lemma putnam_1985_b1_coeff_four_three_not_both_zero
    (m : Fin 5 → ℤ) (hm : Function.Injective m)
    (h4 : (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff 4 = 0)
    (h3 : (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff 3 = 0) : False := by
  have hsum : (∑ i : Fin 5, (m i : ℝ)) = 0 := by
    have hcoeff := Polynomial.prod_X_sub_C_coeff_card_pred
      (s := (Finset.univ : Finset (Fin 5))) (f := fun i => (m i : ℝ)) (R := ℝ)
      (by simp)
    norm_num at hcoeff
    rw [hcoeff] at h4
    linarith
  have he2 : ((Finset.univ : Finset (Fin 5)).val.map (fun i => (m i : ℝ))).esymm 2 = 0 := by
    have hcoeff := Multiset.prod_X_sub_C_coeff
      (((Finset.univ : Finset (Fin 5)).val.map (fun i => (m i : ℝ))) : Multiset ℝ)
      (k := 3) (by simp)
    have hcoeff' : (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff 3 =
        ((Finset.univ : Finset (Fin 5)).val.map (fun i => (m i : ℝ))).esymm 2 := by
      simpa [Finset.prod, Multiset.map_map, Function.comp_def, Polynomial.C_eq_intCast]
        using hcoeff
    rw [hcoeff'] at h3
    exact h3
  have hsqid : (∑ i : Fin 5, (m i : ℝ)) ^ 2 =
      (∑ i : Fin 5, (m i : ℝ) ^ 2) +
        2 * (((Finset.univ : Finset (Fin 5)).val.map (fun i => (m i : ℝ))).esymm 2) := by
    norm_num [Fin.sum_univ_five]
    change ((m 0 : ℝ) + m 1 + m 2 + m 3 + m 4) ^ 2 =
      ((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2 + (m 2 : ℝ) ^ 2 + (m 3 : ℝ) ^ 2 +
          (m 4 : ℝ) ^ 2) +
        2 * (Multiset.esymm ((m 0 : ℝ) ::ₘ (m 1 : ℝ) ::ₘ (m 2 : ℝ) ::ₘ
          (m 3 : ℝ) ::ₘ ({(m 4 : ℝ)} : Multiset ℝ)) 2)
    simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
    ring_nf
  have hsquares : ∑ i : Fin 5, (m i : ℝ) ^ 2 = 0 := by
    nlinarith
  have hsquares' : (m 0 : ℝ)^2 + (m 1 : ℝ)^2 + (m 2 : ℝ)^2 +
      (m 3 : ℝ)^2 + (m 4 : ℝ)^2 = 0 := by
    simpa [Fin.sum_univ_five] using hsquares
  have hm0 : m 0 = 0 := by
    have hm0R : (m 0 : ℝ) = 0 := by
      nlinarith [sq_nonneg (m 0 : ℝ), sq_nonneg (m 1 : ℝ), sq_nonneg (m 2 : ℝ),
        sq_nonneg (m 3 : ℝ), sq_nonneg (m 4 : ℝ)]
    exact_mod_cast hm0R
  have hm1 : m 1 = 0 := by
    have hm1R : (m 1 : ℝ) = 0 := by
      nlinarith [sq_nonneg (m 0 : ℝ), sq_nonneg (m 1 : ℝ), sq_nonneg (m 2 : ℝ),
        sq_nonneg (m 3 : ℝ), sq_nonneg (m 4 : ℝ)]
    exact_mod_cast hm1R
  have h01 : (0 : Fin 5) = 1 := hm (by rw [hm0, hm1])
  norm_num at h01

private lemma putnam_1985_b1_coeff_one_ne_zero_of_const_zero
    (m : Fin 5 → ℤ) (hm : Function.Injective m)
    (h0 : (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff 0 = 0) :
    (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff 1 ≠ 0 := by
  classical
  have heval : (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).eval 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using h0
  simp [Polynomial.eval_prod] at heval
  rw [Finset.prod_eq_zero_iff] at heval
  rcases heval with ⟨z, _hzmem, hz0r⟩
  norm_num at hz0r
  have hz : m z = 0 := by exact_mod_cast hz0r
  let r : Polynomial ℝ := ∏ i ∈ (Finset.univ.erase z), ((X : Polynomial ℝ) - m i)
  have hfactor : (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)) = X * r := by
    dsimp [r]
    rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin 5)))
      (f := fun i => ((X : Polynomial ℝ) - m i)) (a := z) (by simp)]
    rw [hz]
    simp
  rw [hfactor]
  have hcoeff : (X * r).coeff 1 = r.coeff 0 := by
    simp
  rw [hcoeff]
  have hconst : r.coeff 0 = ∏ i ∈ (Finset.univ.erase z), (-(m i : ℝ)) := by
    dsimp [r]
    simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  rw [hconst]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
  have hmi : m i ≠ 0 := by
    intro hmi0
    have hiz : i = z := hm (by rw [hmi0, hz])
    exact hi hiz
  exact neg_ne_zero.mpr (by exact_mod_cast hmi)

private lemma putnam_1985_b1_count_ge_three (m : Fin 5 → ℤ) (hm : Function.Injective m) :
    3 ≤ ({j ∈ Finset.range ((∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).natDegree + 1) |
      (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff j ≠ 0}.card) := by
  let q : Polynomial ℝ := ∏ i : Fin 5, ((X : Polynomial ℝ) - m i)
  have hdeg : q.natDegree = 5 := by
    dsimp [q]
    exact putnam_1985_b1_prod_natDegree_five m
  have h5 : q.coeff 5 ≠ 0 := by
    dsimp [q]
    exact putnam_1985_b1_prod_coeff_five_ne_zero m
  have h43 : q.coeff 4 ≠ 0 ∨ q.coeff 3 ≠ 0 := by
    by_contra h
    push_neg at h
    exact putnam_1985_b1_coeff_four_three_not_both_zero m hm h.1 h.2
  have h5r : 5 < q.natDegree + 1 := by rw [hdeg]; norm_num
  have h4r : 4 < q.natDegree + 1 := by rw [hdeg]; norm_num
  have h3r : 3 < q.natDegree + 1 := by rw [hdeg]; norm_num
  have h1r : 1 < q.natDegree + 1 := by rw [hdeg]; norm_num
  have h0r : 0 < q.natDegree + 1 := by rw [hdeg]; norm_num
  by_cases h0 : q.coeff 0 = 0
  · have h1 : q.coeff 1 ≠ 0 := by
      dsimp [q] at h0 ⊢
      exact putnam_1985_b1_coeff_one_ne_zero_of_const_zero m hm h0
    rcases h43 with h4 | h3
    · exact putnam_1985_b1_coeff_filter_card_ge_three (q := q) (a := 1) (b := 4) (c := 5)
        (by norm_num) (by norm_num) (by norm_num) h1r h4r h5r h1 h4 h5
    · exact putnam_1985_b1_coeff_filter_card_ge_three (q := q) (a := 1) (b := 3) (c := 5)
        (by norm_num) (by norm_num) (by norm_num) h1r h3r h5r h1 h3 h5
  · have h0ne : q.coeff 0 ≠ 0 := h0
    rcases h43 with h4 | h3
    · exact putnam_1985_b1_coeff_filter_card_ge_three (q := q) (a := 0) (b := 4) (c := 5)
        (by norm_num) (by norm_num) (by norm_num) h0r h4r h5r h0ne h4 h5
    · exact putnam_1985_b1_coeff_filter_card_ge_three (q := q) (a := 0) (b := 3) (c := 5)
        (by norm_num) (by norm_num) (by norm_num) h0r h3r h5r h0ne h3 h5

/--
Let $k$ be the smallest positive integer for which there exist distinct integers $m_1, m_2, m_3, m_4, m_5$ such that the polynomial
\[
p(x) = (x-m_1)(x-m_2)(x-m_3)(x-m_4)(x-m_5)
\]
has exactly $k$ nonzero coefficients. Find, with proof, a set of integers $m_1, m_2, m_3, m_4, m_5$ for which this minimum $k$ is achieved.
-/
theorem putnam_1985_b1
(p : (Fin 5 → ℤ) → (Polynomial ℝ))
(hp : p = fun m ↦ ∏ i : Fin 5, ((X : Polynomial ℝ) - m i))
(numnzcoeff : Polynomial ℝ → ℕ)
(hnumnzcoeff : numnzcoeff = fun p ↦ {j ∈ Finset.range (p.natDegree + 1) | coeff p j ≠ 0}.card)
: (Injective putnam_1985_b1_solution ∧ ∀ m : Fin 5 → ℤ, Injective m → numnzcoeff (p putnam_1985_b1_solution) ≤ numnzcoeff (p m)) :=
by
  constructor
  · exact putnam_1985_b1_solution_injective
  · intro m hm
    rw [hp, hnumnzcoeff]
    change
      ({j ∈ Finset.range ((∏ i : Fin 5, ((X : Polynomial ℝ) - putnam_1985_b1_solution i)).natDegree + 1) |
        (∏ i : Fin 5, ((X : Polynomial ℝ) - putnam_1985_b1_solution i)).coeff j ≠ 0}.card) ≤
      ({j ∈ Finset.range ((∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).natDegree + 1) |
        (∏ i : Fin 5, ((X : Polynomial ℝ) - m i)).coeff j ≠ 0}.card)
    rw [putnam_1985_b1_solution_count]
    exact putnam_1985_b1_count_ge_three m hm
