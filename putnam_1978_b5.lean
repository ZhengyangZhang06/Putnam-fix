import Mathlib

open Set Real Filter Topology Polynomial

noncomputable abbrev putnam_1978_b5_solution : Polynomial ℝ :=
  ((1 : Polynomial ℝ) - (2 : Polynomial ℝ) * X ^ 2) * ((1 : Polynomial ℝ) - (2 : Polynomial ℝ) * X ^ 2)

/--
Find the real polynomial $p(x)$ of degree $4$ with largest possible coefficient of $x^4$ such that $p([-1, 1]) \subseteq [0, 1]$.
-/
theorem putnam_1978_b5
(S : Set (Polynomial ℝ))
(hS : S = {p : Polynomial ℝ | p.degree = 4 ∧ ∀ x ∈ Icc (-1) 1, p.eval x ∈ Icc 0 1})
: (putnam_1978_b5_solution ∈ S ∧ (∀ p ∈ S, p.coeff 4 ≤ putnam_1978_b5_solution.coeff 4)) :=
by
  have hsol_expand :
      putnam_1978_b5_solution =
        (4 : Polynomial ℝ) * X ^ 4 - (4 : Polynomial ℝ) * X ^ 2 + 1 := by
    rw [putnam_1978_b5_solution]
    ring
  have hsol_degree : putnam_1978_b5_solution.degree = 4 := by
    rw [hsol_expand]
    apply degree_eq_of_le_of_coeff_ne_zero
    · rw [degree_le_iff_coeff_zero]
      intro m hm
      have hm' : 4 < m := by exact_mod_cast hm
      have hm2 : m ≠ 2 := by omega
      have hm0 : m ≠ 0 := by omega
      simp [coeff_add, coeff_sub, coeff_X_pow, coeff_one,
        hm'.ne', hm2, hm0]
    · norm_num [coeff_add, coeff_sub, coeff_X_pow, coeff_one]
  have hsol_coeff : putnam_1978_b5_solution.coeff 4 = 4 := by
    rw [hsol_expand]
    norm_num [coeff_add, coeff_sub, coeff_X_pow, coeff_one]
  have hsol_eval : ∀ x : ℝ, putnam_1978_b5_solution.eval x = (1 - 2 * x ^ 2) ^ 2 := by
    intro x
    rw [hsol_expand]
    norm_num
    ring
  have hsol_mem : putnam_1978_b5_solution ∈ S := by
    rw [hS]
    refine ⟨hsol_degree, ?_⟩
    intro x hx
    have hx1 : -1 ≤ x := hx.1
    have hx2 : x ≤ 1 := hx.2
    have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have hx_sq_le : x ^ 2 ≤ 1 := by nlinarith [hx1, hx2]
    constructor
    · rw [hsol_eval]
      exact sq_nonneg _
    · rw [hsol_eval]
      nlinarith [hx_sq_nonneg, hx_sq_le, sq_nonneg (1 - 2 * x ^ 2)]
  have real_bound :
      ∀ m n z b o : ℝ, m ≤ 1 → z ≤ 1 → o ≤ 1 → 0 ≤ n → 0 ≤ b →
        m - 2 * n + 2 * z - 2 * b + o ≤ 4 := by
    intro m n z b o hm hz ho hn hb
    linarith
  refine ⟨hsol_mem, ?_⟩
  intro p hpS
  have hp : p.degree = 4 ∧ ∀ x ∈ Icc (-1 : ℝ) 1, p.eval x ∈ Icc (0 : ℝ) 1 := by
    simpa [hS] using hpS
  let a : ℝ := Real.sqrt (1 / 2 : ℝ)
  have ha_sq : a ^ 2 = 1 / 2 := by
    dsimp [a]
    rw [Real.sq_sqrt]
    norm_num
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.sqrt_nonneg _
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (by norm_num)
  have ha_lt_one : a < 1 := by nlinarith
  let v : Fin 5 → ℝ := fun i => (![(-1 : ℝ), -a, 0, a, 1] : Fin 5 → ℝ) i
  have herase0 :
      (Finset.univ : Finset (Fin 5)).erase (0 : Fin 5) =
        ({1, 2, 3, 4} : Finset (Fin 5)) := by
    decide
  have herase1 :
      (Finset.univ : Finset (Fin 5)).erase (1 : Fin 5) =
        ({0, 2, 3, 4} : Finset (Fin 5)) := by
    decide
  have herase2 :
      (Finset.univ : Finset (Fin 5)).erase (2 : Fin 5) =
        ({0, 1, 3, 4} : Finset (Fin 5)) := by
    decide
  have herase3 :
      (Finset.univ : Finset (Fin 5)).erase (3 : Fin 5) =
        ({0, 1, 2, 4} : Finset (Fin 5)) := by
    decide
  have herase4 :
      (Finset.univ : Finset (Fin 5)).erase (4 : Fin 5) =
        ({0, 1, 2, 3} : Finset (Fin 5)) := by
    decide
  have hprod0 :
      (∏ x ∈ (Finset.univ : Finset (Fin 5)).erase (0 : Fin 5),
          (v (0 : Fin 5) - v x)) = 1 := by
    rw [herase0]
    simp [v]
    nlinarith
  have hprod1 :
      (∏ x ∈ (Finset.univ : Finset (Fin 5)).erase (1 : Fin 5),
          (v (1 : Fin 5) - v x)) = -1 / 2 := by
    rw [herase1]
    simp [v]
    nlinarith
  have hprod2 :
      (∏ x ∈ (Finset.univ : Finset (Fin 5)).erase (2 : Fin 5),
          (v (2 : Fin 5) - v x)) = 1 / 2 := by
    rw [herase2]
    simp [v]
    nlinarith
  have hprod3 :
      (∏ x ∈ (Finset.univ : Finset (Fin 5)).erase (3 : Fin 5),
          (v (3 : Fin 5) - v x)) = -1 / 2 := by
    rw [herase3]
    simp [v]
    nlinarith
  have hprod4 :
      (∏ x ∈ (Finset.univ : Finset (Fin 5)).erase (4 : Fin 5),
          (v (4 : Fin 5) - v x)) = 1 := by
    rw [herase4]
    simp [v]
    nlinarith
  have hvinj : Set.InjOn v (Finset.univ : Finset (Fin 5)) := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢
    all_goals nlinarith
  have hp_degree_lt : p.degree < (Finset.univ : Finset (Fin 5)).card := by
    rw [hp.1]
    norm_num
  have hlagrange :=
    Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin 5))) (v := v) (P := p)
      hvinj hp_degree_lt
  have hcoeff :
      p.coeff 4 =
        p.eval (-1) - 2 * p.eval (-a) + 2 * p.eval 0 - 2 * p.eval a + p.eval 1 := by
    calc
      p.coeff 4 =
          ∑ i ∈ (Finset.univ : Finset (Fin 5)),
            p.eval (v i) /
              ∏ j ∈ (Finset.univ : Finset (Fin 5)).erase i, (v i - v j) := by
        simpa using hlagrange
      _ = p.eval (-1) - 2 * p.eval (-a) + 2 * p.eval 0 - 2 * p.eval a + p.eval 1 := by
        rw [Fin.sum_univ_five]
        rw [hprod0, hprod1, hprod2, hprod3, hprod4]
        simp [v]
        ring
  have h_mone_le : p.eval (-1) ≤ 1 := (hp.2 (-1) (by norm_num)).2
  have h_zero_le : p.eval 0 ≤ 1 := (hp.2 0 (by norm_num)).2
  have h_one_le : p.eval 1 ≤ 1 := (hp.2 1 (by norm_num)).2
  have h_neg_a_nonneg : 0 ≤ p.eval (-a) := by
    exact (hp.2 (-a)
      ⟨by
        simpa using neg_le_neg (le_of_lt ha_lt_one),
       by
        exact le_trans (neg_nonpos.mpr ha_nonneg) (by norm_num)⟩).1
  have h_a_nonneg : 0 ≤ p.eval a := by
    exact (hp.2 a
      ⟨by
        exact le_trans (by norm_num) ha_nonneg,
       by
        exact le_of_lt ha_lt_one⟩).1
  have hp_bound : p.coeff 4 ≤ 4 := by
    exact hcoeff.trans_le
      (real_bound (p.eval (-1)) (p.eval (-a)) (p.eval 0) (p.eval a) (p.eval 1)
        h_mone_le h_zero_le h_one_le h_neg_a_nonneg h_a_nonneg)
  rw [hsol_coeff]
  exact hp_bound
