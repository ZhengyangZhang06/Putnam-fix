import Mathlib

open Set Real Filter Topology Polynomial

-- 4 * X ^ 4 - 4 * X ^ 2 + 1
/--
Find the real polynomial $p(x)$ of degree $4$ with largest possible coefficient of $x^4$ such that $p([-1, 1]) \subseteq [0, 1]$.
-/
theorem putnam_1978_b5
(S : Set (Polynomial ℝ))
(hS : S = {p : Polynomial ℝ | p.degree = 4 ∧ ∀ x ∈ Icc (-1) 1, p.eval x ∈ Icc 0 1})
: (((4 * X ^ 4 - 4 * X ^ 2 + 1) : Polynomial ℝ ) ∈ S ∧ (∀ p ∈ S, p.coeff 4 ≤ ((4 * X ^ 4 - 4 * X ^ 2 + 1) : Polynomial ℝ ).coeff 4)) := by
  classical
  let q : Polynomial ℝ := 4 * X ^ 4 - 4 * X ^ 2 + 1
  let r : ℝ := Real.sqrt (1 / 2)
  have hr2 : r ^ 2 = (1 / 2 : ℝ) := by
    dsimp [r]
    rw [Real.sq_sqrt]
    norm_num
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 (by norm_num)
  have hr_lt_one : r < 1 := by
    nlinarith [hr2, sq_nonneg (r - 1)]
  have coeff_formula (p : Polynomial ℝ) (hpdeg : p.degree = 4) :
      p.coeff 4 = p.eval (-1) + p.eval 1 + 2 * p.eval 0 - 2 * p.eval (-r) - 2 * p.eval r := by
    let v : Fin 5 → ℝ := fun i => ![(-1 : ℝ), -r, 0, r, 1] i
    have hvinj : Set.InjOn v ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)) := by
      intro i hi j hj hij
      fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢ <;> nlinarith
    have hdeglt : p.degree < ((Finset.univ : Finset (Fin 5)).card : WithBot ℕ) := by
      rw [hpdeg]
      norm_num
    have e0 : (Finset.univ : Finset (Fin 5)).erase 0 = ({1, 2, 3, 4} : Finset (Fin 5)) := by
      ext x
      fin_cases x <;> simp
    have h0 : (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 0, (v 0 - v j)) = (1 : ℝ) := by
      rw [e0]
      simp [v]
      nlinarith [hr2]
    have e1 : (Finset.univ : Finset (Fin 5)).erase 1 = ({0, 2, 3, 4} : Finset (Fin 5)) := by
      ext x
      fin_cases x <;> simp
    have h1 : (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 1, (v 1 - v j)) = (-1 / 2 : ℝ) := by
      rw [e1]
      simp [v]
      nlinarith [hr2]
    have e2 : (Finset.univ : Finset (Fin 5)).erase 2 = ({0, 1, 3, 4} : Finset (Fin 5)) := by
      ext x
      fin_cases x <;> simp
    have h2 : (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 2, (v 2 - v j)) = (1 / 2 : ℝ) := by
      rw [e2]
      simp [v]
      nlinarith [hr2]
    have e3 : (Finset.univ : Finset (Fin 5)).erase 3 = ({0, 1, 2, 4} : Finset (Fin 5)) := by
      ext x
      fin_cases x <;> simp
    have h3 : (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 3, (v 3 - v j)) = (-1 / 2 : ℝ) := by
      rw [e3]
      simp [v]
      nlinarith [hr2]
    have e4 : (Finset.univ : Finset (Fin 5)).erase 4 = ({0, 1, 2, 3} : Finset (Fin 5)) := by
      ext x
      fin_cases x <;> simp
    have h4 : (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 4, (v 4 - v j)) = (1 : ℝ) := by
      rw [e4]
      simp [v]
      nlinarith [hr2]
    have hc := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin 5))) (v := v) hvinj (P := p) hdeglt
    rw [Finset.card_univ, Fintype.card_fin] at hc
    norm_num at hc
    rw [hc]
    rw [Fin.sum_univ_five]
    rw [h0, h1, h2, h3, h4]
    simp [v]
    ring_nf
  change q ∈ S ∧ (∀ p ∈ S, p.coeff 4 ≤ q.coeff 4)
  constructor
  · rw [hS]
    constructor
    · dsimp [q]
      compute_degree!
    · intro x hx
      rw [mem_Icc] at hx
      constructor
      · dsimp [q]
        simp
        nlinarith [sq_nonneg (2 * x ^ 2 - 1)]
      · have hx2_le : x ^ 2 ≤ 1 := by
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
        dsimp [q]
        simp
        nlinarith [sq_nonneg x, hx2_le]
  · intro p hpS
    have hp : p.degree = 4 ∧ ∀ x ∈ Icc (-1) 1, p.eval x ∈ Icc 0 1 := by
      simpa [hS] using hpS
    have hcoef := coeff_formula p hp.1
    have hneg_one : p.eval (-1) ∈ Icc 0 1 := hp.2 (-1) (by norm_num)
    have hzero : p.eval 0 ∈ Icc 0 1 := hp.2 0 (by norm_num)
    have hone : p.eval 1 ∈ Icc 0 1 := hp.2 1 (by norm_num)
    have hneg_r_mem : -r ∈ Icc (-1) 1 := by
      rw [mem_Icc]
      constructor <;> nlinarith
    have hr_mem : r ∈ Icc (-1) 1 := by
      rw [mem_Icc]
      constructor <;> nlinarith
    have hneg_r : p.eval (-r) ∈ Icc 0 1 := hp.2 (-r) hneg_r_mem
    have hr : p.eval r ∈ Icc 0 1 := hp.2 r hr_mem
    have hqcoeff : q.coeff 4 = 4 := by
      dsimp [q]
      compute_degree!
    rw [hcoef, hqcoeff]
    rw [mem_Icc] at hneg_one hzero hone hneg_r hr
    nlinarith [hneg_one.2, hzero.2, hone.2, hneg_r.1, hr.1]
