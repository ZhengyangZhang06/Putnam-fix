import Mathlib

private def putnam_2015_b3_coeff (α β : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * α * putnam_2015_b3_coeff α β (n + 1) + 8 * β ^ 2 * putnam_2015_b3_coeff α β n

private lemma putnam_2015_b3_coeff_zero (α β : ℝ) :
    putnam_2015_b3_coeff α β 0 = 0 := by
  simp [putnam_2015_b3_coeff]

private lemma putnam_2015_b3_coeff_one (α β : ℝ) :
    putnam_2015_b3_coeff α β 1 = 1 := by
  simp [putnam_2015_b3_coeff]

private lemma putnam_2015_b3_coeff_add_two (α β : ℝ) (n : ℕ) :
    putnam_2015_b3_coeff α β (n + 2) =
      2 * α * putnam_2015_b3_coeff α β (n + 1) +
        8 * β ^ 2 * putnam_2015_b3_coeff α β n := by
  simp [putnam_2015_b3_coeff]

private lemma putnam_2015_b3_coeff_pair_pos {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    ∀ n : ℕ,
      0 < putnam_2015_b3_coeff α β (2 * n + 1) ∧
        0 < α * putnam_2015_b3_coeff α β (2 * n + 2) := by
  intro n
  induction n with
  | zero =>
      constructor
      · simp [putnam_2015_b3_coeff_one]
      · rw [show 2 * 0 + 2 = 0 + 2 by omega,
          putnam_2015_b3_coeff_add_two, putnam_2015_b3_coeff_one,
          putnam_2015_b3_coeff_zero]
        nlinarith [sq_pos_of_ne_zero hα]
  | succ n ih =>
      have hrecOdd :
          putnam_2015_b3_coeff α β (2 * (n + 1) + 1) =
            2 * α * putnam_2015_b3_coeff α β (2 * n + 2) +
              8 * β ^ 2 * putnam_2015_b3_coeff α β (2 * n + 1) := by
        have hidx : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
        rw [hidx, putnam_2015_b3_coeff_add_two]
      have hodd_next : 0 < putnam_2015_b3_coeff α β (2 * (n + 1) + 1) := by
        rw [hrecOdd]
        have hb2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
        nlinarith [ih.1, ih.2, hb2]
      have hrecEven :
          putnam_2015_b3_coeff α β (2 * (n + 1) + 2) =
            2 * α * putnam_2015_b3_coeff α β (2 * (n + 1) + 1) +
              8 * β ^ 2 * putnam_2015_b3_coeff α β (2 * n + 2) := by
        have hidx : 2 * (n + 1) + 2 = (2 * n + 2) + 2 := by omega
        have hidx1 : (2 * n + 2) + 1 = 2 * (n + 1) + 1 := by omega
        rw [hidx, putnam_2015_b3_coeff_add_two, hidx1]
      constructor
      · exact hodd_next
      · rw [hrecEven]
        have ha2 : 0 < α ^ 2 := sq_pos_of_ne_zero hα
        have hb2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
        nlinarith [ha2, hb2, hodd_next, ih.2]

private lemma putnam_2015_b3_coeff_ne_zero_of_pos {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) {n : ℕ} (hn : 0 < n) :
    putnam_2015_b3_coeff α β n ≠ 0 := by
  have hpair := putnam_2015_b3_coeff_pair_pos (α := α) (β := β) hα hβ
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · rcases hn_even with ⟨m, hm⟩
    cases m with
    | zero =>
        subst n
        omega
    | succ m =>
        subst n
        have hidx : m + 1 + (m + 1) = 2 * m + 2 := by omega
        have hpos := (hpair m).2
        intro hzero
        rw [hidx] at hzero
        rw [hzero, mul_zero] at hpos
        exact lt_irrefl 0 hpos
  · rcases hn_odd with ⟨m, hm⟩
    subst n
    have hpos := (hpair m).1
    exact ne_of_gt hpos

private def putnam_2015_b3_mat (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![α - 3 * β, α - β; α + β, α + 3 * β]

private lemma putnam_2015_b3_mat_pow_entries (α β : ℝ) :
    ∀ n : ℕ,
      (putnam_2015_b3_mat α β) ^ (n + 1) =
        !![putnam_2015_b3_coeff α β (n + 1) * (α - 3 * β) +
              8 * β ^ 2 * putnam_2015_b3_coeff α β n,
           putnam_2015_b3_coeff α β (n + 1) * (α - β);
           putnam_2015_b3_coeff α β (n + 1) * (α + β),
           putnam_2015_b3_coeff α β (n + 1) * (α + 3 * β) +
              8 * β ^ 2 * putnam_2015_b3_coeff α β n] := by
  intro n
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [putnam_2015_b3_mat, putnam_2015_b3_coeff]
  | succ n ih =>
      rw [pow_succ]
      rw [ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [putnam_2015_b3_mat, Matrix.mul_apply, Fin.sum_univ_two,
          putnam_2015_b3_coeff] <;> ring

-- {A : Matrix (Fin 2) (Fin 2) ℝ | (∃ α : ℝ, ∀ i j : Fin 2, A i j = α * 1) ∨ (∃ β : ℝ, A 0 0 = β * -3 ∧ A 0 1 = β * -1 ∧ A 1 0 = β * 1 ∧ A 1 1 = β * 3)}
/--
Let $S$ be the set of all $2 \times 2$ real matrices $M=\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ whose entries $a,b,c,d$ (in that order) form an arithmetic progression. Find all matrices $M$ in $S$ for which there is some integer $k>1$ such that $M^k$ is also in $S$.
-/
theorem putnam_2015_b3
  (M : Matrix (Fin 2) (Fin 2) ℝ)
  (S : Set (Matrix (Fin 2) (Fin 2) ℝ))
  (hS : S = {M' | (M' 0 1 - M' 0 0 = M' 1 0 - M' 0 1) ∧ (M' 1 0 - M' 0 1 = M' 1 1 - M' 1 0)}) :
  (M ∈ S ∧ (∃ k > 1, M ^ k ∈ S)) ↔ M ∈ (({A : Matrix (Fin 2) (Fin 2) ℝ | (∃ α : ℝ, ∀ i j : Fin 2, A i j = α * 1) ∨ (∃ β : ℝ, A 0 0 = β * -3 ∧ A 0 1 = β * -1 ∧ A 1 0 = β * 1 ∧ A 1 1 = β * 3)}) : Set (Matrix (Fin 2) (Fin 2) ℝ) ) := by
  rw [hS]
  constructor
  · rintro ⟨hM, ⟨k, hkgt, hkS⟩⟩
    let β : ℝ := (M 0 1 - M 0 0) / 2
    let α : ℝ := M 0 0 + 3 * β
    have h00 : M 0 0 = α - 3 * β := by
      simp [α]
    have h01 : M 0 1 = α - β := by
      simp [α, β]
      ring
    have h10 : M 1 0 = α + β := by
      have hc : M 1 0 = 2 * M 0 1 - M 0 0 := by nlinarith [hM.1]
      rw [hc]
      simp [α, β]
      ring
    have h11 : M 1 1 = α + 3 * β := by
      have hc : M 1 0 = 2 * M 0 1 - M 0 0 := by nlinarith [hM.1]
      have hd : M 1 1 = 2 * M 1 0 - M 0 1 := by nlinarith [hM.2]
      rw [hd, hc]
      simp [α, β]
      ring
    have hMmat : M = putnam_2015_b3_mat α β := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [putnam_2015_b3_mat, h00, h01, h10, h11]
    have hk_eq : k = (k - 1) + 1 := by omega
    have hpowk :
        (putnam_2015_b3_mat α β) ^ k =
          !![putnam_2015_b3_coeff α β ((k - 1) + 1) * (α - 3 * β) +
                8 * β ^ 2 * putnam_2015_b3_coeff α β (k - 1),
             putnam_2015_b3_coeff α β ((k - 1) + 1) * (α - β);
             putnam_2015_b3_coeff α β ((k - 1) + 1) * (α + β),
             putnam_2015_b3_coeff α β ((k - 1) + 1) * (α + 3 * β) +
                8 * β ^ 2 * putnam_2015_b3_coeff α β (k - 1)] := by
      rw [hk_eq]
      exact putnam_2015_b3_mat_pow_entries α β (k - 1)
    have hqzero : 8 * β ^ 2 * putnam_2015_b3_coeff α β (k - 1) = 0 := by
      have hrel := hkS.1
      rw [hMmat] at hrel
      rw [hpowk] at hrel
      simp at hrel
      nlinarith
    have hcases : α = 0 ∨ β = 0 := by
      by_contra hnot
      push_neg at hnot
      have hcoeff_zero : putnam_2015_b3_coeff α β (k - 1) = 0 := by
        have hfac : 8 * β ^ 2 ≠ 0 := by
          nlinarith [sq_pos_of_ne_zero hnot.2]
        exact (mul_eq_zero.mp hqzero).resolve_left hfac
      have hkminus : 0 < k - 1 := by omega
      exact putnam_2015_b3_coeff_ne_zero_of_pos hnot.1 hnot.2 hkminus hcoeff_zero
    rcases hcases with hαzero | hβzero
    · right
      refine ⟨β, ?_, ?_, ?_, ?_⟩
      · simp [hMmat, putnam_2015_b3_mat, hαzero]
        ring
      · simp [hMmat, putnam_2015_b3_mat, hαzero]
      · simp [hMmat, putnam_2015_b3_mat, hαzero]
      · simp [hMmat, putnam_2015_b3_mat, hαzero]
        ring
    · left
      refine ⟨α, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hMmat, putnam_2015_b3_mat, hβzero]
  · rintro (⟨a, hconst⟩ | ⟨b, h00, h01, h10, h11⟩)
    · constructor
      · constructor
        · rw [hconst 0 1, hconst 0 0, hconst 1 0]
        · rw [hconst 1 0, hconst 0 1, hconst 1 1]
      · refine ⟨2, by norm_num, ?_⟩
        have hMconst : M = !![a, a; a, a] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [hconst]
        rw [hMconst]
        constructor
        · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
        · simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    · constructor
      · constructor
        · rw [h01, h00, h10]
          ring
        · rw [h10, h01, h11]
          ring
      · refine ⟨3, by norm_num, ?_⟩
        have hMcenter : M = !![b * -3, b * -1; b * 1, b * 3] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
        rw [hMcenter]
        constructor
        · simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
          ring
        · simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
          ring
