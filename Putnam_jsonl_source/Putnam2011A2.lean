import Mathlib

open Topology Filter

-- 3/2
/--
Let $a_1,a_2,\dots$ and $b_1,b_2,\dots$ be sequences of positive real numbers such that $a_1 = b_1 = 1$ and $b_n = b_{n-1} a_n - 2$ for$n=2,3,\dots$. Assume that the sequence $(b_j)$ is bounded. Prove tha \[ S = \sum_{n=1}^\infty \frac{1}{a_1...a_n} \] converges, and evaluate $S$.
-/
theorem putnam_2011_a2
(a b : ℕ → ℝ)
(habn : ∀ n : ℕ, a n > 0 ∧ b n > 0)
(hab1 : a 0 = 1 ∧ b 0 = 1)
(hb : ∀ n ≥ 1, b n = b (n-1) * a n - 2)
(hbnd : ∃ B : ℝ, ∀ n : ℕ, |b n| ≤ B)
: Tendsto (fun n => ∑ i : Fin n, 1/(∏ j : Fin (i + 1), (a j))) atTop (𝓝 ((3/2) : ℝ )) := by
  let P : ℕ → ℝ := fun n => ∏ j ∈ Finset.range (n + 1), a j
  let F : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, 1 / P i
  have hPsucc : ∀ n, P (n + 1) = P n * a (n + 1) := by
    intro n
    simp [P, Finset.prod_range_succ]
  have hPpos : ∀ n, 0 < P n := by
    intro n
    dsimp [P]
    exact Finset.prod_pos (fun j _ => (habn j).1)
  have hDterm :
      ∀ n, 1 / P (n + 1) = b n / (2 * P n) - b (n + 1) / (2 * P (n + 1)) := by
    intro n
    have hbrec : b (n + 1) = b n * a (n + 1) - 2 := by
      simpa [Nat.add_sub_cancel] using hb (n + 1) (Nat.succ_pos n)
    have hps : P (n + 1) = P n * a (n + 1) := hPsucc n
    have hp0 : P n ≠ 0 := ne_of_gt (hPpos n)
    have hpn0 : P (n + 1) ≠ 0 := ne_of_gt (hPpos (n + 1))
    have ha0 : a (n + 1) ≠ 0 := ne_of_gt (habn (n + 1)).1
    field_simp [hps, hbrec, hp0, hpn0, ha0]
    rw [hbrec, hps]
    ring
  have hsum : ∀ n, F (n + 1) = (3 / 2 : ℝ) - b n / (2 * P n) := by
    intro n
    induction n with
    | zero =>
        simp [F, P, hab1]
        norm_num
    | succ n ih =>
        calc
          F (Nat.succ n + 1) = F (n + 1) + 1 / P (n + 1) := by
            simp [F, Finset.sum_range_succ, Nat.succ_eq_add_one, Nat.add_assoc]
          _ = ((3 / 2 : ℝ) - b n / (2 * P n)) +
              (b n / (2 * P n) - b (n + 1) / (2 * P (n + 1))) := by
            rw [ih, hDterm n]
          _ = (3 / 2 : ℝ) - b (Nat.succ n) / (2 * P (Nat.succ n)) := by
            simp [Nat.succ_eq_add_one]
  let D : ℕ → ℝ := fun n => P n / (b n + 2)
  have hDpos : ∀ n, 0 < D n := by
    intro n
    dsimp [D]
    exact div_pos (hPpos n) (by nlinarith [(habn n).2])
  have hDsucc : ∀ n, D (n + 1) = D n * ((b n + 2) / b n) := by
    intro n
    dsimp [D]
    have hbrec : b (n + 1) = b n * a (n + 1) - 2 := by
      simpa [Nat.add_sub_cancel] using hb (n + 1) (Nat.succ_pos n)
    have hbrec2 : b (n + 1) + 2 = b n * a (n + 1) := by nlinarith
    have hps : P (n + 1) = P n * a (n + 1) := hPsucc n
    have hb0 : b n ≠ 0 := ne_of_gt (habn n).2
    have hb20 : b n + 2 ≠ 0 := by nlinarith [(habn n).2]
    have hbn120 : b (n + 1) + 2 ≠ 0 := by nlinarith [(habn (n + 1)).2]
    have ha0 : a (n + 1) ≠ 0 := ne_of_gt (habn (n + 1)).1
    field_simp [hps, hbrec2, hb0, hb20, hbn120, ha0]
    rw [hps, hbrec2]
    ring
  rcases hbnd with ⟨B, hBabs⟩
  have hB1 : (1 : ℝ) ≤ B := by
    have h0 := hBabs 0
    simpa [hab1.2] using h0
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hble : ∀ n, b n ≤ B := by
    intro n
    exact (le_abs_self (b n)).trans (hBabs n)
  let r : ℝ := 1 + 2 / B
  have hr_gt : 1 < r := by
    dsimp [r]
    have hdiv : 0 < 2 / B := div_pos (by norm_num) hBpos
    linarith
  have hr_nonneg : 0 ≤ r := le_of_lt (lt_trans zero_lt_one hr_gt)
  have hfactor : ∀ n, r ≤ (b n + 2) / b n := by
    intro n
    have hbpos : 0 < b n := (habn n).2
    have h2 : 2 / B ≤ 2 / b n := div_le_div_of_nonneg_left (by norm_num) hbpos (hble n)
    have hb0 : b n ≠ 0 := ne_of_gt hbpos
    have hrewrite : (b n + 2) / b n = 1 + 2 / b n := by
      field_simp [hb0]
    dsimp [r]
    calc
      1 + 2 / B ≤ 1 + 2 / b n := by linarith
      _ = (b n + 2) / b n := hrewrite.symm
  have hD1 : D 1 = 1 := by
    have h : D 1 = (1 + 2 : ℝ)⁻¹ * (1 + 2) := by
      simpa [D, P, hab1] using hDsucc 0
    norm_num at h
    exact h
  have hDge : ∀ n, r ^ n ≤ D (n + 1) := by
    intro n
    induction n with
    | zero =>
        simp [hD1]
    | succ n ih =>
        calc
          r ^ Nat.succ n = r ^ n * r := by rw [pow_succ]
          _ ≤ D (n + 1) * ((b (n + 1) + 2) / b (n + 1)) := by
            exact mul_le_mul ih (hfactor (n + 1)) hr_nonneg (le_of_lt (hDpos (n + 1)))
          _ = D (Nat.succ n + 1) := by
            rw [← hDsucc (n + 1)]
  have hgeo0 : Tendsto (fun n : ℕ => 1 / (2 * r ^ n)) atTop (𝓝 (0 : ℝ)) := by
    have hpow : Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hr_gt
    have hinv : Tendsto (fun n : ℕ => (r ^ n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      hpow.inv_tendsto_atTop
    have hmul : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (r ^ n)⁻¹) atTop
        (𝓝 ((1 / 2 : ℝ) * 0)) := hinv.const_mul (1 / 2 : ℝ)
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hrem_shift : Tendsto (fun n : ℕ => b (n + 1) / (2 * P (n + 1))) atTop
      (𝓝 (0 : ℝ)) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg (le_of_lt (habn (n + 1)).2)
        (le_of_lt (mul_pos (by norm_num) (hPpos (n + 1))))
    · intro n
      have hbpos : 0 < b (n + 1) := (habn (n + 1)).2
      have hDnpos : 0 < D (n + 1) := hDpos (n + 1)
      have hP_eq : P (n + 1) = D (n + 1) * (b (n + 1) + 2) := by
        dsimp [D]
        have hb20 : b (n + 1) + 2 ≠ 0 := by nlinarith
        field_simp [hb20]
      have hfirst : b (n + 1) / (2 * P (n + 1)) ≤ 1 / (2 * D (n + 1)) := by
        have hPposn : 0 < P (n + 1) := hPpos (n + 1)
        have hD0 : D (n + 1) ≠ 0 := ne_of_gt hDnpos
        have hP0 : P (n + 1) ≠ 0 := ne_of_gt hPposn
        field_simp [hP0, hD0, hP_eq]
        nlinarith [mul_pos hDnpos hbpos]
      have hrpos : 0 < r ^ n := pow_pos (lt_trans zero_lt_one hr_gt) n
      have hdenle : 2 * r ^ n ≤ 2 * D (n + 1) := by
        exact mul_le_mul_of_nonneg_left (hDge n) (by norm_num)
      have hsecond : 1 / (2 * D (n + 1)) ≤ 1 / (2 * r ^ n) := by
        exact one_div_le_one_div_of_le (mul_pos (by norm_num) hrpos) hdenle
      exact hfirst.trans hsecond
    · exact hgeo0
  have hrem : Tendsto (fun n : ℕ => b n / (2 * P n)) atTop (𝓝 (0 : ℝ)) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrem_shift
  have hFshift : Tendsto (fun n : ℕ => F (n + 1)) atTop (𝓝 ((3 / 2 : ℝ))) := by
    have hlim : Tendsto (fun n : ℕ => (3 / 2 : ℝ) - b n / (2 * P n)) atTop
        (𝓝 ((3 / 2 : ℝ) - 0)) := tendsto_const_nhds.sub hrem
    simpa [hsum] using hlim
  have hF : Tendsto F atTop (𝓝 ((3 / 2 : ℝ))) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hFshift
  have htarget : (fun n => ∑ i : Fin n, 1 / (∏ j : Fin (i + 1), (a j))) = F := by
    funext n
    rw [Fin.sum_univ_eq_sum_range (fun i => 1 / (∏ j : Fin (i + 1), (a j))) n]
    apply Finset.sum_congr rfl
    intro i _
    have hprod : (∏ j : Fin (i + 1), (a j)) = P i := by
      dsimp [P]
      exact Fin.prod_univ_eq_prod_range a (i + 1)
    rw [hprod]
  rw [htarget]
  exact hF
