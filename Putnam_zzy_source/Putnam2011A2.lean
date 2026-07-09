import Mathlib

open Topology Filter

noncomputable abbrev putnam_2011_a2_solution : ℝ := 3 / 2

/--
Let $a_1,a_2,\dots$ and $b_1,b_2,\dots$ be sequences of positive real numbers such that $a_1 = b_1 = 1$ and $b_n = b_{n-1} a_n - 2$ for$n=2,3,\dots$. Assume that the sequence $(b_j)$ is bounded. Prove tha \[ S = \sum_{n=1}^\infty \frac{1}{a_1...a_n} \] converges, and evaluate $S$.
-/
theorem putnam_2011_a2
(a b : ℕ → ℝ)
(habn : ∀ n : ℕ, a n > 0 ∧ b n > 0)
(hab1 : a 0 = 1 ∧ b 0 = 1)
(hb : ∀ n ≥ 1, b n = b (n-1) * a n - 2)
(hbnd : ∃ B : ℝ, ∀ n : ℕ, |b n| ≤ B)
: Tendsto (fun n => ∑ i : Fin n, 1/(∏ j : Fin (i + 1), (a j))) atTop (𝓝 putnam_2011_a2_solution) :=
by
  classical
  let P : ℕ → ℝ := fun n => ∏ j : Fin (n + 1), a j
  let c : ℕ → ℝ := fun n => b n / P n
  have hP_pos : ∀ n : ℕ, 0 < P n := by
    intro n
    dsimp [P]
    exact Finset.prod_pos (fun j _ => (habn j).1)
  have hP_succ : ∀ n : ℕ, P (n + 1) = P n * a (n + 1) := by
    intro n
    dsimp [P]
    simpa using
      (Fin.prod_univ_castSucc (n := n + 1) (f := fun j : Fin ((n + 1) + 1) => a j))
  have hP0 : P 0 = 1 := by
    dsimp [P]
    simp [hab1.1]
  have hc0 : c 0 = 1 := by
    dsimp [c]
    rw [hab1.2, hP0]
    norm_num
  have hc_next : ∀ n : ℕ, c n = (b (n + 1) + 2) / P (n + 1) := by
    intro n
    dsimp [c]
    rw [hP_succ n]
    have ha_ne : a (n + 1) ≠ 0 := ne_of_gt (habn (n + 1)).1
    have hP_ne : P n ≠ 0 := ne_of_gt (hP_pos n)
    have hbrec : b (n + 1) = b n * a (n + 1) - 2 := by
      simpa using hb (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    have hbplus : b (n + 1) + 2 = b n * a (n + 1) := by
      linarith
    rw [hbplus]
    field_simp [ha_ne, hP_ne]
  have hterm : ∀ n : ℕ, 1 / P (n + 1) = (c n - c (n + 1)) / 2 := by
    intro n
    rw [hc_next n]
    dsimp [c]
    ring
  rcases hbnd with ⟨B, hB⟩
  have hBge1 : 1 ≤ B := by
    have h := hB 0
    rw [hab1.2] at h
    simpa using h
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hBge1
  let q : ℝ := B / (B + 2)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hBpos.le (by linarith)
  have hq_lt_one : q < 1 := by
    dsimp [q]
    have hden : 0 < B + 2 := by linarith
    rw [div_lt_one hden]
    linarith
  have hc_nonneg : ∀ n : ℕ, 0 ≤ c n := by
    intro n
    dsimp [c]
    exact div_nonneg (le_of_lt (habn n).2) (le_of_lt (hP_pos n))
  have hc_step_le : ∀ n : ℕ, c (n + 1) ≤ q * c n := by
    intro n
    have hb_le_B : b (n + 1) ≤ B := (abs_le.mp (hB (n + 1))).2
    have hPp : 0 < P (n + 1) := hP_pos (n + 1)
    have hden : 0 < B + 2 := by linarith
    have h_alg : b (n + 1) / P (n + 1) ≤ q * ((b (n + 1) + 2) / P (n + 1)) := by
      dsimp [q]
      field_simp [hPp.ne', hden.ne']
      nlinarith
    calc
      c (n + 1) = b (n + 1) / P (n + 1) := rfl
      _ ≤ q * ((b (n + 1) + 2) / P (n + 1)) := h_alg
      _ = q * c n := by rw [hc_next n]
  have hc_le_pow : ∀ n : ℕ, c n ≤ q ^ n := by
    intro n
    induction n with
    | zero =>
        rw [hc0]
        norm_num
    | succ n ih =>
        calc
          c (n + 1) ≤ q * c n := hc_step_le n
          _ ≤ q * q ^ n := mul_le_mul_of_nonneg_left ih hq_nonneg
          _ = q ^ (n + 1) := by ring
  have hc_tendsto : Tendsto c atTop (𝓝 0) := by
    exact squeeze_zero hc_nonneg hc_le_pow
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one)
  have hsum : ∀ n : ℕ, (∑ i : Fin (n + 1), 1 / P i) = 3 / 2 - c n / 2 := by
    intro n
    induction n with
    | zero =>
        simp [hP0, hc0]
        norm_num
    | succ n ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih, hterm n]
        ring
  have hS_shift : Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), 1 / P i) atTop (𝓝 (3 / 2 : ℝ)) := by
    have hlim : Tendsto (fun n : ℕ => (3 : ℝ) / 2 - c n / 2) atTop (𝓝 ((3 : ℝ) / 2)) := by
      simpa using (tendsto_const_nhds.sub (hc_tendsto.div_const 2))
    exact Filter.Tendsto.congr' (Eventually.of_forall fun n => (hsum n).symm) hlim
  have hS : Tendsto (fun n : ℕ => ∑ i : Fin n, 1 / P i) atTop (𝓝 (3 / 2 : ℝ)) := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => ∑ i : Fin n, 1 / P i) (l := 𝓝 (3 / 2 : ℝ)) 1).mp hS_shift
  change Tendsto (fun n => ∑ i : Fin n, 1 / P i) atTop (𝓝 putnam_2011_a2_solution)
  simpa [putnam_2011_a2_solution] using hS
