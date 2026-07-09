import Mathlib

open Polynomial Filter Topology Real Set Nat

noncomputable abbrev putnam_2016_a2_solution : ℝ := (3 + Real.sqrt 5) / 2

private lemma putnam_2016_a2_solution_poly :
    putnam_2016_a2_solution ^ 2 - 3 * putnam_2016_a2_solution + 1 = 0 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [putnam_2016_a2_solution]
  nlinarith

private lemma putnam_2016_a2_solution_gt_two : (2 : ℝ) < putnam_2016_a2_solution := by
  have hs : (1 : ℝ) < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
  dsimp [putnam_2016_a2_solution]
  nlinarith

private lemma putnam_2016_a2_solution_nonneg : (0 : ℝ) ≤ putnam_2016_a2_solution := by
  exact le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) putnam_2016_a2_solution_gt_two)

private lemma putnam_2016_a2_choose_lt_iff_quad {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    (m - 1).choose n < m.choose (n - 1) ↔
      (m - n) * (m - n + 1) < m * n := by
  have hm : 0 < m := hn.trans_le hnm
  set A := (m - 1).choose n
  set B := m.choose (n - 1)
  set C := (m - 1).choose (n - 1)
  set x := m - n
  set y := m - n + 1
  have hy : 0 < y := by omega
  have hny : 0 < n * y := Nat.mul_pos hn hy
  have hC : 0 < C := by
    have hle : n - 1 ≤ m - 1 := Nat.sub_le_sub_right hnm 1
    exact Nat.choose_pos hle
  have hA : A * n = C * x := by
    dsimp [A, C, x]
    have hnp : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    have hsub : (m - 1) - (n - 1) = m - n := by omega
    simpa [hnp, hsub] using Nat.choose_succ_right_eq (m - 1) (n - 1)
  have hB' : C * m = B * y := by
    dsimp [B, C, y]
    have hmp : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
    have hsub : m - (n - 1) = m - n + 1 := by omega
    simpa [hmp, hsub] using Nat.choose_mul_succ_eq (m - 1) (n - 1)
  have hB : B * y = C * m := hB'.symm
  have hleft : A * (n * y) = C * (x * y) := by
    calc
      A * (n * y) = (A * n) * y := by ac_rfl
      _ = (C * x) * y := by rw [hA]
      _ = C * (x * y) := by ac_rfl
  have hright : B * (n * y) = C * (m * n) := by
    calc
      B * (n * y) = (B * y) * n := by ac_rfl
      _ = (C * m) * n := by rw [hB]
      _ = C * (m * n) := by ac_rfl
  calc
    A < B ↔ A * (n * y) < B * (n * y) := (Nat.mul_lt_mul_right hny).symm
    _ ↔ C * (x * y) < C * (m * n) := by rw [hleft, hright]
    _ ↔ x * y < m * n := Nat.mul_lt_mul_left hC

private lemma putnam_2016_a2_self_mem {n : ℕ} (hn : 0 < n) :
    0 < n ∧ (n - 1).choose n < n.choose (n - 1) := by
  refine ⟨hn, ?_⟩
  have hleft : (n - 1).choose n = 0 := Nat.choose_eq_zero_of_lt (Nat.sub_lt hn zero_lt_one)
  have hright : 0 < n.choose (n - 1) := Nat.choose_pos (Nat.sub_le n 1)
  simpa [hleft] using hright

private lemma putnam_2016_a2_real_quad_of_le_solution_sub_one {n m : ℝ}
    (hn : 0 < n) (hnm : n ≤ m) (hm : m ≤ putnam_2016_a2_solution * n - 1) :
    (m - n) * (m - n + 1) < m * n := by
  set d := m - n
  have hd0 : 0 ≤ d := by linarith
  have hdup : d ≤ (putnam_2016_a2_solution - 1) * n - 1 := by
    rw [show d = m - n by rfl]
    nlinarith
  have hapos : 0 ≤ putnam_2016_a2_solution - 2 := by
    linarith [putnam_2016_a2_solution_gt_two]
  have hmul : d * (putnam_2016_a2_solution - 2) ≤
      ((putnam_2016_a2_solution - 1) * n - 1) * (putnam_2016_a2_solution - 2) := by
    exact mul_le_mul_of_nonneg_right hdup hapos
  have hcalc : ((putnam_2016_a2_solution - 1) * n - 1) *
      (putnam_2016_a2_solution - 2) = n - (putnam_2016_a2_solution - 2) := by
    nlinarith [putnam_2016_a2_solution_poly]
  have hdlt : d * (putnam_2016_a2_solution - 2) < n := by
    nlinarith
  have hlt : d * (putnam_2016_a2_solution - 1) < d + n := by
    nlinarith
  have hfactor : d + 1 ≤ (putnam_2016_a2_solution - 1) * n := by linarith
  have hmain : d * (d + 1) ≤ d * ((putnam_2016_a2_solution - 1) * n) := by
    exact mul_le_mul_of_nonneg_left hfactor hd0
  have hmain2 : d * ((putnam_2016_a2_solution - 1) * n) < m * n := by
    nlinarith
  linarith

private lemma putnam_2016_a2_nat_quad_of_upper {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hm : (m : ℝ) ≤ putnam_2016_a2_solution * (n : ℝ) - 1) :
    (m - n) * (m - n + 1) < m * n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hreal := putnam_2016_a2_real_quad_of_le_solution_sub_one hnR hnmR hm
  have hsub : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := by
    rw [Nat.cast_sub hnm]
  have hsub1 : ((m - n + 1 : ℕ) : ℝ) = (m : ℝ) - n + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hnm]
  have hcast : ((m - n : ℕ) : ℝ) * ((m - n + 1 : ℕ) : ℝ) <
      (m : ℝ) * (n : ℝ) := by
    simpa [hsub, hsub1] using hreal
  exact_mod_cast hcast

private lemma putnam_2016_a2_lower_candidate {n : ℕ} (hn : 0 < n) :
    let k := ⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ - 1
    n ≤ k ∧ (k - n) * (k - n + 1) < k * n := by
  intro k
  have hprod_nonneg : 0 ≤ putnam_2016_a2_solution * (n : ℝ) :=
    mul_nonneg putnam_2016_a2_solution_nonneg (by positivity)
  have hfloor2n : 2 * n ≤ ⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ := by
    rw [Nat.le_floor_iff hprod_nonneg]
    norm_num [Nat.cast_mul]
    nlinarith [putnam_2016_a2_solution_gt_two, show (0 : ℝ) ≤ n by positivity]
  have hge1 : 1 ≤ ⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ := by omega
  have hnle : n ≤ k := by
    dsimp [k]
    omega
  have hk_cast : (k : ℝ) = (⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ : ℝ) - 1 := by
    dsimp [k]
    rw [Nat.cast_sub hge1]
    norm_num
  have hfloor_le : (⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ : ℝ) ≤
      putnam_2016_a2_solution * (n : ℝ) := Nat.floor_le hprod_nonneg
  have hk_upper : (k : ℝ) ≤ putnam_2016_a2_solution * (n : ℝ) - 1 := by
    rw [hk_cast]
    linarith
  exact ⟨hnle, putnam_2016_a2_nat_quad_of_upper hn hnle hk_upper⟩

private lemma putnam_2016_a2_ratio_le_solution {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hq : (m - n) * (m - n + 1) < m * n) :
    (m : ℝ) / (n : ℝ) ≤ putnam_2016_a2_solution := by
  have hdle : (m - n) * (m - n) ≤ (m - n) * (m - n + 1) := by
    exact Nat.mul_le_mul_left (m - n) (Nat.le_succ (m - n))
  have hdlt_nat : (m - n) * (m - n) < m * n := lt_of_le_of_lt hdle hq
  have hdlt : ((m - n : ℕ) : ℝ) * ((m - n : ℕ) : ℝ) < (m : ℝ) * (n : ℝ) := by
    exact_mod_cast hdlt_nat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hm_eq : (m : ℝ) = ((m - n : ℕ) : ℝ) + n := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hnm]
  have hquad : ((m : ℝ) / (n : ℝ) - 1) ^ 2 < (m : ℝ) / (n : ℝ) := by
    field_simp [hnpos.ne']
    rw [hm_eq]
    nlinarith
  have hge_one : (1 : ℝ) ≤ (m : ℝ) / (n : ℝ) := by
    have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
    rw [le_div_iff₀ hnpos]
    simpa using hnmR
  by_contra hnot
  have hlt : putnam_2016_a2_solution < (m : ℝ) / (n : ℝ) := lt_of_not_ge hnot
  nlinarith [putnam_2016_a2_solution_poly, putnam_2016_a2_solution_gt_two,
    sq_nonneg ((m : ℝ) / (n : ℝ) - putnam_2016_a2_solution)]

private lemma putnam_2016_a2_lower_tendsto :
    Tendsto
      (fun n : ℕ ↦ ((⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ - 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 putnam_2016_a2_solution) := by
  have hfloor : Tendsto
      (fun n : ℕ ↦ (⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
      atTop (𝓝 putnam_2016_a2_solution) := by
    exact (tendsto_nat_floor_mul_div_atTop putnam_2016_a2_solution_nonneg).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    Filter.Tendsto.inv_tendsto_atTop
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hdiff : Tendsto
      (fun n : ℕ ↦ (⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ : ℝ) / (n : ℝ) - (n : ℝ)⁻¹)
      atTop (𝓝 putnam_2016_a2_solution) := by
    simpa using hfloor.sub hinv
  refine hdiff.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hprod_nonneg : 0 ≤ putnam_2016_a2_solution * (n : ℝ) :=
    mul_nonneg putnam_2016_a2_solution_nonneg (by positivity)
  have hfloor2n : 2 * n ≤ ⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ := by
    rw [Nat.le_floor_iff hprod_nonneg]
    norm_num [Nat.cast_mul]
    nlinarith [putnam_2016_a2_solution_gt_two, show (0 : ℝ) ≤ n by positivity]
  have hge1 : 1 ≤ ⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ := by omega
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_sub hge1]
  field_simp [hnne]
  norm_num

/--
Given a positive integer $n$, let $M(n)$ be the largest integer $m$ such that
\[
\binom{m}{n-1} > \binom{m-1}{n}.
\]
Evaluate
\[
\lim_{n \to \infty} \frac{M(n)}{n}.
\]
-/
theorem putnam_2016_a2
    (M : ℕ → ℕ)
    (hM : ∀ n > 0, IsGreatest {m | 0 < m ∧ (m - 1).choose n < m.choose (n - 1)} (M n)) :
    Tendsto (fun n ↦ M n / (n : ℝ)) atTop (𝓝 putnam_2016_a2_solution) :=
  by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' putnam_2016_a2_lower_tendsto
    tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    let k := ⌊putnam_2016_a2_solution * (n : ℝ)⌋₊ - 1
    have hk : n ≤ k ∧ (k - n) * (k - n + 1) < k * n :=
      putnam_2016_a2_lower_candidate hn
    have hk_mem : k ∈ {m | 0 < m ∧ (m - 1).choose n < m.choose (n - 1)} := by
      refine ⟨hn.trans_le hk.1, ?_⟩
      exact (putnam_2016_a2_choose_lt_iff_quad hn hk.1).mpr hk.2
    have hk_le_M : k ≤ M n := (hM n hn).2 hk_mem
    have hn_nonneg : (0 : ℝ) ≤ n := by positivity
    exact div_le_div_of_nonneg_right (by exact_mod_cast hk_le_M) hn_nonneg
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hgreat := hM n hn
    have hn_mem : n ∈ {m | 0 < m ∧ (m - 1).choose n < m.choose (n - 1)} :=
      putnam_2016_a2_self_mem hn
    have hnleM : n ≤ M n := hgreat.2 hn_mem
    have hM_mem : M n ∈ {m | 0 < m ∧ (m - 1).choose n < m.choose (n - 1)} := hgreat.1
    have hquad : (M n - n) * (M n - n + 1) < M n * n :=
      (putnam_2016_a2_choose_lt_iff_quad hn hnleM).mp hM_mem.2
    exact putnam_2016_a2_ratio_le_solution hn hnleM hquad
