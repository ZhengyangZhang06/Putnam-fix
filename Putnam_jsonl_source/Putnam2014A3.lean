import Mathlib

open Topology Filter Nat

-- 3 / 7
/--
Let \( a_0 = \frac{5}{2} \) and \( a_k = a_{k-1}^2 - 2 \) for \( k \geq 1 \). Compute \( \prod_{k=0}^{\infty} \left(1 - \frac{1}{a_k}\right) \) in closed form.
-/
theorem putnam_2014_a3
(a : ℕ → ℝ)
(a0 : a 0 = 5 / 2)
(ak : ∀ k ≥ 1, a k = (a (k - 1)) ^ 2 - 2)
: Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, (1 - 1 / a k)) atTop (𝓝 ((3 / 7) : ℝ )) := by
  let q : ℕ → ℝ := fun n => (2 : ℝ) ^ (2 ^ n)
  have hq_succ : ∀ n, q (n + 1) = (q n) ^ 2 := by
    intro n
    dsimp [q]
    norm_num [pow_succ, pow_mul]
  have hq_pos : ∀ n, 0 < q n := by
    intro n
    dsimp [q]
    positivity
  have hq_ne : ∀ n, q n ≠ 0 := fun n => (hq_pos n).ne'
  have hq_gt_one : ∀ n, 1 < q n := by
    intro n
    dsimp [q]
    simpa using (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2)
      (Nat.pow_pos (n := n) (by norm_num : 0 < 2)))
  have hq_sq_sub_ne : ∀ n, q n ^ 2 - 1 ≠ 0 := by
    intro n
    have h : 1 < q n := hq_gt_one n
    have hsq : 1 < q n ^ 2 := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr h)]
    nlinarith
  have hq_sq_add_ne : ∀ n, q n ^ 2 + 1 ≠ 0 := by
    intro n
    have hp : 0 < q n ^ 2 := sq_pos_of_pos (hq_pos n)
    nlinarith
  have ha : ∀ n, a n = q n + (q n)⁻¹ := by
    intro n
    induction n with
    | zero =>
        rw [a0]
        dsimp [q]
        norm_num
    | succ n ih =>
        rw [ak (n + 1) (by omega)]
        have hs : n + 1 - 1 = n := by omega
        rw [hs, ih, hq_succ]
        field_simp [hq_ne n]
        ring
  have hprod : ∀ n : ℕ,
      (∏ k ∈ Finset.range n, (1 - 1 / a k)) =
        3 * (q n ^ 2 + q n + 1) / (7 * (q n ^ 2 - 1)) := by
    intro n
    induction n with
    | zero =>
        dsimp [q]
        norm_num
    | succ n ih =>
        rw [Finset.prod_range_succ, ih, ha n, hq_succ]
        have hnext : (q n ^ 2) ^ 2 - 1 ≠ 0 := by
          rw [← hq_succ n]
          exact hq_sq_sub_ne (n + 1)
        have hnext' : q n ^ 4 - 1 ≠ 0 := by
          ring_nf at hnext ⊢
          exact hnext
        field_simp [hq_ne n, hq_sq_sub_ne n, hq_sq_add_ne n, hnext']
        ring_nf
  have hq_tendsto : Tendsto q atTop atTop := by
    simpa [q] using
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))))
  have hq2_tendsto : Tendsto (fun n => q n ^ 2) atTop atTop := by
    exact (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hq_tendsto
  have hq2sub_tendsto : Tendsto (fun n => q n ^ 2 - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hq2_tendsto
  have hq_inv_tendsto : Tendsto (fun n => (q n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    exact hq_tendsto.inv_tendsto_atTop
  have hq2_inv_tendsto : Tendsto (fun n => (q n ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    exact hq2_tendsto.inv_tendsto_atTop
  have hcorr_aux : Tendsto
      (fun n => ((q n)⁻¹ + 2 * (q n ^ 2)⁻¹) / (1 - (q n ^ 2)⁻¹))
      atTop (𝓝 (0 : ℝ)) := by
    have hnum : Tendsto (fun n => (q n)⁻¹ + 2 * (q n ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using hq_inv_tendsto.add (tendsto_const_nhds.mul hq2_inv_tendsto)
    have hden : Tendsto (fun n => 1 - (q n ^ 2)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hq2_inv_tendsto
    simpa using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hcorr : Tendsto (fun n => (q n + 2) / (q n ^ 2 - 1)) atTop (𝓝 (0 : ℝ)) := by
    refine hcorr_aux.congr' ?_
    exact Eventually.of_forall fun n => by
      symm
      field_simp [hq_ne n, hq_sq_sub_ne n]
  have hclosed : Tendsto
      (fun n => 3 * (q n ^ 2 + q n + 1) / (7 * (q n ^ 2 - 1)))
      atTop (𝓝 ((3 / 7) : ℝ)) := by
    have hscaled : Tendsto (fun n => (3 / 7 : ℝ) * ((q n + 2) / (q n ^ 2 - 1)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hcorr
    have hsum : Tendsto (fun n => (3 / 7 : ℝ) + (3 / 7 : ℝ) * ((q n + 2) / (q n ^ 2 - 1)))
        atTop (𝓝 ((3 / 7) : ℝ)) := by
      simpa using tendsto_const_nhds.add hscaled
    refine hsum.congr' ?_
    exact Eventually.of_forall fun n => by
      symm
      field_simp [hq_sq_sub_ne n]
      ring
  exact hclosed.congr' (Eventually.of_forall fun n => (hprod n).symm)
