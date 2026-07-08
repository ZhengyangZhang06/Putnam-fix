import Mathlib

open Topology Filter Set

noncomputable abbrev putnam_2019_b2_solution : ℝ := 8 / Real.pi ^ 3

private noncomputable def putnam_2019_b2_term (n : ℕ) (k : ℤ) : ℝ :=
  Real.sin ((2*k - 1)*Real.pi/(2*n))/((Real.cos ((k - 1)*Real.pi/(2*n))^2)*(Real.cos (k*Real.pi/(2*n))^2))

private noncomputable def putnam_2019_b2_sum (n : ℕ) : ℝ :=
  ∑ k : Set.Icc (1 : ℤ) (n - 1), putnam_2019_b2_term n k

private lemma putnam_2019_b2_trig (a b : ℝ)
    (hca : Real.cos a ≠ 0) (hcb : Real.cos b ≠ 0)
    (hs : Real.sin (b - a) ≠ 0) :
    Real.sin (a + b) / (Real.cos a ^ 2 * Real.cos b ^ 2) =
      (Real.tan b ^ 2 - Real.tan a ^ 2) / Real.sin (b - a) := by
  rw [eq_div_iff hs]
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hca, hcb]
  rw [Real.sin_add, Real.sin_sub]
  ring

private lemma putnam_2019_b2_sum_div_eval {n : ℕ} (hn : 2 ≤ n) :
    putnam_2019_b2_sum n / (n : ℝ) ^ 3 =
      Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        (((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) ^ 3) := by
  let x : ℝ := Real.pi / (2 * (n : ℝ))
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnR : (n : ℝ) ≠ 0 := hnRpos.ne'
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hnx : (n : ℝ) * x = Real.pi / 2 := by
    dsimp [x]
    field_simp [hnR]
  have hxlt_half : x < Real.pi / 2 := by
    have hn_gt_one : (1 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
    have h := mul_lt_mul_of_pos_right hn_gt_one hxpos
    simpa [one_mul, hnx] using h
  have hxlt_pi : x < Real.pi := by linarith [hxlt_half, Real.pi_pos]
  have hsinx_pos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hxlt_pi
  have hsinx : Real.sin x ≠ 0 := hsinx_pos.ne'
  have hcosx : Real.cos x ≠ 0 := by
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt_half⟩).ne'
  have hangle_lt (m : ℕ) (hm : m < n) : (m : ℝ) * x < Real.pi / 2 := by
    have hmR : (m : ℝ) < n := by exact_mod_cast hm
    have h := mul_lt_mul_of_pos_right hmR hxpos
    simpa [hnx] using h
  have hangle_nonneg (m : ℕ) : 0 ≤ (m : ℝ) * x := by
    exact mul_nonneg (Nat.cast_nonneg m) hxpos.le
  have hcos_angle (m : ℕ) (hm : m < n) : Real.cos ((m : ℝ) * x) ≠ 0 := by
    have hlt := hangle_lt m hm
    have hnon := hangle_nonneg m
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hnon], hlt⟩).ne'
  have hsubtype : putnam_2019_b2_sum n =
      ∑ k ∈ Finset.Icc (1 : ℤ) (n - 1), putnam_2019_b2_term n k := by
    unfold putnam_2019_b2_sum
    symm
    exact Finset.sum_subtype (Finset.Icc (1 : ℤ) (n - 1))
      (by intro y; simp [Finset.mem_Icc]) (putnam_2019_b2_term n)
  have hreindex : (∑ k ∈ Finset.Icc (1 : ℤ) (n - 1), putnam_2019_b2_term n k) =
      ∑ i ∈ Finset.range (n - 1), putnam_2019_b2_term n (i + 1 : ℤ) := by
    rw [Int.Icc_eq_finset_map]
    rw [Finset.sum_map]
    simp [add_comm]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n - 1)) :
      putnam_2019_b2_term n (i + 1 : ℤ) =
        (Real.tan (((i + 1 : ℕ) : ℝ) * x) ^ 2 - Real.tan ((i : ℝ) * x) ^ 2) / Real.sin x := by
    have hi_lt_pred : i < n - 1 := Finset.mem_range.mp hi
    have hi1_lt_n : i + 1 < n := by omega
    have hi_lt_n : i < n := by omega
    have hca : Real.cos ((i : ℝ) * x) ≠ 0 := hcos_angle i hi_lt_n
    have hcb : Real.cos (((i + 1 : ℕ) : ℝ) * x) ≠ 0 := hcos_angle (i + 1) hi1_lt_n
    have hsub : (((i + 1 : ℕ) : ℝ) * x - (i : ℝ) * x) = x := by
      norm_num
      ring
    have hs : Real.sin ((((i + 1 : ℕ) : ℝ) * x - (i : ℝ) * x)) ≠ 0 := by
      rw [hsub]
      exact hsinx
    have htrig := putnam_2019_b2_trig ((i : ℝ) * x) (((i + 1 : ℕ) : ℝ) * x) hca hcb hs
    calc
      putnam_2019_b2_term n (i + 1 : ℤ) =
          Real.sin (((i : ℝ) * x) + (((i + 1 : ℕ) : ℝ) * x)) /
            (Real.cos ((i : ℝ) * x) ^ 2 * Real.cos (((i + 1 : ℕ) : ℝ) * x) ^ 2) := by
        dsimp [putnam_2019_b2_term, x]
        norm_num [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
        ring_nf
      _ = (Real.tan (((i + 1 : ℕ) : ℝ) * x) ^ 2 - Real.tan ((i : ℝ) * x) ^ 2) /
            Real.sin ((((i + 1 : ℕ) : ℝ) * x - (i : ℝ) * x)) := htrig
      _ = (Real.tan (((i + 1 : ℕ) : ℝ) * x) ^ 2 - Real.tan ((i : ℝ) * x) ^ 2) / Real.sin x := by
        rw [hsub]
  let f : ℕ → ℝ := fun m => Real.tan ((m : ℝ) * x) ^ 2
  have hsum : putnam_2019_b2_sum n = (f (n - 1) - f 0) / Real.sin x := by
    rw [hsubtype, hreindex]
    calc
      (∑ i ∈ Finset.range (n - 1), putnam_2019_b2_term n (i + 1 : ℤ)) =
          ∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) / Real.sin x := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa [f] using hterm i hi
      _ = (∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i)) / Real.sin x := by
        rw [Finset.sum_div]
      _ = (f (n - 1) - f 0) / Real.sin x := by
        rw [Finset.sum_range_sub]
  have hlast_angle : (((n - 1 : ℕ) : ℝ) * x) = Real.pi / 2 - x := by
    have hn1 : 1 ≤ n := by omega
    rw [Nat.cast_sub hn1]
    norm_num
    calc
      ((n : ℝ) - 1) * x = (n : ℝ) * x - x := by ring
      _ = Real.pi / 2 - x := by rw [hnx]
  have htanlast : Real.tan (((n - 1 : ℕ) : ℝ) * x) = (Real.tan x)⁻¹ := by
    rw [hlast_angle, Real.tan_pi_div_two_sub]
  have hsum_cos : putnam_2019_b2_sum n = Real.cos x ^ 2 / Real.sin x ^ 3 := by
    rw [hsum]
    simp [f]
    rw [htanlast]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hsinx, hcosx]
  calc
    putnam_2019_b2_sum n / (n : ℝ) ^ 3 = (Real.cos x ^ 2 / Real.sin x ^ 3) / (n : ℝ) ^ 3 := by
      rw [hsum_cos]
    _ = Real.cos x ^ 2 / (((n : ℝ) * Real.sin x) ^ 3) := by
      field_simp [hsinx, hnR]
    _ = Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        (((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) ^ 3) := by
      dsimp [x]

private lemma putnam_2019_b2_sin_div_limit :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h := (Real.hasDerivAt_sin (0 : ℝ)).tendsto_slope_zero
  simpa [Real.sin_zero, Real.cos_zero, div_eq_inv_mul, add_comm] using h

private lemma putnam_2019_b2_n_sin_limit :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) atTop
      (𝓝 (Real.pi / 2)) := by
  let x : ℕ → ℝ := fun n => Real.pi / (2 * (n : ℝ))
  have hx : Tendsto x atTop (𝓝 0) := by
    simpa [x, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.pi / 2))
  have hx' : Tendsto x atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hx, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    exact div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num) hnR)
  have hratio : Tendsto (fun n : ℕ => Real.sin (x n) / x n) atTop (𝓝 1) :=
    putnam_2019_b2_sin_div_limit.comp hx'
  have hnx : Tendsto (fun n : ℕ => (n : ℝ) * x n) atTop (𝓝 (Real.pi / 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    dsimp [x]
    field_simp [hnR]
  have hprod : Tendsto (fun n : ℕ => (Real.sin (x n) / x n) * ((n : ℝ) * x n)) atTop
      (𝓝 (Real.pi / 2)) := by
    simpa using hratio.mul hnx
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hxne : x n ≠ 0 := by
    dsimp [x]
    exact div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num) hnR)
  calc
    (Real.sin (x n) / x n) * ((n : ℝ) * x n) = (n : ℝ) * Real.sin (x n) := by
      field_simp [hxne]
    _ = (n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ))) := by
      dsimp [x]

private lemma putnam_2019_b2_limit :
    Tendsto (fun n : ℕ => Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
      (((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) ^ 3)) atTop
      (𝓝 putnam_2019_b2_solution) := by
  have hx : Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.pi / 2))
  have hcos : Tendsto (fun n : ℕ => Real.cos (Real.pi / (2 * (n : ℝ)))) atTop (𝓝 1) := by
    simpa [Real.cos_zero] using (Real.continuous_cos.tendsto 0).comp hx
  have hlim0 : Tendsto (fun n : ℕ => Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
      (((n : ℝ) * Real.sin (Real.pi / (2 * (n : ℝ)))) ^ 3)) atTop
      (𝓝 (1 ^ 2 / ((Real.pi / 2) ^ 3))) := by
    exact (hcos.pow 2).div (putnam_2019_b2_n_sin_limit.pow 3)
      (pow_ne_zero 3 (div_ne_zero Real.pi_ne_zero (by norm_num)))
  convert hlim0 using 1
  unfold putnam_2019_b2_solution
  field_simp [Real.pi_ne_zero]
  ring_nf

/--
For all $n \geq 1$, let
\[
a_n = \sum_{k=1}^{n-1} \frac{\sin \left( \frac{(2k-1)\pi}{2n} \right)}{\cos^2 \left( \frac{(k-1)\pi}{2n} \right) \cos^2 \left( \frac{k\pi}{2n} \right)}.
\]
Determine
\[
\lim_{n \to \infty} \frac{a_n}{n^3}.
\]
-/
theorem putnam_2019_b2
(a : ℕ → ℝ)
(ha : a = fun n : ℕ => ∑ k : Icc (1 : ℤ) (n - 1),
Real.sin ((2*k - 1)*Real.pi/(2*n))/((Real.cos ((k - 1)*Real.pi/(2*n))^2)*(Real.cos (k*Real.pi/(2*n))^2)))
: Tendsto (fun n : ℕ => (a n)/n^3) atTop (𝓝 putnam_2019_b2_solution) :=
by
  rw [ha]
  change Tendsto (fun n : ℕ => putnam_2019_b2_sum n / (n : ℝ) ^ 3) atTop
    (𝓝 putnam_2019_b2_solution)
  refine Filter.Tendsto.congr' ?_ putnam_2019_b2_limit
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  exact (putnam_2019_b2_sum_div_eval hn).symm
