import Mathlib

open Topology Filter Nat

noncomputable abbrev putnam_2014_a3_solution : ℝ := 3 / 7

/--
Let \( a_0 = \frac{5}{2} \) and \( a_k = a_{k-1}^2 - 2 \) for \( k \geq 1 \). Compute \( \prod_{k=0}^{\infty} \left(1 - \frac{1}{a_k}\right) \) in closed form.
-/
theorem putnam_2014_a3
(a : ℕ → ℝ)
(a0 : a 0 = 5 / 2)
(ak : ∀ k ≥ 1, a k = (a (k - 1)) ^ 2 - 2)
: Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, (1 - 1 / a k)) atTop (𝓝 putnam_2014_a3_solution) :=
by
  have ha : ∀ k, a k = (1 / 2 : ℝ) ^ (2 ^ k) + ((1 / 2 : ℝ) ^ (2 ^ k))⁻¹ := by
    intro k
    induction k with
    | zero =>
        norm_num [a0]
    | succ k ih =>
        have hak : a (k + 1) = (a k) ^ 2 - 2 := by
          have := ak (k + 1) (by omega)
          simpa using this
        rw [hak, ih]
        set x : ℝ := (1 / 2 : ℝ) ^ (2 ^ k)
        have hxne : x ≠ 0 := by
          dsimp [x]
          positivity
        have hpow : (1 / 2 : ℝ) ^ (2 ^ (k + 1)) = x ^ 2 := by
          dsimp [x]
          rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [pow_succ]]
          rw [pow_mul]
        rw [hpow]
        field_simp [hxne]
        ring
  have hfactor :
      ∀ k,
        1 - 1 / a k =
          (1 + (1 / 2 : ℝ) ^ (3 * 2 ^ k)) /
            ((1 + (1 / 2 : ℝ) ^ (2 ^ k)) *
              (1 + (1 / 2 : ℝ) ^ (2 ^ (k + 1)))) := by
    intro k
    set x : ℝ := (1 / 2 : ℝ) ^ (2 ^ k)
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hpow2 : (1 / 2 : ℝ) ^ (2 ^ (k + 1)) = x ^ 2 := by
      dsimp [x]
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [pow_succ]]
      rw [pow_mul]
    have hpow3 : (1 / 2 : ℝ) ^ (3 * 2 ^ k) = x ^ 3 := by
      rw [mul_comm]
      dsimp [x]
      rw [pow_mul]
    rw [ha k, hpow2, hpow3]
    dsimp [x]
    field_simp [hxne]
    ring
  have geom :
      ∀ m n : ℕ,
        (1 - (1 / 2 : ℝ) ^ m) ≠ 0 →
          (∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (m * 2 ^ k))) =
            (1 - (1 / 2 : ℝ) ^ (m * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ m) := by
    intro m n hden
    induction n with
    | zero =>
        field_simp [hden]
        simp
    | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        have hpow :
            (1 / 2 : ℝ) ^ (m * 2 ^ (n + 1)) =
              ((1 / 2 : ℝ) ^ (m * 2 ^ n)) ^ 2 := by
          rw [show m * 2 ^ (n + 1) = (m * 2 ^ n) * 2 by
            rw [pow_succ]
            ring]
          rw [pow_mul]
        rw [hpow]
        field_simp [hden]
        ring
  have hprod :
      ∀ n,
        (∏ k ∈ Finset.range n, (1 - 1 / a k)) =
          ((1 - (1 / 2 : ℝ) ^ (3 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 3)) /
            (((1 - (1 / 2 : ℝ) ^ (2 ^ n)) / (1 - (1 / 2 : ℝ))) *
              ((1 - (1 / 2 : ℝ) ^ (2 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 2))) := by
    intro n
    have hgeom3 :
        (∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (3 * 2 ^ k))) =
          (1 - (1 / 2 : ℝ) ^ (3 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 3) := by
      simpa using geom 3 n (by norm_num)
    have hgeom1 :
        (∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (2 ^ k))) =
          (1 - (1 / 2 : ℝ) ^ (2 ^ n)) / (1 - (1 / 2 : ℝ)) := by
      simpa using geom 1 n (by norm_num)
    have hgeom2 :
        (∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (2 ^ (k + 1)))) =
          (1 - (1 / 2 : ℝ) ^ (2 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 2) := by
      calc
        (∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (2 ^ (k + 1))))
            = ∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (2 * 2 ^ k)) := by
              apply Finset.prod_congr rfl
              intro k hk
              congr 2
              rw [show 2 ^ (k + 1) = 2 * 2 ^ k by
                rw [pow_succ]
                ring]
        _ = (1 - (1 / 2 : ℝ) ^ (2 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 2) := by
              simpa using geom 2 n (by norm_num)
    calc
      (∏ k ∈ Finset.range n, (1 - 1 / a k))
          = ∏ k ∈ Finset.range n,
              (1 + (1 / 2 : ℝ) ^ (3 * 2 ^ k)) /
                ((1 + (1 / 2 : ℝ) ^ (2 ^ k)) *
                  (1 + (1 / 2 : ℝ) ^ (2 ^ (k + 1)))) := by
            apply Finset.prod_congr rfl
            intro k hk
            exact hfactor k
      _ = (∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (3 * 2 ^ k))) /
            ((∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (2 ^ k))) *
              (∏ k ∈ Finset.range n, (1 + (1 / 2 : ℝ) ^ (2 ^ (k + 1))))) := by
            rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
      _ = ((1 - (1 / 2 : ℝ) ^ (3 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 3)) /
            (((1 - (1 / 2 : ℝ) ^ (2 ^ n)) / (1 - (1 / 2 : ℝ))) *
              ((1 - (1 / 2 : ℝ) ^ (2 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 2))) := by
            rw [hgeom3, hgeom1, hgeom2]
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((1 - (1 / 2 : ℝ) ^ (3 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 3)) /
            (((1 - (1 / 2 : ℝ) ^ (2 ^ n)) / (1 - (1 / 2 : ℝ))) *
              ((1 - (1 / 2 : ℝ) ^ (2 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 2))))
        atTop (𝓝 (3 / 7)) := by
    have h2pow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (2 ^ n)) atTop (𝓝 0) := by
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have h3pow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (3 * 2 ^ n)) atTop (𝓝 0) := by
      have h :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by positivity : 0 ≤ ((1 / 2 : ℝ) ^ 3))
          (by norm_num : ((1 / 2 : ℝ) ^ 3) < 1)).comp
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
      simpa [pow_mul] using h
    have h22pow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (2 * 2 ^ n)) atTop (𝓝 0) := by
      have h :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by positivity : 0 ≤ ((1 / 2 : ℝ) ^ 2))
          (by norm_num : ((1 / 2 : ℝ) ^ 2) < 1)).comp
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
      simpa [pow_mul] using h
    have hA :
        Tendsto
          (fun n : ℕ => (1 - (1 / 2 : ℝ) ^ (3 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 3))
          atTop (𝓝 ((1 - 0) / (1 - (1 / 2 : ℝ) ^ 3))) := by
      exact (tendsto_const_nhds.sub h3pow).div_const _
    have hB :
        Tendsto
          (fun n : ℕ => (1 - (1 / 2 : ℝ) ^ (2 ^ n)) / (1 - (1 / 2 : ℝ)))
          atTop (𝓝 ((1 - 0) / (1 - (1 / 2 : ℝ)))) := by
      exact (tendsto_const_nhds.sub h2pow).div_const _
    have hC :
        Tendsto
          (fun n : ℕ => (1 - (1 / 2 : ℝ) ^ (2 * 2 ^ n)) / (1 - (1 / 2 : ℝ) ^ 2))
          atTop (𝓝 ((1 - 0) / (1 - (1 / 2 : ℝ) ^ 2))) := by
      exact (tendsto_const_nhds.sub h22pow).div_const _
    have h := hA.div (hB.mul hC) (by norm_num)
    convert h using 1
    norm_num
  simpa [putnam_2014_a3_solution] using
    hlim.congr' (Filter.Eventually.of_forall fun n => (hprod n).symm)
