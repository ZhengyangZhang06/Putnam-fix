import Mathlib

open Polynomial Filter Topology Real Set Nat

-- (3 + √ 5) / 2
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
    Tendsto (fun n ↦ M n / (n : ℝ)) atTop (𝓝 (((3 + √ 5) / 2) : ℝ )) := by
  have choose_ineq_iff {n m : ℕ} (hn : 0 < n) (hmn : n < m) :
      ((m - 1).choose n < m.choose (n - 1)) ↔
        (m - n) * (m - n + 1) < m * n := by
    let C := (m - 1).choose (n - 1)
    have hnsub : n - 1 + 1 = n := by omega
    have hmsub : m - 1 + 1 = m := by omega
    have hsub : (m - 1) - (n - 1) = m - n := by omega
    have hsub2 : m - (n - 1) = m - n + 1 := by omega
    have hCpos : 0 < C := by
      dsimp [C]
      exact Nat.choose_pos (by omega)
    have hA : (m - 1).choose n * n = C * (m - n) := by
      have h := Nat.choose_succ_right_eq (m - 1) (n - 1)
      dsimp [C]
      simpa [hnsub, hsub] using h
    have hB : m.choose (n - 1) * (m - n + 1) = C * m := by
      have h := (Nat.choose_mul_succ_eq (m - 1) (n - 1)).symm
      dsimp [C]
      simpa [hmsub, hsub2] using h
    constructor
    · intro hlt
      have hmul1 : (m - 1).choose n * n < m.choose (n - 1) * n := by
        exact Nat.mul_lt_mul_of_pos_right hlt hn
      have hdpos : 0 < m - n + 1 := by omega
      have hmul2 : ((m - 1).choose n * n) * (m - n + 1) <
          (m.choose (n - 1) * n) * (m - n + 1) := by
        exact Nat.mul_lt_mul_of_pos_right hmul1 hdpos
      have hmul3 : C * ((m - n) * (m - n + 1)) < C * (m * n) := by
        calc
          C * ((m - n) * (m - n + 1)) =
              ((m - 1).choose n * n) * (m - n + 1) := by
            rw [hA]
            ring
          _ < (m.choose (n - 1) * n) * (m - n + 1) := hmul2
          _ = C * (m * n) := by
            rw [mul_assoc (m.choose (n - 1)) n (m - n + 1)]
            rw [mul_comm n (m - n + 1)]
            rw [← mul_assoc (m.choose (n - 1)) (m - n + 1) n]
            rw [hB]
            ring
      exact Nat.lt_of_mul_lt_mul_left hmul3
    · intro hquad
      have hmul : C * ((m - n) * (m - n + 1)) < C * (m * n) := by
        exact (Nat.mul_lt_mul_left hCpos).2 hquad
      have hmul2 :
          ((m - 1).choose n * n) * (m - n + 1) <
            (m.choose (n - 1) * n) * (m - n + 1) := by
        calc
          ((m - 1).choose n * n) * (m - n + 1) =
              C * ((m - n) * (m - n + 1)) := by
            rw [hA]
            ring
          _ < C * (m * n) := hmul
          _ = (m.choose (n - 1) * n) * (m - n + 1) := by
            rw [mul_assoc (m.choose (n - 1)) n (m - n + 1)]
            rw [mul_comm n (m - n + 1)]
            rw [← mul_assoc (m.choose (n - 1)) (m - n + 1) n]
            rw [hB]
            ring
      have hmul1 : (m - 1).choose n * n < m.choose (n - 1) * n := by
        exact Nat.lt_of_mul_lt_mul_right hmul2
      exact Nat.lt_of_mul_lt_mul_right hmul1
  have normalized_quad_neg {n m : ℕ} (hn : 0 < n) (hmn : n < m)
      (hq : (m - n) * (m - n + 1) < m * n) :
      ((m : ℝ) / (n : ℝ)) ^ 2 -
          (3 - ((n : ℝ)⁻¹)) * ((m : ℝ) / (n : ℝ)) +
            (1 - ((n : ℝ)⁻¹)) < 0 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hpoly :
        ((m : ℝ) - (n : ℝ)) * ((m : ℝ) - (n : ℝ) + 1) < (m : ℝ) * (n : ℝ) := by
      have hqR : (((m - n) * (m - n + 1) : ℕ) : ℝ) < ((m * n : ℕ) : ℝ) := by
        exact_mod_cast hq
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (le_of_lt hmn)] using hqR
    have hpoly2 :
        (m : ℝ) ^ 2 - (3 * (n : ℝ) - 1) * (m : ℝ) + ((n : ℝ) ^ 2 - (n : ℝ)) < 0 := by
      nlinarith
    field_simp [hnne]
    nlinarith
  have normalized_quad_nonneg {n m : ℕ} (hn : 0 < n) (hmn : n < m)
      (hq : m * n ≤ (m - n) * (m - n + 1)) :
      0 ≤ ((m : ℝ) / (n : ℝ)) ^ 2 -
          (3 - ((n : ℝ)⁻¹)) * ((m : ℝ) / (n : ℝ)) +
            (1 - ((n : ℝ)⁻¹)) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hpoly :
        (m : ℝ) * (n : ℝ) ≤ ((m : ℝ) - (n : ℝ)) * ((m : ℝ) - (n : ℝ) + 1) := by
      have hqR : ((m * n : ℕ) : ℝ) ≤ (((m - n) * (m - n + 1) : ℕ) : ℝ) := by
        exact_mod_cast hq
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (le_of_lt hmn)] using hqR
    have hpoly2 :
        0 ≤ (m : ℝ) ^ 2 - (3 * (n : ℝ) - 1) * (m : ℝ) + ((n : ℝ) ^ 2 - (n : ℝ)) := by
      nlinarith
    field_simp [hnne]
    nlinarith
  have root_upper {t x : ℝ} (ht1 : t ≤ 1)
      (hquad : x ^ 2 - (3 - t) * x + (1 - t) < 0) :
      x < (3 - t + √(5 - 2 * t + t ^ 2)) / 2 := by
    let s : ℝ := √(5 - 2 * t + t ^ 2)
    let l : ℝ := (3 - t - s) / 2
    let u : ℝ := (3 - t + s) / 2
    have hrad : 0 ≤ 5 - 2 * t + t ^ 2 := by
      nlinarith [sq_nonneg (t - 1)]
    have hlt_s : 1 - t < s := by
      dsimp [s]
      rw [Real.lt_sqrt (by linarith)]
      ring_nf
      norm_num
    have hl_lt_one : l < 1 := by
      dsimp [l]
      nlinarith
    have hfactor : x ^ 2 - (3 - t) * x + (1 - t) = (x - l) * (x - u) := by
      dsimp [l, u, s]
      ring_nf
      have hs_sq : (√(5 - t * 2 + t ^ 2)) ^ 2 = 5 - t * 2 + t ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (t - 1)]
      rw [hs_sq]
      ring
    have hprod : (x - l) * (x - u) < 0 := by
      rwa [← hfactor]
    by_contra hnot
    have hxu : 0 ≤ x - u := sub_nonneg.mpr (le_of_not_gt hnot)
    have hxl : 0 ≤ x - l := by linarith
    exact not_lt_of_ge (mul_nonneg hxl hxu) hprod
  have root_lower {t x : ℝ} (ht1 : t ≤ 1) (hx : 1 < x)
      (hquad : 0 ≤ x ^ 2 - (3 - t) * x + (1 - t)) :
      (3 - t + √(5 - 2 * t + t ^ 2)) / 2 ≤ x := by
    let s : ℝ := √(5 - 2 * t + t ^ 2)
    let l : ℝ := (3 - t - s) / 2
    let u : ℝ := (3 - t + s) / 2
    have hrad : 0 ≤ 5 - 2 * t + t ^ 2 := by
      nlinarith [sq_nonneg (t - 1)]
    have hlt_s : 1 - t < s := by
      dsimp [s]
      rw [Real.lt_sqrt (by linarith)]
      ring_nf
      norm_num
    have hl_lt_one : l < 1 := by
      dsimp [l]
      nlinarith
    have hfactor : x ^ 2 - (3 - t) * x + (1 - t) = (x - l) * (x - u) := by
      dsimp [l, u, s]
      ring_nf
      have hs_sq : (√(5 - t * 2 + t ^ 2)) ^ 2 = 5 - t * 2 + t ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (t - 1)]
      rw [hs_sq]
      ring
    by_contra hnot
    have hxu : x - u < 0 := sub_neg.mpr (lt_of_not_ge hnot)
    have hxl : 0 < x - l := by linarith
    have hprodneg : (x - l) * (x - u) < 0 := mul_neg_of_pos_of_neg hxl hxu
    have hprodnonneg : 0 ≤ (x - l) * (x - u) := by
      rwa [← hfactor]
    exact not_lt_of_ge hprodnonneg hprodneg
  have root_ge_one {t : ℝ} (ht1 : t ≤ 1) :
      1 ≤ (3 - t + √(5 - 2 * t + t ^ 2)) / 2 := by
    have hs_nonneg : 0 ≤ √(5 - 2 * t + t ^ 2) := Real.sqrt_nonneg _
    nlinarith
  let Uraw : ℕ → ℝ :=
    fun n ↦ (3 - ((n : ℝ)⁻¹) + √(5 - 2 * ((n : ℝ)⁻¹) + ((n : ℝ)⁻¹) ^ 2)) / 2
  let U : ℕ → ℝ := fun n ↦ if n = 0 then 0 else Uraw n
  let L : ℕ → ℝ := fun n ↦ if n = 0 then 0 else Uraw n - ((n : ℝ)⁻¹)
  have upper_bound : (fun n ↦ (M n : ℝ) / (n : ℝ)) ≤ U := by
    intro n
    by_cases hn0 : n = 0
    · simp [U, hn0]
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have ht1 : ((n : ℝ)⁻¹) ≤ 1 := by
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        exact inv_le_one_of_one_le₀ hn1
      have hgreat := hM n hn
      have hn_mem :
          n ∈ {m | 0 < m ∧ (m - 1).choose n < m.choose (n - 1)} := by
        constructor
        · exact hn
        · have hzero : (n - 1).choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [hzero]
          exact Nat.choose_pos (by omega)
      have hMn_ge : n ≤ M n := hgreat.2 hn_mem
      have hU_ge_one : 1 ≤ Uraw n := by
        simpa [Uraw] using root_ge_one ht1
      have htarget : (M n : ℝ) / (n : ℝ) ≤ Uraw n := by
        by_cases hstrict : n < M n
        · have hquadNat :
              (M n - n) * (M n - n + 1) < M n * n :=
            (choose_ineq_iff hn hstrict).1 hgreat.1.2
          have hquad :=
            normalized_quad_neg hn hstrict hquadNat
          exact le_of_lt (by
            simpa [Uraw] using
              root_upper (t := ((n : ℝ)⁻¹)) (x := (M n : ℝ) / (n : ℝ)) ht1 hquad)
        · have hMn_le : M n ≤ n := le_of_not_gt hstrict
          have hxle1 : (M n : ℝ) / (n : ℝ) ≤ 1 := by
            rw [div_le_one hnpos]
            exact_mod_cast hMn_le
          exact le_trans hxle1 hU_ge_one
      simpa [U, hn0] using htarget
  have lower_bound : L ≤ (fun n ↦ (M n : ℝ) / (n : ℝ)) := by
    intro n
    by_cases hn0 : n = 0
    · simp [L, hn0]
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have ht1 : ((n : ℝ)⁻¹) ≤ 1 := by
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        exact inv_le_one_of_one_le₀ hn1
      have hgreat := hM n hn
      have hn_mem :
          n ∈ {m | 0 < m ∧ (m - 1).choose n < m.choose (n - 1)} := by
        constructor
        · exact hn
        · have hzero : (n - 1).choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [hzero]
          exact Nat.choose_pos (by omega)
      have hMn_ge : n ≤ M n := hgreat.2 hn_mem
      have hnot_mem_succ :
          M n + 1 ∉ {m | 0 < m ∧ (m - 1).choose n < m.choose (n - 1)} := by
        intro hmem
        have hle := hgreat.2 hmem
        omega
      have hmn_succ : n < M n + 1 := by omega
      have hnotineq :
          ¬ ((M n + 1 - 1).choose n < (M n + 1).choose (n - 1)) := by
        intro hlt
        exact hnot_mem_succ ⟨by omega, hlt⟩
      have hnotquad :
          ¬ ((M n + 1 - n) * (M n + 1 - n + 1) < (M n + 1) * n) := by
        intro hq
        exact hnotineq ((choose_ineq_iff hn hmn_succ).2 hq)
      have hquadNat :
          (M n + 1) * n ≤ (M n + 1 - n) * (M n + 1 - n + 1) :=
        le_of_not_gt hnotquad
      have hquad :=
        normalized_quad_nonneg hn hmn_succ hquadNat
      have hxgt : 1 < ((M n + 1 : ℕ) : ℝ) / (n : ℝ) := by
        rw [one_lt_div hnpos]
        exact_mod_cast hmn_succ
      have hU_le_succ : Uraw n ≤ ((M n + 1 : ℕ) : ℝ) / (n : ℝ) := by
        simpa [Uraw] using
          root_lower (t := ((n : ℝ)⁻¹)) (x := ((M n + 1 : ℕ) : ℝ) / (n : ℝ))
            ht1 hxgt hquad
      have hlower_raw : Uraw n - ((n : ℝ)⁻¹) ≤ (M n : ℝ) / (n : ℝ) := by
        calc
          Uraw n - ((n : ℝ)⁻¹) ≤
              ((M n + 1 : ℕ) : ℝ) / (n : ℝ) - ((n : ℝ)⁻¹) :=
            sub_le_sub_right hU_le_succ _
          _ = (M n : ℝ) / (n : ℝ) := by
            field_simp [hnne]
            norm_num
      simpa [L, hn0] using hlower_raw
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hUraw_tendsto : Tendsto Uraw atTop (𝓝 (((3 + √5) / 2) : ℝ)) := by
    dsimp [Uraw]
    have htwoinv :
        Tendsto (fun n : ℕ ↦ (2 : ℝ) * ((n : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      simpa using hinv.const_mul (2 : ℝ)
    have hfive_minus :
        Tendsto (fun n : ℕ ↦ (5 : ℝ) - (2 : ℝ) * ((n : ℝ)⁻¹)) atTop (𝓝 (5 : ℝ)) := by
      simpa using htwoinv.const_sub (5 : ℝ)
    have hinv_sq :
        Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using hinv.pow 2
    have hradlim :
        Tendsto
          (fun n : ℕ ↦ (5 : ℝ) - (2 : ℝ) * ((n : ℝ)⁻¹) + ((n : ℝ)⁻¹) ^ 2)
          atTop (𝓝 (5 : ℝ)) := by
      simpa using hfive_minus.add hinv_sq
    have hsqrtlim :
        Tendsto
          (fun n : ℕ ↦ √((5 : ℝ) - (2 : ℝ) * ((n : ℝ)⁻¹) + ((n : ℝ)⁻¹) ^ 2))
          atTop (𝓝 (√(5 : ℝ))) := by
      simpa using hradlim.sqrt
    have hthree_minus :
        Tendsto (fun n : ℕ ↦ (3 : ℝ) - ((n : ℝ)⁻¹)) atTop (𝓝 (3 : ℝ)) := by
      simpa using hinv.const_sub (3 : ℝ)
    have hnum :
        Tendsto
          (fun n : ℕ ↦
            (3 : ℝ) - ((n : ℝ)⁻¹) +
              √((5 : ℝ) - (2 : ℝ) * ((n : ℝ)⁻¹) + ((n : ℝ)⁻¹) ^ 2))
          atTop (𝓝 ((3 : ℝ) + √(5 : ℝ))) := by
      simpa using hthree_minus.add hsqrtlim
    simpa [div_eq_mul_inv] using hnum.mul_const ((2 : ℝ)⁻¹)
  have hU_event : Uraw =ᶠ[atTop] U := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    simp [U, hn0]
  have hU_tendsto : Tendsto U atTop (𝓝 (((3 + √5) / 2) : ℝ)) :=
    Filter.Tendsto.congr' hU_event hUraw_tendsto
  have hLraw_tendsto :
      Tendsto (fun n : ℕ ↦ Uraw n - ((n : ℝ)⁻¹)) atTop (𝓝 (((3 + √5) / 2) : ℝ)) := by
    simpa using hUraw_tendsto.sub hinv
  have hL_event : (fun n : ℕ ↦ Uraw n - ((n : ℝ)⁻¹)) =ᶠ[atTop] L := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    simp [L, hn0]
  have hL_tendsto : Tendsto L atTop (𝓝 (((3 + √5) / 2) : ℝ)) :=
    Filter.Tendsto.congr' hL_event hLraw_tendsto
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le hL_tendsto hU_tendsto lower_bound upper_bound
