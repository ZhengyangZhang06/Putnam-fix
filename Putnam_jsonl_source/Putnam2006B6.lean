import Mathlib

open Set Topology Filter

-- fun k => ((k+1)/k)^k
/--
Let $k$ be an integer greater than 1. Suppose $a_0 > 0$, and define \[ a_{n+1} = a_n + \frac{1}{\sqrt[k]{a_n}} \] for $n > 0$. Evaluate \[\lim_{n \to \infty} \frac{a_n^{k+1}}{n^k}.\]
-/
theorem putnam_2006_b6
(k : ℕ)
(hk : k > 1)
(a : ℕ → ℝ)
(ha0 : a 0 > 0)
(ha : ∀ n : ℕ, a (n + 1) = a n + 1/((a n)^((1 : ℝ)/k)))
: Tendsto (fun n => (a n)^(k+1)/(n ^ k)) atTop (𝓝 (((fun k => ((k+1)/k)^k) : ℕ → ℝ ) k)) := by
  let p : ℝ := ((k : ℝ) + 1) / (k : ℝ)
  have hkpos_nat : 0 < k := lt_trans Nat.zero_lt_one hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkpos_nat
  have hpdef : p = 1 + (1 : ℝ) / k := by
    dsimp [p]
    field_simp [hkpos.ne']
  have hp_pos : 0 < p := by
    rw [hpdef]
    positivity
  have hp_ge_one : 1 ≤ p := by
    rw [hpdef]
    have hnonneg : 0 ≤ (1 : ℝ) / k := by positivity
    linarith
  have hpos : ∀ n : ℕ, 0 < a n := by
    intro n
    induction n with
    | zero => simpa using ha0
    | succ n ih =>
        rw [ha n]
        positivity
  have hrec_mul : ∀ n : ℕ,
      a (n + 1) = a n * (1 + ((a n) ^ p)⁻¹) := by
    intro n
    rw [ha n]
    have hnpos : 0 < a n := hpos n
    dsimp [p]
    have hpdef' : ((k : ℝ) + 1) / (k : ℝ) = 1 + (1 : ℝ) / k := by
      field_simp [hkpos.ne']
    rw [hpdef', Real.rpow_add hnpos 1 ((1 : ℝ) / k), Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos hnpos ((1 : ℝ) / k)).ne']
  have hstep_lower : ∀ n : ℕ, (a n) ^ p + p ≤ (a (n + 1)) ^ p := by
    intro n
    have hnpos : 0 < a n := hpos n
    have hnpowpos : 0 < (a n) ^ p := Real.rpow_pos_of_pos hnpos p
    rw [hrec_mul n]
    have hbase : 0 ≤ 1 + ((a n) ^ p)⁻¹ := by positivity
    rw [Real.mul_rpow hnpos.le hbase]
    have hs : -1 ≤ ((a n) ^ p)⁻¹ := by
      have hnonneg : 0 ≤ ((a n) ^ p)⁻¹ := by positivity
      linarith
    have hbern : 1 + p * ((a n) ^ p)⁻¹ ≤
        (1 + ((a n) ^ p)⁻¹) ^ p := by
      exact one_add_mul_self_le_rpow_one_add (s := ((a n) ^ p)⁻¹) (p := p) hs hp_ge_one
    calc
      (a n) ^ p + p = (a n) ^ p * (1 + p * ((a n) ^ p)⁻¹) := by
        field_simp [hnpowpos.ne']
      _ ≤ (a n) ^ p * (1 + ((a n) ^ p)⁻¹) ^ p := by
        exact mul_le_mul_of_nonneg_left hbern hnpowpos.le
  have hb_lower : ∀ n : ℕ, (a 0) ^ p + (n : ℝ) * p ≤ (a n) ^ p := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          (a 0) ^ p + (n.succ : ℝ) * p
              = ((a 0) ^ p + (n : ℝ) * p) + p := by
                norm_num [Nat.cast_succ]
                ring
          _ ≤ (a n) ^ p + p := by
                linarith
          _ ≤ (a (n + 1)) ^ p := hstep_lower n
  have hb_atTop : Tendsto (fun n : ℕ => (a n) ^ p) atTop atTop := by
    have hlin : Tendsto (fun n : ℕ => (a 0) ^ p + (n : ℝ) * p) atTop atTop := by
      exact tendsto_atTop_add_const_left atTop ((a 0) ^ p)
        ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_mul_const hp_pos)
    exact Filter.tendsto_atTop_mono' atTop (Eventually.of_forall hb_lower) hlin
  have hinv : Tendsto (fun n : ℕ => ((a n) ^ p)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hb_atTop
  have hpunctured : Tendsto (fun n : ℕ => ((a n) ^ p)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hinv, Eventually.of_forall ?_⟩
    intro n
    have hne : ((a n) ^ p)⁻¹ ≠ 0 :=
      inv_ne_zero (Real.rpow_pos_of_pos (hpos n) p).ne'
    simpa using hne
  have hquot : Tendsto (fun t : ℝ => t⁻¹ * ((1 + t) ^ p - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 p) := by
    have hgderiv : HasDerivAt (fun t : ℝ => (1 + t) ^ p) p 0 := by
      have hinner : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))
      have houter : HasDerivAt (fun x : ℝ => x ^ p)
          (p * ((1 : ℝ) + 0) ^ (p - 1)) ((1 : ℝ) + 0) := by
        simpa using (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := p) (Or.inl one_ne_zero))
      simpa [Function.comp_def] using houter.comp 0 hinner
    simpa using hgderiv.tendsto_slope_zero
  have hdiff_eq : ∀ n : ℕ,
      (a (n + 1)) ^ p - (a n) ^ p =
        ((((a n) ^ p)⁻¹)⁻¹) *
          ((1 + ((a n) ^ p)⁻¹) ^ p - 1) := by
    intro n
    have hnpos : 0 < a n := hpos n
    rw [hrec_mul n]
    have hbase : 0 ≤ 1 + ((a n) ^ p)⁻¹ := by positivity
    rw [Real.mul_rpow hnpos.le hbase]
    rw [inv_inv]
    ring
  have hdiff_tendsto : Tendsto (fun n : ℕ => (a (n + 1)) ^ p - (a n) ^ p)
      atTop (𝓝 p) := by
    refine Filter.Tendsto.congr' (Eventually.of_forall ?_) (hquot.comp hpunctured)
    intro n
    exact (hdiff_eq n).symm
  have hcesaro : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ((a n) ^ p - (a 0) ^ p))
      atTop (𝓝 p) := by
    refine Filter.Tendsto.congr' (Eventually.of_forall ?_) hdiff_tendsto.cesaro
    intro n
    rw [Finset.sum_range_sub (fun m : ℕ => (a m) ^ p) n]
  have hzero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (a 0) ^ p) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul tendsto_const_nhds
  have hratio : Tendsto (fun n : ℕ => ((a n) ^ p) / (n : ℝ)) atTop (𝓝 p) := by
    have hsum : Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * ((a n) ^ p - (a 0) ^ p) + (n : ℝ)⁻¹ * (a 0) ^ p)
        atTop (𝓝 p) := by
      simpa using hcesaro.add hzero
    refine Filter.Tendsto.congr' (Eventually.of_forall ?_) hsum
    intro n
    ring
  have hpow : Tendsto (fun n : ℕ => (((a n) ^ p) / (n : ℝ)) ^ k) atTop (𝓝 (p ^ k)) :=
    hratio.pow k
  have htarget : Tendsto (fun n : ℕ => (a n) ^ (k + 1) / (n ^ k)) atTop (𝓝 (p ^ k)) := by
    refine Filter.Tendsto.congr' (Eventually.of_forall ?_) hpow
    intro n
    rw [div_pow]
    congr 1
    calc
      ((a n) ^ p) ^ k = ((a n) ^ p) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (a n) ^ (p * (k : ℝ)) := by
        rw [Real.rpow_mul (hpos n).le]
      _ = (a n) ^ (((k + 1 : ℕ) : ℝ)) := by
        congr 1
        dsimp [p]
        rw [div_mul_cancel₀ _ hkpos.ne']
        norm_num
      _ = (a n) ^ (k + 1 : ℕ) := by
        rw [Real.rpow_natCast]
  simpa [p] using htarget
