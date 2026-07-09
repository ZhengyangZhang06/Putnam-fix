import Mathlib

open Topology Filter Real
open scoped BigOperators

private noncomputable def putnam_2017_b4_block (k : ℕ) : ℝ :=
  3 * log (4 * k + 2) / (4 * k + 2)
    - log (4 * k + 3) / (4 * k + 3)
    - log (4 * k + 4) / (4 * k + 4)
    - log (4 * k + 5) / (4 * k + 5)

private noncomputable def putnam_2017_b4_alt (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (n + 1)

private noncomputable def putnam_2017_b4_logAlt (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * log (n + 1) / (n + 1)

private noncomputable def putnam_2017_b4_evenLogAlt (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * log (2 * (n + 1)) / (n + 1)

private lemma putnam_2017_b4_even_split (n : ℕ) :
    putnam_2017_b4_evenLogAlt n =
      log 2 * putnam_2017_b4_alt n + putnam_2017_b4_logAlt n := by
  have hlog : log (2 * (n + 1 : ℝ)) = log 2 + log (n + 1 : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
  simp [putnam_2017_b4_evenLogAlt, putnam_2017_b4_alt, putnam_2017_b4_logAlt, hlog]
  ring

private lemma putnam_2017_b4_step (N : ℕ) :
    putnam_2017_b4_evenLogAlt (2 * N) + putnam_2017_b4_evenLogAlt (2 * N + 1)
      - (putnam_2017_b4_logAlt (4 * N + 1) + putnam_2017_b4_logAlt (4 * N + 2)
        + putnam_2017_b4_logAlt (4 * N + 3) + putnam_2017_b4_logAlt (4 * N + 4))
      = putnam_2017_b4_block N := by
  simp [putnam_2017_b4_block, putnam_2017_b4_logAlt, putnam_2017_b4_evenLogAlt]
  norm_num [pow_succ]
  ring_nf
  field_simp
  ring

private lemma putnam_2017_b4_finite_id (N : ℕ) :
    (∑ k ∈ Finset.range N, putnam_2017_b4_block k) =
      (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_evenLogAlt i) -
        (∑ i ∈ Finset.range (4 * N + 1), putnam_2017_b4_logAlt i) := by
  induction N with
  | zero =>
      simp [putnam_2017_b4_logAlt]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      conv_rhs =>
        lhs
        rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega]
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
      conv_rhs =>
        rhs
        rw [show 4 * (N + 1) + 1 = 4 * N + 1 + 1 + 1 + 1 + 1 by omega]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ]
      rw [← putnam_2017_b4_step N]
      ring

private lemma putnam_2017_b4_finite_split (N : ℕ) :
    (∑ k ∈ Finset.range N, putnam_2017_b4_block k) =
      log 2 * (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_alt i) -
        ((∑ i ∈ Finset.range (4 * N + 1), putnam_2017_b4_logAlt i) -
          (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_logAlt i)) := by
  rw [putnam_2017_b4_finite_id]
  simp_rw [putnam_2017_b4_even_split]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  ring

private lemma putnam_2017_b4_alt_even_harmonic (N : ℕ) :
    (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_alt i) =
      (harmonic (2 * N) : ℝ) - (harmonic N : ℝ) := by
  induction N with
  | zero =>
      simp [putnam_2017_b4_alt]
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [harmonic_succ, harmonic_succ, harmonic_succ]
      simp [putnam_2017_b4_alt]
      norm_num [pow_succ]
      ring_nf
      field_simp
      ring

private lemma putnam_2017_b4_tendsto_alt_even :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (2 * N), putnam_2017_b4_alt i) atTop
      (𝓝 (log 2)) := by
  have htwo : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    refine Filter.tendsto_atTop_mono (f := fun N : ℕ => N) (g := fun N : ℕ => 2 * N) ?_
      Filter.tendsto_id
    intro N
    dsimp
    omega
  have hA : Tendsto (fun N : ℕ => (harmonic (2 * N) : ℝ) - log (2 * N)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simpa [Function.comp_def, Nat.cast_mul] using Real.tendsto_harmonic_sub_log.comp htwo
  have hB : Tendsto (fun N : ℕ => (harmonic N : ℝ) - log N) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hdiff : Tendsto (fun N : ℕ =>
        ((harmonic (2 * N) : ℝ) - log (2 * N)) - ((harmonic N : ℝ) - log N))
      atTop (𝓝 0) := by
    simpa using hA.sub hB
  have hlogeq : (fun N : ℕ => log (2 * N) - log N) =ᶠ[atTop] fun _ : ℕ => log 2 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
    rw [show (2 * N : ℝ) = (2 : ℝ) * (N : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hNp)]
    ring
  have hlog : Tendsto (fun N : ℕ => log (2 * N) - log N) atTop (𝓝 (log 2)) := by
    exact Filter.Tendsto.congr' hlogeq.symm tendsto_const_nhds
  have hmain : Tendsto (fun N : ℕ =>
        ((harmonic (2 * N) : ℝ) - log (2 * N)) - ((harmonic N : ℝ) - log N) +
          (log (2 * N) - log N)) atTop (𝓝 (log 2)) := by
    simpa using hdiff.add hlog
  have hharm : Tendsto (fun N : ℕ => (harmonic (2 * N) : ℝ) - (harmonic N : ℝ)) atTop
      (𝓝 (log 2)) := by
    refine Filter.Tendsto.congr' ?_ hmain
    filter_upwards with N
    ring
  refine Filter.Tendsto.congr' ?_ hharm
  filter_upwards with N
  rw [putnam_2017_b4_alt_even_harmonic]

private lemma putnam_2017_b4_logTail_antitone :
    Antitone (fun n : ℕ => log (n + 3 : ℝ) / (n + 3 : ℝ)) := by
  intro m n hmn
  refine Real.log_div_self_antitoneOn ?hm ?hn ?hle
  · exact (le_of_lt Real.exp_one_lt_three).trans (by exact_mod_cast (Nat.le_add_left 3 m))
  · exact (le_of_lt Real.exp_one_lt_three).trans (by exact_mod_cast (Nat.le_add_left 3 n))
  · have : m + 3 ≤ n + 3 := by omega
    exact_mod_cast this

private lemma putnam_2017_b4_logTail_tendsto_zero :
    Tendsto (fun n : ℕ => log (n + 3 : ℝ) / (n + 3 : ℝ)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (3 : ℝ) hcast
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
    (by norm_num : (1 : ℝ) ≠ 0)).comp hadd
  simpa [Function.comp_def, Nat.cast_add, pow_one] using h

private lemma putnam_2017_b4_logAlt_shift (i : ℕ) :
    putnam_2017_b4_logAlt (i + 2) =
      (-1 : ℝ) ^ i * (log (i + 3 : ℝ) / (i + 3 : ℝ)) := by
  simp [putnam_2017_b4_logAlt]
  ring_nf

private lemma putnam_2017_b4_logAlt_prefix_shift (t : ℕ) :
    (∑ i ∈ Finset.range (t + 2), putnam_2017_b4_logAlt i) =
      (∑ i ∈ Finset.range 2, putnam_2017_b4_logAlt i) +
        ∑ i ∈ Finset.range t, putnam_2017_b4_logAlt (i + 2) := by
  rw [show t + 2 = 2 + t by omega]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [add_comm]

private lemma putnam_2017_b4_tendsto_logAlt_tail_diff_zero :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range (4 * N + 1), putnam_2017_b4_logAlt i) -
      (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_logAlt i)) atTop (𝓝 0) := by
  have hQ_cauchy : CauchySeq fun n : ℕ => ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (log (i + 3 : ℝ) / (i + 3 : ℝ)) :=
    putnam_2017_b4_logTail_antitone.cauchySeq_alternating_series_of_tendsto_zero
      putnam_2017_b4_logTail_tendsto_zero
  have hQlog_cauchy : CauchySeq fun n : ℕ =>
      ∑ i ∈ Finset.range n, putnam_2017_b4_logAlt (i + 2) := by
    convert hQ_cauchy with n i hi
    rw [putnam_2017_b4_logAlt_shift]
  obtain ⟨L, hQlog⟩ := cauchySeq_tendsto_of_complete hQlog_cauchy
  have h2m : Tendsto (fun N : ℕ => 2 * N - 2) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N _hN
    dsimp
    omega
  have h4m : Tendsto (fun N : ℕ => 4 * N - 1) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N _hN
    dsimp
    omega
  let C : ℝ := ∑ i ∈ Finset.range 2, putnam_2017_b4_logAlt i
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have hP2 : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range (2 * N), putnam_2017_b4_logAlt i) atTop (𝓝 (C + L)) := by
    have h := hconst.add (hQlog.comp h2m)
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N _hN
    dsimp [C]
    rw [← putnam_2017_b4_logAlt_prefix_shift (t := 2 * N - 2)]
    rw [show 2 * N - 2 + 2 = 2 * N by omega]
  have hP4 : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range (4 * N + 1), putnam_2017_b4_logAlt i) atTop (𝓝 (C + L)) := by
    have h := hconst.add (hQlog.comp h4m)
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N _hN
    dsimp [C]
    rw [← putnam_2017_b4_logAlt_prefix_shift (t := 4 * N - 1)]
    rw [show 4 * N - 1 + 2 = 4 * N + 1 by omega]
  simpa using hP4.sub hP2

private lemma putnam_2017_b4_tendsto_block_partial :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, putnam_2017_b4_block k) atTop
      (𝓝 ((log 2) ^ 2)) := by
  have hconst : Tendsto (fun _ : ℕ => log 2) atTop (𝓝 (log 2)) := tendsto_const_nhds
  have hprod : Tendsto (fun N : ℕ =>
      log 2 * (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_alt i)) atTop
      (𝓝 (log 2 * log 2)) := hconst.mul putnam_2017_b4_tendsto_alt_even
  have hmain : Tendsto (fun N : ℕ =>
      log 2 * (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_alt i) -
        ((∑ i ∈ Finset.range (4 * N + 1), putnam_2017_b4_logAlt i) -
          (∑ i ∈ Finset.range (2 * N), putnam_2017_b4_logAlt i))) atTop
      (𝓝 ((log 2) ^ 2)) := by
    have h := hprod.sub putnam_2017_b4_tendsto_logAlt_tail_diff_zero
    simpa [pow_two] using h
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards with N
  rw [putnam_2017_b4_finite_split]

private lemma putnam_2017_b4_block_tail_nonneg (k : ℕ) :
    0 ≤ putnam_2017_b4_block (k + 1) := by
  have hbase : exp 1 ≤ (4 * ((k + 1 : ℕ) : ℝ) + 2) := by
    have he3 : exp 1 ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
    have hge : (3 : ℝ) ≤ 4 * ((k + 1 : ℕ) : ℝ) + 2 := by
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith
    exact he3.trans hge
  have h3 : exp 1 ≤ (4 * ((k + 1 : ℕ) : ℝ) + 3) := by
    exact hbase.trans (by norm_num)
  have h4 : exp 1 ≤ (4 * ((k + 1 : ℕ) : ℝ) + 4) := by
    exact hbase.trans (by norm_num)
  have h5 : exp 1 ≤ (4 * ((k + 1 : ℕ) : ℝ) + 5) := by
    exact hbase.trans (by norm_num)
  let A : ℝ := log (4 * ((k + 1 : ℕ) : ℝ) + 2) / (4 * ((k + 1 : ℕ) : ℝ) + 2)
  let B : ℝ := log (4 * ((k + 1 : ℕ) : ℝ) + 3) / (4 * ((k + 1 : ℕ) : ℝ) + 3)
  let C : ℝ := log (4 * ((k + 1 : ℕ) : ℝ) + 4) / (4 * ((k + 1 : ℕ) : ℝ) + 4)
  let D : ℝ := log (4 * ((k + 1 : ℕ) : ℝ) + 5) / (4 * ((k + 1 : ℕ) : ℝ) + 5)
  have hb3 : B ≤ A := by
    exact Real.log_div_self_antitoneOn hbase h3 (by norm_num)
  have hb4 : C ≤ A := by
    exact Real.log_div_self_antitoneOn hbase h4 (by norm_num)
  have hb5 : D ≤ A := by
    exact Real.log_div_self_antitoneOn hbase h5 (by norm_num)
  have hlin : 0 ≤ 3 * A - B - C - D := by nlinarith [hb3, hb4, hb5]
  unfold putnam_2017_b4_block
  rw [show 3 * log (4 * ↑(k + 1) + 2) / (4 * ↑(k + 1) + 2) =
      3 * (log (4 * ↑(k + 1) + 2) / (4 * ↑(k + 1) + 2)) by ring]
  simpa [A, B, C, D] using hlin

-- (log 2) ^ 2
/--
Evaluate the sum \begin{gather*} \sum_{k=0}^\infty \left( 3 \cdot \frac{\ln(4k+2)}{4k+2} - \frac{\ln(4k+3)}{4k+3} - \frac{\ln(4k+4)}{4k+4} - \frac{\ln(4k+5)}{4k+5} \right) \ = 3 \cdot \frac{\ln 2}{2} - \frac{\ln 3}{3} - \frac{\ln 4}{4} - \frac{\ln 5}{5} + 3 \cdot \frac{\ln 6}{6} - \frac{\ln 7}{7} \ - \frac{\ln 8}{8} - \frac{\ln 9}{9} + 3 \cdot \frac{\ln 10}{10} - \cdots . \end{gather*} (As usual, $\ln x$ denotes the natural logarithm of $x$.)
-/
theorem putnam_2017_b4 :
  (∑' k : ℕ, (3 * log (4 * k + 2) / (4 * k + 2) - log (4 * k + 3) / (4 * k + 3) - log (4 * k + 4) / (4 * k + 4) - log (4 * k + 5) / (4 * k + 5)) = (((log 2) ^ 2) : ℝ )) := by
  change (∑' k : ℕ, putnam_2017_b4_block k) = (((log 2) ^ 2) : ℝ)
  have hsucc_atTop : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n) (g := fun n : ℕ => n + 1) ?_
      Filter.tendsto_id
    intro n
    dsimp
    omega
  have hsucc : Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1), putnam_2017_b4_block k) atTop (𝓝 ((log 2) ^ 2)) :=
    putnam_2017_b4_tendsto_block_partial.comp hsucc_atTop
  have htail_tendsto : Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.range n, putnam_2017_b4_block (k + 1)) atTop
      (𝓝 (((log 2) ^ 2) - putnam_2017_b4_block 0)) := by
    have h := hsucc.sub (tendsto_const_nhds (x := putnam_2017_b4_block 0))
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with n
    rw [Finset.sum_range_succ']
    ring
  have htail_hasSum : HasSum (fun k : ℕ => putnam_2017_b4_block (k + 1))
      (((log 2) ^ 2) - putnam_2017_b4_block 0) :=
    (hasSum_iff_tendsto_nat_of_nonneg putnam_2017_b4_block_tail_nonneg _).2 htail_tendsto
  have hfull : HasSum putnam_2017_b4_block
      (putnam_2017_b4_block 0 + (((log 2) ^ 2) - putnam_2017_b4_block 0)) :=
    htail_hasSum.zero_add
  have hfull' : HasSum putnam_2017_b4_block ((log 2) ^ 2) := by
    convert hfull using 1
    ring
  exact hfull'.tsum_eq
