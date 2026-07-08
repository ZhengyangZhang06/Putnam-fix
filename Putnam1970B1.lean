import Mathlib

open Metric Set EuclideanGeometry Filter Topology

noncomputable abbrev putnam_1970_b1_solution : ℝ :=
  Real.exp (∫ x in (0 : ℝ)..(2 : ℝ), Real.log (1 + x ^ 2))

private noncomputable def putnam_1970_b1_f (x : ℝ) : ℝ :=
  Real.log (1 + x ^ 2)

private lemma putnam_1970_b1_trapezoidal_tendsto :
    Tendsto (fun n : ℕ => trapezoidal_integral putnam_1970_b1_f (2 * n) (0 : ℝ) 2)
      atTop (𝓝 (∫ x in (0 : ℝ)..2, putnam_1970_b1_f x)) := by
  have h02 : (0 : ℝ) < 2 := by norm_num
  have h_c2 : ContDiffOn ℝ 2 putnam_1970_b1_f (Set.uIcc (0 : ℝ) 2) := by
    dsimp [putnam_1970_b1_f]
    apply ContDiffOn.log
    · fun_prop
    · intro x hx
      positivity
  have h_unique : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 2) := by
    rw [Set.uIcc_of_le h02.le]
    exact uniqueDiffOn_Icc h02
  have hcont :
      ContinuousOn
        (iteratedDerivWithin 2 putnam_1970_b1_f (Set.uIcc (0 : ℝ) 2))
        (Set.uIcc (0 : ℝ) 2) :=
    ContDiffOn.continuousOn_iteratedDerivWithin h_c2 (by norm_num) h_unique
  obtain ⟨C, hC⟩ :=
    (isCompact_uIcc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn hcont
  let ζ : ℝ := max 0 C
  have hζ : ∀ x : ℝ,
      |iteratedDerivWithin 2 putnam_1970_b1_f (Set.uIcc (0 : ℝ) 2) x| ≤ ζ := by
    intro x
    by_cases hx : x ∈ Set.uIcc (0 : ℝ) 2
    · have hxC :
          |iteratedDerivWithin 2 putnam_1970_b1_f (Set.uIcc (0 : ℝ) 2) x| ≤ C := by
        simpa [Real.norm_eq_abs] using hC x hx
      exact hxC.trans (le_max_right _ _)
    · have hx' : x ∉ closure (Set.uIcc (0 : ℝ) 2) := by
        simpa [Set.uIcc_of_le h02.le, closure_Icc] using hx
      rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure hx', abs_zero]
      exact le_max_left _ _
  have herr : ∀ᶠ n : ℕ in atTop,
      |trapezoidal_integral putnam_1970_b1_f (2 * n) (0 : ℝ) 2 -
          (∫ x in (0 : ℝ)..2, putnam_1970_b1_f x)| ≤
        |(2 : ℝ) - 0| ^ 3 * ζ / (12 * ((2 * n : ℕ) : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := Nat.succ_le_iff.mp hn
    have hN : 0 < 2 * n := Nat.mul_pos (by norm_num) hnpos
    simpa [trapezoidal_error] using
      (trapezoidal_error_le_of_c2 (f := putnam_1970_b1_f) (a := (0 : ℝ)) (b := 2)
        h_c2 hζ hN)
  have hden : Tendsto (fun n : ℕ => (12 : ℝ) * ((2 * n : ℕ) : ℝ) ^ 2) atTop atTop := by
    have hlin : Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ)) atTop atTop := by
      have hmul : Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop
      simpa [Nat.cast_mul] using hmul
    have hpow : Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp hlin
    exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 12) hpow
  have hzero :
      Tendsto
        (fun n : ℕ => |(2 : ℝ) - 0| ^ 3 * ζ / (12 * ((2 * n : ℕ) : ℝ) ^ 2))
        atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop hden (|(2 : ℝ) - 0| ^ 3 * ζ)
  have habs :
      Tendsto
        (fun n : ℕ =>
          |trapezoidal_integral putnam_1970_b1_f (2 * n) (0 : ℝ) 2 -
            (∫ x in (0 : ℝ)..2, putnam_1970_b1_f x)|)
        atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) herr hzero
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          trapezoidal_integral putnam_1970_b1_f (2 * n) (0 : ℝ) 2 -
            (∫ x in (0 : ℝ)..2, putnam_1970_b1_f x))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using habs
  have hconst :
      Tendsto (fun _ : ℕ => ∫ x in (0 : ℝ)..2, putnam_1970_b1_f x) atTop
        (𝓝 (∫ x in (0 : ℝ)..2, putnam_1970_b1_f x)) :=
    tendsto_const_nhds
  have hmain := hdiff.add hconst
  simpa [sub_add_cancel] using hmain

private lemma putnam_1970_b1_range_sum_tendsto :
    Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.range (2 * n),
            putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ))) / (n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..2, putnam_1970_b1_f x)) := by
  have hcorr :
      Tendsto (fun n : ℕ => (putnam_1970_b1_f 2 - putnam_1970_b1_f 0) /
        (2 * (n : ℝ))) atTop (𝓝 0) := by
    have h :=
      tendsto_const_div_atTop_nhds_zero_nat
        ((putnam_1970_b1_f 2 - putnam_1970_b1_f 0) / 2 : ℝ)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hsum :
      Tendsto
        (fun n : ℕ =>
          trapezoidal_integral putnam_1970_b1_f (2 * n) (0 : ℝ) 2 +
            (putnam_1970_b1_f 2 - putnam_1970_b1_f 0) / (2 * (n : ℝ)))
        atTop (𝓝 ((∫ x in (0 : ℝ)..2, putnam_1970_b1_f x) + 0)) :=
    putnam_1970_b1_trapezoidal_tendsto.add hcorr
  have heq :
      (fun n : ℕ =>
        (∑ k ∈ Finset.range (2 * n),
            putnam_1970_b1_f (((k + 1 : ℕ) : ℝ) / (n : ℝ))) / (n : ℝ))
        =ᶠ[atTop]
      (fun n : ℕ =>
        trapezoidal_integral putnam_1970_b1_f (2 * n) (0 : ℝ) 2 +
          (putnam_1970_b1_f 2 - putnam_1970_b1_f 0) / (2 * (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := Nat.succ_le_iff.mp hn
    have h2n : 0 < 2 * n := Nat.mul_pos (by norm_num) hnpos
    have h2n_eq : 2 * n = (2 * n - 1) + 1 := (Nat.sub_add_cancel h2n).symm
    rw [h2n_eq, Finset.sum_range_succ]
    unfold trapezoidal_integral
    simp [Nat.cast_mul, Nat.cast_add, Nat.cast_sub h2n, hnpos.ne', add_comm]
    field_simp [hnpos.ne']
    ring
  simpa using hsum.congr' heq.symm

private lemma putnam_1970_b1_log_sum_tendsto :
    Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
          ((1 : ℝ) / (n : ℝ)) * Real.log (1 + ((i : ℝ) / (n : ℝ)) ^ 2))
      atTop (𝓝 (∫ x in (0 : ℝ)..2, Real.log (1 + x ^ 2))) := by
  have hrange := putnam_1970_b1_range_sum_tendsto
  have hlog :
      Tendsto
        (fun n : ℕ =>
          ∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
            ((1 : ℝ) / (n : ℝ)) * putnam_1970_b1_f ((i : ℝ) / (n : ℝ)))
        atTop (𝓝 (∫ x in (0 : ℝ)..2, putnam_1970_b1_f x)) := by
    refine hrange.congr' ?_
    filter_upwards with n
    rw [Int.Icc_eq_finset_map]
    rw [show 2 * (n : ℤ) + 1 - 1 = 2 * (n : ℤ) by ring]
    have hto : (2 * (n : ℤ)).toNat = 2 * n := by
      apply Int.ofNat.inj
      change (((2 * (n : ℤ)).toNat : ℤ) = ((2 * n : ℕ) : ℤ))
      rw [Int.toNat_of_nonneg (by positivity : 0 ≤ 2 * (n : ℤ))]
      norm_num
    rw [hto]
    simp [putnam_1970_b1_f, Finset.mul_sum, div_eq_mul_inv, mul_comm, add_comm]
  simpa [putnam_1970_b1_f]
    using hlog

private lemma putnam_1970_b1_product_eq (n : ℕ) (hn : 0 < n) :
    1 / (((n : ℤ) ^ 4 : ℤ) : ℝ) *
        ∏ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
          ((((n : ℤ) ^ 2 + i ^ 2 : ℤ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      =
        Real.exp
          (∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
            ((1 : ℝ) / (n : ℝ)) * Real.log (1 + ((i : ℝ) / (n : ℝ)) ^ 2)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcard : (Finset.Icc (1 : ℤ) (2 * (n : ℤ))).card = 2 * n := by
    rw [Int.card_Icc]
    rw [show 2 * (n : ℤ) + 1 - 1 = 2 * (n : ℤ) by ring]
    apply Int.ofNat.inj
    change (((2 * (n : ℤ)).toNat : ℤ) = ((2 * n : ℕ) : ℤ))
    rw [Int.toNat_of_nonneg (by positivity : 0 ≤ 2 * (n : ℤ))]
    norm_num
  have hterm : ∀ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
      ((((n : ℤ) ^ 2 + i ^ 2 : ℤ) : ℝ) ^ ((1 : ℝ) / (n : ℝ))) =
        (((n : ℝ) ^ 2) ^ ((1 : ℝ) / (n : ℝ))) *
          ((1 + ((i : ℝ) / (n : ℝ)) ^ 2) ^ ((1 : ℝ) / (n : ℝ))) := by
    intro i hi
    have hbase : (((n : ℤ) ^ 2 + i ^ 2 : ℤ) : ℝ) =
        ((n : ℝ) ^ 2) * (1 + ((i : ℝ) / (n : ℝ)) ^ 2) := by
      norm_num [Int.cast_add, Int.cast_pow]
      field_simp [hn0]
    rw [hbase]
    rw [Real.mul_rpow (sq_nonneg (n : ℝ))
      (by positivity : 0 ≤ 1 + ((i : ℝ) / (n : ℝ)) ^ 2)]
  calc
    1 / (((n : ℤ) ^ 4 : ℤ) : ℝ) *
        ∏ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
          ((((n : ℤ) ^ 2 + i ^ 2 : ℤ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        = 1 / (((n : ℤ) ^ 4 : ℤ) : ℝ) *
            (∏ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
              (((n : ℝ) ^ 2) ^ ((1 : ℝ) / (n : ℝ))) *
                ((1 + ((i : ℝ) / (n : ℝ)) ^ 2) ^ ((1 : ℝ) / (n : ℝ)))) := by
          congr 1
          exact Finset.prod_congr rfl hterm
    _ = (1 / (((n : ℤ) ^ 4 : ℤ) : ℝ) *
            ((((n : ℝ) ^ 2) ^ ((1 : ℝ) / (n : ℝ))) ^ (2 * n))) *
            (∏ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
              ((1 + ((i : ℝ) / (n : ℝ)) ^ 2) ^ ((1 : ℝ) / (n : ℝ)))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
          ring
    _ = ∏ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
              ((1 + ((i : ℝ) / (n : ℝ)) ^ 2) ^ ((1 : ℝ) / (n : ℝ))) := by
          have hconst :
              1 / (((n : ℤ) ^ 4 : ℤ) : ℝ) *
                  ((((n : ℝ) ^ 2) ^ ((1 : ℝ) / (n : ℝ))) ^ (2 * n)) = 1 := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul (sq_nonneg (n : ℝ))]
            have hexp : (1 : ℝ) / (n : ℝ) * (2 * n : ℕ) = 2 := by
              norm_num [Nat.cast_mul]
              field_simp [hn0]
            rw [hexp, Real.rpow_two]
            norm_num
            field_simp [hn0]
          rw [hconst]
          ring
    _ = Real.exp
          (∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
            ((1 : ℝ) / (n : ℝ)) * Real.log (1 + ((i : ℝ) / (n : ℝ)) ^ 2)) := by
          rw [Real.exp_sum]
          refine Finset.prod_congr rfl ?_
          intro i hi
          rw [Real.rpow_def_of_pos]
          · ring_nf
          · positivity

/--
Evaluate the infinite product $\lim_{n \to \infty} \frac{1}{n^4} \prod_{i = 1}^{2n} (n^2 + i^2)^{1/n}$.
-/
theorem putnam_1970_b1
: Tendsto (fun n => 1/(n^4) * ∏ i ∈ Finset.Icc (1 : ℤ) (2*n), ((n^2 + i^2) : ℝ)^((1 : ℝ)/n)) atTop (𝓝 putnam_1970_b1_solution) :=
by
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            (∑ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
              ((1 : ℝ) / (n : ℝ)) * Real.log (1 + ((i : ℝ) / (n : ℝ)) ^ 2)))
        atTop (𝓝 putnam_1970_b1_solution) := by
    simpa [putnam_1970_b1_solution] using putnam_1970_b1_log_sum_tendsto.rexp
  have hnat :
      Tendsto
        (fun n : ℕ =>
          1 / (((n : ℤ) ^ 4 : ℤ) : ℝ) *
            ∏ i ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)),
              ((((n : ℤ) ^ 2 + i ^ 2 : ℤ) : ℝ) ^ ((1 : ℝ) / (n : ℝ))))
        atTop (𝓝 putnam_1970_b1_solution) := by
    refine hexp.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := Nat.succ_le_iff.mp hn
    exact (putnam_1970_b1_product_eq n hnpos).symm
  rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff]
  simpa [Function.comp_def, Nat.cast_mul] using hnat
