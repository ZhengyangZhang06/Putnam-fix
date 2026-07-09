import Mathlib

open Nat Filter Topology

private lemma putnam_1989_b3_bound_integrable (n : ℕ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-√x)) (Set.Ioi 0) := by
  let g : ℝ → ℝ := fun y => y ^ n * Real.exp (-√y)
  have hs : (-1 : ℝ) < (((2 * n + 1 : ℕ) : ℝ)) := by
    have h0 : (0 : ℝ) ≤ (((2 * n + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.zero_le _
    linarith
  have hgamma : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (((2 * n + 1 : ℕ) : ℝ)) * Real.exp (-x)) (Set.Ioi 0) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_rpow (p := (1 : ℝ))
        (s := (((2 * n + 1 : ℕ) : ℝ))) hs (by norm_num))
  have hconst : MeasureTheory.IntegrableOn
      (fun x : ℝ => (2 : ℝ) * (x ^ (((2 * n + 1 : ℕ) : ℝ)) * Real.exp (-x)))
      (Set.Ioi 0) := by
    change MeasureTheory.Integrable
      (fun x : ℝ => (2 : ℝ) * (x ^ (((2 * n + 1 : ℕ) : ℝ)) * Real.exp (-x)))
      (MeasureTheory.volume.restrict (Set.Ioi 0))
    exact hgamma.integrable.const_mul 2
  have hleft : MeasureTheory.IntegrableOn
      (fun x : ℝ => (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ)))
      (Set.Ioi 0) := by
    refine hconst.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    dsimp [g]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_natCast]
    simp [Real.sqrt_sq hx0.le]
    rw [← pow_mul]
    rw [show 2 * n + 1 = (2 * n).succ by omega]
    rw [pow_succ]
    ring
  exact (MeasureTheory.integrableOn_Ioi_comp_rpow_iff (E := ℝ) g
    (by norm_num : (2 : ℝ) ≠ 0)).mp hleft

private lemma putnam_1989_b3_boundary_bound (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ (n + 1) * Real.exp (-√x)) atTop (𝓝 0) := by
  have hsqrt :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * (n + 1))).comp
      Real.tendsto_sqrt_atTop
  refine hsqrt.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hsq : (√x) ^ (2 * (n + 1)) = x ^ (n + 1) := by
    rw [pow_mul, Real.sq_sqrt hx]
  simp [hsq]

private lemma putnam_1989_b3_prod_int_eq_range (n : ℕ) :
    (∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - (2 : ℝ) ^ (-m))) =
      ∏ k ∈ Finset.range n, (1 + -((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let fac : ℤ → ℝ := fun m => 1 - (2 : ℝ) ^ (-m)
      have hprod : (∏ m ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), fac m) =
          (∏ m ∈ Finset.Icc (1 : ℤ) (n : ℤ), fac m) * fac ((n : ℤ) + 1) := by
        rw [Finset.prod_Icc_eq_prod_Ico_mul fac (by omega : (1 : ℤ) ≤ (n : ℤ) + 1)]
        rw [Finset.Ico_add_one_right_eq_Icc]
      have hfac : fac ((n : ℤ) + 1) = 1 + -((2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) := by
        dsimp [fac]
        norm_num
        ring
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by norm_num]
      calc
        (∏ m ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), fac m)
            = (∏ m ∈ Finset.Icc (1 : ℤ) (n : ℤ), fac m) * fac ((n : ℤ) + 1) := hprod
        _ = (∏ k ∈ Finset.range n, (1 + -((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))))) *
              fac ((n : ℤ) + 1) := by rw [ih]
        _ = (∏ k ∈ Finset.range n, (1 + -((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))))) *
              (1 + -((2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)))) := by rw [hfac]
        _ = ∏ k ∈ Finset.range (n + 1),
              (1 + -((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)))) := by
          rw [Finset.prod_range_succ]

private lemma putnam_1989_b3_prod_tendsto :
    ∃ L : ℝ, L ≠ 0 ∧ Tendsto
      (fun n : ℕ => ∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - (2 : ℝ) ^ (-m)))
      atTop (𝓝 L) := by
  let u : ℕ → ℝ := fun k => -((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)))
  have hsum_norm : Summable (fun k : ℕ => ‖u k‖) := by
    have hgeom : Summable (fun k : ℕ => ((1 / 2 : ℝ) ^ k)) := by
      exact summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have hsucc : Summable (fun k : ℕ => ((1 / 2 : ℝ) ^ (k + 1))) :=
      hgeom.comp_injective Nat.succ_injective
    refine hsucc.congr ?_
    intro k
    dsimp [u]
    calc
      (1 / 2 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1))⁻¹ := by
        rw [one_div, inv_pow]
      _ = ‖-((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)))‖ := by
        rw [norm_neg, Real.norm_of_nonneg]
        · rw [zpow_neg, zpow_natCast]
        · positivity
  have hfactor_ne : ∀ k, 1 + u k ≠ 0 := by
    intro k
    dsimp [u]
    have hlt : (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) < 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_lt_one_of_one_lt₀
        (one_lt_pow₀ (a := (2 : ℝ)) one_lt_two (Nat.succ_ne_zero k))
    have hpos : 0 < 1 + -((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) := by linarith
    exact ne_of_gt hpos
  have hmult : Multipliable (fun k : ℕ => 1 + u k) :=
    multipliable_one_add_of_summable hsum_norm
  let L : ℝ := ∏' k : ℕ, (1 + u k)
  refine ⟨L, ?_, ?_⟩
  · exact tprod_one_add_ne_zero_of_summable hfactor_ne hsum_norm
  · have ht := hmult.hasProd.tendsto_prod_nat
    refine ht.congr' ?_
    filter_upwards with n
    rw [putnam_1989_b3_prod_int_eq_range n]

private lemma putnam_1989_b3_seq_formula (μ : ℕ → ℝ)
    (hrec : ∀ n, μ (n + 1) = μ n * (n + 1) /
      (3 * (1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))))) :
    ∀ n, μ n = μ 0 * n ! /
      (3 ^ n * ∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - (2 : ℝ) ^ (-m))) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      let fac : ℤ → ℝ := fun m => 1 - (2 : ℝ) ^ (-m)
      have hprod : (∏ m ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), fac m) =
          (∏ m ∈ Finset.Icc (1 : ℤ) (n : ℤ), fac m) * fac ((n : ℤ) + 1) := by
        rw [Finset.prod_Icc_eq_prod_Ico_mul fac (by omega : (1 : ℤ) ≤ (n : ℤ) + 1)]
        rw [Finset.Ico_add_one_right_eq_Icc]
      set P : ℝ := ∏ m ∈ Finset.Icc (1 : ℤ) (n : ℤ), fac m
      set A : ℝ := fac ((n : ℤ) + 1)
      rw [hrec n, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [hprod]
      change (μ 0 * n ! / ((3 : ℝ) ^ n * P)) * (n + 1 : ℝ) / (3 * A) =
        μ 0 * (n + 1)! / ((3 : ℝ) ^ (n + 1) * (P * A))
      simp [Nat.factorial_succ, pow_succ]
      ring_nf

-- fun n c ↦ c * n ! / (3 ^ n * ∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - 2 ^ (-m)))
/--
Let $f$ be a function on $[0,\infty)$, differentiable and satisfying
\[
f'(x)=-3f(x)+6f(2x)
\]
for $x>0$. Assume that $|f(x)|\le e^{-\sqrt{x}}$ for $x\ge 0$ (so that $f(x)$ tends rapidly to $0$ as $x$ increases). For $n$ a non-negative integer, define
\[
\mu_n=\int_0^\infty x^n f(x)\,dx
\]
(sometimes called the $n$th moment of $f$).
\begin{enumerate}
\item[a)] Express $\mu_n$ in terms of $\mu_0$.
\item[b)] Prove that the sequence $\{\mu_n \frac{3^n}{n!}\}$ always converges, and that the limit is $0$ only if $\mu_0=0$.
\end{enumerate}
-/
theorem putnam_1989_b3
    (f : ℝ → ℝ)
    (hfdiff : Differentiable ℝ f)
    (hfderiv : ∀ x > 0, deriv f x = -3 * f x + 6 * f (2 * x))
    (hdecay : ∀ x ≥ 0, |f x| ≤ Real.exp (- √x))
    (μ : ℕ → ℝ)
    (μ_def : ∀ n, μ n = ∫ x in Set.Ioi 0, x ^ n * f x) :
    (∀ n, μ n = ((fun n c ↦ c * n ! / (3 ^ n * ∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - 2 ^ (-m)))) : ℕ → ℝ → ℝ ) n (μ 0)) ∧
    (∃ L, Tendsto (fun n ↦ (μ n) * 3 ^ n / n !) atTop (𝓝 L)) ∧
    (Tendsto (fun n ↦ (μ n) * 3 ^ n / n !) atTop (𝓝 0) → μ 0 = 0) := by
  have hrec : ∀ n, μ (n + 1) = μ n * (n + 1) /
      (3 * (1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)))) := by
    have hmoment : ∀ n, MeasureTheory.IntegrableOn (fun x : ℝ => x ^ n * f x) (Set.Ioi 0) := by
      intro n
      have hbound := putnam_1989_b3_bound_integrable n
      have hmeas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ n * f x)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
        exact ((continuous_pow n).mul hfdiff.continuous).aestronglyMeasurable
      have hle : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
          ‖x ^ n * f x‖ ≤ ‖x ^ n * Real.exp (-√x)‖ := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0le : 0 ≤ x := le_of_lt hx
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg hx0le n), abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hdecay x hx0le) (pow_nonneg hx0le n)
      change MeasureTheory.Integrable (fun x : ℝ => x ^ n * f x)
          (MeasureTheory.volume.restrict (Set.Ioi 0))
      exact hbound.integrable.mono hmeas hle
    have hcomp_moment : ∀ k, MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ k * f (2 * x)) (Set.Ioi 0) := by
      intro k
      let g : ℝ → ℝ := fun y => y ^ k * f y
      have hg : MeasureTheory.IntegrableOn g (Set.Ioi (2 * 0)) := by
        simpa [g] using hmoment k
      have hgcomp : MeasureTheory.IntegrableOn
          (fun x : ℝ => (2 * x) ^ k * f (2 * x)) (Set.Ioi 0) := by
        simpa [g] using
          ((MeasureTheory.integrableOn_Ioi_comp_mul_left_iff (E := ℝ) g 0
            (by norm_num : (0 : ℝ) < 2)).2 hg)
      have hscaled : MeasureTheory.IntegrableOn
          (fun x : ℝ => ((2 : ℝ) ^ k)⁻¹ * ((2 * x) ^ k * f (2 * x)))
          (Set.Ioi 0) := by
        change MeasureTheory.Integrable
          (fun x : ℝ => ((2 : ℝ) ^ k)⁻¹ * ((2 * x) ^ k * f (2 * x)))
          (MeasureTheory.volume.restrict (Set.Ioi 0))
        exact hgcomp.integrable.const_mul _
      refine hscaled.congr_fun ?_ measurableSet_Ioi
      intro x hx
      dsimp
      rw [mul_pow]
      field_simp [pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]
    have hboundary : ∀ n, Tendsto (fun x : ℝ => x ^ (n + 1) * f x) atTop (𝓝 0) := by
      intro n
      refine squeeze_zero_norm' ?_ (putnam_1989_b3_boundary_bound n)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have hpownonneg : 0 ≤ x ^ (n + 1) := pow_nonneg hx _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpownonneg]
      exact mul_le_mul_of_nonneg_left (hdecay x hx) hpownonneg
    have hcomp_int : ∀ k, (∫ x in Set.Ioi 0, x ^ k * f (2 * x)) =
        (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) * μ k := by
      intro k
      let g : ℝ → ℝ := fun y => y ^ k * f y
      have hchange : (∫ x in Set.Ioi 0, (2 * x) ^ k * f (2 * x)) =
          (2 : ℝ)⁻¹ * ∫ y in Set.Ioi 0, y ^ k * f y := by
        simpa [g, smul_eq_mul] using
          (MeasureTheory.integral_comp_mul_left_Ioi (E := ℝ) g 0
            (by norm_num : (0 : ℝ) < 2))
      calc
        (∫ x in Set.Ioi 0, x ^ k * f (2 * x))
            = ∫ x in Set.Ioi 0, ((2 : ℝ) ^ k)⁻¹ * ((2 * x) ^ k * f (2 * x)) := by
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
              intro x hx
              dsimp
              rw [mul_pow]
              field_simp [pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]
        _ = ((2 : ℝ) ^ k)⁻¹ * (∫ x in Set.Ioi 0, (2 * x) ^ k * f (2 * x)) := by
              rw [MeasureTheory.integral_const_mul]
        _ = ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ)⁻¹ * μ k) := by rw [hchange, ← μ_def k]
        _ = (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) * μ k := by
              rw [zpow_neg, zpow_natCast]
              rw [pow_succ]
              field_simp [pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]
    intro n
    let derivExpr : ℝ → ℝ := fun x =>
      ((n + 1 : ℝ) * (x ^ n * f x)) + x ^ (n + 1) * (-3 * f x + 6 * f (2 * x))
    have hderiv_int : MeasureTheory.IntegrableOn derivExpr (Set.Ioi 0) := by
      have h1 : MeasureTheory.IntegrableOn
          (fun x : ℝ => (n + 1 : ℝ) * (x ^ n * f x)) (Set.Ioi 0) := by
        change MeasureTheory.Integrable (fun x : ℝ => (n + 1 : ℝ) * (x ^ n * f x))
          (MeasureTheory.volume.restrict (Set.Ioi 0))
        exact (hmoment n).integrable.const_mul _
      have h2a : MeasureTheory.IntegrableOn
          (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x)) (Set.Ioi 0) := by
        change MeasureTheory.Integrable (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x))
          (MeasureTheory.volume.restrict (Set.Ioi 0))
        exact (hmoment (n + 1)).integrable.const_mul _
      have h2b : MeasureTheory.IntegrableOn
          (fun x : ℝ => (6 : ℝ) * (x ^ (n + 1) * f (2 * x))) (Set.Ioi 0) := by
        change MeasureTheory.Integrable
          (fun x : ℝ => (6 : ℝ) * (x ^ (n + 1) * f (2 * x)))
          (MeasureTheory.volume.restrict (Set.Ioi 0))
        exact (hcomp_moment (n + 1)).integrable.const_mul _
      have h2sum : MeasureTheory.IntegrableOn
          (fun x : ℝ => x ^ (n + 1) * (-3 * f x + 6 * f (2 * x))) (Set.Ioi 0) := by
        have hadd : MeasureTheory.IntegrableOn
            (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x) +
              (6 : ℝ) * (x ^ (n + 1) * f (2 * x))) (Set.Ioi 0) := by
          change MeasureTheory.Integrable
            (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x) +
              (6 : ℝ) * (x ^ (n + 1) * f (2 * x)))
            (MeasureTheory.volume.restrict (Set.Ioi 0))
          exact h2a.integrable.add h2b.integrable
        refine hadd.congr_fun ?_ measurableSet_Ioi
        intro x hx
        ring
      change MeasureTheory.Integrable derivExpr (MeasureTheory.volume.restrict (Set.Ioi 0))
      exact h1.integrable.add h2sum.integrable
    have hderiv : ∀ x ∈ Set.Ioi 0,
        HasDerivAt (fun y : ℝ => y ^ (n + 1) * f y) (derivExpr x) x := by
      intro x hx
      have hxpos : x > 0 := hx
      have hpow : HasDerivAt (fun y : ℝ => y ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
        simpa using (hasDerivAt_pow (n + 1) x)
      have hf' : HasDerivAt f (deriv f x) x := (hfdiff x).hasDerivAt
      have hprod := hpow.mul hf'
      simpa [derivExpr, Pi.mul_apply, hfderiv x hxpos, mul_add, mul_assoc, add_assoc,
        add_comm, add_left_comm] using hprod
    have hFTC : (∫ x in Set.Ioi 0, derivExpr x) = 0 := by
      have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun y : ℝ => y ^ (n + 1) * f y) (f' := derivExpr)
        (a := (0 : ℝ)) (m := (0 : ℝ))
        (((continuous_pow (n + 1)).mul hfdiff.continuous).continuousWithinAt)
        hderiv hderiv_int (hboundary n)
      simpa using h
    have hintegral : (∫ x in Set.Ioi 0, derivExpr x) =
        (n + 1 : ℝ) * μ n - 3 * μ (n + 1) +
          6 * ((2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) * μ (n + 1)) := by
      have h1int : (∫ x in Set.Ioi 0, (n + 1 : ℝ) * (x ^ n * f x)) =
          (n + 1 : ℝ) * μ n := by
        rw [MeasureTheory.integral_const_mul, ← μ_def n]
      have h2int : (∫ x in Set.Ioi 0, x ^ (n + 1) * (-3 * f x + 6 * f (2 * x))) =
          -3 * μ (n + 1) + 6 * ((2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) * μ (n + 1)) := by
        have hcongr : (∫ x in Set.Ioi 0, x ^ (n + 1) * (-3 * f x + 6 * f (2 * x))) =
            ∫ x in Set.Ioi 0, (-3 : ℝ) * (x ^ (n + 1) * f x) +
              (6 : ℝ) * (x ^ (n + 1) * f (2 * x)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          ring
        rw [hcongr]
        rw [MeasureTheory.integral_add]
        · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            ← μ_def (n + 1), hcomp_int (n + 1)]
        · change MeasureTheory.Integrable (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x))
            (MeasureTheory.volume.restrict (Set.Ioi 0))
          exact (hmoment (n + 1)).integrable.const_mul _
        · change MeasureTheory.Integrable
            (fun x : ℝ => (6 : ℝ) * (x ^ (n + 1) * f (2 * x)))
            (MeasureTheory.volume.restrict (Set.Ioi 0))
          exact (hcomp_moment (n + 1)).integrable.const_mul _
      dsimp [derivExpr]
      rw [MeasureTheory.integral_add]
      · rw [h1int, h2int]
        norm_num
        ring
      · change MeasureTheory.Integrable (fun x : ℝ => (n + 1 : ℝ) * (x ^ n * f x))
          (MeasureTheory.volume.restrict (Set.Ioi 0))
        exact (hmoment n).integrable.const_mul _
      · have h2a : MeasureTheory.IntegrableOn
            (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x)) (Set.Ioi 0) := by
          change MeasureTheory.Integrable
            (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x))
            (MeasureTheory.volume.restrict (Set.Ioi 0))
          exact (hmoment (n + 1)).integrable.const_mul _
        have h2b : MeasureTheory.IntegrableOn
            (fun x : ℝ => (6 : ℝ) * (x ^ (n + 1) * f (2 * x))) (Set.Ioi 0) := by
          change MeasureTheory.Integrable
            (fun x : ℝ => (6 : ℝ) * (x ^ (n + 1) * f (2 * x)))
            (MeasureTheory.volume.restrict (Set.Ioi 0))
          exact (hcomp_moment (n + 1)).integrable.const_mul _
        have hadd : MeasureTheory.IntegrableOn
            (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x) +
              (6 : ℝ) * (x ^ (n + 1) * f (2 * x))) (Set.Ioi 0) := by
          change MeasureTheory.Integrable
            (fun x : ℝ => (-3 : ℝ) * (x ^ (n + 1) * f x) +
              (6 : ℝ) * (x ^ (n + 1) * f (2 * x)))
            (MeasureTheory.volume.restrict (Set.Ioi 0))
          exact h2a.integrable.add h2b.integrable
        refine hadd.congr_fun ?_ measurableSet_Ioi
        intro x hx
        ring
    have hzero : (n + 1 : ℝ) * μ n - 3 * μ (n + 1) +
          6 * ((2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) * μ (n + 1)) = 0 := by
      rw [← hintegral, hFTC]
    have hlt : (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) < 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_lt_one_of_one_lt₀
        (one_lt_pow₀ (a := (2 : ℝ)) one_lt_two (Nat.succ_ne_zero n))
    have hfacpos : 0 < 1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by linarith
    have hfac_ne : 1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) ≠ 0 := ne_of_gt hfacpos
    have hcoef : 3 * (1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) ≠ 0 :=
      mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hfac_ne
    have hzpowcoef : (6 : ℝ) * (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) =
        3 * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      field_simp [pow_ne_zero (n + 1) (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hmain : (n + 1 : ℝ) * μ n =
        (3 * (1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)))) * μ (n + 1) := by
      have hzC : 6 * (((2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ))) * μ (n + 1)) =
          3 * ((2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) * μ (n + 1) := by
        rw [← hzpowcoef]
        ring
      nlinarith
    calc
      μ (n + 1) =
          ((n + 1 : ℝ) * μ n) / (3 * (1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)))) := by
        rw [hmain]
        field_simp [hcoef, hfac_ne]
      _ = μ n * (n + 1) / (3 * (1 - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)))) := by
        ring
  have hformula : ∀ n, μ n = μ 0 * n ! /
      (3 ^ n * ∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - (2 : ℝ) ^ (-m))) :=
    putnam_1989_b3_seq_formula μ hrec
  have hprod_lim := putnam_1989_b3_prod_tendsto
  rcases hprod_lim with ⟨Pinf, hPinf_ne, hPinf⟩
  have hscaled_eq : ∀ n,
      μ n * (3 : ℝ) ^ n / n ! =
        μ 0 / (∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - (2 : ℝ) ^ (-m))) := by
    intro n
    rw [hformula n]
    field_simp [pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
  have hscaled_tend : Tendsto (fun n ↦ μ n * (3 : ℝ) ^ n / n !) atTop
      (𝓝 (μ 0 / Pinf)) := by
    have hdiv : Tendsto
        (fun n : ℕ => μ 0 / (∏ m ∈ Finset.Icc (1 : ℤ) n, (1 - (2 : ℝ) ^ (-m))))
        atTop (𝓝 (μ 0 / Pinf)) :=
      tendsto_const_nhds.div hPinf hPinf_ne
    exact hdiv.congr' (Eventually.of_forall (fun n => (hscaled_eq n).symm))
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa using hformula n
  · exact ⟨μ 0 / Pinf, hscaled_tend⟩
  · intro hzero_lim
    have hlim_eq : μ 0 / Pinf = 0 :=
      tendsto_nhds_unique hscaled_tend hzero_lim
    field_simp [hPinf_ne] at hlim_eq
    simpa using hlim_eq
