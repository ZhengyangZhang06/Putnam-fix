import Mathlib

open Nat Set Topology Filter MeasureTheory
open scoped Interval

noncomputable def putnamKernel (m : ℕ) (x t : ℝ) : ℝ :=
  (x - t) ^ m / (m ! : ℝ)

noncomputable def putnamVolterra (n : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, putnamKernel (n - 1) x t * g t

lemma putnam_iterated_D (i : ℕ) (y : ℝ → ℝ) (x : ℝ)
    (hy : ContDiffAt ℝ (i + 1 : ℕ) y x) :
    iteratedDeriv i (fun z : ℝ => z * deriv y z - (i : ℝ) * y z) x =
      x * iteratedDeriv (i + 1) y x := by
  have hswap : (fun z : ℝ => z * deriv y z - (i : ℝ) * y z)
      = (fun z : ℝ => deriv y z * id z - (i : ℝ) • y z) := by
    funext z
    simp [id_eq, smul_eq_mul, mul_comm]
  rw [hswap]
  have hsub := iteratedDeriv_fun_sub
    (n := i) (x := x) (f := fun z : ℝ => deriv y z * id z)
    (g := fun z : ℝ => (i : ℝ) • y z)
    ((hy.derivWithin (by norm_num)).mul contDiffAt_id)
    ((hy.of_le (by norm_num)).const_smul (i : ℝ))
  rw [hsub]
  rw [iteratedDeriv_fun_mul]
  · change
      (∑ j ∈ Finset.range (i + 1),
          ↑(i.choose j) * iteratedDeriv j (deriv y) x * iteratedDeriv (i - j) id x) -
          iteratedDeriv i ((i : ℝ) • y) x =
        x * iteratedDeriv (i + 1) y x
    rw [iteratedDeriv_const_smul ((hy.of_le (by norm_num)) : ContDiffAt ℝ (i : ℕ) y x) (i : ℝ)]
    cases i with
    | zero =>
        simp [iteratedDeriv_zero, mul_comm]
    | succ k =>
        simp +contextual [iteratedDeriv_id, iteratedDeriv_succ', Finset.sum_range_succ,
          show ∀ j ∈ Finset.range k, k + 1 - j ≠ 0 by simp; omega,
          show ∀ j ∈ Finset.range k, k + 1 - j ≠ 1 by simp; omega,
          Nat.choose_self, Nat.cast_add, Nat.cast_one, smul_eq_mul, mul_comm]
  · exact hy.derivWithin (by norm_num)
  · exact contDiffAt_id

lemma putnam_P_eq_iteratedDeriv (P : ℕ → (ℝ → ℝ) → (ℝ → ℝ))
    (hP : P 0 = id ∧ ∀ i y, P (i + 1) y = P i (fun x ↦ x * deriv y x - i * y x))
    (n : ℕ) (y : ℝ → ℝ) (x : ℝ) (hy : ContDiffAt ℝ n y x) :
    P n y x = x ^ n * iteratedDeriv n y x := by
  induction n generalizing y with
  | zero =>
      simp [hP.1]
  | succ i ih =>
      rw [hP.2 i y]
      have hD : ContDiffAt ℝ (i : ℕ) (fun x ↦ x * deriv y x - (i : ℝ) * y x) x := by
        exact (contDiffAt_id.mul (hy.derivWithin (by norm_num))).sub
          ((hy.of_le (by norm_num)).const_smul (i : ℝ))
      rw [ih (fun x ↦ x * deriv y x - (i : ℝ) * y x) hD]
      rw [putnam_iterated_D i y x hy]
      ring

lemma putnam_taylor_identity (n : ℕ) (hn : 0 < n) (y : ℝ → ℝ) {x : ℝ} (hx : 1 < x)
    (hy : ContDiffOn ℝ n y (Icc (1 : ℝ) x)) :
    (∫ t in (1 : ℝ)..x,
        putnamKernel (n - 1) x t * iteratedDerivWithin n y (Icc (1 : ℝ) x) t)
      = y x - taylorWithinEval y (n - 1) (Icc (1 : ℝ) x) 1 x := by
  have huniq : UniqueDiffOn ℝ (Icc (1 : ℝ) x) := uniqueDiffOn_Icc hx
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hlt : ((n - 1 : ℕ) : WithTop ℕ∞) < n := by
    exact_mod_cast Nat.sub_one_lt hn_ne
  have hle_sub : ((n - 1 : ℕ) : WithTop ℕ∞) ≤ n := le_of_lt hlt
  have hdiff :
      DifferentiableOn ℝ (iteratedDerivWithin (n - 1) y (Icc (1 : ℝ) x)) (Ioo (1 : ℝ) x) := by
    exact (hy.differentiableOn_iteratedDerivWithin hlt huniq).mono Ioo_subset_Icc_self
  have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
      HasDerivAt (fun u => taylorWithinEval y (n - 1) (Icc (1 : ℝ) x) u x)
        (putnamKernel (n - 1) x t * iteratedDerivWithin n y (Icc (1 : ℝ) x) t) t := by
    intro t ht
    have h := taylorWithinEval_hasDerivAt_Ioo (f := y) (a := (1 : ℝ)) (b := x) (t := t)
        (x := x) (n := n - 1) hx ht (hy.of_le hle_sub) hdiff
    simpa [putnamKernel, Nat.sub_one_add_one hn_ne, smul_eq_mul, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm] using h
  have hcont : ContinuousOn (fun u => taylorWithinEval y (n - 1) (Icc (1 : ℝ) x) u x)
      (Icc (1 : ℝ) x) := by
    exact continuousOn_taylorWithinEval huniq (hy.of_le hle_sub)
  have hint : IntervalIntegrable
      (fun t => putnamKernel (n - 1) x t * iteratedDerivWithin n y (Icc (1 : ℝ) x) t)
      volume (1 : ℝ) x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx.le
    have hcw : ContinuousOn (iteratedDerivWithin n y (Icc (1 : ℝ) x)) (Icc (1 : ℝ) x) := by
      exact hy.continuousOn_iteratedDerivWithin le_rfl huniq
    apply ContinuousOn.mul _ hcw
    change ContinuousOn (fun t : ℝ => (x - t) ^ (n - 1) / ((n - 1)! : ℝ)) (Icc (1 : ℝ) x)
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun u => taylorWithinEval y (n - 1) (Icc (1 : ℝ) x) u x)
      (f' := fun t => putnamKernel (n - 1) x t * iteratedDerivWithin n y (Icc (1 : ℝ) x) t)
      hx.le hcont hderiv hint
  simpa using hftc

lemma putnamKernel_hasDerivAt {k : ℕ} (hk : 0 < k) (x t : ℝ) :
    HasDerivAt (fun u : ℝ => putnamKernel k x u) (-putnamKernel (k - 1) x t) t := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have hpow := monomial_has_deriv_aux t x (k - 1)
  have h := hpow.const_mul (((k ! : ℕ) : ℝ)⁻¹)
  convert h using 1
  · ext u
    simp [putnamKernel, Nat.sub_one_add_one hk_ne, div_eq_mul_inv, mul_comm]
  · simp only [putnamKernel, div_eq_mul_inv]
    have hkfac : ((k ! : ℕ) : ℝ) = (((k - 1 : ℕ) : ℝ) + 1) * ((k - 1)! : ℝ) := by
      conv_lhs => rw [← Nat.sub_one_add_one hk_ne]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hkfac]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))]

lemma putnam_primitive_continuousOn_Ici (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (1 : ℝ))) :
    ContinuousOn (fun x : ℝ => ∫ t in (1 : ℝ)..x, g t) (Ici (1 : ℝ)) := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := hx
  have hx_le : (1 : ℝ) ≤ x + 1 := by linarith
  have hx_mem : x ∈ uIcc (1 : ℝ) (x + 1) := by
    simp [uIcc_of_le hx_le, hx1, le_add_of_nonneg_right zero_le_one]
  have h_int : IntegrableOn g (uIcc (1 : ℝ) (x + 1)) volume := by
    rw [uIcc_of_le hx_le]
    exact ContinuousOn.integrableOn_Icc (hg.mono Icc_subset_Ici_self)
  have hc := intervalIntegral.continuousOn_primitive_interval
    (μ := volume) (a := (1 : ℝ)) (b := x + 1) h_int
  refine (hc x hx_mem).mono_of_mem_nhdsWithin ?_
  have hupper : Iio (x + 1) ∈ 𝓝[Ici (1 : ℝ)] x := by
    exact nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (lt_add_of_pos_right x zero_lt_one))
  filter_upwards [self_mem_nhdsWithin, hupper] with y hyIci hylt
  exact (by
    simpa [uIcc_of_le hx_le] using
      (⟨hyIci, le_of_lt hylt⟩ : y ∈ Icc (1 : ℝ) (x + 1)))

lemma putnam_volterra_succ (k : ℕ) (hk : 0 < k) (g : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x)
    (hg : ContinuousOn g (Icc (1 : ℝ) x)) :
    (∫ t in (1 : ℝ)..x, putnamKernel k x t * g t) =
      ∫ t in (1 : ℝ)..x, putnamKernel (k - 1) x t * (∫ s in (1 : ℝ)..t, g s) := by
  rcases hx.eq_or_lt with rfl | hxlt
  · simp
  have hGcont : ContinuousOn (fun t : ℝ => ∫ s in (1 : ℝ)..t, g s) (Icc (1 : ℝ) x) := by
    have hint : IntegrableOn g (uIcc (1 : ℝ) x) volume := by
      simpa [uIcc_of_le hx] using (ContinuousOn.integrableOn_Icc hg)
    simpa [uIcc_of_le hx] using
      (intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := (1 : ℝ)) (b := x) hint)
  have hucont : ContinuousOn (fun t : ℝ => putnamKernel k x t) [[(1 : ℝ), x]] := by
    rw [uIcc_of_le hx]
    change ContinuousOn (fun t : ℝ => (x - t) ^ k / (k ! : ℝ)) (Icc (1 : ℝ) x)
    fun_prop
  have hvcont : ContinuousOn (fun t : ℝ => ∫ s in (1 : ℝ)..t, g s) [[(1 : ℝ), x]] := by
    simpa [uIcc_of_le hx] using hGcont
  have huderiv : ∀ t ∈ Ioo (min (1 : ℝ) x) (max (1 : ℝ) x),
      HasDerivAt (fun t : ℝ => putnamKernel k x t) (-putnamKernel (k - 1) x t) t := by
    intro t ht
    exact putnamKernel_hasDerivAt hk x t
  have hvderiv : ∀ t ∈ Ioo (min (1 : ℝ) x) (max (1 : ℝ) x),
      HasDerivAt (fun t : ℝ => ∫ s in (1 : ℝ)..t, g s) (g t) t := by
    intro t ht
    have ht' : t ∈ Ioo (1 : ℝ) x := by simpa [min_eq_left hx, max_eq_right hx] using ht
    have hg_at : ContinuousAt g t := hg.continuousAt (Icc_mem_nhds ht'.1 ht'.2)
    have hg_int : IntervalIntegrable g volume (1 : ℝ) t := by
      exact (hg.mono (Icc_subset_Icc_right ht'.2.le)).intervalIntegrable_of_Icc ht'.1.le
    exact intervalIntegral.integral_hasDerivAt_right hg_int
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun z hz => hg.continuousAt (Icc_mem_nhds hz.1 hz.2)) t ht') hg_at
  have hu_int : IntervalIntegrable (fun t : ℝ => -putnamKernel (k - 1) x t) volume (1 : ℝ) x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    change ContinuousOn (fun t : ℝ => -((x - t) ^ (k - 1) / ((k - 1)! : ℝ))) (Icc (1 : ℝ) x)
    fun_prop
  have hv_int : IntervalIntegrable g volume (1 : ℝ) x := by
    exact hg.intervalIntegrable_of_Icc hx
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (1 : ℝ)) (b := x)
    (u := fun t : ℝ => putnamKernel k x t) (v := fun t : ℝ => ∫ s in (1 : ℝ)..t, g s)
    (u' := fun t : ℝ => -putnamKernel (k - 1) x t) (v' := g)
    hucont hvcont huderiv hvderiv hu_int hv_int
  have hKx : putnamKernel k x x = 0 := by simp [putnamKernel, hk.ne']
  simpa [hKx, intervalIntegral.integral_neg] using H

lemma putnamVolterra_one_hasDerivWithinAt (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (1 : ℝ))) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivWithinAt (fun u : ℝ => putnamVolterra 1 g u) (g x) (Ici (1 : ℝ)) x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · have hcontIci : ContinuousWithinAt g (Ici (1 : ℝ)) 1 := hg.continuousWithinAt (by simp)
    have hcontIoi : ContinuousWithinAt g (Ioi (1 : ℝ)) 1 := hcontIci.mono Ioi_subset_Ici_self
    have hmeas : StronglyMeasurableAtFilter g (𝓝[Ioi (1 : ℝ)] 1) := by
      exact (hg.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 1
    have hint : IntervalIntegrable g volume (1 : ℝ) 1 := by simp
    have H := intervalIntegral.integral_hasDerivWithinAt_right (a := (1 : ℝ)) (b := (1 : ℝ))
      (f := g) (s := Ici (1 : ℝ)) (t := Ioi (1 : ℝ)) hint hmeas hcontIoi
    convert H using 1
    ext u
    simp [putnamVolterra, putnamKernel]
  · have hcont : ContinuousAt g x :=
      hg.continuousAt (mem_of_superset (isOpen_Ioi.mem_nhds hxlt) Ioi_subset_Ici_self)
    have hint : IntervalIntegrable g volume (1 : ℝ) x := by
      exact (hg.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hxlt.le
    have H := intervalIntegral.integral_hasDerivAt_right (a := (1 : ℝ)) (b := x) hint
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (fun z hz => hg.continuousAt
          (mem_of_superset (isOpen_Ioi.mem_nhds hz) Ioi_subset_Ici_self)) x hxlt) hcont
    convert H.hasDerivWithinAt using 1
    ext u
    simp [putnamVolterra, putnamKernel]

lemma putnamVolterra_hasDerivWithinAt (n : ℕ) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (1 : ℝ))) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivWithinAt (fun u : ℝ => putnamVolterra (n + 1) g u)
      (if n = 0 then g x else putnamVolterra n g x) (Ici (1 : ℝ)) x := by
  induction n generalizing g x with
  | zero =>
      simpa using putnamVolterra_one_hasDerivWithinAt g hg hx
  | succ n ih =>
      let G : ℝ → ℝ := fun u => ∫ t in (1 : ℝ)..u, g t
      have hGcont : ContinuousOn G (Ici (1 : ℝ)) := putnam_primitive_continuousOn_Ici g hg
      have hrel : (fun u : ℝ => putnamVolterra (n + 1 + 1) g u) =ᶠ[𝓝[Ici (1 : ℝ)] x]
          (fun u : ℝ => putnamVolterra (n + 1) G u) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu1 : (1 : ℝ) ≤ u := hu
        have hgI : ContinuousOn g (Icc (1 : ℝ) u) := hg.mono Icc_subset_Ici_self
        have H := putnam_volterra_succ (n + 1) (Nat.succ_pos n) g hu1 hgI
        simpa [putnamVolterra, G, Nat.add_sub_cancel] using H
      have hder := ih G hGcont hx
      have hder' : HasDerivWithinAt (fun u : ℝ => putnamVolterra (n + 1) G u)
          (putnamVolterra (n + 1) g x) (Ici (1 : ℝ)) x := by
        cases n with
        | zero =>
            have hval : G x = putnamVolterra 1 g x := by
              simp [putnamVolterra, G, putnamKernel]
            exact hder.congr_deriv (by simp [hval])
        | succ k =>
            have Hx := putnam_volterra_succ (k + 1) (Nat.succ_pos k) g hx
              (hg.mono Icc_subset_Ici_self)
            have hval : putnamVolterra (k + 1) G x = putnamVolterra (k + 1 + 1) g x := by
              simpa [putnamVolterra, G, Nat.add_sub_cancel] using Hx.symm
            exact hder.congr_deriv (by simp [hval])
      exact hder'.congr_of_eventuallyEq_of_mem hrel hx

noncomputable def putnamW (g : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => g
  | k + 1 => putnamVolterra (k + 1) g

lemma putnamW_hasDerivWithinAt (k : ℕ) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (1 : ℝ))) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivWithinAt (putnamW g (k + 1)) (putnamW g k x) (Ici (1 : ℝ)) x := by
  cases k with
  | zero =>
      simpa [putnamW] using putnamVolterra_hasDerivWithinAt 0 g hg hx
  | succ k =>
      have h := putnamVolterra_hasDerivWithinAt (k + 1) g hg hx
      simpa [putnamW] using h

lemma putnam_derivWithin_W (k : ℕ) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (1 : ℝ))) {x : ℝ} (hx : 1 ≤ x) :
    derivWithin (putnamW g (k + 1)) (Ici (1 : ℝ)) x = putnamW g k x := by
  exact (putnamW_hasDerivWithinAt k g hg hx).derivWithin (uniqueDiffOn_Ici (1 : ℝ) x hx)

lemma putnam_iteratedDerivWithin_W (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (1 : ℝ)))
    (n i : ℕ) (hi : i ≤ n) :
    EqOn (iteratedDerivWithin i (putnamW g n) (Ici (1 : ℝ))) (putnamW g (n - i))
      (Ici (1 : ℝ)) := by
  induction i generalizing n with
  | zero =>
      intro x hx
      simp
  | succ i ih =>
      intro x hx
      cases n with
      | zero =>
          omega
      | succ n =>
          have hi' : i ≤ n := by omega
          rw [iteratedDerivWithin_succ']
          have hderEq : EqOn (derivWithin (putnamW g (n + 1)) (Ici (1 : ℝ))) (putnamW g n)
              (Ici (1 : ℝ)) := by
            intro y hy
            exact putnam_derivWithin_W n g hg hy
          have hc := iteratedDerivWithin_congr (s := Ici (1 : ℝ)) (n := i) hderEq
          rw [hc hx]
          have hih := ih n hi' hx
          simpa [Nat.succ_sub_succ_eq_sub] using hih

lemma putnam_iteratedDerivWithin_volterra_self (n : ℕ) (hn : 0 < n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (1 : ℝ))) :
    EqOn (iteratedDerivWithin n (putnamVolterra n g) (Ici (1 : ℝ))) g (Ici (1 : ℝ)) := by
  intro x hx
  have h := putnam_iteratedDerivWithin_W g hg n n le_rfl hx
  cases n with
  | zero =>
      omega
  | succ n =>
      simpa [putnamW] using h

lemma putnam_iteratedDerivWithin_volterra_lt_one (n i : ℕ) (hi : i < n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (1 : ℝ))) :
    iteratedDerivWithin i (putnamVolterra n g) (Ici (1 : ℝ)) 1 = 0 := by
  have hle : i ≤ n := le_of_lt hi
  have h := putnam_iteratedDerivWithin_W g hg n i hle (by simp : (1 : ℝ) ∈ Ici (1 : ℝ))
  have hpos : 0 < n - i := Nat.sub_pos_of_lt hi
  cases n with
  | zero =>
      omega
  | succ n =>
      rw [show putnamVolterra (n + 1) g = putnamW g (n + 1) by rfl]
      rw [h]
      cases hni : n + 1 - i with
      | zero =>
          omega
      | succ k =>
          simp [putnamW, putnamVolterra]

-- fun (f : ℝ → ℝ) (n : ℕ) (x : ℝ) (t : ℝ) ↦ (x - t) ^ (n - 1) * (f t) / ((n - 1)! * t ^ n)
/--
Find an integral formula (i.e., a function $z$ such that $y(x) = \int_{1}^{x} z(t) dt$) for the solution of the differential equation $$\delta (\delta - 1) (\delta - 2) \cdots (\delta - n + 1) y = f(x)$$ with the initial conditions $y(1) = y'(1) = \cdots = y^{(n-1)}(1) = 0$, where $n \in \mathbb{N}$, $f$ is continuous for all $x \ge 1$, and $\delta$ denotes $x\frac{d}{dx}$.
-/
theorem putnam_1963_a3
    (P : ℕ → (ℝ → ℝ) → (ℝ → ℝ))
    (hP : P 0 = id ∧ ∀ i y, P (i + 1) y = P i (fun x ↦ x * deriv y x - i * y x))
    (n : ℕ)
    (hn : 0 < n)
    (f y : ℝ → ℝ)
    (hf : ContinuousOn f (Ici 1))
    (hy : ContDiffOn ℝ n y (Ici 1))
    (hy1 : ContDiffAt ℝ n y 1) :
    (∀ i < n, deriv^[i] y 1 = 0) ∧ (Ici 1).EqOn (P n y) f ↔
    ∀ x ≥ 1, y x = ∫ t in (1 : ℝ)..x, ((fun (f : ℝ → ℝ) (n : ℕ) (x : ℝ) (t : ℝ) ↦ (x - t) ^ (n - 1) * (f t) / ((n - 1)! * t ^ n)) : (ℝ → ℝ) → ℕ → ℝ → ℝ → ℝ ) f n x t := by
  constructor
  · intro h x hxge
    rcases hxge.eq_or_lt with rfl | hxlt_rev
    · have h0 := h.1 0 hn
      simpa using h0
    · have hxlt : (1 : ℝ) < x := hxlt_rev
      have hyI : ContDiffOn ℝ n y (Icc (1 : ℝ) x) := hy.mono Icc_subset_Ici_self
      have hTI := putnam_taylor_identity n hn y hxlt hyI
      have hT0 : taylorWithinEval y (n - 1) (Icc (1 : ℝ) x) 1 x = 0 := by
        rw [taylor_within_apply]
        apply Finset.sum_eq_zero
        intro i hi
        have hin : i < n := by
          have := Finset.mem_range.mp hi
          omega
        have hwithin : iteratedDerivWithin i y (Icc (1 : ℝ) x) 1 = deriv^[i] y 1 := by
          rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxlt)
            (hy1.of_le (by exact_mod_cast le_of_lt hin)) (by simp [hxlt.le])]
          rw [iteratedDeriv_eq_iterate]
        rw [hwithin, h.1 i hin]
        simp
      have hyint : y x =
          ∫ t in (1 : ℝ)..x,
            putnamKernel (n - 1) x t * iteratedDerivWithin n y (Icc (1 : ℝ) x) t := by
        rw [hTI, hT0, sub_zero]
      rw [hyint]
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc (1 : ℝ) x := by
        simpa [uIcc_of_le hxlt.le] using ht
      have htIci : t ∈ Ici (1 : ℝ) := htIcc.1
      have htpos : t ≠ 0 := by linarith [htIcc.1]
      have hct : ContDiffAt ℝ n y t := by
        rcases htIcc.1.eq_or_lt with ht1 | hgt
        · simpa [ht1] using hy1
        · exact hy.contDiffAt (mem_of_superset (isOpen_Ioi.mem_nhds hgt) Ioi_subset_Ici_self)
      have hwithin : iteratedDerivWithin n y (Icc (1 : ℝ) x) t = iteratedDeriv n y t := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxlt) hct htIcc
      have hp := putnam_P_eq_iteratedDeriv P hP n y t hct
      have heqP : P n y t = f t := h.2 htIci
      have hder : iteratedDeriv n y t = f t / t ^ n := by
        have hpow : t ^ n ≠ 0 := pow_ne_zero n htpos
        have hmul : t ^ n * iteratedDeriv n y t = f t := by
          simpa [hp] using heqP
        rw [eq_div_iff hpow]
        simpa [mul_comm] using hmul
      change putnamKernel (n - 1) x t * iteratedDerivWithin n y (Icc (1 : ℝ) x) t =
        (x - t) ^ (n - 1) * f t / ((n - 1)! * t ^ n)
      rw [hwithin, hder]
      simp [putnamKernel, div_eq_mul_inv]
      field_simp [pow_ne_zero n htpos, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 1))]
  · intro h
    let g : ℝ → ℝ := fun t => f t / t ^ n
    have hg : ContinuousOn g (Ici (1 : ℝ)) := by
      exact hf.div (continuousOn_id.pow n)
        (fun t ht => pow_ne_zero n (by linarith [show (1 : ℝ) ≤ t from ht]))
    have hEq : EqOn y (putnamVolterra n g) (Ici (1 : ℝ)) := by
      intro x hx
      rw [h x hx]
      unfold putnamVolterra
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc (1 : ℝ) x := by
        simpa [uIcc_of_le (show (1 : ℝ) ≤ x from hx)] using ht
      have htpos : t ≠ 0 := by linarith [htIcc.1]
      change (x - t) ^ (n - 1) * f t / ((n - 1)! * t ^ n) =
        putnamKernel (n - 1) x t * g t
      simp [putnamKernel, g, div_eq_mul_inv]
      field_simp [pow_ne_zero n htpos, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 1))]
    refine ⟨?_, ?_⟩
    · intro i hi
      have hwithin_y :
          iteratedDerivWithin i y (Ici (1 : ℝ)) 1 = deriv^[i] y 1 := by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (1 : ℝ))
          (hy1.of_le (by exact_mod_cast le_of_lt hi)) (by simp)]
        rw [iteratedDeriv_eq_iterate]
      have hcong := iteratedDerivWithin_congr (s := Ici (1 : ℝ)) (n := i) hEq
        (by simp : (1 : ℝ) ∈ Ici (1 : ℝ))
      have hzero := putnam_iteratedDerivWithin_volterra_lt_one n i hi g hg
      rw [← hwithin_y, hcong, hzero]
    · intro x hx
      have hct : ContDiffAt ℝ n y x := by
        rcases (show (1 : ℝ) ≤ x from hx).eq_or_lt with rfl | hxlt
        · exact hy1
        · exact hy.contDiffAt (mem_of_superset (isOpen_Ioi.mem_nhds hxlt) Ioi_subset_Ici_self)
      have hwithin_y : iteratedDerivWithin n y (Ici (1 : ℝ)) x = iteratedDeriv n y x := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (1 : ℝ)) hct hx
      have hcong := iteratedDerivWithin_congr (s := Ici (1 : ℝ)) (n := n) hEq hx
      have hself := putnam_iteratedDerivWithin_volterra_self n hn g hg hx
      have hiter : iteratedDeriv n y x = g x := by
        rw [← hwithin_y, hcong, hself]
      have hp := putnam_P_eq_iteratedDeriv P hP n y x hct
      rw [hp, hiter]
      have hxpos : x ≠ 0 := by linarith [show (1 : ℝ) ≤ x from hx]
      simp [g]
      field_simp [pow_ne_zero n hxpos]
