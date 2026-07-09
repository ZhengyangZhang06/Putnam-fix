import Mathlib

open Nat Set Topology Filter

noncomputable abbrev putnam_1963_a3_solution : (ℝ → ℝ) → ℕ → ℝ → ℝ → ℝ :=
  fun f n x t => f t * (x - t) ^ (n - 1) / t ^ n / ((n - 1).factorial : ℝ)

lemma putnam_1963_a3_euler_iteratedDeriv_sub (m : ℕ) {y : ℝ → ℝ} {x : ℝ}
    (hy : ContDiffAt ℝ (m + 1 : ℕ) y x) :
    iteratedDeriv m (fun z => z * deriv y z - (m : ℝ) * y z) x =
      x * iteratedDeriv (m + 1) y x := by
  have hderiv : ContDiffAt ℝ (m : ℕ) (deriv y) x := by
    exact hy.derivWithin (by norm_num)
  have hy_m : ContDiffAt ℝ (m : ℕ) y x := hy.of_le (by norm_num)
  rw [iteratedDeriv_fun_sub]
  · rw [iteratedDeriv_fun_mul]
    · rw [iteratedDeriv_const_mul hy_m]
      have hsplit :
          (fun i : ℕ => (↑(m.choose i) * iteratedDeriv i (fun z : ℝ => z) x *
              iteratedDeriv (m - i) (deriv y) x : ℝ)) =
            (fun i : ℕ => (if i = 0 then x * iteratedDeriv m (deriv y) x else 0) +
              (if i = 1 then (m : ℝ) * iteratedDeriv (m - 1) (deriv y) x else 0)) := by
        funext i
        by_cases h0 : i = 0
        · subst i
          simp
        · by_cases h1 : i = 1
          · subst i
            simp [h0]
          · simp [iteratedDeriv_fun_id, h0, h1]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
      cases m with
      | zero => simp [iteratedDeriv_succ']
      | succ m => simp [iteratedDeriv_succ']
    · fun_prop
    · exact hderiv
  · exact (contDiffAt_id.mul hderiv)
  · exact contDiffAt_const.mul hy_m

lemma putnam_1963_a3_P_eq_pow_iteratedDeriv
    (P : ℕ → (ℝ → ℝ) → (ℝ → ℝ))
    (hP : P 0 = id ∧ ∀ i y, P (i + 1) y = P i (fun x ↦ x * deriv y x - i * y x))
    (m : ℕ) {y : ℝ → ℝ} {x : ℝ}
    (hy : ContDiffAt ℝ (m : ℕ) y x) :
    P m y x = x ^ m * iteratedDeriv m y x := by
  induction m generalizing y with
  | zero =>
      simp [hP.1]
  | succ m ih =>
      have hderiv : ContDiffAt ℝ (m : ℕ) (deriv y) x := by
        exact hy.derivWithin (by norm_num)
      have hy_m : ContDiffAt ℝ (m : ℕ) y x := hy.of_le (by norm_num)
      have hg : ContDiffAt ℝ (m : ℕ) (fun z => z * deriv y z - (m : ℝ) * y z) x := by
        exact (contDiffAt_id.mul hderiv).sub (contDiffAt_const.mul hy_m)
      rw [hP.2 m y]
      calc
        P m (fun x => x * deriv y x - ↑m * y x) x =
            x ^ m * iteratedDeriv m (fun z => z * deriv y z - (m : ℝ) * y z) x := ih hg
        _ = x ^ m * (x * iteratedDeriv (m + 1) y x) := by
            rw [putnam_1963_a3_euler_iteratedDeriv_sub m hy]
        _ = x ^ (m + 1) * iteratedDeriv (m + 1) y x := by ring

lemma putnam_1963_a3_taylor_integral_remainder_zero
    (n : ℕ) (hn : 0 < n) {f : ℝ → ℝ} {a x : ℝ} (hax : a < x)
    (hf : ContDiffOn ℝ (n : ℕ) f (Icc a x))
    (hfa : ContDiffAt ℝ (n : ℕ) f a)
    (hzero : ∀ i < n, iteratedDeriv i f a = 0) :
    f x = ∫ t in a..x,
      (((((n - 1).factorial : ℝ)⁻¹ * (x - t) ^ (n - 1)) : ℝ) *
        iteratedDerivWithin n f (Icc a x) t) := by
  let m := n - 1
  have hm1 : m + 1 = n := Nat.sub_add_cancel hn
  have hfu : ContDiffOn ℝ (m + 1 : ℕ) f (Icc a x) := by simpa [hm1] using hf
  have hfm : ContDiffOn ℝ (m : ℕ) f (Icc a x) := hfu.of_succ
  have hfdiff : DifferentiableOn ℝ (iteratedDerivWithin m f (Icc a x)) (Ioo a x) := by
    exact (hfu.differentiableOn_iteratedDerivWithin
      (Nat.cast_lt.mpr m.lt_succ_self) (uniqueDiffOn_Icc hax)).mono Ioo_subset_Icc_self
  have hcontG : ContinuousOn (fun y => taylorWithinEval f m (Icc a x) y x) (Icc a x) :=
    continuousOn_taylorWithinEval (uniqueDiffOn_Icc hax) hfm
  have hderivG : ∀ y ∈ Ioo a x,
      HasDerivAt (fun u => taylorWithinEval f m (Icc a x) u x)
        ((((m.factorial : ℝ)⁻¹ * (x - y) ^ m) : ℝ) *
          iteratedDerivWithin (m + 1) f (Icc a x) y) y := by
    intro y hy
    simpa [smul_eq_mul] using
      taylorWithinEval_hasDerivAt_Ioo (f := f) (a := a) (b := x) (t := y)
        x hax hy hfm hfdiff
  have hcontKernel :
      ContinuousOn (fun y : ℝ => ((m.factorial : ℝ)⁻¹ * (x - y) ^ m : ℝ)) (Icc a x) := by
    fun_prop
  have hcontIDeriv : ContinuousOn (iteratedDerivWithin (m + 1) f (Icc a x)) (Icc a x) :=
    hfu.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hax)
  have hcontDeriv : ContinuousOn
      (fun y => (((m.factorial : ℝ)⁻¹ * (x - y) ^ m : ℝ) *
        iteratedDerivWithin (m + 1) f (Icc a x) y)) (Icc a x) :=
    hcontKernel.mul hcontIDeriv
  have hint : IntervalIntegrable
      (fun y => (((m.factorial : ℝ)⁻¹ * (x - y) ^ m : ℝ) *
        iteratedDerivWithin (m + 1) f (Icc a x) y)) MeasureTheory.volume a x :=
    hcontDeriv.intervalIntegrable_of_Icc hax.le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax.le hcontG hderivG hint
  have hTaylor0 : taylorWithinEval f m (Icc a x) a x = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hkltm1 : k < m + 1 := by simpa using hk
    have hklt : k < n := by simpa [hm1] using hkltm1
    have hwithin : iteratedDerivWithin k f (Icc a x) a = iteratedDeriv k f a := by
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hax)
        (hfa.of_le (by exact_mod_cast hklt.le)) (left_mem_Icc.mpr hax.le)
    rw [hwithin, hzero k hklt]
    simp
  calc
    f x = taylorWithinEval f m (Icc a x) x x - taylorWithinEval f m (Icc a x) a x := by
      simp [taylorWithinEval_self, hTaylor0]
    _ = ∫ y in a..x, (((m.factorial : ℝ)⁻¹ * (x - y) ^ m : ℝ) *
        iteratedDerivWithin (m + 1) f (Icc a x) y) := hftc.symm
    _ = ∫ t in a..x, (((((n - 1).factorial : ℝ)⁻¹ * (x - t) ^ (n - 1)) : ℝ) *
        iteratedDerivWithin n f (Icc a x) t) := by
      simp [m, hm1]

noncomputable def putnam_1963_a3_primitive (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => g
  | m + 1 => fun x => ∫ t in (1 : ℝ)..x, putnam_1963_a3_primitive g m t

lemma putnam_1963_a3_primitive_hasDerivWithinAt
    {g : ℝ → ℝ} (m : ℕ)
    (hg : ContinuousOn (putnam_1963_a3_primitive g m) (Ici (1 : ℝ))) :
    ∀ x ∈ Ici (1 : ℝ),
      HasDerivWithinAt (putnam_1963_a3_primitive g (m + 1))
        (putnam_1963_a3_primitive g m x) (Ici (1 : ℝ)) x := by
  intro x hx
  have hsub : uIcc (1 : ℝ) x ⊆ Ici (1 : ℝ) := by
    intro z hz
    have hzIcc : z ∈ Icc (1 : ℝ) x := by
      simpa [Set.uIcc_of_le (show (1 : ℝ) ≤ x from hx)] using hz
    exact hzIcc.1
  have hint : IntervalIntegrable (putnam_1963_a3_primitive g m) MeasureTheory.volume (1 : ℝ) x :=
    (hg.mono hsub).intervalIntegrable
  by_cases hx1 : x = 1
  · subst x
    have hmeas : StronglyMeasurableAtFilter (putnam_1963_a3_primitive g m)
        (𝓝[Ioi (1 : ℝ)] (1 : ℝ)) MeasureTheory.volume := by
      exact (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ici (1 : ℝ)).filter_mono
        (nhdsWithin_mono (1 : ℝ) Ioi_subset_Ici_self)
    have hcont : ContinuousWithinAt (putnam_1963_a3_primitive g m)
        (Ioi (1 : ℝ)) (1 : ℝ) :=
      (hg.continuousWithinAt self_mem_Ici).mono Ioi_subset_Ici_self
    simpa [putnam_1963_a3_primitive] using
      (intervalIntegral.integral_hasDerivWithinAt_right
        (f := putnam_1963_a3_primitive g m) (a := (1 : ℝ)) (b := (1 : ℝ))
        (s := Ici (1 : ℝ)) (t := Ioi (1 : ℝ)) hint hmeas hcont)
  · have hxlt : (1 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hx1)
    have hcontAt : ContinuousAt (putnam_1963_a3_primitive g m) x :=
      (hg.continuousWithinAt hx).continuousAt (Ici_mem_nhds hxlt)
    have hmeas : StronglyMeasurableAtFilter (putnam_1963_a3_primitive g m)
        (𝓝 x) MeasureTheory.volume := by
      exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioi (1 : ℝ)) isOpen_Ioi
        (fun z hz => (hg.continuousWithinAt
          (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz)))).continuousAt
          (Ici_mem_nhds (Set.mem_Ioi.mp hz)))
        x hxlt
    simpa [putnam_1963_a3_primitive] using
      (intervalIntegral.integral_hasDerivAt_right
        (f := putnam_1963_a3_primitive g m) (a := (1 : ℝ)) (b := x)
        hint hmeas hcontAt).hasDerivWithinAt

lemma putnam_1963_a3_primitive_continuousOn
    {g : ℝ → ℝ} (hg : ContinuousOn g (Ici (1 : ℝ))) :
    ∀ m : ℕ, ContinuousOn (putnam_1963_a3_primitive g m) (Ici (1 : ℝ))
  | 0 => hg
  | m + 1 =>
      HasDerivWithinAt.continuousOn
        (putnam_1963_a3_primitive_hasDerivWithinAt m
          (putnam_1963_a3_primitive_continuousOn hg m))

lemma putnam_1963_a3_primitive_iteratedDerivWithin
    {g : ℝ → ℝ} (hg : ContinuousOn g (Ici (1 : ℝ))) :
    ∀ m i : ℕ, i ≤ m →
      EqOn (iteratedDerivWithin i (putnam_1963_a3_primitive g m) (Ici (1 : ℝ)))
        (putnam_1963_a3_primitive g (m - i)) (Ici (1 : ℝ)) := by
  intro m i hi
  induction i generalizing m with
  | zero =>
      intro x hx
      simp
  | succ i ih =>
      intro x hx
      have him : i ≤ m := Nat.le_trans (Nat.le_succ i) hi
      have hlt : i < m := Nat.lt_of_succ_le hi
      have hpred : m - i = (m - (i + 1)) + 1 := by
        omega
      rw [iteratedDerivWithin_succ]
      have hcongr := iteratedDerivWithin_congr (n := i)
        (f := putnam_1963_a3_primitive g m)
        (g := putnam_1963_a3_primitive g m)
        (s := Ici (1 : ℝ)) (fun y hy => rfl)
      have hderiv_congr :
          EqOn (iteratedDerivWithin i (putnam_1963_a3_primitive g m) (Ici (1 : ℝ)))
            (putnam_1963_a3_primitive g (m - i)) (Ici (1 : ℝ)) :=
        ih m him
      rw [derivWithin_congr hderiv_congr (hderiv_congr hx), hpred]
      exact (putnam_1963_a3_primitive_hasDerivWithinAt (m - (i + 1))
        (putnam_1963_a3_primitive_continuousOn hg (m - (i + 1))) x hx).derivWithin
          ((uniqueDiffOn_Ici (1 : ℝ)).uniqueDiffWithinAt hx)

lemma putnam_1963_a3_primitive_zero_at_one (g : ℝ → ℝ) :
    ∀ m : ℕ, 0 < m → putnam_1963_a3_primitive g m 1 = 0
  | 0, h => (Nat.not_lt_zero _ h).elim
  | m + 1, _ => by simp [putnam_1963_a3_primitive]

lemma putnam_1963_a3_primitive_shift (g : ℝ → ℝ) :
    ∀ m : ℕ,
      putnam_1963_a3_primitive (putnam_1963_a3_primitive g 1) m =
        putnam_1963_a3_primitive g (m + 1)
  | 0 => rfl
  | m + 1 => by
      change (fun x => ∫ t in (1 : ℝ)..x,
          putnam_1963_a3_primitive (putnam_1963_a3_primitive g 1) m t) =
        fun x => ∫ t in (1 : ℝ)..x, putnam_1963_a3_primitive g (m + 1) t
      rw [putnam_1963_a3_primitive_shift g m]

lemma putnam_1963_a3_kernel_eq_primitive
    {g : ℝ → ℝ} (hg : ContinuousOn g (Ici (1 : ℝ))) :
    ∀ m : ℕ, EqOn
      (fun x : ℝ => ∫ t in (1 : ℝ)..x,
        (((m.factorial : ℝ)⁻¹ * (x - t) ^ m : ℝ) * g t))
      (putnam_1963_a3_primitive g (m + 1)) (Ici (1 : ℝ)) := by
  intro m
  induction m generalizing g with
  | zero =>
      intro x hx
      apply intervalIntegral.integral_congr
      intro t ht
      simp [putnam_1963_a3_primitive]
  | succ m ih =>
      intro x hx
      let G : ℝ → ℝ := putnam_1963_a3_primitive g 1
      have hGcont : ContinuousOn G (Ici (1 : ℝ)) :=
        putnam_1963_a3_primitive_continuousOn hg 1
      have hsub : uIcc (1 : ℝ) x ⊆ Ici (1 : ℝ) := by
        intro z hz
        have hzIcc : z ∈ Icc (1 : ℝ) x := by
          simpa [Set.uIcc_of_le (show (1 : ℝ) ≤ x from hx)] using hz
        exact hzIcc.1
      have hintg : IntervalIntegrable g MeasureTheory.volume (1 : ℝ) x :=
        (hg.mono hsub).intervalIntegrable
      have hintv' : IntervalIntegrable
          (fun t : ℝ => - (x - t) ^ m / (m.factorial : ℝ))
          MeasureTheory.volume (1 : ℝ) x := by
        exact (by fun_prop : ContinuousOn
          (fun t : ℝ => - (x - t) ^ m / (m.factorial : ℝ)) (uIcc (1 : ℝ) x)).intervalIntegrable
      have hderivPrim :
          ∀ t ∈ uIcc (1 : ℝ) x,
            HasDerivWithinAt G (g t) (uIcc (1 : ℝ) x) t := by
        intro t ht
        have htIci : t ∈ Ici (1 : ℝ) := by
          have htIcc : t ∈ Icc (1 : ℝ) x := by
            simpa [Set.uIcc_of_le (show (1 : ℝ) ≤ x from hx)] using ht
          exact htIcc.1
        exact (putnam_1963_a3_primitive_hasDerivWithinAt 0 hg t htIci).mono (by
            intro z hz
            have hzIcc : z ∈ Icc (1 : ℝ) x := by
              simpa [Set.uIcc_of_le (show (1 : ℝ) ≤ x from hx)] using hz
            exact hzIcc.1)
      have hpoly :
          ∀ t ∈ uIcc (1 : ℝ) x,
            HasDerivWithinAt (fun t : ℝ =>
              (x - t) ^ (m + 1) / (((m + 1).factorial : ℝ)))
              (-(x - t) ^ m / (m.factorial : ℝ)) (uIcc (1 : ℝ) x) t := by
        intro t ht
        have h :
            HasDerivAt (fun t : ℝ =>
              (x - t) ^ (m + 1) / (((m + 1).factorial : ℝ)))
              (-(x - t) ^ m / (m.factorial : ℝ)) t := by
          have hpow : HasDerivAt (fun t : ℝ => (x - t) ^ (m + 1))
              ((m + 1 : ℝ) * (x - t) ^ m * (-1)) t := by
            simpa using ((hasDerivAt_const t x).sub (hasDerivAt_id t)).pow (m + 1)
          convert hpow.div_const (((m + 1).factorial : ℝ)) using 1
          have hfac : (((m + 1).factorial : ℝ) : ℝ) =
              (m + 1 : ℝ) * (m.factorial : ℝ) := by
            norm_num [Nat.factorial_succ, Nat.cast_mul]
          have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
          have hmf : ((m.factorial : ℝ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero m
          rw [hfac]
          field_simp [hm1, hmf]
        exact h.hasDerivWithinAt
      have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
        (u := G)
        (v := fun t : ℝ => (x - t) ^ (m + 1) / (((m + 1).factorial : ℝ)))
        (u' := g)
        (v' := fun t : ℝ => - (x - t) ^ m / (m.factorial : ℝ))
        hderivPrim hpoly
        hintg hintv'
      have hboundary :
          G x *
              ((x - x) ^ (m + 1) / (((m + 1).factorial : ℝ))) -
            G 1 *
              ((x - 1) ^ (m + 1) / (((m + 1).factorial : ℝ))) = 0 := by
        simp [G, putnam_1963_a3_primitive]
      rw [hboundary, zero_sub] at hparts
      have hleft :
          ∫ t in (1 : ℝ)..x,
              G t * (-(x - t) ^ m / (m.factorial : ℝ)) =
            -∫ t in (1 : ℝ)..x,
              (((m.factorial : ℝ)⁻¹ * (x - t) ^ m : ℝ) * G t) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t ht
        have hmf : ((m.factorial : ℝ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero m
        field_simp [hmf]
      have hright :
          ∫ t in (1 : ℝ)..x,
              g t * ((x - t) ^ (m + 1) / (((m + 1).factorial : ℝ))) =
            ∫ t in (1 : ℝ)..x,
              (((((m + 1).factorial : ℝ)⁻¹ * (x - t) ^ (m + 1)) : ℝ) * g t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hmf : (((m + 1).factorial : ℝ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (m + 1)
        field_simp [hmf]
      rw [hleft, hright] at hparts
      have hkernel :
          (∫ t in (1 : ℝ)..x,
              (((((m + 1).factorial : ℝ)⁻¹ * (x - t) ^ (m + 1)) : ℝ) * g t)) =
            ∫ t in (1 : ℝ)..x,
              (((m.factorial : ℝ)⁻¹ * (x - t) ^ m : ℝ) * G t) := by
        exact (neg_inj.mp hparts).symm
      calc
        (∫ t in (1 : ℝ)..x,
            (((((m + 1).factorial : ℝ)⁻¹ * (x - t) ^ (m + 1)) : ℝ) * g t)) =
            ∫ t in (1 : ℝ)..x,
              (((m.factorial : ℝ)⁻¹ * (x - t) ^ m : ℝ) * G t) := hkernel
        _ = putnam_1963_a3_primitive G (m + 1) x := (ih hGcont) hx
        _ = putnam_1963_a3_primitive g (m + 2) x := by
          rw [putnam_1963_a3_primitive_shift g (m + 1)]

lemma putnam_1963_a3_ratio_kernel (n : ℕ) (_hn : 0 < n) {x t a : ℝ}
    (htne : t ≠ 0) :
    (((((n - 1).factorial : ℝ)⁻¹ * (x - t) ^ (n - 1)) : ℝ) * (a / t ^ n)) =
      a * (x - t) ^ (n - 1) / t ^ n / ((n - 1).factorial : ℝ) := by
  have htpow : t ^ n ≠ 0 := pow_ne_zero n htne
  have hfact : ((n - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  field_simp [htpow, hfact]

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
    ∀ x ≥ 1, y x = ∫ t in (1 : ℝ)..x, putnam_1963_a3_solution f n x t :=
  by
  constructor
  · rintro ⟨hinit, hEq⟩ x hx
    by_cases hx1 : x = 1
    · subst x
      have hy10 : y 1 = 0 := by
        simpa using hinit 0 hn
      simp [hy10]
    · have hlt : (1 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hx1)
      have hyIcc : ContDiffOn ℝ (n : ℕ) y (Icc (1 : ℝ) x) := by
        exact hy.mono Set.Icc_subset_Ici_self
      have hzeroIter : ∀ i < n, iteratedDeriv i y 1 = 0 := by
        intro i hi
        simpa [iteratedDeriv_eq_iterate] using hinit i hi
      have hTaylor := putnam_1963_a3_taylor_integral_remainder_zero
        n hn hlt hyIcc hy1 hzeroIter
      rw [hTaylor]
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc (1 : ℝ) x := by
        simpa [Set.uIcc_of_le hlt.le] using ht
      have htIci : t ∈ Ici (1 : ℝ) := htIcc.1
      have hcdt : ContDiffAt ℝ (n : ℕ) y t := by
        by_cases ht1 : t = 1
        · simpa [ht1] using hy1
        · have hgt : (1 : ℝ) < t := lt_of_le_of_ne htIcc.1 (Ne.symm ht1)
          exact hy.contDiffAt (Ici_mem_nhds hgt)
      have hwithin :
          iteratedDerivWithin n y (Icc (1 : ℝ) x) t = iteratedDeriv n y t := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt) hcdt htIcc
      have hPcalc := putnam_1963_a3_P_eq_pow_iteratedDeriv P hP n hcdt
      have hPval : P n y t = f t := hEq htIci
      have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one htIcc.1)
      have htpow : t ^ n ≠ 0 := pow_ne_zero n htne
      have hderiv : iteratedDeriv n y t = f t / t ^ n := by
        rw [hPcalc] at hPval
        rw [← hPval]
        field_simp [htpow]
      change (((((n - 1).factorial : ℝ)⁻¹ * (x - t) ^ (n - 1)) : ℝ) *
          iteratedDerivWithin n y (Icc (1 : ℝ) x) t) =
        putnam_1963_a3_solution f n x t
      rw [hwithin, hderiv, putnam_1963_a3_solution]
      exact putnam_1963_a3_ratio_kernel n hn (x := x) (t := t) (a := f t) htne
  · intro h
    let g : ℝ → ℝ := fun t => f t / t ^ n
    have hg : ContinuousOn g (Ici (1 : ℝ)) := by
      dsimp [g]
      refine hf.div (continuousOn_id.pow n) ?_
      intro t ht
      exact pow_ne_zero n (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))
    have hEqPrim : EqOn y (putnam_1963_a3_primitive g n) (Ici (1 : ℝ)) := by
      intro x hx
      have hkernel :=
        putnam_1963_a3_kernel_eq_primitive hg (n - 1) hx
      have hconv :
          (∫ t in (1 : ℝ)..x, putnam_1963_a3_solution f n x t) =
            ∫ t in (1 : ℝ)..x,
              (((((n - 1).factorial : ℝ)⁻¹ * (x - t) ^ (n - 1)) : ℝ) * g t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Icc (1 : ℝ) x := by
          simpa [Set.uIcc_of_le (show (1 : ℝ) ≤ x from hx)] using ht
        have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one htIcc.1)
        rw [putnam_1963_a3_solution]
        dsimp [g]
        exact (putnam_1963_a3_ratio_kernel n hn (x := x) (t := t) (a := f t) htne).symm
      calc
        y x = ∫ t in (1 : ℝ)..x, putnam_1963_a3_solution f n x t := h x hx
        _ = ∫ t in (1 : ℝ)..x,
              (((((n - 1).factorial : ℝ)⁻¹ * (x - t) ^ (n - 1)) : ℝ) * g t) := hconv
        _ = putnam_1963_a3_primitive g ((n - 1) + 1) x := hkernel
        _ = putnam_1963_a3_primitive g n x := by rw [Nat.sub_add_cancel hn]
    constructor
    · intro i hi
      have hwithin_y :
          iteratedDerivWithin i y (Ici (1 : ℝ)) 1 = iteratedDeriv i y 1 := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (1 : ℝ))
          (hy1.of_le (by exact_mod_cast hi.le)) self_mem_Ici
      have hcongr :
          iteratedDerivWithin i y (Ici (1 : ℝ)) 1 =
            iteratedDerivWithin i (putnam_1963_a3_primitive g n) (Ici (1 : ℝ)) 1 :=
        (iteratedDerivWithin_congr (n := i) (s := Ici (1 : ℝ)) hEqPrim) self_mem_Ici
      have hprim :
          iteratedDerivWithin i (putnam_1963_a3_primitive g n) (Ici (1 : ℝ)) 1 =
            putnam_1963_a3_primitive g (n - i) 1 :=
        (putnam_1963_a3_primitive_iteratedDerivWithin hg n i hi.le) self_mem_Ici
      have hiter : iteratedDeriv i y 1 = 0 := by
        calc
          iteratedDeriv i y 1 = iteratedDerivWithin i y (Ici (1 : ℝ)) 1 := hwithin_y.symm
          _ = iteratedDerivWithin i (putnam_1963_a3_primitive g n) (Ici (1 : ℝ)) 1 := hcongr
          _ = putnam_1963_a3_primitive g (n - i) 1 := hprim
          _ = 0 := putnam_1963_a3_primitive_zero_at_one g (n - i)
            (Nat.sub_pos_of_lt hi)
      simpa [iteratedDeriv_eq_iterate] using hiter
    · intro x hx
      have hcdx : ContDiffAt ℝ (n : ℕ) y x := by
        by_cases hx1 : x = 1
        · simpa [hx1] using hy1
        · have hxlt : (1 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hx1)
          exact hy.contDiffAt (Ici_mem_nhds hxlt)
      have hwithin_y :
          iteratedDerivWithin n y (Ici (1 : ℝ)) x = iteratedDeriv n y x := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (1 : ℝ)) hcdx hx
      have hcongr :
          iteratedDerivWithin n y (Ici (1 : ℝ)) x =
            iteratedDerivWithin n (putnam_1963_a3_primitive g n) (Ici (1 : ℝ)) x :=
        (iteratedDerivWithin_congr (n := n) (s := Ici (1 : ℝ)) hEqPrim) hx
      have hprim :
          iteratedDerivWithin n (putnam_1963_a3_primitive g n) (Ici (1 : ℝ)) x = g x := by
        have h0 :=
          (putnam_1963_a3_primitive_iteratedDerivWithin hg n n le_rfl) hx
        simpa [putnam_1963_a3_primitive] using h0
      have hiter : iteratedDeriv n y x = g x := by
        calc
          iteratedDeriv n y x = iteratedDerivWithin n y (Ici (1 : ℝ)) x := hwithin_y.symm
          _ = iteratedDerivWithin n (putnam_1963_a3_primitive g n) (Ici (1 : ℝ)) x := hcongr
          _ = g x := hprim
      have hPcalc := putnam_1963_a3_P_eq_pow_iteratedDeriv P hP n hcdx
      have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
      have hxpow : x ^ n ≠ 0 := pow_ne_zero n hxne
      rw [hPcalc, hiter]
      dsimp [g]
      field_simp [hxpow]
