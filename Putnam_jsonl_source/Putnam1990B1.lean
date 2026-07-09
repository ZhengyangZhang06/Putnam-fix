import Mathlib

open Filter Topology Nat

-- {fun x : ℝ => (Real.sqrt 1990) * Real.exp x, fun x : ℝ => -(Real.sqrt 1990) * Real.exp x}
/--
Find all real-valued continuously differentiable functions $f$ on the real line such that for all $x$, $(f(x))^2=\int_0^x [(f(t))^2+(f'(t))^2]\,dt+1990$.
-/
theorem putnam_1990_b1
    (P : (ℝ → ℝ) → Prop)
    (P_def : ∀ f, P f ↔ ∀ x,
      (f x) ^ 2 = (∫ t in (0 : ℝ)..x, (f t) ^ 2 + (deriv f t) ^ 2) + 1990)
    (f : ℝ → ℝ) :
    (ContDiff ℝ 1 f ∧ P f) ↔ f ∈ (({fun x : ℝ => (Real.sqrt 1990) * Real.exp x, fun x : ℝ => -(Real.sqrt 1990) * Real.exp x}) : Set (ℝ → ℝ) ) := by
  have deriv_eq_self_of_integral_eq : ∀ g : ℝ → ℝ, ContDiff ℝ 1 g →
      (∀ x, (g x) ^ 2 = (∫ t in (0 : ℝ)..x, (g t) ^ 2 + (deriv g t) ^ 2) + 1990) →
      ∀ x, deriv g x = g x := by
    intro g hg hP x
    have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hcont_g : Continuous g := hg.continuous
    have hcont_deriv : Continuous (deriv g) :=
      hg.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
    have hcont_int : Continuous fun t : ℝ => (g t) ^ 2 + (deriv g t) ^ 2 :=
      (hcont_g.pow 2).add (hcont_deriv.pow 2)
    let integrand : ℝ → ℝ := fun t => (g t) ^ 2 + (deriv g t) ^ 2
    have hleft : HasDerivAt (fun y : ℝ => (g y) ^ 2) (2 * g x * deriv g x) x := by
      simpa [pow_one, Nat.cast_ofNat, mul_assoc] using ((hgdiff x).hasDerivAt.pow 2)
    have hright0 : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, integrand t) (integrand x) x := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · exact hcont_int.intervalIntegrable 0 x
      · exact hcont_int.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 x)
      · exact hcont_int.continuousAt
    have hright : HasDerivAt (fun y : ℝ => (∫ t in (0 : ℝ)..y, integrand t) + 1990)
        (integrand x) x := by
      exact hright0.add_const 1990
    have hevent : (fun y : ℝ => (∫ t in (0 : ℝ)..y, integrand t) + 1990) =ᶠ[𝓝 x]
        (fun y : ℝ => (g y) ^ 2) := by
      exact Filter.Eventually.of_forall (fun y => (hP y).symm)
    have hleft' : HasDerivAt (fun y : ℝ => (∫ t in (0 : ℝ)..y, integrand t) + 1990)
        (2 * g x * deriv g x) x := hleft.congr_of_eventuallyEq hevent
    have huniq : 2 * g x * deriv g x = (g x) ^ 2 + (deriv g x) ^ 2 := by
      simpa [integrand] using hleft'.unique hright
    have hsq : (deriv g x - g x) ^ 2 = 0 := by
      nlinarith [huniq]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have P_of_deriv_eq_self : ∀ g : ℝ → ℝ, ContDiff ℝ 1 g → (∀ x, deriv g x = g x) →
      (g 0) ^ 2 = (1990 : ℝ) → P g := by
    intro g hg hder h0
    refine (P_def g).2 ?_
    have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    intro x
    have hsqcd : ContDiffOn ℝ 1 (fun t : ℝ => (g t) ^ 2) (Set.uIcc (0 : ℝ) x) := by
      exact (hg.contDiffOn.pow 2)
    have hftc := intervalIntegral.integral_deriv_of_contDiffOn_uIcc hsqcd
    calc
      (g x) ^ 2 = ((g x) ^ 2 - (g 0) ^ 2) + 1990 := by
        rw [h0]
        ring
      _ = (∫ t in (0 : ℝ)..x, deriv (fun y : ℝ => (g y) ^ 2) t) + 1990 := by
        rw [hftc]
      _ = (∫ t in (0 : ℝ)..x, (g t) ^ 2 + (deriv g t) ^ 2) + 1990 := by
        congr 1
        exact intervalIntegral.integral_congr (fun t ht => by
          change deriv (g ^ 2) t = (g t) ^ 2 + (deriv g t) ^ 2
          rw [deriv_pow (hgdiff t) 2, hder t]
          ring)
  have exp_solution : ∀ c : ℝ, c ^ 2 = (1990 : ℝ) →
      ContDiff ℝ 1 (fun x : ℝ => c * Real.exp x) ∧ P (fun x : ℝ => c * Real.exp x) := by
    intro c hc
    have hcd : ContDiff ℝ 1 (fun x : ℝ => c * Real.exp x) := by
      exact contDiff_const.mul Real.contDiff_exp
    have hder : ∀ x : ℝ, deriv (fun y : ℝ => c * Real.exp y) x = c * Real.exp x := by
      intro x
      exact ((Real.hasDerivAt_exp x).const_mul c).deriv
    have h0 : ((fun x : ℝ => c * Real.exp x) 0) ^ 2 = (1990 : ℝ) := by
      simp [Real.exp_zero, hc]
    exact ⟨hcd, P_of_deriv_eq_self (fun x : ℝ => c * Real.exp x) hcd hder h0⟩
  constructor
  · rintro ⟨hf, hPf⟩
    have hEq : ∀ x, (f x) ^ 2 = (∫ t in (0 : ℝ)..x, (f t) ^ 2 + (deriv f t) ^ 2) + 1990 :=
      (P_def f).1 hPf
    have hderiv : ∀ x, deriv f x = f x := deriv_eq_self_of_integral_eq f hf hEq
    have hf0sq : (f 0) ^ 2 = (1990 : ℝ) := by
      simpa using hEq 0
    have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hprodDiff : Differentiable ℝ (fun x : ℝ => f x * Real.exp (-x)) := by
      fun_prop
    have hprodDeriv : ∀ x, deriv (fun y : ℝ => f y * Real.exp (-y)) x = 0 := by
      intro x
      have hfder : HasDerivAt f (f x) x := ((hfdiff x).hasDerivAt).congr_deriv (hderiv x)
      have hexpneg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
        simpa using (hasDerivAt_neg' x).exp
      have hprod := hfder.mul hexpneg
      change deriv (f * fun y : ℝ => Real.exp (-y)) x = 0
      rw [hprod.deriv]
      ring
    have hconst : ∀ x, f x * Real.exp (-x) = f 0 := by
      intro x
      simpa using is_const_of_deriv_eq_zero hprodDiff hprodDeriv x 0
    have hform : ∀ x, f x = f 0 * Real.exp x := by
      intro x
      have h := congrArg (fun y : ℝ => y * Real.exp x) (hconst x)
      change (f x * Real.exp (-x)) * Real.exp x = f 0 * Real.exp x at h
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
      exact h
    have hf0_cases : f 0 = Real.sqrt 1990 ∨ f 0 = -Real.sqrt 1990 := by
      have hs : (f 0) ^ 2 = (Real.sqrt 1990) ^ 2 := by
        rw [Real.sq_sqrt]
        · exact hf0sq
        · norm_num
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hs
    rcases hf0_cases with hpos | hneg
    · have hf_eq_pos : f = fun x : ℝ => (Real.sqrt 1990) * Real.exp x := by
        funext x
        rw [hform x, hpos]
      rw [hf_eq_pos]
      simp
    · have hf_eq_neg : f = fun x : ℝ => -(Real.sqrt 1990) * Real.exp x := by
        funext x
        rw [hform x, hneg]
      rw [hf_eq_neg]
      simp
  · intro hfmem
    rcases (by simpa using hfmem :
        f = (fun x : ℝ => (Real.sqrt 1990) * Real.exp x) ∨
          f = (fun x : ℝ => -(Real.sqrt 1990) * Real.exp x)) with hpos | hneg
    · subst f
      have hs : (Real.sqrt 1990) ^ 2 = (1990 : ℝ) := by
        exact Real.sq_sqrt (by norm_num)
      simpa using exp_solution (Real.sqrt 1990) hs
    · subst f
      have hs : (-(Real.sqrt 1990)) ^ 2 = (1990 : ℝ) := by
        rw [neg_sq]
        exact Real.sq_sqrt (by norm_num)
      simpa using exp_solution (-(Real.sqrt 1990)) hs
