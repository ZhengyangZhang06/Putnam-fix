import Mathlib

open Filter Topology Nat

abbrev putnam_1990_b1_solution : Set (ℝ → ℝ) :=
  {f | ∃ c : ℝ, c ∈ ({Real.sqrt 1990, -Real.sqrt 1990} : Set ℝ) ∧
    f = (fun x : ℝ => c * Real.exp x)}

/--
Find all real-valued continuously differentiable functions $f$ on the real line such that for all $x$, $(f(x))^2=\int_0^x [(f(t))^2+(f'(t))^2]\,dt+1990$.
-/
theorem putnam_1990_b1
    (P : (ℝ → ℝ) → Prop)
    (P_def : ∀ f, P f ↔ ∀ x,
      (f x) ^ 2 = (∫ t in (0 : ℝ)..x, (f t) ^ 2 + (deriv f t) ^ 2) + 1990)
    (f : ℝ → ℝ) :
    (ContDiff ℝ 1 f ∧ P f) ↔ f ∈ putnam_1990_b1_solution :=
  by
  constructor
  · rintro ⟨hfcd, hfP⟩
    have hEq : ∀ x, (f x) ^ 2 = (∫ t in (0 : ℝ)..x,
        (f t) ^ 2 + (deriv f t) ^ 2) + 1990 := (P_def f).mp hfP
    have hderiv : ∀ x, deriv f x = f x := by
      have hcont : Continuous fun t : ℝ => (f t) ^ 2 + (deriv f t) ^ 2 :=
        (hfcd.continuous.pow 2).add (hfcd.continuous_deriv_one.pow 2)
      intro x
      have hleft : HasDerivAt (fun u : ℝ => (f u) ^ 2) (2 * f x * deriv f x) x := by
        simpa [pow_succ, mul_assoc, two_mul] using ((hfcd.differentiable_one x).hasDerivAt.pow 2)
      have hright0 : HasDerivAt
          (fun u : ℝ => (∫ t in (0 : ℝ)..u, (f t) ^ 2 + (deriv f t) ^ 2) + 1990)
          ((f x) ^ 2 + (deriv f x) ^ 2) x := by
        exact (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
          (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).add_const 1990
      have hright : HasDerivAt (fun u : ℝ => (f u) ^ 2)
          ((f x) ^ 2 + (deriv f x) ^ 2) x := by
        refine hright0.congr_of_eventuallyEq ?_
        exact Filter.Eventually.of_forall fun u => hEq u
      have hrel : 2 * f x * deriv f x = (f x) ^ 2 + (deriv f x) ^ 2 := hleft.unique hright
      have hs : (deriv f x - f x) ^ 2 = 0 := by
        nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    have hconst : ∀ x, f x = f 0 * Real.exp x := by
      intro x
      have hgdiff : Differentiable ℝ (fun y : ℝ => f y * Real.exp (-y)) := by
        fun_prop (disch := exact hfcd.differentiable_one)
      have hgderiv : ∀ y : ℝ, deriv (fun z : ℝ => f z * Real.exp (-z)) y = 0 := by
        intro y
        have hfder : HasDerivAt f (f y) y := by
          simpa [hderiv y] using (hfcd.differentiable_one y).hasDerivAt
        have hneg : HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) y := by
          simpa using (hasDerivAt_id y).neg
        have hexp : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-y)) y := by
          simpa using hneg.exp
        have hmul : HasDerivAt (fun z : ℝ => f z * Real.exp (-z))
            (f y * Real.exp (-y) + f y * (-Real.exp (-y))) y := hfder.mul hexp
        simpa using hmul.deriv
      have hc := is_const_of_deriv_eq_zero hgdiff hgderiv x 0
      have hc' : f x * Real.exp (-x) = f 0 := by
        simpa using hc
      calc
        f x = (f x * Real.exp (-x)) * Real.exp x := by
          rw [Real.exp_neg]
          field_simp [Real.exp_ne_zero x]
        _ = f 0 * Real.exp x := by rw [hc']
    have h0sq : (f 0) ^ 2 = 1990 := by
      simpa using hEq 0
    have hcoeff : f 0 ∈ ({Real.sqrt 1990, -Real.sqrt 1990} : Set ℝ) := by
      have hsqrt_sq : (Real.sqrt 1990) ^ 2 = (1990 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hsqeq : (f 0) ^ 2 = (Real.sqrt 1990) ^ 2 := by
        rw [h0sq, hsqrt_sq]
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq) with hpos | hneg
      · simp [hpos]
      · simp [hneg]
    refine ⟨f 0, hcoeff, ?_⟩
    funext x
    exact hconst x
  · intro hfmem
    have h_exp (c : ℝ) (hc : c ^ 2 = 1990) :
        ContDiff ℝ 1 (fun x : ℝ => c * Real.exp x) ∧
          P (fun x : ℝ => c * Real.exp x) := by
      constructor
      · fun_prop
      · rw [P_def]
        intro x
        let g : ℝ → ℝ := fun y => c * Real.exp y
        have hgderivAt : ∀ y : ℝ, HasDerivAt g (g y) y := by
          intro y
          simpa [g] using (Real.hasDerivAt_exp y).const_mul c
        have hgderiv : ∀ y : ℝ, deriv g y = g y := fun y => (hgderivAt y).deriv
        have hcont : Continuous fun y : ℝ => (g y) ^ 2 + (deriv g y) ^ 2 := by
          fun_prop
        have hderiv_sq : ∀ y ∈ Set.uIcc (0 : ℝ) x,
            HasDerivAt (fun u : ℝ => (g u) ^ 2) ((g y) ^ 2 + (deriv g y) ^ 2) y := by
          intro y hy
          have hs : HasDerivAt (fun u : ℝ => (g u) ^ 2) (2 * g y * g y) y := by
            simpa [pow_succ, mul_assoc, two_mul] using ((hgderivAt y).pow 2)
          convert hs using 1
          rw [hgderiv y]
          ring
        have hint : IntervalIntegrable (fun y : ℝ => (g y) ^ 2 + (deriv g y) ^ 2)
            MeasureTheory.volume 0 x := hcont.intervalIntegrable _ _
        have hint_eq : (∫ t in (0 : ℝ)..x, (g t) ^ 2 + (deriv g t) ^ 2) =
            (g x) ^ 2 - (g 0) ^ 2 :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_sq hint
        have hg0 : (g 0) ^ 2 = 1990 := by
          simp [g, hc]
        change (g x) ^ 2 = (∫ t in (0 : ℝ)..x, (g t) ^ 2 + (deriv g t) ^ 2) + 1990
        rw [hint_eq, hg0]
        ring
    rcases hfmem with ⟨c, hcset, hcf⟩
    have hc : c ^ 2 = 1990 := by
      rcases (by simpa using hcset :
          c = Real.sqrt 1990 ∨ c = -Real.sqrt 1990) with hpos | hneg
      · rw [hpos, Real.sq_sqrt]
        norm_num
      · rw [hneg, neg_sq, Real.sq_sqrt]
        norm_num
    rw [hcf]
    exact h_exp c hc
