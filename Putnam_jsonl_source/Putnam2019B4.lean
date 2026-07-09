import Mathlib

open Topology Filter Set Matrix

private abbrev putnam_2019_b4_e0 : Fin 2 → ℝ := ![(1 : ℝ), 0]
private abbrev putnam_2019_b4_e1 : Fin 2 → ℝ := ![(0 : ℝ), 1]

private lemma putnam_2019_b4_vec_eq
    (vec : ℝ → ℝ → (Fin 2 → ℝ))
    (hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y 1) = y) (x y : ℝ) :
    vec x y = ![x, y] := by
  funext i
  fin_cases i <;> simp [hvec]

private lemma putnam_2019_b4_lineX_contDiff (y : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ => ![x, y]) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa using (contDiff_id : ContDiff ℝ (2 : WithTop ℕ∞) (fun x : ℝ => x))
  · simpa using (contDiff_const : ContDiff ℝ (2 : WithTop ℕ∞) (fun x : ℝ => y))

private lemma putnam_2019_b4_lineY_contDiff (x : ℝ) :
    ContDiff ℝ 2 (fun y : ℝ => ![x, y]) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa using (contDiff_const : ContDiff ℝ (2 : WithTop ℕ∞) (fun y : ℝ => x))
  · simpa using (contDiff_id : ContDiff ℝ (2 : WithTop ℕ∞) (fun y : ℝ => y))

private lemma putnam_2019_b4_lineX_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => ![t, y]) putnam_2019_b4_e0 x := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [putnam_2019_b4_e0] using
      (hasDerivAt_id x : HasDerivAt (fun t : ℝ => t) 1 x)
  · simpa [putnam_2019_b4_e0] using
      (hasDerivAt_const x y : HasDerivAt (fun t : ℝ => y) 0 x)

private lemma putnam_2019_b4_lineY_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => ![x, t]) putnam_2019_b4_e1 y := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [putnam_2019_b4_e1] using
      (hasDerivAt_const y x : HasDerivAt (fun t : ℝ => x) 0 y)
  · simpa [putnam_2019_b4_e1] using
      (hasDerivAt_id y : HasDerivAt (fun t : ℝ => t) 1 y)

private lemma putnam_2019_b4_lineX_iteratedDeriv_two_zero (x y : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => ![t, y]) x = 0 := by
  have hderfun :
      deriv (fun t : ℝ => ![t, y]) = fun _ : ℝ => putnam_2019_b4_e0 := by
    funext z
    exact (putnam_2019_b4_lineX_hasDerivAt z y).deriv
  rw [show iteratedDeriv 2 (fun t : ℝ => ![t, y]) =
      deriv (deriv (fun t : ℝ => ![t, y])) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [hderfun]
  simp [deriv_const]

private lemma putnam_2019_b4_lineY_iteratedDeriv_two_zero (x y : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => ![x, t]) y = 0 := by
  have hderfun :
      deriv (fun t : ℝ => ![x, t]) = fun _ : ℝ => putnam_2019_b4_e1 := by
    funext z
    exact (putnam_2019_b4_lineY_hasDerivAt x z).deriv
  rw [show iteratedDeriv 2 (fun t : ℝ => ![x, t]) =
      deriv (deriv (fun t : ℝ => ![x, t])) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [hderfun]
  simp [deriv_const]

private lemma putnam_2019_b4_partial_x_fderiv
    (f : (Fin 2 → ℝ) → ℝ) (vec : ℝ → ℝ → (Fin 2 → ℝ))
    (fdiff : ContDiff ℝ 2 f)
    (hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y 1) = y) (x y : ℝ) :
    deriv (fun x' : ℝ => f (vec x' y)) x =
      (fderiv ℝ f ![x, y]) putnam_2019_b4_e0 := by
  have hfun : (fun x' : ℝ => f (vec x' y)) = fun x' : ℝ => f ![x', y] := by
    funext x'
    rw [putnam_2019_b4_vec_eq vec hvec x' y]
  rw [hfun]
  have hfder : HasFDerivAt f (fderiv ℝ f ![x, y]) ![x, y] := by
    exact ((fdiff.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) ![x, y]).hasFDerivAt
  have hcomp := hfder.comp_hasDerivAt x (putnam_2019_b4_lineX_hasDerivAt x y)
  simpa [Function.comp_def] using hcomp.deriv

private lemma putnam_2019_b4_partial_y_fderiv
    (f : (Fin 2 → ℝ) → ℝ) (vec : ℝ → ℝ → (Fin 2 → ℝ))
    (fdiff : ContDiff ℝ 2 f)
    (hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y 1) = y) (x y : ℝ) :
    deriv (fun y' : ℝ => f (vec x y')) y =
      (fderiv ℝ f ![x, y]) putnam_2019_b4_e1 := by
  have hfun : (fun y' : ℝ => f (vec x y')) = fun y' : ℝ => f ![x, y'] := by
    funext y'
    rw [putnam_2019_b4_vec_eq vec hvec x y']
  rw [hfun]
  have hfder : HasFDerivAt f (fderiv ℝ f ![x, y]) ![x, y] := by
    exact ((fdiff.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) ![x, y]).hasFDerivAt
  have hcomp := hfder.comp_hasDerivAt y (putnam_2019_b4_lineY_hasDerivAt x y)
  simpa [Function.comp_def] using hcomp.deriv

private lemma putnam_2019_b4_partial_xx_iteratedFDeriv
    (f : (Fin 2 → ℝ) → ℝ) (vec : ℝ → ℝ → (Fin 2 → ℝ))
    (fdiff : ContDiff ℝ 2 f)
    (hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y 1) = y) (x y : ℝ) :
    iteratedDeriv 2 (fun x' : ℝ => f (vec x' y)) x =
      (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e0] := by
  have hfun : (fun x' : ℝ => f (vec x' y)) = fun x' : ℝ => f ![x', y] := by
    funext x'
    rw [putnam_2019_b4_vec_eq vec hvec x' y]
  rw [hfun]
  have hcomp := iteratedDeriv_vcomp_two (g := f) (f := fun t : ℝ => ![t, y])
      (x := x) (fdiff.contDiffAt) ((putnam_2019_b4_lineX_contDiff y).contDiffAt)
  have hder : deriv (fun t : ℝ => ![t, y]) x = putnam_2019_b4_e0 :=
    (putnam_2019_b4_lineX_hasDerivAt x y).deriv
  have h2 : iteratedDeriv 2 (fun t : ℝ => ![t, y]) x = 0 :=
    putnam_2019_b4_lineX_iteratedDeriv_two_zero x y
  have hconst : (fun _ : Fin 2 => putnam_2019_b4_e0) =
      ![putnam_2019_b4_e0, putnam_2019_b4_e0] := by
    ext i
    fin_cases i <;> simp
  simpa [Function.comp_def, hder, h2, hconst] using hcomp

private lemma putnam_2019_b4_partial_yy_iteratedFDeriv
    (f : (Fin 2 → ℝ) → ℝ) (vec : ℝ → ℝ → (Fin 2 → ℝ))
    (fdiff : ContDiff ℝ 2 f)
    (hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y 1) = y) (x y : ℝ) :
    iteratedDeriv 2 (fun y' : ℝ => f (vec x y')) y =
      (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e1, putnam_2019_b4_e1] := by
  have hfun : (fun y' : ℝ => f (vec x y')) = fun y' : ℝ => f ![x, y'] := by
    funext y'
    rw [putnam_2019_b4_vec_eq vec hvec x y']
  rw [hfun]
  have hcomp := iteratedDeriv_vcomp_two (g := f) (f := fun t : ℝ => ![x, t])
      (x := y) (fdiff.contDiffAt) ((putnam_2019_b4_lineY_contDiff x).contDiffAt)
  have hder : deriv (fun t : ℝ => ![x, t]) y = putnam_2019_b4_e1 :=
    (putnam_2019_b4_lineY_hasDerivAt x y).deriv
  have h2 : iteratedDeriv 2 (fun t : ℝ => ![x, t]) y = 0 :=
    putnam_2019_b4_lineY_iteratedDeriv_two_zero x y
  have hconst : (fun _ : Fin 2 => putnam_2019_b4_e1) =
      ![putnam_2019_b4_e1, putnam_2019_b4_e1] := by
    ext i
    fin_cases i <;> simp
  simpa [Function.comp_def, hder, h2, hconst] using hcomp

private lemma putnam_2019_b4_hasDerivAt_fderiv_lineX
    (f : (Fin 2 → ℝ) → ℝ) (fdiff : ContDiff ℝ 2 f) (x y : ℝ) (v : Fin 2 → ℝ) :
    HasDerivAt (fun t : ℝ => (fderiv ℝ f ![t, y]) v)
      ((iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, v]) x := by
  have hp : DifferentiableAt ℝ (fderiv ℝ f) ![x, y] := by
    have hcd : ContDiffAt ℝ 1 (fderiv ℝ f) ![x, y] := by
      exact fdiff.contDiffAt.fderiv_right (m := 1) (by norm_num)
    exact hcd.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  let ev : ((Fin 2 → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ) v
  have houter : HasFDerivAt (fun q : Fin 2 → ℝ => (fderiv ℝ f q) v)
      (ev.comp (fderiv ℝ (fderiv ℝ f) ![x, y])) ![x, y] := by
    simpa [ev] using
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp ![x, y] hp.hasFDerivAt)
  have hcomp := houter.comp_hasDerivAt x (putnam_2019_b4_lineX_hasDerivAt x y)
  have hcomp' : HasDerivAt (fun t : ℝ => (fderiv ℝ f ![t, y]) v)
      ((ev.comp (fderiv ℝ (fderiv ℝ f) ![x, y])) putnam_2019_b4_e0) x := by
    simpa [Function.comp_def] using hcomp
  have hval : (ev.comp (fderiv ℝ (fderiv ℝ f) ![x, y])) putnam_2019_b4_e0 =
      (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, v] := by
    rw [iteratedFDeriv_two_apply]
    simp [ev, putnam_2019_b4_e0]
  simpa [hval] using hcomp'

private lemma putnam_2019_b4_hasDerivAt_fderiv_lineY
    (f : (Fin 2 → ℝ) → ℝ) (fdiff : ContDiff ℝ 2 f) (x y : ℝ) (v : Fin 2 → ℝ) :
    HasDerivAt (fun t : ℝ => (fderiv ℝ f ![x, t]) v)
      ((iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e1, v]) y := by
  have hp : DifferentiableAt ℝ (fderiv ℝ f) ![x, y] := by
    have hcd : ContDiffAt ℝ 1 (fderiv ℝ f) ![x, y] := by
      exact fdiff.contDiffAt.fderiv_right (m := 1) (by norm_num)
    exact hcd.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  let ev : ((Fin 2 → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ) v
  have houter : HasFDerivAt (fun q : Fin 2 → ℝ => (fderiv ℝ f q) v)
      (ev.comp (fderiv ℝ (fderiv ℝ f) ![x, y])) ![x, y] := by
    simpa [ev] using
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp ![x, y] hp.hasFDerivAt)
  have hcomp := houter.comp_hasDerivAt y (putnam_2019_b4_lineY_hasDerivAt x y)
  have hcomp' : HasDerivAt (fun t : ℝ => (fderiv ℝ f ![x, t]) v)
      ((ev.comp (fderiv ℝ (fderiv ℝ f) ![x, y])) putnam_2019_b4_e1) y := by
    simpa [Function.comp_def] using hcomp
  have hval : (ev.comp (fderiv ℝ (fderiv ℝ f) ![x, y])) putnam_2019_b4_e1 =
      (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e1, v] := by
    rw [iteratedFDeriv_two_apply]
    simp [ev, putnam_2019_b4_e1]
  simpa [hval] using hcomp'

private lemma putnam_2019_b4_hasDerivAt_f_lineY
    (f : (Fin 2 → ℝ) → ℝ) (fdiff : ContDiff ℝ 2 f) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f ![x, t])
      ((fderiv ℝ f ![x, y]) putnam_2019_b4_e1) y := by
  have hfder : HasFDerivAt f (fderiv ℝ f ![x, y]) ![x, y] := by
    exact ((fdiff.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) ![x, y]).hasFDerivAt
  have hcomp := hfder.comp_hasDerivAt y (putnam_2019_b4_lineY_hasDerivAt x y)
  simpa [Function.comp_def] using hcomp

private lemma putnam_2019_b4_deriv_rhs_x {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    deriv (fun t : ℝ => t * y * Real.log (t * y)) x =
      y * (Real.log (x * y) + 1) := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have ht : HasDerivAt (fun t : ℝ => t * y) y x := by
    simpa using (hasDerivAt_id x).mul_const y
  have hlog : HasDerivAt (fun t : ℝ => Real.log (t * y)) (y / (x * y)) x := by
    simpa using ht.log hxy
  have hprod : HasDerivAt (fun t : ℝ => (t * y) * Real.log (t * y))
      (y * Real.log (x * y) + (x * y) * (y / (x * y))) x := by
    simpa using ht.mul hlog
  rw [hprod.deriv]
  field_simp [hxy]

private lemma putnam_2019_b4_deriv_rhs_y {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    deriv (fun t : ℝ => x * t * Real.log (x * t)) y =
      x * (Real.log (x * y) + 1) := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have ht : HasDerivAt (fun t : ℝ => x * t) x y := by
    simpa [mul_comm] using (hasDerivAt_id y).const_mul x
  have hlog : HasDerivAt (fun t : ℝ => Real.log (x * t)) (x / (x * y)) y := by
    simpa using ht.log hxy
  have hprod : HasDerivAt (fun t : ℝ => (x * t) * Real.log (x * t))
      (x * Real.log (x * y) + (x * y) * (x / (x * y))) y := by
    simpa using ht.mul hlog
  rw [hprod.deriv]
  field_simp [hxy]

private lemma putnam_2019_b4_hasDerivAt_A {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => t * Real.log (t * y) / 2)
      ((Real.log (x * y) + 1) / 2) x := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have ht : HasDerivAt (fun t : ℝ => t * y) y x := by
    simpa using (hasDerivAt_id x).mul_const y
  have hlog : HasDerivAt (fun t : ℝ => Real.log (t * y)) (y / (x * y)) x := by
    simpa using ht.log hxy
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa using hasDerivAt_id x
  have hprod : HasDerivAt (fun t : ℝ => t * Real.log (t * y))
      (1 * Real.log (x * y) + x * (y / (x * y))) x := by
    simpa using hid.mul hlog
  have hdiv := hprod.div_const 2
  convert hdiv using 1
  field_simp [hxy]

private lemma putnam_2019_b4_hasDerivAt_y_log_mul_sub {c y : ℝ}
    (hc : c ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => t * Real.log (c * t) - t)
      (Real.log (c * y)) y := by
  have hcy : c * y ≠ 0 := mul_ne_zero hc hy
  have ht : HasDerivAt (fun t : ℝ => c * t) c y := by
    simpa using (hasDerivAt_id y).const_mul c
  have hlog : HasDerivAt (fun t : ℝ => Real.log (c * t)) (c / (c * y)) y := by
    simpa using ht.log hcy
  have hid : HasDerivAt (fun t : ℝ => t) 1 y := by
    simpa using hasDerivAt_id y
  have hprod : HasDerivAt (fun t : ℝ => t * Real.log (c * t))
      (1 * Real.log (c * y) + y * (c / (c * y))) y := by
    simpa using hid.mul hlog
  have hsub := hprod.sub hid
  convert hsub using 1
  field_simp [hcy]
  ring

private lemma putnam_2019_b4_hasDerivAt_B {s y : ℝ}
    (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) (hy : y ≠ 0) :
    HasDerivAt
      (fun t : ℝ => (((s + 1) * (t * Real.log ((s + 1) * t) - t)) -
        s * (t * Real.log (s * t) - t)) / 2)
      (((s + 1) * Real.log ((s + 1) * y) - s * Real.log (s * y)) / 2) y := by
  have h1 := (putnam_2019_b4_hasDerivAt_y_log_mul_sub
    (c := s + 1) (y := y) hs1 hy).const_mul (s + 1)
  have h2 := (putnam_2019_b4_hasDerivAt_y_log_mul_sub
    (c := s) (y := y) hs hy).const_mul s
  have hsub := h1.sub h2
  have hdiv := hsub.div_const 2
  convert hdiv using 1

private lemma putnam_2019_b4_hasDerivAt_G {x : ℝ} (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    HasDerivAt
      (fun t : ℝ => (t + 1) * Real.log (t + 1) - t * Real.log t - (1 / 2 : ℝ))
      (Real.log (x + 1) - Real.log x) x := by
  have hA : HasDerivAt (fun t : ℝ => t + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 : ℝ)
  have hlogA : HasDerivAt (fun t : ℝ => Real.log (t + 1)) (1 / (x + 1)) x := by
    simpa using hA.log hx1
  have hprodA : HasDerivAt (fun t : ℝ => (t + 1) * Real.log (t + 1))
      (1 * Real.log (x + 1) + (x + 1) * (1 / (x + 1))) x := by
    simpa using hA.mul hlogA
  have hB : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa using hasDerivAt_id x
  have hlogB : HasDerivAt (fun t : ℝ => Real.log t) (1 / x) x := by
    simpa using hB.log hx
  have hprodB : HasDerivAt (fun t : ℝ => t * Real.log t)
      (1 * Real.log x + x * (1 / x)) x := by
    simpa using hB.mul hlogB
  have hconst : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 x := by
    simpa using hasDerivAt_const x (1 / 2 : ℝ)
  have htotal := (hprodA.sub hprodB).sub hconst
  have htarget :
      (fun t : ℝ => (t + 1) * Real.log (t + 1) - t * Real.log t - (1 / 2 : ℝ)) =
        (((fun t : ℝ => (t + 1) * Real.log (t + 1)) -
          (fun t : ℝ => t * Real.log t)) - (fun _ : ℝ => (1 / 2 : ℝ))) := by
    funext t
    simp [Pi.sub_apply]
  rw [htarget]
  convert htotal using 1
  field_simp [hx, hx1]
  ring

private lemma putnam_2019_b4_G_mono :
    MonotoneOn
      (fun t : ℝ => (t + 1) * Real.log (t + 1) - t * Real.log t - (1 / 2 : ℝ))
      (Set.Ici (1 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ))
  · fun_prop
  · rw [interior_Ici]
    intro x hx
    have hxgt : 1 < x := hx
    have hxpos : 0 < x := by linarith
    have hx1pos : 0 < x + 1 := by linarith
    exact (putnam_2019_b4_hasDerivAt_G (ne_of_gt hxpos) (ne_of_gt hx1pos)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    have hxgt : 1 < x := hx
    have hxpos : 0 < x := by linarith
    have hx1pos : 0 < x + 1 := by linarith
    rw [(putnam_2019_b4_hasDerivAt_G (ne_of_gt hxpos) (ne_of_gt hx1pos)).deriv]
    exact sub_nonneg.mpr (Real.log_le_log hxpos (by linarith))

-- Note: boosts the domain of f to the entire 2D plane
-- 2 * Real.log 2 - 1 / 2
/--
Let $\mathcal{F}$ be the set of functions $f(x,y)$ that are twice continuously differentiable for $x \geq 1,y \geq 1$ and that satisfy the following two equations (where subscripts denote partial derivatives):
\begin{gather*}
xf_x+yf_y=xy\ln(xy), \\
x^2f_{xx}+y^2f_{yy}=xy.
\end{gather*}
For each $f \in \mathcal{F}$, let $m(f)=\min_{s \geq 1} (f(s+1,s+1)-f(s+1,s)-f(s,s+1)+f(s,s))$. Determine $m(f)$, and show that it is independent of the choice of $f$.
-/
theorem putnam_2019_b4
(f : (Fin 2 → ℝ) → ℝ)
(vec : ℝ → ℝ → (Fin 2 → ℝ))
(fdiff : ContDiff ℝ 2 f)
(hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y 1) = y)
(feq1 : ∀ x ≥ 1, ∀ y ≥ 1, x * deriv (fun x' : ℝ => f (vec x' y)) x + y * deriv (fun y' : ℝ => f (vec x y')) y = x * y * Real.log (x * y))
(feq2 : ∀ x ≥ 1, ∀ y ≥ 1, x ^ 2 * iteratedDeriv 2 (fun x' : ℝ => f (vec x' y)) x + y ^ 2 * iteratedDeriv 2 (fun y' : ℝ => f (vec x y')) y = x * y)
: sInf {f (vec (s + 1) (s + 1)) - f (vec (s + 1) s) - f (vec s (s + 1)) + f (vec s s) | s ≥ 1} = ((2 * Real.log 2 - 1 / 2) : ℝ ) := by
  classical
  let G : ℝ → ℝ := fun t => (t + 1) * Real.log (t + 1) - t * Real.log t - (1 / 2 : ℝ)
  have hmixed : ∀ x y : ℝ, 1 < x → 1 < y →
      (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e1] =
        (Real.log (x * y) + 1) / 2 := by
    intro x y hx hy
    have hxpos : 0 < x := by linarith
    have hypos : 0 < y := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hy0 : y ≠ 0 := ne_of_gt hypos
    have hxge : 1 ≤ x := le_of_lt hx
    have hyge : 1 ≤ y := le_of_lt hy
    have hEqx :
        (fun t : ℝ => t * (fderiv ℝ f ![t, y]) putnam_2019_b4_e0 +
            y * (fderiv ℝ f ![t, y]) putnam_2019_b4_e1) =ᶠ[𝓝 x]
          (fun t : ℝ => t * y * Real.log (t * y)) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      have htge : 1 ≤ t := le_of_lt ht
      have h := feq1 t htge y hyge
      simpa [putnam_2019_b4_partial_x_fderiv f vec fdiff hvec t y,
        putnam_2019_b4_partial_y_fderiv f vec fdiff hvec t y] using h
    have hFx := putnam_2019_b4_hasDerivAt_fderiv_lineX f fdiff x y putnam_2019_b4_e0
    have hFy := putnam_2019_b4_hasDerivAt_fderiv_lineX f fdiff x y putnam_2019_b4_e1
    have hLeftx : deriv (fun t : ℝ => t * (fderiv ℝ f ![t, y]) putnam_2019_b4_e0 +
            y * (fderiv ℝ f ![t, y]) putnam_2019_b4_e1) x =
          (fderiv ℝ f ![x, y]) putnam_2019_b4_e0 +
            x * (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e0] +
            y * (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e1] := by
      have htotal := ((hasDerivAt_id x).mul hFx).add (hFy.const_mul y)
      convert htotal.deriv using 1
      simp [id]
    have hdx0 := hEqx.deriv_eq
    rw [hLeftx, putnam_2019_b4_deriv_rhs_x hx0 hy0] at hdx0
    have hdx := hdx0
    have hEqy :
        (fun t : ℝ => x * (fderiv ℝ f ![x, t]) putnam_2019_b4_e0 +
            t * (fderiv ℝ f ![x, t]) putnam_2019_b4_e1) =ᶠ[𝓝 y]
          (fun t : ℝ => x * t * Real.log (x * t)) := by
      filter_upwards [eventually_gt_nhds hy] with t ht
      have htge : 1 ≤ t := le_of_lt ht
      have h := feq1 x hxge t htge
      simpa [putnam_2019_b4_partial_x_fderiv f vec fdiff hvec x t,
        putnam_2019_b4_partial_y_fderiv f vec fdiff hvec x t] using h
    have hFxy := putnam_2019_b4_hasDerivAt_fderiv_lineY f fdiff x y putnam_2019_b4_e0
    have hFyy := putnam_2019_b4_hasDerivAt_fderiv_lineY f fdiff x y putnam_2019_b4_e1
    have hLefty : deriv (fun t : ℝ => x * (fderiv ℝ f ![x, t]) putnam_2019_b4_e0 +
            t * (fderiv ℝ f ![x, t]) putnam_2019_b4_e1) y =
          x * (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e1, putnam_2019_b4_e0] +
            ((fderiv ℝ f ![x, y]) putnam_2019_b4_e1 +
              y * (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e1, putnam_2019_b4_e1]) := by
      have htotal := (hFxy.const_mul x).add ((hasDerivAt_id y).mul hFyy)
      convert htotal.deriv using 1
      simp [id]
    have hdy0 := hEqy.deriv_eq
    rw [hLefty, putnam_2019_b4_deriv_rhs_y hx0 hy0] at hdy0
    have hsym0 := (fdiff.contDiffAt (x := ![x, y])).isSymmSndFDerivAt
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
    have hsym :
        (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e1, putnam_2019_b4_e0] =
          (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e1] := by
      simpa using (IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hsym0)
        (v := putnam_2019_b4_e1) (w := putnam_2019_b4_e0))
    have hdy := hdy0
    rw [hsym] at hdy
    have hpde1 : x * (fderiv ℝ f ![x, y]) putnam_2019_b4_e0 +
          y * (fderiv ℝ f ![x, y]) putnam_2019_b4_e1 = x * y * Real.log (x * y) := by
      simpa [putnam_2019_b4_partial_x_fderiv f vec fdiff hvec x y,
        putnam_2019_b4_partial_y_fderiv f vec fdiff hvec x y] using feq1 x hxge y hyge
    have hpde2 : x ^ 2 * (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e0] +
          y ^ 2 * (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e1, putnam_2019_b4_e1] = x * y := by
      simpa [putnam_2019_b4_partial_xx_iteratedFDeriv f vec fdiff hvec x y,
        putnam_2019_b4_partial_yy_iteratedFDeriv f vec fdiff hvec x y] using feq2 x hxge y hyge
    have hdxm := congrArg (fun z : ℝ => x * z) hdx
    have hdym := congrArg (fun z : ℝ => y * z) hdy
    nlinarith [hdxm, hdym, hpde1, hpde2, mul_pos hxpos hypos]
  have hrect_explicit : ∀ s : ℝ, 1 ≤ s →
      f ![s + 1, s + 1] - f ![s + 1, s] - f ![s, s + 1] + f ![s, s] = G s := by
    intro s hs
    have hsle : s ≤ s + 1 := by linarith
    have hspos : 0 < s := by linarith
    have hs0 : s ≠ 0 := ne_of_gt hspos
    have hs1pos : 0 < s + 1 := by linarith
    have hs10 : s + 1 ≠ 0 := ne_of_gt hs1pos
    let K : ℝ → ℝ → ℝ := fun x y => (Real.log (x * y) + 1) / 2
    let A : ℝ → ℝ → ℝ := fun x y => x * Real.log (x * y) / 2
    let B : ℝ → ℝ := fun y =>
      (((s + 1) * (y * Real.log ((s + 1) * y) - y)) -
        s * (y * Real.log (s * y) - y)) / 2
    have hinner : ∀ y : ℝ, 1 < y →
        (fderiv ℝ f ![s + 1, y]) putnam_2019_b4_e1 -
          (fderiv ℝ f ![s, y]) putnam_2019_b4_e1 =
            A (s + 1) y - A s y := by
      intro y hy
      have hypos : 0 < y := by linarith
      have hy0 : y ≠ 0 := ne_of_gt hypos
      have hIF : Continuous (iteratedFDeriv ℝ 2 f) := by
        exact fdiff.continuous_iteratedFDeriv (m := 2) (by norm_num)
      have hline : Continuous (fun x : ℝ => ![x, y]) :=
        (putnam_2019_b4_lineX_contDiff y).continuous
      have hFxycont : Continuous
          (fun x : ℝ => (iteratedFDeriv ℝ 2 f ![x, y])
            ![putnam_2019_b4_e0, putnam_2019_b4_e1]) := by
        exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => (Fin 2 → ℝ)) ℝ
          ![putnam_2019_b4_e0, putnam_2019_b4_e1]).continuous.comp (hIF.comp hline)
      have hftc :
          ∫ x in s..s + 1,
              (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e1] =
            (fderiv ℝ f ![s + 1, y]) putnam_2019_b4_e1 -
              (fderiv ℝ f ![s, y]) putnam_2019_b4_e1 := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => putnam_2019_b4_hasDerivAt_fderiv_lineX f fdiff x y putnam_2019_b4_e1)
          (hFxycont.intervalIntegrable s (s + 1))
      have hcongr :
          ∫ x in s..s + 1,
              (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e1] =
            ∫ x in s..s + 1, K x y := by
        apply intervalIntegral.integral_congr_ae
        exact MeasureTheory.ae_of_all _ (fun x hxmem => by
          rw [Set.uIoc_of_le hsle] at hxmem
          have hxgt : s < x := hxmem.1
          have hx1 : 1 < x := lt_of_le_of_lt hs hxgt
          exact hmixed x y hx1 hy)
      have hKcont : ContinuousOn (fun x : ℝ => K x y) (Set.uIcc s (s + 1)) := by
        rw [Set.uIcc_of_le hsle]
        intro x hx
        have hxpos : 0 < x := by linarith [hx.1]
        fun_prop (disch := positivity)
      have hAint : ∫ x in s..s + 1, K x y = A (s + 1) y - A s y := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hxmem => by
            rw [Set.uIcc_of_le hsle] at hxmem
            have hxpos : 0 < x := by linarith [hxmem.1]
            simpa [A, K] using putnam_2019_b4_hasDerivAt_A (ne_of_gt hxpos) hy0)
          hKcont.intervalIntegrable
      calc
        (fderiv ℝ f ![s + 1, y]) putnam_2019_b4_e1 -
            (fderiv ℝ f ![s, y]) putnam_2019_b4_e1
            = ∫ x in s..s + 1,
                (iteratedFDeriv ℝ 2 f ![x, y]) ![putnam_2019_b4_e0, putnam_2019_b4_e1] := hftc.symm
        _ = ∫ x in s..s + 1, K x y := hcongr
        _ = A (s + 1) y - A s y := hAint
    have hfdcont : Continuous (fderiv ℝ f) :=
      fdiff.continuous_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hterm1 : Continuous (fun y : ℝ => (fderiv ℝ f ![s + 1, y]) putnam_2019_b4_e1) := by
      exact (ContinuousLinearMap.apply ℝ ℝ putnam_2019_b4_e1).continuous.comp
        (hfdcont.comp (putnam_2019_b4_lineY_contDiff (s + 1)).continuous)
    have hterm0 : Continuous (fun y : ℝ => (fderiv ℝ f ![s, y]) putnam_2019_b4_e1) := by
      exact (ContinuousLinearMap.apply ℝ ℝ putnam_2019_b4_e1).continuous.comp
        (hfdcont.comp (putnam_2019_b4_lineY_contDiff s).continuous)
    have houterFTC :
        ∫ y in s..s + 1,
            ((fderiv ℝ f ![s + 1, y]) putnam_2019_b4_e1 -
              (fderiv ℝ f ![s, y]) putnam_2019_b4_e1) =
          (f ![s + 1, s + 1] - f ![s, s + 1]) -
            (f ![s + 1, s] - f ![s, s]) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => (putnam_2019_b4_hasDerivAt_f_lineY f fdiff (s + 1) y).sub
          (putnam_2019_b4_hasDerivAt_f_lineY f fdiff s y))
        ((hterm1.sub hterm0).intervalIntegrable s (s + 1))
    have houterCongr :
        ∫ y in s..s + 1,
            ((fderiv ℝ f ![s + 1, y]) putnam_2019_b4_e1 -
              (fderiv ℝ f ![s, y]) putnam_2019_b4_e1) =
          ∫ y in s..s + 1, A (s + 1) y - A s y := by
      apply intervalIntegral.integral_congr_ae
      exact MeasureTheory.ae_of_all _ (fun y hymem => by
        rw [Set.uIoc_of_le hsle] at hymem
        have hygt : s < y := hymem.1
        have hy1 : 1 < y := lt_of_le_of_lt hs hygt
        exact hinner y hy1)
    have hAcont : ContinuousOn (fun y : ℝ => A (s + 1) y - A s y) (Set.uIcc s (s + 1)) := by
      rw [Set.uIcc_of_le hsle]
      intro y hy
      have hypos : 0 < y := by linarith [hy.1]
      fun_prop (disch := positivity)
    have hBint : ∫ y in s..s + 1, A (s + 1) y - A s y = B (s + 1) - B s := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hymem => by
          rw [Set.uIcc_of_le hsle] at hymem
          have hypos : 0 < y := by linarith [hymem.1]
          have hBder := putnam_2019_b4_hasDerivAt_B hs0 hs10 (ne_of_gt hypos)
          convert hBder using 1
          simp [A]
          ring_nf)
        hAcont.intervalIntegrable
    have hB_simpl : B (s + 1) - B s = G s := by
      dsimp [B, G]
      rw [Real.log_mul hs10 hs10]
      rw [Real.log_mul hs0 hs10]
      rw [Real.log_mul hs10 hs0]
      rw [Real.log_mul hs0 hs0]
      ring
    calc
      f ![s + 1, s + 1] - f ![s + 1, s] - f ![s, s + 1] + f ![s, s]
          = (f ![s + 1, s + 1] - f ![s, s + 1]) -
              (f ![s + 1, s] - f ![s, s]) := by ring
      _ = ∫ y in s..s + 1,
            ((fderiv ℝ f ![s + 1, y]) putnam_2019_b4_e1 -
              (fderiv ℝ f ![s, y]) putnam_2019_b4_e1) := houterFTC.symm
      _ = ∫ y in s..s + 1, A (s + 1) y - A s y := houterCongr
      _ = B (s + 1) - B s := hBint
      _ = G s := hB_simpl
  have hrect : ∀ s : ℝ, 1 ≤ s →
      f (vec (s + 1) (s + 1)) - f (vec (s + 1) s) - f (vec s (s + 1)) + f (vec s s) = G s := by
    intro s hs
    simpa [putnam_2019_b4_vec_eq vec hvec (s + 1) (s + 1),
      putnam_2019_b4_vec_eq vec hvec (s + 1) s,
      putnam_2019_b4_vec_eq vec hvec s (s + 1),
      putnam_2019_b4_vec_eq vec hvec s s] using hrect_explicit s hs
  have hG_one : G 1 = (2 * Real.log 2 - 1 / 2 : ℝ) := by
    dsimp [G]
    rw [Real.log_one]
    ring
  let S : Set ℝ :=
    {f (vec (s + 1) (s + 1)) - f (vec (s + 1) s) - f (vec s (s + 1)) + f (vec s s) | s ≥ 1}
  have hleast : IsLeast S (G 1) := by
    constructor
    · refine ⟨1, le_rfl, ?_⟩
      simpa using hrect 1 le_rfl
    · intro a ha
      rcases ha with ⟨s, hs, rfl⟩
      rw [hrect s hs]
      exact putnam_2019_b4_G_mono (by simp : (1 : ℝ) ∈ Set.Ici (1 : ℝ)) hs hs
  calc
    sInf {f (vec (s + 1) (s + 1)) - f (vec (s + 1) s) - f (vec s (s + 1)) + f (vec s s) | s ≥ 1}
        = G 1 := hleast.csInf_eq
    _ = (2 * Real.log 2 - 1 / 2 : ℝ) := hG_one
