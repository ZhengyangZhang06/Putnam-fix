import Mathlib

open Topology MvPolynomial Filter Set

noncomputable abbrev putnam_2009_a2_solution : ℝ → ℝ :=
  fun x => (Real.tan (6 * x + Real.pi / 4)) ^ ((1 : ℝ) / 6) *
    ((1 / (2 * (Real.cos (6 * x + Real.pi / 4)) ^ 2)) ^ ((1 : ℝ) / 12))

/--
Functions $f,g,h$ are differentiable on some open interval around $0$
and satisfy the equations and initial conditions
\begin{gather*}
f' = 2f^2gh+\frac{1}{gh},\quad f(0)=1, \\
g'=fg^2h+\frac{4}{fh}, \quad g(0)=1, \\
h'=3fgh^2+\frac{1}{fg}, \quad h(0)=1.
\end{gather*}
Find an explicit formula for $f(x)$, valid in some open interval around $0$.
-/
theorem putnam_2009_a2
(f g h : ℝ → ℝ)
(a b : ℝ)
(hab : 0 ∈ Ioo a b)
(hdiff : DifferentiableOn ℝ f (Ioo a b) ∧ DifferentiableOn ℝ g (Ioo a b) ∧ DifferentiableOn ℝ h (Ioo a b))
(hf : (∀ x ∈ Ioo a b, deriv f x = 2 * (f x)^2 * (g x) * (h x) + 1 / ((g x) * (h x))) ∧ f 0 = 1)
(hg : (∀ x ∈ Ioo a b, deriv g x = (f x) * (g x)^2 * (h x) + 4 / ((f x) * (h x))) ∧ g 0 = 1)
(hh : (∀ x ∈ Ioo a b, deriv h x = 3 * (f x) * (g x) * (h x)^2 + 1 / ((f x) * (g x))) ∧ h 0 = 1)
: (∃ c d : ℝ, 0 ∈ Ioo c d ∧ ∀ x ∈ Ioo c d, f x = putnam_2009_a2_solution x) :=
by
  classical
  let y : ℝ → ℝ := fun x => f x * g x * h x
  let q : ℝ → ℝ := fun x => (1 + (y x)^2) / 2
  have hf_at0 : DifferentiableAt ℝ f 0 :=
    hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hab)
  have hg_at0 : DifferentiableAt ℝ g 0 :=
    hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hab)
  have hh_at0 : DifferentiableAt ℝ h 0 :=
    hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hab)
  have hfpos_nhds : {x : ℝ | 0 < f x} ∈ 𝓝 0 := by
    exact hf_at0.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by simp [hf.2]))
  have hgpos_nhds : {x : ℝ | 0 < g x} ∈ 𝓝 0 := by
    exact hg_at0.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by simp [hg.2]))
  have hhpos_nhds : {x : ℝ | 0 < h x} ∈ 𝓝 0 := by
    exact hh_at0.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by simp [hh.2]))
  have hgood_nhds :
      {x : ℝ | x ∈ Ioo a b ∧ 0 < f x ∧ 0 < g x ∧ 0 < h x} ∈ 𝓝 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hab, hfpos_nhds, hgpos_nhds, hhpos_nhds] with
      x hxab hfx hgx hhx
    exact ⟨hxab, hfx, hgx, hhx⟩
  obtain ⟨c, d, h0cd, hcd⟩ :=
    Filter.Eventually.exists_Ioo_subset
      (show ∀ᶠ x in 𝓝 0, x ∈ Ioo a b ∧ 0 < f x ∧ 0 < g x ∧ 0 < h x from
        hgood_nhds)
  refine ⟨c, d, h0cd, ?_⟩
  have hsopen : IsOpen (Ioo c d : Set ℝ) := isOpen_Ioo
  have hspre : IsPreconnected (Ioo c d : Set ℝ) := isPreconnected_Ioo
  have hsub_ab : Ioo c d ⊆ Ioo a b := fun x hx => (hcd hx).1
  have hfpos : ∀ x ∈ Ioo c d, 0 < f x := fun x hx => (hcd hx).2.1
  have hgpos : ∀ x ∈ Ioo c d, 0 < g x := fun x hx => (hcd hx).2.2.1
  have hhpos : ∀ x ∈ Ioo c d, 0 < h x := fun x hx => (hcd hx).2.2.2
  have hfd_at : ∀ x ∈ Ioo c d, DifferentiableAt ℝ f x := by
    intro x hx
    exact hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds (hsub_ab hx))
  have hgd_at : ∀ x ∈ Ioo c d, DifferentiableAt ℝ g x := by
    intro x hx
    exact hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds (hsub_ab hx))
  have hhd_at : ∀ x ∈ Ioo c d, DifferentiableAt ℝ h x := by
    intro x hx
    exact hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds (hsub_ab hx))
  have hydiff_at : ∀ x ∈ Ioo c d, DifferentiableAt ℝ y x := by
    intro x hx
    change DifferentiableAt ℝ (fun t => f t * g t * h t) x
    exact ((hfd_at x hx).mul (hgd_at x hx)).mul (hhd_at x hx)
  have hypos : ∀ x ∈ Ioo c d, 0 < y x := by
    intro x hx
    dsimp [y]
    exact mul_pos (mul_pos (hfpos x hx) (hgpos x hx)) (hhpos x hx)
  have hqpos : ∀ x ∈ Ioo c d, 0 < q x := by
    intro x hx
    dsimp [q]
    have hsq : 0 ≤ (y x)^2 := sq_nonneg (y x)
    nlinarith
  have hy_deriv : ∀ x ∈ Ioo c d, deriv y x = 6 * (y x)^2 + 6 := by
    intro x hx
    have hfnz : f x ≠ 0 := ne_of_gt (hfpos x hx)
    have hgnz : g x ≠ 0 := ne_of_gt (hgpos x hx)
    have hhnz : h x ≠ 0 := ne_of_gt (hhpos x hx)
    dsimp [y]
    change deriv ((f * g) * h) x = 6 * (f x * g x * h x) ^ 2 + 6
    rw [deriv_mul ((hfd_at x hx).mul (hgd_at x hx)) (hhd_at x hx)]
    rw [deriv_mul (hfd_at x hx) (hgd_at x hx)]
    simp only [Pi.mul_apply]
    rw [hf.1 x (hsub_ab hx), hg.1 x (hsub_ab hx), hh.1 x (hsub_ab hx)]
    field_simp [hfnz, hgnz, hhnz, mul_ne_zero]; ring
  have hq_has_deriv_at : ∀ x ∈ Ioo c d, HasDerivAt q (y x * (6 * (y x)^2 + 6)) x := by
    intro x hx
    have hyHas : HasDerivAt y (6 * (y x)^2 + 6) x := by
      simpa [hy_deriv x hx] using (hydiff_at x hx).hasDerivAt
    dsimp [q]
    have hsq : HasDerivAt (fun t => (y t)^2) (2 * y x * (6 * (y x)^2 + 6)) x := by
      convert hyHas.mul hyHas using 1
      · ext t
        simp [pow_two]
      · ring
    convert (hsq.const_add 1).div_const 2 using 1; ring
  have hqdiff_at : ∀ x ∈ Ioo c d, DifferentiableAt ℝ q x := by
    intro x hx
    exact (hq_has_deriv_at x hx).differentiableAt
  have harctan_diff : DifferentiableOn ℝ (fun x => Real.arctan (y x)) (Ioo c d) := by
    intro x hx
    exact ((hydiff_at x hx).arctan).differentiableWithinAt
  have hlin_has_deriv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 6 * x + Real.pi / 4) 6 x := by
    intro x
    simpa using (((hasDerivAt_id x).const_mul (6 : ℝ)).add_const (Real.pi / 4))
  have hlin_diff : DifferentiableOn ℝ (fun x : ℝ => 6 * x + Real.pi / 4) (Ioo c d) := by
    intro x hx
    exact (hlin_has_deriv x).differentiableAt.differentiableWithinAt
  have harctan_deriv_eq :
      (Ioo c d).EqOn (deriv (fun x => Real.arctan (y x)))
        (deriv (fun x : ℝ => 6 * x + Real.pi / 4)) := by
    intro x hx
    rw [deriv_arctan (hydiff_at x hx), hy_deriv x hx, (hlin_has_deriv x).deriv]
    have hden : 1 + (y x)^2 ≠ 0 := by nlinarith [sq_nonneg (y x)]
    field_simp [hden]; ring
  have harctan_eq :
      (Ioo c d).EqOn (fun x => Real.arctan (y x)) (fun x : ℝ => 6 * x + Real.pi / 4) := by
    apply hsopen.eqOn_of_deriv_eq hspre harctan_diff hlin_diff harctan_deriv_eq h0cd
    dsimp [y]
    rw [hf.2, hg.2, hh.2]
    norm_num [Real.arctan_one]
  have hy_tan : ∀ x ∈ Ioo c d, y x = Real.tan (6 * x + Real.pi / 4) := by
    intro x hx
    have htan := congrArg Real.tan (harctan_eq hx)
    simpa [Real.tan_arctan] using htan
  have hlogf_diff : DifferentiableOn ℝ (fun x => Real.log (f x)) (Ioo c d) := by
    intro x hx
    exact ((hfd_at x hx).log (ne_of_gt (hfpos x hx))).differentiableWithinAt
  have hR_diff :
      DifferentiableOn ℝ
        (fun x => (1 / 6 : ℝ) * Real.log (y x) + (1 / 12 : ℝ) * Real.log (q x))
        (Ioo c d) := by
    intro x hx
    have hlogy : DifferentiableAt ℝ (fun t => Real.log (y t)) x :=
      (hydiff_at x hx).log (ne_of_gt (hypos x hx))
    have hlogq : DifferentiableAt ℝ (fun t => Real.log (q t)) x :=
      (hqdiff_at x hx).log (ne_of_gt (hqpos x hx))
    exact
      ((hlogy.const_mul ((1 : ℝ) / 6)).add
        (hlogq.const_mul ((1 : ℝ) / 12))).differentiableWithinAt
  have hlog_deriv_eq :
      (Ioo c d).EqOn (deriv (fun x => Real.log (f x)))
        (deriv
          (fun x => (1 / 6 : ℝ) * Real.log (y x) + (1 / 12 : ℝ) * Real.log (q x))) := by
    intro x hx
    have hfnz : f x ≠ 0 := ne_of_gt (hfpos x hx)
    have hgnz : g x ≠ 0 := ne_of_gt (hgpos x hx)
    have hhnz : h x ≠ 0 := ne_of_gt (hhpos x hx)
    have hynz : y x ≠ 0 := ne_of_gt (hypos x hx)
    have hqne : q x ≠ 0 := ne_of_gt (hqpos x hx)
    have hder_logf : deriv (fun t => Real.log (f t)) x = 2 * y x + 1 / y x := by
      rw [deriv.log (hfd_at x hx) hfnz]
      rw [hf.1 x (hsub_ab hx)]
      dsimp [y]
      field_simp [hfnz, hgnz, hhnz, mul_ne_zero]
    have hyHas : HasDerivAt y (6 * (y x)^2 + 6) x := by
      simpa [hy_deriv x hx] using (hydiff_at x hx).hasDerivAt
    have hlogy_has :
        HasDerivAt (fun t => Real.log (y t)) ((6 * (y x)^2 + 6) / y x) x :=
      hyHas.log hynz
    have hlogq_has :
        HasDerivAt (fun t => Real.log (q t)) ((y x * (6 * (y x)^2 + 6)) / q x) x :=
      (hq_has_deriv_at x hx).log hqne
    have hR_has :
        HasDerivAt
          (fun t => (1 / 6 : ℝ) * Real.log (y t) + (1 / 12 : ℝ) * Real.log (q t))
          ((1 / 6 : ℝ) * ((6 * (y x)^2 + 6) / y x) +
            (1 / 12 : ℝ) * ((y x * (6 * (y x)^2 + 6)) / q x)) x := by
      exact (hlogy_has.const_mul ((1 : ℝ) / 6)).add
        (hlogq_has.const_mul ((1 : ℝ) / 12))
    have hder_R :
        deriv
          (fun t => (1 / 6 : ℝ) * Real.log (y t) + (1 / 12 : ℝ) * Real.log (q t)) x =
            2 * y x + 1 / y x := by
      rw [hR_has.deriv]
      dsimp [q]
      have hden : 1 + (y x)^2 ≠ 0 := by nlinarith [sq_nonneg (y x)]
      field_simp [hynz, hden]; ring
    exact hder_logf.trans hder_R.symm
  have hlog_eq :
      (Ioo c d).EqOn (fun x => Real.log (f x))
        (fun x => (1 / 6 : ℝ) * Real.log (y x) + (1 / 12 : ℝ) * Real.log (q x)) := by
    apply hsopen.eqOn_of_deriv_eq hspre hlogf_diff hR_diff hlog_deriv_eq h0cd
    dsimp [y, q]
    rw [hf.2, hg.2, hh.2]
    norm_num [Real.log_one]
  intro x hx
  have hlogx := hlog_eq hx
  have hyxpos : 0 < y x := hypos x hx
  have hqxpos : 0 < q x := hqpos x hx
  calc
    f x = Real.exp (Real.log (f x)) := (Real.exp_log (hfpos x hx)).symm
    _ = Real.exp ((1 / 6 : ℝ) * Real.log (y x) + (1 / 12 : ℝ) * Real.log (q x)) := by
      simpa using congrArg Real.exp hlogx
    _ = (y x) ^ ((1 : ℝ) / 6) * (q x) ^ ((1 : ℝ) / 12) := by
      rw [Real.rpow_def_of_pos hyxpos, Real.rpow_def_of_pos hqxpos, ← Real.exp_add]
      congr 1
      ring
    _ = putnam_2009_a2_solution x := by
      let θ : ℝ := 6 * x + Real.pi / 4
      have hyθ : y x = Real.tan θ := by
        simpa [θ] using hy_tan x hx
      have hθ_arctan : Real.arctan (y x) = θ := by
        simpa [θ] using harctan_eq hx
      have hcospos : 0 < Real.cos θ := by
        simpa [hθ_arctan.symm] using Real.cos_arctan_pos (y x)
      have hqeq : q x = 1 / (2 * (Real.cos θ)^2) := by
        dsimp [q]
        rw [hyθ, Real.tan_eq_sin_div_cos]
        have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcospos
        field_simp [hcosne]
        nlinarith [Real.sin_sq_add_cos_sq θ]
      calc
        (y x) ^ ((1 : ℝ) / 6) * (q x) ^ ((1 : ℝ) / 12)
            = (Real.tan θ) ^ ((1 : ℝ) / 6) *
              ((1 / (2 * (Real.cos θ)^2)) ^ ((1 : ℝ) / 12)) := by
          rw [hyθ, hqeq]
        _ = putnam_2009_a2_solution x := by
          simp [putnam_2009_a2_solution, θ]
