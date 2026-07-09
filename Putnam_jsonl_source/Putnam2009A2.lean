import Mathlib

open Topology MvPolynomial Filter Set

private lemma putnam_2009_a2_product_deriv
    (f g h : ℝ → ℝ) (x : ℝ)
    (hfd : DifferentiableAt ℝ f x) (hgd : DifferentiableAt ℝ g x)
    (hhd : DifferentiableAt ℝ h x)
    (hfder : deriv f x = 2 * (f x)^2 * (g x) * (h x) + 1 / ((g x) * (h x)))
    (hgder : deriv g x = (f x) * (g x)^2 * (h x) + 4 / ((f x) * (h x)))
    (hhder : deriv h x = 3 * (f x) * (g x) * (h x)^2 + 1 / ((f x) * (g x)))
    (hfpos : 0 < f x) (hgpos : 0 < g x) (hhpos : 0 < h x) :
    deriv (fun y => f y * g y * h y) x = 6 * ((f x * g x * h x)^2 + 1) := by
  have hmul1 : deriv (fun y => f y * g y * h y) x =
      deriv (fun y => f y * g y) x * h x + (f x * g x) * deriv h x := by
    simpa only [Pi.mul_apply] using
      (deriv_mul (c := fun y => f y * g y) (d := h) (x := x) (hfd.mul hgd) hhd)
  rw [hmul1]
  have hmul2 : deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x := by
    simpa only [Pi.mul_apply] using (deriv_mul (c := f) (d := g) (x := x) hfd hgd)
  rw [hmul2]
  rw [hfder, hgder, hhder]
  have hfnz : f x ≠ 0 := ne_of_gt hfpos
  have hgnz : g x ≠ 0 := ne_of_gt hgpos
  have hhnz : h x ≠ 0 := ne_of_gt hhpos
  field_simp [hfnz, hgnz, hhnz]
  ring

private lemma putnam_2009_a2_f_deriv
    (f g h : ℝ → ℝ) (x : ℝ)
    (hfder : deriv f x = 2 * (f x)^2 * (g x) * (h x) + 1 / ((g x) * (h x)))
    (hfpos : 0 < f x) (hgpos : 0 < g x) (hhpos : 0 < h x) :
    deriv f x = f x * (2 * (f x * g x * h x) + 1 / (f x * g x * h x)) := by
  rw [hfder]
  have hfnz : f x ≠ 0 := ne_of_gt hfpos
  have hgnz : g x ≠ 0 := ne_of_gt hgpos
  have hhnz : h x ≠ 0 := ne_of_gt hhpos
  field_simp [hfnz, hgnz, hhnz]

private lemma putnam_2009_a2_arctan_deriv
    (p : ℝ → ℝ) (x : ℝ)
    (hpd : DifferentiableAt ℝ p x)
    (hpder : deriv p x = 6 * ((p x)^2 + 1)) :
    deriv (fun y => Real.arctan (p y) - (6 * y + Real.pi / 4)) x = 0 := by
  have htheta_diff : DifferentiableAt ℝ (fun y : ℝ => 6 * y + Real.pi / 4) x := by
    fun_prop
  have hsub : deriv (fun y => Real.arctan (p y) - (6 * y + Real.pi / 4)) x =
      deriv (fun y => Real.arctan (p y)) x -
        deriv (fun y : ℝ => 6 * y + Real.pi / 4) x := by
    simpa only [Pi.sub_apply] using
      (deriv_sub (f := fun y => Real.arctan (p y))
        (g := fun y : ℝ => 6 * y + Real.pi / 4) (x := x) hpd.arctan htheta_diff)
  rw [hsub, deriv_arctan hpd, hpder]
  have htheta : deriv (fun y : ℝ => 6 * y + Real.pi / 4) x = 6 := by
    have hmul : deriv (fun y : ℝ => 6 * y) x = 6 := by
      simpa using ((hasDerivAt_id x).const_mul (6 : ℝ)).deriv
    rw [show (fun y : ℝ => 6 * y + Real.pi / 4) =
        (fun y => 6 * y) + fun _ => Real.pi / 4 by ext; rfl]
    rw [deriv_add]
    · simp [hmul]
    · fun_prop
    · fun_prop
  rw [htheta]
  have hpne : 1 + p x ^ 2 ≠ 0 := by positivity
  field_simp [hpne]
  ring

private lemma putnam_2009_a2_ratio_deriv
    (f p : ℝ → ℝ) (x : ℝ)
    (hfd : DifferentiableAt ℝ f x) (hpd : DifferentiableAt ℝ p x)
    (hfder : deriv f x = f x * (2 * p x + 1 / p x))
    (hpder : deriv p x = 6 * ((p x)^2 + 1))
    (hfpos : 0 < f x) (hppos : 0 < p x) :
    deriv (fun y => (2 * (f y)^12) / ((p y)^2 * (1 + (p y)^2))) x = 0 := by
  let num : ℝ → ℝ := fun y => 2 * (f y)^12
  let den : ℝ → ℝ := fun y => (p y)^2 * (1 + (p y)^2)
  have hnumd : DifferentiableAt ℝ num x := by
    dsimp [num]
    fun_prop
  have hdend : DifferentiableAt ℝ den x := by
    dsimp [den]
    fun_prop
  have hden_ne : den x ≠ 0 := by
    dsimp [den]
    positivity
  have hdiv : deriv (fun y => (2 * (f y)^12) / ((p y)^2 * (1 + (p y)^2))) x =
      (deriv num x * den x - num x * deriv den x) / den x ^ 2 := by
    simpa [num, den] using
      (deriv_div (c := num) (d := den) (x := x) hnumd hdend hden_ne)
  rw [hdiv]
  have hpowf : deriv (fun y => (f y)^12) x = 12 * (f x)^11 * deriv f x := by
    change deriv (f ^ 12) x = 12 * (f x)^11 * deriv f x
    simpa [pow_one] using (deriv_pow (f := f) (x := x) hfd 12)
  have hnumder : deriv num x = 24 * (f x)^11 * deriv f x := by
    dsimp [num]
    rw [deriv_const_mul_field, hpowf]
    ring
  have hp2 : deriv (fun y => (p y)^2) x = 2 * p x * deriv p x := by
    change deriv (p ^ 2) x = 2 * p x * deriv p x
    simpa [pow_one] using (deriv_pow (f := p) (x := x) hpd 2)
  have hdender :
      deriv den x =
        (2 * p x * deriv p x) * (1 + (p x)^2) + (p x)^2 * (2 * p x * deriv p x) := by
    dsimp [den]
    have hadd : deriv (fun y => 1 + (p y)^2) x = 2 * p x * deriv p x := by
      have hderadd := deriv_add (f := fun _ : ℝ => 1) (g := fun y => (p y)^2)
        (x := x) (by fun_prop) (hpd.pow 2)
      simpa only [Pi.add_apply, deriv_const', zero_add, hp2] using hderadd
    have hmul := deriv_mul (c := fun y => (p y)^2) (d := fun y => 1 + (p y)^2)
      (x := x) (hpd.pow 2) (by fun_prop)
    simpa only [Pi.mul_apply, hp2, hadd] using hmul
  rw [hnumder, hdender, hfder, hpder]
  have hpnz : p x ≠ 0 := ne_of_gt hppos
  have hfnz : f x ≠ 0 := ne_of_gt hfpos
  have hpquad : 1 + p x ^ 2 ≠ 0 := by positivity
  dsimp [num, den]
  field_simp [hpnz, hfnz, hpquad]
  ring

private lemma putnam_2009_a2_trig_square (t : ℝ) (hcos : Real.cos t ≠ 0) :
    (Real.tan t)^2 * (1 + (Real.tan t)^2) / 2 =
      (Real.sin t / (Real.cos t)^2)^2 / 2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  nlinarith [Real.sin_sq_add_cos_sq t]

private lemma putnam_2009_a2_rpow_formula
    (u B : ℝ) (hupos : 0 < u) (hBpos : 0 < B)
    (hpow : u ^ 12 = B ^ 2 / 2) :
    u = 2 ^ (-(1 : ℝ) / 12) * B ^ ((1 : ℝ) / 6) := by
  have hcand_nonneg : 0 ≤ 2 ^ (-(1 : ℝ) / 12) * B ^ ((1 : ℝ) / 6) := by
    positivity
  apply (pow_left_inj₀ hupos.le hcand_nonneg (by norm_num : (12 : ℕ) ≠ 0)).mp
  rw [hpow]
  have hcandpow :
      (2 ^ (-(1 : ℝ) / 12) * B ^ ((1 : ℝ) / 6)) ^ (12 : ℕ) = B ^ 2 / 2 := by
    rw [mul_pow]
    rw [show (2 ^ (-(1 : ℝ) / 12) : ℝ) ^ (12 : ℕ) = (1 / 2 : ℝ) by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [Real.rpow_neg_one]]
    rw [show (B ^ ((1 : ℝ) / 6) : ℝ) ^ (12 : ℕ) = B ^ 2 by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hBpos.le]
      norm_num]
    ring
  rw [hcandpow]

-- fun x ↦ 2 ^ (-(1 : ℝ) / 12) * (Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4)) ^ 2) ^ ((1 : ℝ) / 6)
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
: (∃ c d : ℝ, 0 ∈ Ioo c d ∧ ∀ x ∈ Ioo c d, f x = ((fun x ↦ 2 ^ (-(1 : ℝ) / 12) * (Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4)) ^ 2) ^ ((1 : ℝ) / 6)) : ℝ → ℝ ) x) := by
  let p : ℝ → ℝ := fun x => f x * g x * h x
  let θ : ℝ → ℝ := fun x => 6 * x + Real.pi / 4
  have hfdiff0 : DifferentiableAt ℝ f 0 :=
    hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hab)
  have hgdiff0 : DifferentiableAt ℝ g 0 :=
    hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hab)
  have hhdiff0 : DifferentiableAt ℝ h 0 :=
    hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hab)
  have hfpos_mem : {x | 0 < f x} ∈ 𝓝 (0 : ℝ) := by
    have hpre := hfdiff0.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (by simp [hf.2] : (0 : ℝ) < f 0))
    simpa using hpre
  have hgpos_mem : {x | 0 < g x} ∈ 𝓝 (0 : ℝ) := by
    have hpre := hgdiff0.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (by simp [hg.2] : (0 : ℝ) < g 0))
    simpa using hpre
  have hhpos_mem : {x | 0 < h x} ∈ 𝓝 (0 : ℝ) := by
    have hpre := hhdiff0.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (by simp [hh.2] : (0 : ℝ) < h 0))
    simpa using hpre
  have hsmall_mem : Ioo (-(Real.pi) / 24) (Real.pi / 24) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hU :
      ((((Ioo a b ∩ {x | 0 < f x}) ∩ {x | 0 < g x}) ∩ {x | 0 < h x}) ∩
          Ioo (-(Real.pi) / 24) (Real.pi / 24)) ∈ 𝓝 (0 : ℝ) :=
    inter_mem (inter_mem (inter_mem (inter_mem (isOpen_Ioo.mem_nhds hab) hfpos_mem)
      hgpos_mem) hhpos_mem) hsmall_mem
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU with ⟨c, d, hcd, hsubU⟩
  refine ⟨c, d, hcd, ?_⟩
  have hdata (x : ℝ) (hx : x ∈ Ioo c d) :
      x ∈ Ioo a b ∧ 0 < f x ∧ 0 < g x ∧ 0 < h x ∧
        x ∈ Ioo (-(Real.pi) / 24) (Real.pi / 24) := by
    have hxU := hsubU hx
    exact ⟨hxU.1.1.1.1, hxU.1.1.1.2, hxU.1.1.2, hxU.1.2, hxU.2⟩
  have hsubset : Ioo c d ⊆ Ioo a b := fun x hx => (hdata x hx).1
  have hfpos_s : ∀ x ∈ Ioo c d, 0 < f x := fun x hx => (hdata x hx).2.1
  have hgpos_s : ∀ x ∈ Ioo c d, 0 < g x := fun x hx => (hdata x hx).2.2.1
  have hhpos_s : ∀ x ∈ Ioo c d, 0 < h x := fun x hx => (hdata x hx).2.2.2.1
  have hsmall_s : ∀ x ∈ Ioo c d, x ∈ Ioo (-(Real.pi) / 24) (Real.pi / 24) :=
    fun x hx => (hdata x hx).2.2.2.2
  have hfdiff_s : DifferentiableOn ℝ f (Ioo c d) := hdiff.1.mono hsubset
  have hgdiff_s : DifferentiableOn ℝ g (Ioo c d) := hdiff.2.1.mono hsubset
  have hhdiff_s : DifferentiableOn ℝ h (Ioo c d) := hdiff.2.2.mono hsubset
  have hpdiff_s : DifferentiableOn ℝ p (Ioo c d) := by
    simpa [p, Pi.mul_apply, mul_assoc] using (hfdiff_s.mul hgdiff_s).mul hhdiff_s
  have hpderiv : ∀ x ∈ Ioo c d, deriv p x = 6 * ((p x)^2 + 1) := by
    intro x hx
    have hxorig := hsubset hx
    have hfdx : DifferentiableAt ℝ f x := hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hxorig)
    have hgdx : DifferentiableAt ℝ g x := hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hxorig)
    have hhdx : DifferentiableAt ℝ h x := hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hxorig)
    have hcalc := putnam_2009_a2_product_deriv f g h x hfdx hgdx hhdx
      (hf.1 x hxorig) (hg.1 x hxorig) (hh.1 x hxorig)
      (hfpos_s x hx) (hgpos_s x hx) (hhpos_s x hx)
    simpa [p] using hcalc
  have hp_pos : ∀ x ∈ Ioo c d, 0 < p x := by
    intro x hx
    dsimp [p]
    exact mul_pos (mul_pos (hfpos_s x hx) (hgpos_s x hx)) (hhpos_s x hx)
  have harctan_diff : DifferentiableOn ℝ
      (fun x => Real.arctan (p x) - (6 * x + Real.pi / 4)) (Ioo c d) := by
    exact hpdiff_s.arctan.sub (by fun_prop)
  have harctan_deriv : EqOn
      (deriv (fun x => Real.arctan (p x) - (6 * x + Real.pi / 4))) 0 (Ioo c d) := by
    intro x hx
    have hpd_x : DifferentiableAt ℝ p x :=
      hpdiff_s.differentiableAt (isOpen_Ioo.mem_nhds hx)
    exact putnam_2009_a2_arctan_deriv p x hpd_x (hpderiv x hx)
  have harctan_eq : EqOn (fun x => Real.arctan (p x) - (6 * x + Real.pi / 4)) 0
      (Ioo c d) := by
    intro x hx
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo harctan_diff
      harctan_deriv hx hcd
    have hzero : Real.arctan (p 0) - Real.pi / 4 = 0 := by
      dsimp [p]
      simp [hf.2, hg.2, hh.2, Real.arctan_one]
    simpa [hzero] using hconst
  have hp_tan : ∀ x ∈ Ioo c d, p x = Real.tan (θ x) := by
    intro x hx
    have hθ : Real.arctan (p x) = θ x := by
      have h := harctan_eq hx
      dsimp [θ] at h ⊢
      linarith
    calc
      p x = Real.tan (Real.arctan (p x)) := by rw [Real.tan_arctan]
      _ = Real.tan (θ x) := by rw [hθ]
  have hratio_diff : DifferentiableOn ℝ
      (fun y => (2 * (f y)^12) / ((p y)^2 * (1 + (p y)^2))) (Ioo c d) := by
    refine (hfdiff_s.pow 12).const_mul (2 : ℝ) |>.div ?_ ?_
    · exact (hpdiff_s.pow 2).mul ((differentiableOn_const (1 : ℝ)).add (hpdiff_s.pow 2))
    · intro x hx
      have hppos := hp_pos x hx
      positivity
  have hratio_deriv : EqOn
      (deriv (fun y => (2 * (f y)^12) / ((p y)^2 * (1 + (p y)^2)))) 0 (Ioo c d) := by
    intro x hx
    have hxorig := hsubset hx
    have hfdx : DifferentiableAt ℝ f x := hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hxorig)
    have hpdx : DifferentiableAt ℝ p x := hpdiff_s.differentiableAt (isOpen_Ioo.mem_nhds hx)
    have hfderx := putnam_2009_a2_f_deriv f g h x (hf.1 x hxorig)
      (hfpos_s x hx) (hgpos_s x hx) (hhpos_s x hx)
    simpa [p] using putnam_2009_a2_ratio_deriv f p x hfdx hpdx
      (by simpa [p] using hfderx) (hpderiv x hx) (hfpos_s x hx) (hp_pos x hx)
  have hratio_eq : EqOn
      (fun y => (2 * (f y)^12) / ((p y)^2 * (1 + (p y)^2))) 1 (Ioo c d) := by
    intro x hx
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hratio_diff
      hratio_deriv hx hcd
    have hzero : (2 * (f 0)^12) / ((p 0)^2 * (1 + (p 0)^2)) = (1 : ℝ) := by
      dsimp [p]
      norm_num [hf.2, hg.2, hh.2]
    simpa [hzero] using hconst
  intro x hx
  have hxdata := hdata x hx
  have hθIoo : θ x ∈ Ioo 0 (Real.pi / 2) := by
    dsimp [θ]
    constructor <;> nlinarith [hsmall_s x hx |>.1, hsmall_s x hx |>.2, Real.pi_pos]
  have hcospos : 0 < Real.cos (θ x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθIoo.1, Real.pi_pos], hθIoo.2⟩
  have hsinpos : 0 < Real.sin (θ x) :=
    Real.sin_pos_of_mem_Ioo ⟨hθIoo.1, by linarith [hθIoo.2, Real.pi_pos]⟩
  have hBpos : 0 < Real.sin (θ x) / (Real.cos (θ x)) ^ 2 := by
    positivity
  have hpoly : (f x)^12 = (p x)^2 * (1 + (p x)^2) / 2 := by
    have hratio : 2 * (f x)^12 / ((p x)^2 * (1 + (p x)^2)) = (1 : ℝ) := by
      simpa using hratio_eq hx
    have hppos : 0 < p x := hp_pos x hx
    have hp2ne : (p x)^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hppos)
    have hpquadne : 1 + (p x)^2 ≠ 0 := by positivity
    field_simp [hp2ne, hpquadne] at hratio
    nlinarith
  have htrigpow :
      (f x)^12 = (Real.sin (θ x) / (Real.cos (θ x)) ^ 2)^2 / 2 := by
    calc
      (f x)^12 = (p x)^2 * (1 + (p x)^2) / 2 := hpoly
      _ = (Real.tan (θ x))^2 * (1 + (Real.tan (θ x))^2) / 2 := by
        rw [hp_tan x hx]
      _ = (Real.sin (θ x) / (Real.cos (θ x)) ^ 2)^2 / 2 :=
        putnam_2009_a2_trig_square (θ x) hcospos.ne'
  have hform := putnam_2009_a2_rpow_formula (f x)
    (Real.sin (θ x) / (Real.cos (θ x)) ^ 2) (hfpos_s x hx) hBpos htrigpow
  simpa [θ] using hform
