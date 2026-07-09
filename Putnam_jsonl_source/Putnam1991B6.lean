import Mathlib

open Filter Topology

private lemma putnam_1991_b6_base {u x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * Real.exp (u * x) * Real.sinh u ≤ Real.exp u * Real.sinh (u * x) := by
  have ht : |1 - 2 * x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h := Real.exp_mul_le_cosh_add_mul_sinh (t := 1 - 2 * x) ht u
  have h' : Real.exp ((1 - 2 * x) * u) ≤ Real.exp u - 2 * x * Real.sinh u := by
    calc
      Real.exp ((1 - 2 * x) * u) ≤ Real.cosh u + (1 - 2 * x) * Real.sinh u := h
      _ = Real.exp u - 2 * x * Real.sinh u := by
        rw [← Real.cosh_add_sinh u]
        ring
  have h'' : 2 * x * Real.sinh u ≤ Real.exp u - Real.exp ((1 - 2 * x) * u) := by
    linarith
  have hnon : 0 ≤ Real.exp (u * x) / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left h'' hnon
  have hleft : Real.exp (u * x) / 2 * (2 * x * Real.sinh u) =
      x * Real.exp (u * x) * Real.sinh u := by
    ring
  have hright :
      Real.exp (u * x) / 2 * (Real.exp u - Real.exp ((1 - 2 * x) * u)) =
        Real.exp u * Real.sinh (u * x) := by
    rw [Real.sinh_eq]
    ring_nf
    repeat rw [← Real.exp_add]
    ring_nf
  rw [hleft, hright] at hmul
  exact hmul

private lemma putnam_1991_b6_eq_at (u x : ℝ) :
    Real.exp u * Real.sinh (u * x) + Real.sinh (u * (1 - x)) =
      Real.exp (u * x) * Real.sinh u := by
  rw [Real.sinh_eq, Real.sinh_eq, Real.sinh_eq]
  ring_nf
  repeat rw [← Real.exp_add]
  ring_nf

private lemma putnam_1991_b6_exp_conv {d x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (d * x) - 1 ≤ x * (Real.exp d - 1) := by
  have hconv : Real.exp (x * d + (1 - x) * 0) ≤
      x * Real.exp d + (1 - x) * Real.exp 0 := by
    simpa [smul_eq_mul] using
      (convexOn_exp.2 (Set.mem_univ d) (Set.mem_univ (0 : ℝ)) hx0
        (sub_nonneg.mpr hx1) (by ring))
  have hconv' : Real.exp (d * x) ≤ x * Real.exp d + (1 - x) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hconv
  linarith

private lemma putnam_1991_b6_core_pos {r u x : ℝ} (hu : 0 < u) (hur : u ≤ r)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (r * x) * Real.sinh u ≤
      Real.exp r * Real.sinh (u * x) + Real.sinh (u * (1 - x)) := by
  let d := r - u
  have hd : 0 ≤ d := by
    dsimp [d]
    linarith
  have hdexp : 0 ≤ Real.exp d - 1 := by
    exact sub_nonneg.mpr ((Real.one_le_exp_iff).mpr hd)
  have hconv : Real.exp (d * x) ≤ 1 + x * (Real.exp d - 1) := by
    have := putnam_1991_b6_exp_conv (d := d) hx0 hx1
    linarith
  have hfactor : 0 ≤ Real.exp (u * x) * Real.sinh u := by
    exact mul_nonneg (Real.exp_pos _).le (Real.sinh_pos_iff.mpr hu).le
  have hstep := mul_le_mul_of_nonneg_left hconv hfactor
  have hbase := putnam_1991_b6_base (u := u) hx0 hx1
  have hbase_mul := mul_le_mul_of_nonneg_left hbase hdexp
  have heq := putnam_1991_b6_eq_at u x
  have hexp1 : Real.exp (r * x) = Real.exp (u * x) * Real.exp (d * x) := by
    dsimp [d]
    rw [← Real.exp_add]
    ring_nf
  have hexp2 : Real.exp r = Real.exp u * Real.exp d := by
    dsimp [d]
    rw [← Real.exp_add]
    ring_nf
  calc
    Real.exp (r * x) * Real.sinh u
        = (Real.exp (u * x) * Real.sinh u) * Real.exp (d * x) := by
            rw [hexp1]
            ring
    _ ≤ (Real.exp (u * x) * Real.sinh u) * (1 + x * (Real.exp d - 1)) := hstep
    _ = Real.exp (u * x) * Real.sinh u +
        (Real.exp d - 1) * (x * Real.exp (u * x) * Real.sinh u) := by
          ring
    _ ≤ Real.exp (u * x) * Real.sinh u +
        (Real.exp d - 1) * (Real.exp u * Real.sinh (u * x)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hbase_mul (Real.exp (u * x) * Real.sinh u)
    _ = Real.exp r * Real.sinh (u * x) + Real.sinh (u * (1 - x)) := by
          rw [← heq, hexp2]
          ring

private lemma putnam_1991_b6_core_abs {r u x : ℝ} (hu : 0 < u) (hur : u ≤ |r|)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (r * x) * Real.sinh u ≤
      Real.exp r * Real.sinh (u * x) + Real.sinh (u * (1 - x)) := by
  by_cases hr : 0 ≤ r
  · have hur' : u ≤ r := by
      simpa [abs_of_nonneg hr] using hur
    exact putnam_1991_b6_core_pos hu hur' hx0 hx1
  · have hrlt : r < 0 := lt_of_not_ge hr
    have hur' : u ≤ -r := by
      simpa [abs_of_neg hrlt] using hur
    have hy0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    have hy1 : 1 - x ≤ 1 := by linarith
    have hpos := putnam_1991_b6_core_pos (r := -r) (u := u) (x := 1 - x) hu
      hur' hy0 hy1
    have hmul := mul_le_mul_of_nonneg_left hpos (Real.exp_pos r).le
    have hexp1 : Real.exp (r * x) = Real.exp r * Real.exp ((-r) * (1 - x)) := by
      rw [← Real.exp_add]
      ring_nf
    have hexp2 : Real.exp r * Real.exp (-r) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (r * x) * Real.sinh u
          = Real.exp r * (Real.exp ((-r) * (1 - x)) * Real.sinh u) := by
              rw [hexp1]
              ring
      _ ≤ Real.exp r * (Real.exp (-r) * Real.sinh (u * (1 - x)) +
            Real.sinh (u * (1 - (1 - x)))) := hmul
      _ = Real.exp r * Real.sinh (u * x) + Real.sinh (u * (1 - x)) := by
              rw [mul_add, ← mul_assoc, hexp2, one_mul]
              ring_nf

private lemma putnam_1991_b6_lhs (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ x * b ^ (1 - x) = b * Real.exp (Real.log (a / b) * x) := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
  rw [← Real.exp_add]
  rw [Real.log_div ha.ne' hb.ne']
  have harg : Real.log a * x + Real.log b * (1 - x) =
      Real.log b + (Real.log a - Real.log b) * x := by
    ring
  rw [harg, Real.exp_add, Real.exp_log hb]

private lemma putnam_1991_b6_a_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a = b * Real.exp (Real.log (a / b)) := by
  rw [Real.exp_log (div_pos ha hb)]
  field_simp [hb.ne']

private lemma putnam_1991_b6_sinh_ratio_abs (u x : ℝ) :
    Real.sinh (u * x) / Real.sinh u = Real.sinh (|u| * x) / Real.sinh |u| := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
  · have hlt : u < 0 := lt_of_not_ge hu
    rw [abs_of_neg hlt]
    conv_rhs => arg 1; rw [show -u * x = -(u * x) by ring]
    rw [Real.sinh_neg, Real.sinh_neg]
    ring

private lemma putnam_1991_b6_main_ineq (a b u x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < |u|) (hur : |u| ≤ |Real.log (a / b)|) (hx0 : 0 < x) (hx1 : x < 1) :
    a ^ x * b ^ (1 - x) ≤
      a * (Real.sinh (u * x) / Real.sinh u) +
        b * (Real.sinh (u * (1 - x)) / Real.sinh u) := by
  let r := Real.log (a / b)
  let v := |u|
  have hvpos : 0 < v := by
    simpa [v] using hu
  have hcore := putnam_1991_b6_core_abs (r := r) (u := v) (x := x) hvpos
    (by simpa [r, v] using hur) (le_of_lt hx0) (le_of_lt hx1)
  have hsinhpos : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hvpos
  have hdiv : Real.exp (r * x) ≤
      (Real.exp r * Real.sinh (v * x) + Real.sinh (v * (1 - x))) / Real.sinh v := by
    exact (le_div_iff₀ hsinhpos).2 hcore
  have hmul := mul_le_mul_of_nonneg_left hdiv hb.le
  calc
    a ^ x * b ^ (1 - x) = b * Real.exp (r * x) := by
      simpa [r] using putnam_1991_b6_lhs a b x ha hb
    _ ≤ b * ((Real.exp r * Real.sinh (v * x) + Real.sinh (v * (1 - x))) /
        Real.sinh v) := hmul
    _ = a * (Real.sinh (u * x) / Real.sinh u) +
        b * (Real.sinh (u * (1 - x)) / Real.sinh u) := by
      rw [putnam_1991_b6_a_eq a b ha hb]
      rw [putnam_1991_b6_sinh_ratio_abs u x, putnam_1991_b6_sinh_ratio_abs u (1 - x)]
      simp [r, v]
      ring

private lemma putnam_1991_b6_exp_add_one_eq (r : ℝ) :
    Real.exp r + 1 = 2 * Real.exp (r / 2) * Real.cosh (r / 2) := by
  rw [Real.cosh_eq]
  rw [Real.exp_neg]
  have hpos : Real.exp (r / 2) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hpos]
  rw [sq, ← Real.exp_add]
  ring_nf

private lemma putnam_1991_b6_core_half_strict {r v : ℝ} (hv : 0 < v) (hvr : |r| < v) :
    Real.exp r * Real.sinh (v * (1 / 2 : ℝ)) +
        Real.sinh (v * (1 - (1 / 2 : ℝ))) <
      Real.exp (r * (1 / 2 : ℝ)) * Real.sinh v := by
  have hsinh : 0 < Real.sinh (v / 2) := by
    apply Real.sinh_pos_iff.mpr
    linarith
  have hcosh : Real.cosh (r / 2) < Real.cosh (v / 2) := by
    rw [Real.cosh_lt_cosh]
    have hvr' : |r| < |v| := by
      simpa [abs_of_pos hv] using hvr
    have : |r / 2| < |v / 2| := by
      rw [abs_div, abs_div]
      exact div_lt_div_of_pos_right hvr' (by norm_num)
    simpa [abs_of_pos (by linarith : 0 < v / 2)] using this
  have hpos : 0 < 2 * Real.exp (r / 2) * Real.sinh (v / 2) := by positivity
  have hmul := mul_lt_mul_of_pos_left hcosh hpos
  calc
    Real.exp r * Real.sinh (v * (1 / 2 : ℝ)) +
        Real.sinh (v * (1 - (1 / 2 : ℝ)))
        = (Real.exp r + 1) * Real.sinh (v / 2) := by
          ring_nf
    _ = (2 * Real.exp (r / 2) * Real.sinh (v / 2)) * Real.cosh (r / 2) := by
          rw [putnam_1991_b6_exp_add_one_eq r]
          ring
    _ < (2 * Real.exp (r / 2) * Real.sinh (v / 2)) * Real.cosh (v / 2) := hmul
    _ = Real.exp (r * (1 / 2 : ℝ)) * Real.sinh v := by
          rw [show v = 2 * (v / 2) by ring, Real.sinh_two_mul]
          ring_nf

private lemma putnam_1991_b6_midpoint_fails (a b u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hur : |Real.log (a / b)| < u) :
    a * (Real.sinh (u * (1 / 2 : ℝ)) / Real.sinh u) +
        b * (Real.sinh (u * (1 - (1 / 2 : ℝ))) / Real.sinh u) <
      a ^ (1 / 2 : ℝ) * b ^ (1 - (1 / 2 : ℝ)) := by
  let r := Real.log (a / b)
  have hcore := putnam_1991_b6_core_half_strict (r := r) (v := u) hu
    (by simpa [r] using hur)
  have hsinhpos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hdiv :
      (Real.exp r * Real.sinh (u * (1 / 2 : ℝ)) +
          Real.sinh (u * (1 - (1 / 2 : ℝ)))) / Real.sinh u <
        Real.exp (r * (1 / 2 : ℝ)) := by
    exact (div_lt_iff₀ hsinhpos).2 hcore
  have hmul := mul_lt_mul_of_pos_left hdiv hb
  calc
    a * (Real.sinh (u * (1 / 2 : ℝ)) / Real.sinh u) +
        b * (Real.sinh (u * (1 - (1 / 2 : ℝ))) / Real.sinh u)
        = b * ((Real.exp r * Real.sinh (u * (1 / 2 : ℝ)) +
            Real.sinh (u * (1 - (1 / 2 : ℝ)))) / Real.sinh u) := by
          rw [putnam_1991_b6_a_eq a b ha hb]
          simp [r]
          ring
    _ < b * Real.exp (r * (1 / 2 : ℝ)) := hmul
    _ = a ^ (1 / 2 : ℝ) * b ^ (1 - (1 / 2 : ℝ)) := by
          rw [putnam_1991_b6_lhs a b (1 / 2 : ℝ) ha hb]

-- (fun a b : ℝ => |Real.log (a / b)|)
/--
Let $a$ and $b$ be positive numbers. Find the largest number $c$, in terms of $a$ and $b$, such that $a^xb^{1-x} \leq a\frac{\sinh ux}{\sinh u}+b\frac{\sinh u(1-x)}{\sinh u}$ for all $u$ with $0<|u| \leq c$ and for all $x$, $0< x<1$. (Note: $\sinh u=(e^u-e^{-u})/2$.)
-/
theorem putnam_1991_b6
  (a b : ℝ)
  (abpos : a > 0 ∧ b > 0) :
  IsGreatest {c | ∀ u,
    (0 < |u| ∧ |u| ≤ c) →
    (∀ x ∈ Set.Ioo 0 1, a ^ x * b ^ (1 - x) ≤ a * (Real.sinh (u * x) / Real.sinh u) + b * (Real.sinh (u * (1 - x)) / Real.sinh u))}
  (((fun a b : ℝ => |Real.log (a / b)|) : ℝ → ℝ → ℝ ) a b) := by
  constructor
  · intro u hu x hx
    exact putnam_1991_b6_main_ineq a b u x abpos.1 abpos.2 hu.1 hu.2 hx.1 hx.2
  · intro c hc
    by_contra hle
    have hlt : |Real.log (a / b)| < c := lt_of_not_ge hle
    let u := (c + |Real.log (a / b)|) / 2
    have hLnonneg : 0 ≤ |Real.log (a / b)| := abs_nonneg _
    have hu_pos : 0 < u := by
      dsimp [u]
      linarith
    have hu_abs : |u| = u := abs_of_pos hu_pos
    have hLtu : |Real.log (a / b)| < u := by
      dsimp [u]
      linarith
    have hule : |u| ≤ c := by
      rw [hu_abs]
      dsimp [u]
      linarith
    have hucond : 0 < |u| ∧ |u| ≤ c := by
      constructor
      · simpa [hu_abs] using hu_pos
      · exact hule
    have hineq := hc u hucond (1 / 2 : ℝ) (by
      constructor <;> norm_num)
    have hfail := putnam_1991_b6_midpoint_fails a b u abpos.1 abpos.2 hu_pos hLtu
    linarith
