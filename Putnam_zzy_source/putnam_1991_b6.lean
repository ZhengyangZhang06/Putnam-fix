import Mathlib

open Filter Topology

noncomputable abbrev putnam_1991_b6_solution : ℝ → ℝ → ℝ :=
  fun a b ↦ if a < b then Real.log (b / a) else Real.log (a / b)

lemma putnam_1991_b6_geom_eq_exp_log_div (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ x * b ^ (1 - x) = b * Real.exp ((Real.log (a / b)) * x) := by
  calc
    a ^ x * b ^ (1 - x)
        = Real.exp (Real.log a * x + Real.log b * (1 - x)) := by
          rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.exp_add]
    _ = Real.exp (Real.log b + Real.log (a / b) * x) := by
          congr 1
          rw [Real.log_div ha.ne' hb.ne']
          ring
    _ = Real.exp (Real.log b) * Real.exp (Real.log (a / b) * x) := by
          rw [Real.exp_add]
    _ = b * Real.exp (Real.log (a / b) * x) := by
          rw [Real.exp_log hb]

lemma putnam_1991_b6_sinh_le_mul_cosh_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have hmono : MonotoneOn (fun y : ℝ ↦ y * Real.cosh y - Real.sinh y) (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?cont ?diff ?deriv
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro y hy
      exact ((differentiableAt_id.fun_mul Real.differentiableAt_cosh).sub
        Real.differentiableAt_sinh).differentiableWithinAt
    · intro y hy
      have hypos : 0 < y := by simpa [interior_Ici] using hy
      have hder : deriv (fun y : ℝ ↦ y * Real.cosh y - Real.sinh y) y = y * Real.sinh y := by
        rw [deriv_fun_sub]
        · rw [deriv_fun_mul]
          · rw [Real.deriv_cosh, Real.deriv_sinh, deriv_id'']
            ring_nf
          · exact differentiableAt_id
          · exact Real.differentiableAt_cosh
        · exact differentiableAt_id.fun_mul Real.differentiableAt_cosh
        · exact Real.differentiableAt_sinh
      rw [hder]
      exact mul_nonneg (le_of_lt hypos) (by
        simpa using (Real.sinh_nonneg_iff.mpr (le_of_lt hypos)))
  have hle := hmono (by simp) hx hx
  simpa using hle

lemma putnam_1991_b6_sinh_div_self_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.sinh x / x ≤ Real.sinh y / y := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hmono : MonotoneOn (fun z : ℝ ↦ Real.sinh z / z) (Set.Ioi (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ)) ?cont ?diff ?deriv
    · intro z hz
      exact (Real.continuous_sinh.continuousAt.div continuousAt_id hz.ne').continuousWithinAt
    · intro z hz
      have hzpos : 0 < z := by simpa [interior_Ioi] using hz
      exact (Real.differentiableAt_sinh.div differentiableAt_id hzpos.ne').differentiableWithinAt
    · intro z hz
      have hzpos : 0 < z := by simpa [interior_Ioi] using hz
      have hder : deriv (fun z : ℝ ↦ Real.sinh z / z) z =
          (z * Real.cosh z - Real.sinh z) / z ^ 2 := by
        rw [deriv_fun_div]
        · rw [Real.deriv_sinh, deriv_id'']
          ring_nf
        · exact Real.differentiableAt_sinh
        · exact differentiableAt_id
        · exact hzpos.ne'
      rw [hder]
      exact div_nonneg
        (sub_nonneg.mpr (putnam_1991_b6_sinh_le_mul_cosh_of_nonneg (le_of_lt hzpos)))
        (sq_nonneg z)
  exact hmono hx hy hxy

lemma putnam_1991_b6_t_mul_cosh_mul_sinh_le (t z : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : 0 < z) :
    t * Real.cosh (t * z) * Real.sinh z ≤ Real.sinh (t * z) * Real.cosh z := by
  have hE : 0 ≤ Real.sinh (t * z) * Real.cosh z - t * Real.cosh (t * z) * Real.sinh z := by
    have htwice :
        2 * (Real.sinh (t * z) * Real.cosh z - t * Real.cosh (t * z) * Real.sinh z)
          = (1 - t) * Real.sinh ((1 + t) * z) -
            (1 + t) * Real.sinh ((1 - t) * z) := by
      have h1 : (1 + t) * z = z + t * z := by ring
      have h2 : (1 - t) * z = z - t * z := by ring
      rw [h1, h2, Real.sinh_add, Real.sinh_sub]
      ring
    have htwice_nonneg :
        0 ≤ 2 * (Real.sinh (t * z) * Real.cosh z - t * Real.cosh (t * z) * Real.sinh z) := by
      rw [htwice]
      by_cases htlt : t < 1
      · let A : ℝ := (1 - t) * z
        let B : ℝ := (1 + t) * z
        have hApos : 0 < A := by dsimp [A]; nlinarith
        have hBpos : 0 < B := by dsimp [B]; nlinarith
        have hAB : A ≤ B := by dsimp [A, B]; nlinarith
        have hdiv := putnam_1991_b6_sinh_div_self_mono hApos hAB
        have hcross : Real.sinh A * B ≤ Real.sinh B * A :=
          (div_le_div_iff₀ hApos hBpos).mp hdiv
        have hcross' : (1 + t) * Real.sinh A ≤ (1 - t) * Real.sinh B := by
          have hzmul : ((1 + t) * Real.sinh A) * z ≤
              ((1 - t) * Real.sinh B) * z := by
            dsimp [A, B] at hcross ⊢
            nlinarith
          exact le_of_mul_le_mul_right hzmul hz
        have : 0 ≤ (1 - t) * Real.sinh B - (1 + t) * Real.sinh A :=
          sub_nonneg.mpr hcross'
        simpa [A, B] using this
      · have ht : t = 1 := by linarith
        simp [ht]
    nlinarith
  linarith

lemma putnam_1991_b6_sinh_mul_div_sinh_anti {t r R : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 0 < r) (hR : r ≤ R) :
    Real.sinh (R * t) / Real.sinh R ≤ Real.sinh (r * t) / Real.sinh r := by
  have hRpos : 0 < R := lt_of_lt_of_le hr hR
  have hanti : AntitoneOn (fun z : ℝ ↦ Real.sinh (z * t) / Real.sinh z) (Set.Ioi (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ)) ?cont ?diff ?deriv
    · intro z hz
      exact (((Real.continuous_sinh.comp (continuous_id.mul continuous_const))).continuousAt.div
        Real.continuous_sinh.continuousAt
        (by simpa [Real.sinh_ne_zero] using hz.ne')).continuousWithinAt
    · intro z hz
      have hzpos : 0 < z := by simpa [interior_Ioi] using hz
      exact (((differentiableAt_id.mul (differentiableAt_const t)).sinh).div
        Real.differentiableAt_sinh
        (by simpa [Real.sinh_ne_zero] using hzpos.ne')).differentiableWithinAt
    · intro z hz
      have hzpos : 0 < z := by simpa [interior_Ioi] using hz
      have hsinhz : Real.sinh z ≠ 0 := by simpa [Real.sinh_ne_zero] using hzpos.ne'
      have hder : deriv (fun z : ℝ ↦ Real.sinh (z * t) / Real.sinh z) z =
          (t * Real.cosh (t * z) * Real.sinh z -
            Real.sinh (t * z) * Real.cosh z) / (Real.sinh z) ^ 2 := by
        rw [deriv_fun_div]
        · simp [deriv_id'']
          ring_nf
        · exact (differentiableAt_id.mul (differentiableAt_const t)).sinh
        · exact Real.differentiableAt_sinh
        · exact hsinhz
      rw [hder]
      have hnum : t * Real.cosh (t * z) * Real.sinh z -
          Real.sinh (t * z) * Real.cosh z ≤ 0 := by
        exact sub_nonpos.mpr (putnam_1991_b6_t_mul_cosh_mul_sinh_le t z ht0 ht1 hzpos)
      exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)
  exact hanti hr hRpos hR

lemma putnam_1991_b6_sinh_ratio_abs (u t : ℝ) :
    Real.sinh (u * t) / Real.sinh u = Real.sinh (|u| * t) / Real.sinh |u| := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
  · have hult : u < 0 := lt_of_not_ge hu
    rw [abs_of_neg hult]
    have harg : -u * t = -(u * t) := by ring
    rw [harg, Real.sinh_neg, Real.sinh_neg]
    ring

lemma putnam_1991_b6_hyper_pos (d x : ℝ) (hd : d ≠ 0) :
    Real.exp d * (Real.sinh (d * x) / Real.sinh d) +
      Real.sinh (d * (1 - x)) / Real.sinh d = Real.exp (d * x) := by
  have hsd : Real.sinh d ≠ 0 := by simpa [Real.sinh_ne_zero] using hd
  field_simp [hsd]
  have harg : d * (1 - x) = d - d * x := by ring
  rw [harg, Real.sinh_sub]
  rw [← Real.sinh_add_cosh d, ← Real.sinh_add_cosh (d * x)]
  ring

lemma putnam_1991_b6_hyper_neg (d x : ℝ) (hd : d ≠ 0) :
    Real.exp (-d) * (Real.sinh (d * x) / Real.sinh d) +
      Real.sinh (d * (1 - x)) / Real.sinh d = Real.exp ((-d) * x) := by
  have h := putnam_1991_b6_hyper_pos d (1 - x) hd
  have hcomm : Real.sinh (d * x) / Real.sinh d +
      Real.exp d * (Real.sinh (d * (1 - x)) / Real.sinh d) =
      Real.exp (d * (1 - x)) := by
    convert h using 1
    ring_nf
  have hexp : Real.exp (-d) * Real.exp d = 1 := by
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero d)]
  calc
    Real.exp (-d) * (Real.sinh (d * x) / Real.sinh d) +
        Real.sinh (d * (1 - x)) / Real.sinh d
        = Real.exp (-d) * (Real.sinh (d * x) / Real.sinh d +
            Real.exp d * (Real.sinh (d * (1 - x)) / Real.sinh d)) := by
          rw [mul_add]
          rw [← mul_assoc, hexp]
          ring
    _ = Real.exp (-d) * Real.exp (d * (1 - x)) := by rw [hcomm]
    _ = Real.exp ((-d) * x) := by
          rw [← Real.exp_add]
          congr 1
          ring

lemma putnam_1991_b6_weighted_abs_log_eq_geom (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hCpos : 0 < |Real.log (a / b)|) :
    a * (Real.sinh (|Real.log (a / b)| * x) / Real.sinh |Real.log (a / b)|) +
      b * (Real.sinh (|Real.log (a / b)| * (1 - x)) /
        Real.sinh |Real.log (a / b)|) =
      a ^ x * b ^ (1 - x) := by
  let d := Real.log (a / b)
  let C := |d|
  have hdivpos : 0 < a / b := div_pos ha hb
  have haeq : a = b * Real.exp d := by
    dsimp [d]
    rw [Real.exp_log hdivpos]
    field_simp [hb.ne']
  have hgeom : a ^ x * b ^ (1 - x) = b * Real.exp (d * x) := by
    dsimp [d]
    exact putnam_1991_b6_geom_eq_exp_log_div a b x ha hb
  change a * (Real.sinh (C * x) / Real.sinh C) +
      b * (Real.sinh (C * (1 - x)) / Real.sinh C) = a ^ x * b ^ (1 - x)
  by_cases hdnonneg : 0 ≤ d
  · have hC : C = d := by simp [C, abs_of_nonneg hdnonneg]
    have hdne : d ≠ 0 := by
      intro hd0
      have : C = 0 := by simp [C, hd0]
      linarith
    calc
      a * (Real.sinh (C * x) / Real.sinh C) +
          b * (Real.sinh (C * (1 - x)) / Real.sinh C)
          = b * (Real.exp d * (Real.sinh (d * x) / Real.sinh d) +
              Real.sinh (d * (1 - x)) / Real.sinh d) := by
            rw [hC, haeq]
            ring
      _ = b * Real.exp (d * x) := by rw [putnam_1991_b6_hyper_pos d x hdne]
      _ = a ^ x * b ^ (1 - x) := by rw [hgeom]
  · have hdlt : d < 0 := lt_of_not_ge hdnonneg
    have hC : C = -d := by simp [C, abs_of_neg hdlt]
    have hCne : C ≠ 0 := by
      intro h0
      have : |Real.log (a / b)| = 0 := by simpa [d, C] using h0
      linarith
    have hdC : d = -C := by rw [hC]; ring
    calc
      a * (Real.sinh (C * x) / Real.sinh C) +
          b * (Real.sinh (C * (1 - x)) / Real.sinh C)
          = b * (Real.exp (-C) * (Real.sinh (C * x) / Real.sinh C) +
              Real.sinh (C * (1 - x)) / Real.sinh C) := by
            rw [haeq, hdC]
            ring
      _ = b * Real.exp ((-C) * x) := by rw [putnam_1991_b6_hyper_neg C x hCne]
      _ = b * Real.exp (d * x) := by
            congr 1
            rw [hdC]
      _ = a ^ x * b ^ (1 - x) := by rw [hgeom]

lemma putnam_1991_b6_sum_eq_two_geom_cosh (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a + b = 2 * (a ^ ((1 : ℝ) / 2) * b ^ (1 - (1 : ℝ) / 2)) *
      Real.cosh (|Real.log (a / b)| / 2) := by
  let d := Real.log (a / b)
  have hdivpos : 0 < a / b := div_pos ha hb
  have haeq : a = b * Real.exp d := by
    dsimp [d]
    rw [Real.exp_log hdivpos]
    field_simp [hb.ne']
  have hgeom : a ^ ((1 : ℝ) / 2) * b ^ (1 - (1 : ℝ) / 2) = b * Real.exp (d / 2) := by
    dsimp [d]
    convert putnam_1991_b6_geom_eq_exp_log_div a b ((1 : ℝ) / 2) ha hb using 2
    ring_nf
  rw [hgeom]
  change a + b = 2 * (b * Real.exp (d / 2)) * Real.cosh (|d| / 2)
  rw [haeq]
  have hcosh : Real.cosh (|d| / 2) = Real.cosh (d / 2) := by
    have habs : |d| / 2 = |d / 2| := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    rw [habs, Real.cosh_abs]
  rw [hcosh]
  rw [Real.cosh_eq]
  rw [Real.exp_neg]
  have hE : Real.exp (d / 2) ≠ 0 := Real.exp_ne_zero _
  field_simp [hE]
  ring_nf
  congr 1
  rw [sq, ← Real.exp_add]
  congr 1
  ring

lemma putnam_1991_b6_midpoint_rhs (a b u : ℝ) (hu : u ≠ 0) :
    a * (Real.sinh (u * ((1 : ℝ) / 2)) / Real.sinh u) +
      b * (Real.sinh (u * (1 - (1 : ℝ) / 2)) / Real.sinh u)
      = (a + b) / (2 * Real.cosh (u / 2)) := by
  have hhalf : u * ((1 : ℝ) / 2) = u / 2 := by ring
  have hhalf' : u * (1 - (1 : ℝ) / 2) = u / 2 := by ring
  have hu2 : u / 2 ≠ 0 := by
    intro h
    apply hu
    nlinarith
  have hsinhhalf : Real.sinh (u / 2) ≠ 0 := by simpa [Real.sinh_ne_zero] using hu2
  have hcosh : Real.cosh (u / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hsinh : Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    calc
      Real.sinh u = Real.sinh (2 * (u / 2)) := by congr 1; ring
      _ = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by rw [Real.sinh_two_mul]
  rw [hhalf, hhalf', hsinh]
  field_simp [hsinhhalf, hcosh]

lemma putnam_1991_b6_midpoint_lt_geom_of_abs_log_lt (a b u : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hCu : |Real.log (a / b)| < u) (hu : 0 < u) :
    (a + b) / (2 * Real.cosh (u / 2)) <
      a ^ ((1 : ℝ) / 2) * b ^ (1 - (1 : ℝ) / 2) := by
  let G := a ^ ((1 : ℝ) / 2) * b ^ (1 - (1 : ℝ) / 2)
  let C := |Real.log (a / b)|
  have hGpos : 0 < G := by
    dsimp [G]
    exact mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have hdenpos : 0 < 2 * Real.cosh (u / 2) := by positivity
  have hcoshlt : Real.cosh (C / 2) < Real.cosh (u / 2) := by
    rw [Real.cosh_lt_cosh]
    have hCnonneg : 0 ≤ C := by dsimp [C]; exact abs_nonneg _
    have hCu2 : C / 2 < u / 2 := by linarith
    rw [abs_of_nonneg (div_nonneg hCnonneg (by norm_num)),
      abs_of_pos (by linarith : 0 < u / 2)]
    exact hCu2
  rw [putnam_1991_b6_sum_eq_two_geom_cosh a b ha hb]
  change (2 * G * Real.cosh (C / 2)) / (2 * Real.cosh (u / 2)) < G
  rw [div_lt_iff₀ hdenpos]
  have hmul : 2 * G * Real.cosh (C / 2) < 2 * G * Real.cosh (u / 2) := by
    exact mul_lt_mul_of_pos_left hcoshlt (mul_pos (by norm_num) hGpos)
  nlinarith

/--
Let $a$ and $b$ be positive numbers. Find the largest number $c$, in terms of $a$ and $b$, such that $a^xb^{1-x} \leq a\frac{\sinh ux}{\sinh u}+b\frac{\sinh u(1-x)}{\sinh u}$ for all $u$ with $0<|u| \leq c$ and for all $x$, $0< x<1$. (Note: $\sinh u=(e^u-e^{-u})/2$.)
-/
theorem putnam_1991_b6
  (a b : ℝ)
  (abpos : a > 0 ∧ b > 0) :
  IsGreatest {c | ∀ u,
    (0 < |u| ∧ |u| ≤ c) →
    (∀ x ∈ Set.Ioo 0 1, a ^ x * b ^ (1 - x) ≤ a * (Real.sinh (u * x) / Real.sinh u) + b * (Real.sinh (u * (1 - x)) / Real.sinh u))}
  (putnam_1991_b6_solution a b) :=
by
  classical
  dsimp [putnam_1991_b6_solution]
  have hlog_solution :
      |Real.log (a / b)| =
        (if a < b then Real.log (b / a) else Real.log (a / b)) := by
    by_cases hab : a < b
    · rw [if_pos hab]
      have hleab : a ≤ b := le_of_lt hab
      have hdivab : Real.log (a / b) = Real.log a - Real.log b := by
        rw [Real.log_div abpos.1.ne' abpos.2.ne']
      have hdivba : Real.log (b / a) = Real.log b - Real.log a := by
        rw [Real.log_div abpos.2.ne' abpos.1.ne']
      rw [hdivab, hdivba]
      have hlogle : Real.log a ≤ Real.log b := Real.log_le_log abpos.1 hleab
      have hle : Real.log a - Real.log b ≤ 0 := by linarith
      rw [abs_of_nonpos hle]
      ring
    · rw [if_neg hab]
      have hba : b ≤ a := le_of_not_gt hab
      have hdivab : Real.log (a / b) = Real.log a - Real.log b := by
        rw [Real.log_div abpos.1.ne' abpos.2.ne']
      rw [hdivab]
      have hlogle : Real.log b ≤ Real.log a := Real.log_le_log abpos.2 hba
      have hle : 0 ≤ Real.log a - Real.log b := by linarith
      rw [abs_of_nonneg hle]
  constructor
  · intro u hu x hx
    let C := |Real.log (a / b)|
    let v := |u|
    have ha : 0 < a := abpos.1
    have hb : 0 < b := abpos.2
    have hCpos : 0 < C := by
      change 0 < |Real.log (a / b)|
      rw [hlog_solution]
      exact lt_of_lt_of_le hu.1 hu.2
    have hv_le_C : v ≤ C := by
      change |u| ≤ |Real.log (a / b)|
      rw [hlog_solution]
      exact hu.2
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hx1 : x ≤ 1 := le_of_lt hx.2
    have h1x0 : 0 ≤ 1 - x := by linarith
    have h1x1 : 1 - x ≤ 1 := by linarith
    have hratiox :
        Real.sinh (C * x) / Real.sinh C ≤ Real.sinh (v * x) / Real.sinh v :=
      putnam_1991_b6_sinh_mul_div_sinh_anti hx0 hx1 hu.1 hv_le_C
    have hratio1x :
        Real.sinh (C * (1 - x)) / Real.sinh C ≤
          Real.sinh (v * (1 - x)) / Real.sinh v :=
      putnam_1991_b6_sinh_mul_div_sinh_anti h1x0 h1x1 hu.1 hv_le_C
    have hux := putnam_1991_b6_sinh_ratio_abs u x
    have hu1x := putnam_1991_b6_sinh_ratio_abs u (1 - x)
    calc
      a ^ x * b ^ (1 - x)
          = a * (Real.sinh (C * x) / Real.sinh C) +
              b * (Real.sinh (C * (1 - x)) / Real.sinh C) := by
            change a ^ x * b ^ (1 - x) =
              a * (Real.sinh (|Real.log (a / b)| * x) /
                    Real.sinh |Real.log (a / b)|) +
                b * (Real.sinh (|Real.log (a / b)| * (1 - x)) /
                    Real.sinh |Real.log (a / b)|)
            rw [putnam_1991_b6_weighted_abs_log_eq_geom a b x ha hb hCpos]
      _ ≤ a * (Real.sinh (v * x) / Real.sinh v) +
              b * (Real.sinh (v * (1 - x)) / Real.sinh v) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hratiox ha.le)
              (mul_le_mul_of_nonneg_left hratio1x hb.le)
      _ = a * (Real.sinh (u * x) / Real.sinh u) +
              b * (Real.sinh (u * (1 - x)) / Real.sinh u) := by
            rw [← hux, ← hu1x]
  · intro c hc
    by_contra hle
    let C := |Real.log (a / b)|
    have hCc : C < c := by
      have hquot_lt :
          (if a < b then Real.log (b / a) else Real.log (a / b)) < c :=
        lt_of_not_ge hle
      change |Real.log (a / b)| < c
      rw [hlog_solution]
      exact hquot_lt
    let u := (C + c) / 2
    have hCnonneg : 0 ≤ C := by dsimp [C]; exact abs_nonneg _
    have hu_pos : 0 < u := by dsimp [u]; linarith
    have hCu : C < u := by dsimp [u]; linarith
    have hu_abs : |u| = u := abs_of_pos hu_pos
    have hu_le_c : |u| ≤ c := by rw [hu_abs]; dsimp [u]; linarith
    have hineq := hc u ⟨by simpa [hu_abs] using hu_pos, hu_le_c⟩ ((1 : ℝ) / 2)
      (by norm_num [Set.mem_Ioo])
    have hmid :
        a * (Real.sinh (u * ((1 : ℝ) / 2)) / Real.sinh u) +
          b * (Real.sinh (u * (1 - (1 : ℝ) / 2)) / Real.sinh u)
          = (a + b) / (2 * Real.cosh (u / 2)) :=
      putnam_1991_b6_midpoint_rhs a b u hu_pos.ne'
    have hle_mid :
        a ^ ((1 : ℝ) / 2) * b ^ (1 - (1 : ℝ) / 2) ≤
          (a + b) / (2 * Real.cosh (u / 2)) := by
      rw [hmid] at hineq
      exact hineq
    have hlt_mid :
        (a + b) / (2 * Real.cosh (u / 2)) <
          a ^ ((1 : ℝ) / 2) * b ^ (1 - (1 : ℝ) / 2) :=
      putnam_1991_b6_midpoint_lt_geom_of_abs_log_lt a b u abpos.1 abpos.2 (by simpa [C] using hCu) hu_pos
    exact (lt_irrefl (a ^ ((1 : ℝ) / 2) * b ^ (1 - (1 : ℝ) / 2)))
      (lt_of_le_of_lt hle_mid hlt_mid)
