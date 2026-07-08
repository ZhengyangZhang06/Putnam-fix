import Mathlib

open Topology Filter MeasureTheory Set

noncomputable abbrev putnam_2011_a3_solution : ℝ × ℝ := (((-1 : ℤ) : ℝ), 2 / Real.pi)

private noncomputable def putnamA3a : ℝ := Real.pi / 2

private noncomputable def putnamA3I (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..putnamA3a, x ^ r * Real.sin x

private noncomputable def putnamA3J (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..putnamA3a, x ^ r * Real.cos x

private lemma putnamA3a_pos : 0 < putnamA3a := by
  dsimp [putnamA3a]
  positivity

private lemma putnamA3a_nonneg : 0 ≤ putnamA3a :=
  putnamA3a_pos.le

private lemma putnamA3a_lt_pi : putnamA3a < Real.pi := by
  dsimp [putnamA3a]
  linarith [Real.pi_pos]

private lemma putnamA3_setIntegral_eq_interval (f : ℝ → ℝ) :
    (∫ x in Ioo (0 : ℝ) putnamA3a, f x) = ∫ x in (0 : ℝ)..putnamA3a, f x := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le putnamA3a_nonneg]

private lemma putnamA3I_intervalIntegrable {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => x ^ r * Real.sin x) volume (0 : ℝ) putnamA3a :=
  (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := putnamA3a) hr).mul_continuousOn
    Real.continuous_sin.continuousOn

private lemma putnamA3_rpow_sin_intervalIntegrable {r b c : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => x ^ r * Real.sin x) volume b c :=
  (intervalIntegral.intervalIntegrable_rpow' (a := b) (b := c) hr).mul_continuousOn
    Real.continuous_sin.continuousOn

private lemma putnamA3_diff_intervalIntegrable {r l b c : ℝ} (hr : -1 < r) :
    IntervalIntegrable
      (fun x : ℝ => x ^ (r + 1) * Real.sin x - l * (x ^ r * Real.sin x)) volume b c :=
  (putnamA3_rpow_sin_intervalIntegrable (b := b) (c := c) (r := r + 1) (by linarith)).sub
    ((putnamA3_rpow_sin_intervalIntegrable (b := b) (c := c) (r := r) hr).const_mul l)

private lemma putnamA3I_pos {r : ℝ} (hr : 0 ≤ r) : 0 < putnamA3I r := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (putnamA3I_intervalIntegrable (by linarith))
    ?_ putnamA3a_pos
  intro x hx
  exact mul_pos (Real.rpow_pos_of_pos hx.1 r)
    (Real.sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans putnamA3a_lt_pi))

private lemma putnamA3J_eq {r : ℝ} (hr : -1 < r) :
    putnamA3J r = putnamA3I (r + 1) / (r + 1) := by
  have hr1pos : 0 < r + 1 := by linarith
  have hr1ne : r + 1 ≠ 0 := by linarith
  have hcont_cos : ContinuousOn Real.cos (uIcc (0 : ℝ) putnamA3a) :=
    Real.continuous_cos.continuousOn
  have hcont_v :
      ContinuousOn (fun x : ℝ => x ^ (r + 1) / (r + 1)) (uIcc (0 : ℝ) putnamA3a) := by
    exact (continuousOn_id.rpow_const (p := r + 1) (s := uIcc (0 : ℝ) putnamA3a)
      (fun x hx => Or.inr hr1pos.le)).div_const (r + 1)
  have hderiv_cos :
      ∀ x ∈ Ioo (min (0 : ℝ) putnamA3a) (max (0 : ℝ) putnamA3a),
        HasDerivAt Real.cos (-Real.sin x) x := by
    intro x hx
    simpa using Real.hasDerivAt_cos x
  have hderiv_v :
      ∀ x ∈ Ioo (min (0 : ℝ) putnamA3a) (max (0 : ℝ) putnamA3a),
        HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
    intro x hx
    have hxpos : 0 < x := by
      rw [min_eq_left putnamA3a_nonneg, max_eq_right putnamA3a_nonneg] at hx
      exact hx.1
    have h :=
      (Real.hasDerivAt_rpow_const (x := x) (p := r + 1) (Or.inl hxpos.ne')).div_const
        (r + 1)
    convert h using 1
    field_simp [hr1ne]
    ring_nf
  have hInt_cos' : IntervalIntegrable (fun x : ℝ => -Real.sin x) volume (0 : ℝ) putnamA3a :=
    Real.continuous_sin.neg.continuousOn.intervalIntegrable
  have hInt_v' : IntervalIntegrable (fun x : ℝ => x ^ r) volume (0 : ℝ) putnamA3a :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := putnamA3a)
    (u := Real.cos) (v := fun x : ℝ => x ^ (r + 1) / (r + 1))
    (u' := fun x : ℝ => -Real.sin x) (v' := fun x : ℝ => x ^ r)
    hcont_cos hcont_v hderiv_cos hderiv_v hInt_cos' hInt_v'
  dsimp [putnamA3J, putnamA3I]
  calc
    ∫ x in (0 : ℝ)..putnamA3a, x ^ r * Real.cos x =
        ∫ x in (0 : ℝ)..putnamA3a, Real.cos x * x ^ r := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      ring
    _ = Real.cos putnamA3a * (putnamA3a ^ (r + 1) / (r + 1)) -
          Real.cos 0 * (0 ^ (r + 1) / (r + 1)) -
        ∫ x in (0 : ℝ)..putnamA3a, (-Real.sin x) * (x ^ (r + 1) / (r + 1)) :=
      hparts
    _ = ∫ x in (0 : ℝ)..putnamA3a, Real.sin x * (x ^ (r + 1) / (r + 1)) := by
      simp [putnamA3a, Real.cos_pi_div_two, hr1pos.ne']
    _ = ∫ x in (0 : ℝ)..putnamA3a, x ^ (r + 1) / (r + 1) * Real.sin x := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      ring
    _ = (∫ x in (0 : ℝ)..putnamA3a, x ^ (r + 1) * Real.sin x) / (r + 1) := by
      rw [← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr ?_
      intro x hx
      ring

private lemma putnamA3_avg_le {r : ℝ} (hr : 0 ≤ r) :
    putnamA3I (r + 1) / putnamA3I r ≤ putnamA3a := by
  have hpos : 0 < putnamA3I r := putnamA3I_pos hr
  rw [div_le_iff₀ hpos]
  dsimp [putnamA3I]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on_of_le_Ioo putnamA3a_nonneg
    (putnamA3I_intervalIntegrable (r := r + 1) (by linarith))
    ((putnamA3I_intervalIntegrable (r := r) (by linarith)).const_mul putnamA3a) ?_
  intro x hx
  have hxpos : 0 < x := hx.1
  have hxle : x ≤ putnamA3a := hx.2.le
  have hsin : 0 ≤ Real.sin x :=
    (Real.sin_pos_of_pos_of_lt_pi hxpos (hx.2.trans putnamA3a_lt_pi)).le
  calc
    x ^ (r + 1) * Real.sin x = (x ^ r * Real.sin x) * x := by
      rw [Real.rpow_add hxpos r 1, Real.rpow_one]
      ring
    _ ≤ (x ^ r * Real.sin x) * putnamA3a := by
      exact mul_le_mul_of_nonneg_left hxle (mul_nonneg (Real.rpow_nonneg hxpos.le r) hsin)
    _ = putnamA3a * (x ^ r * Real.sin x) := by ring

private lemma putnamA3_avg_eventually_gt (l : ℝ) (hl : l < putnamA3a) :
    ∀ᶠ r in atTop, l < putnamA3I (r + 1) / putnamA3I r := by
  by_cases hlpos : 0 < l
  · let c : ℝ := (l + putnamA3a) / 2
    have hlc : l < c := by dsimp [c]; linarith
    have hca : c < putnamA3a := by dsimp [c]; linarith
    have hcpos : 0 < c := hlpos.trans hlc
    have hKpos : 0 < (c - l) * Real.sin c := by
      exact mul_pos (sub_pos.mpr hlc)
        (Real.sin_pos_of_pos_of_lt_pi hcpos (hca.trans putnamA3a_lt_pi))
    have hq :
        Tendsto (fun r : ℝ => (c / putnamA3a) ^ (r + 1)) atTop (𝓝 0) := by
      have hbase := tendsto_rpow_atTop_of_base_lt_one (c / putnamA3a)
        (by have : 0 < c / putnamA3a := div_pos hcpos putnamA3a_pos; linarith)
        ((div_lt_one putnamA3a_pos).2 hca)
      exact hbase.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    have hp :
        Tendsto (fun r : ℝ => (l / putnamA3a) ^ (r + 1)) atTop (𝓝 0) := by
      have hbase := tendsto_rpow_atTop_of_base_lt_one (l / putnamA3a)
        (by have : 0 < l / putnamA3a := div_pos hlpos putnamA3a_pos; linarith)
        ((div_lt_one putnamA3a_pos).2 hl)
      exact hbase.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    have hD :
        Tendsto
          (fun r : ℝ =>
            (c - l) * Real.sin c * (1 - (c / putnamA3a) ^ (r + 1)) -
              l * (l / putnamA3a) ^ (r + 1))
          atTop (𝓝 ((c - l) * Real.sin c)) := by
      have h1 : Tendsto (fun r : ℝ => 1 - (c / putnamA3a) ^ (r + 1)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub hq
      have h2 :
          Tendsto
            (fun r : ℝ => (c - l) * Real.sin c * (1 - (c / putnamA3a) ^ (r + 1)))
            atTop (𝓝 ((c - l) * Real.sin c * (1 - 0))) :=
        tendsto_const_nhds.mul h1
      have h3 :
          Tendsto (fun r : ℝ => l * (l / putnamA3a) ^ (r + 1)) atTop (𝓝 (l * 0)) :=
        tendsto_const_nhds.mul hp
      simpa using h2.sub h3
    have hDpos :
        ∀ᶠ (r : ℝ) in atTop,
          0 <
            (c - l) * Real.sin c * (1 - (c / putnamA3a) ^ (r + 1)) -
              l * (l / putnamA3a) ^ (r + 1) :=
      hD.eventually (Ioi_mem_nhds hKpos)
    filter_upwards [eventually_ge_atTop (0 : ℝ), hDpos] with r hr hDr
    have hden : 0 < putnamA3I r := putnamA3I_pos hr
    refine (lt_div_iff₀ hden).2 ?_
    rw [← sub_pos]
    have hr1pos : 0 < r + 1 := by linarith
    let f : ℝ → ℝ := fun x => x ^ (r + 1) * Real.sin x - l * (x ^ r * Real.sin x)
    have hf0l : IntervalIntegrable f volume (0 : ℝ) l :=
      putnamA3_diff_intervalIntegrable (r := r) (l := l) (b := (0 : ℝ)) (c := l) (by linarith)
    have hflc : IntervalIntegrable f volume l c :=
      putnamA3_diff_intervalIntegrable (r := r) (l := l) (b := l) (c := c) (by linarith)
    have hf0c : IntervalIntegrable f volume (0 : ℝ) c :=
      putnamA3_diff_intervalIntegrable (r := r) (l := l) (b := (0 : ℝ)) (c := c) (by linarith)
    have hfca : IntervalIntegrable f volume c putnamA3a :=
      putnamA3_diff_intervalIntegrable (r := r) (l := l) (b := c) (c := putnamA3a) (by linarith)
    have hdiff_eq : putnamA3I (r + 1) - l * putnamA3I r =
        ∫ x in (0 : ℝ)..putnamA3a, f x := by
      dsimp [putnamA3I, f]
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_sub
        (putnamA3I_intervalIntegrable (r := r + 1) (by linarith))
        ((putnamA3I_intervalIntegrable (r := r) (by linarith)).const_mul l)]
    have hsplit :
        ∫ x in (0 : ℝ)..putnamA3a, f x =
          (∫ x in (0 : ℝ)..l, f x) + (∫ x in l..c, f x) +
            (∫ x in c..putnamA3a, f x) := by
      have h0c := intervalIntegral.integral_add_adjacent_intervals hf0l hflc
      have h0a := intervalIntegral.integral_add_adjacent_intervals hf0c hfca
      calc
        ∫ x in (0 : ℝ)..putnamA3a, f x =
            (∫ x in (0 : ℝ)..c, f x) + ∫ x in c..putnamA3a, f x := by
          rw [h0a]
        _ = (∫ x in (0 : ℝ)..l, f x) + (∫ x in l..c, f x) +
            (∫ x in c..putnamA3a, f x) := by
          rw [h0c]
    have h0 :
        (-l) * (∫ x in (0 : ℝ)..l, x ^ r) ≤ ∫ x in (0 : ℝ)..l, f x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on_of_le_Ioo hlpos.le
        ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := l) (r := r)
          (by linarith)).const_mul (-l)) hf0l ?_
      intro x hx
      have hxpos : 0 < x := hx.1
      have hxrp : 0 ≤ x ^ r := Real.rpow_nonneg hxpos.le r
      have hsin_nonneg : 0 ≤ Real.sin x :=
        (Real.sin_pos_of_pos_of_lt_pi hxpos ((hx.2.trans hl).trans putnamA3a_lt_pi)).le
      have hsin_le : Real.sin x ≤ 1 := Real.sin_le_one x
      have hsub : x - l ≤ 0 := by linarith [hx.2]
      have hA_nonpos : x ^ r * (x - l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hxrp hsub
      have hA_le :
          x ^ r * (x - l) ≤ (x ^ r * (x - l)) * Real.sin x := by
        have := mul_le_mul_of_nonpos_left hsin_le hA_nonpos
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      calc
        (-l) * x ^ r = x ^ r * (-l) := by ring
        _ ≤ x ^ r * (x - l) := by
          exact mul_le_mul_of_nonneg_left (by linarith : -l ≤ x - l) hxrp
        _ ≤ (x ^ r * (x - l)) * Real.sin x := hA_le
        _ = f x := by
          dsimp [f]
          rw [Real.rpow_add hxpos r 1, Real.rpow_one]
          ring
    have hmid : 0 ≤ ∫ x in l..c, f x := by
      refine intervalIntegral.integral_nonneg hlc.le ?_
      intro x hx
      have hxpos : 0 < x := hlpos.trans_le hx.1
      have hxsub : 0 ≤ x - l := sub_nonneg.mpr hx.1
      have hsin : 0 ≤ Real.sin x :=
        (Real.sin_pos_of_pos_of_lt_pi hxpos ((hx.2.trans hca.le).trans_lt putnamA3a_lt_pi)).le
      dsimp [f]
      rw [Real.rpow_add hxpos r 1, Real.rpow_one]
      calc
        0 ≤ x ^ r * ((x - l) * Real.sin x) :=
          mul_nonneg (Real.rpow_nonneg hxpos.le r) (mul_nonneg hxsub hsin)
        _ = x ^ r * x * Real.sin x - l * (x ^ r * Real.sin x) := by ring
    have htail :
        ((c - l) * Real.sin c) * (∫ x in c..putnamA3a, x ^ r) ≤
          ∫ x in c..putnamA3a, f x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on_of_le_Ioo hca.le
        ((intervalIntegral.intervalIntegrable_rpow' (a := c) (b := putnamA3a) (r := r)
          (by linarith)).const_mul ((c - l) * Real.sin c)) hfca ?_
      intro x hx
      have hxpos : 0 < x := hcpos.trans hx.1
      have hxrp : 0 ≤ x ^ r := Real.rpow_nonneg hxpos.le r
      have hsin_c_nonneg : 0 ≤ Real.sin c :=
        (Real.sin_pos_of_pos_of_lt_pi hcpos (hca.trans putnamA3a_lt_pi)).le
      have hsin_le : Real.sin c ≤ Real.sin x :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by
          simpa [putnamA3a] using hx.2.le) hx.1.le
      have hprod : (c - l) * Real.sin c ≤ (x - l) * Real.sin x := by
        refine mul_le_mul (by linarith [hx.1.le]) hsin_le hsin_c_nonneg
          (by linarith [hlc, hx.1.le])
      calc
        ((c - l) * Real.sin c) * x ^ r ≤ ((x - l) * Real.sin x) * x ^ r := by
          exact mul_le_mul_of_nonneg_right hprod hxrp
        _ = f x := by
          dsimp [f]
          rw [Real.rpow_add hxpos r 1, Real.rpow_one]
          ring
    have hLowerPos :
        0 <
          (-l) * (∫ x in (0 : ℝ)..l, x ^ r) +
            ((c - l) * Real.sin c) * (∫ x in c..putnamA3a, x ^ r) := by
      have hfactor : 0 < putnamA3a ^ (r + 1) / (r + 1) :=
        div_pos (Real.rpow_pos_of_pos putnamA3a_pos _) hr1pos
      rw [integral_rpow (a := (0 : ℝ)) (b := l) (r := r) (Or.inl (by linarith)),
        integral_rpow (a := c) (b := putnamA3a) (r := r) (Or.inl (by linarith))]
      rw [Real.zero_rpow hr1pos.ne']
      convert mul_pos hfactor hDr using 1
      rw [Real.div_rpow hcpos.le putnamA3a_pos.le, Real.div_rpow hlpos.le putnamA3a_pos.le]
      have haposr : 0 < putnamA3a ^ (r + 1) := Real.rpow_pos_of_pos putnamA3a_pos _
      field_simp [hr1pos.ne', haposr.ne']
      ring
    rw [hdiff_eq, hsplit]
    linarith
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    have hnum : 0 < putnamA3I (r + 1) := putnamA3I_pos (by linarith)
    have hden : 0 < putnamA3I r := putnamA3I_pos hr
    exact lt_of_le_of_lt (le_of_not_gt hlpos) (div_pos hnum hden)

private lemma putnamA3_avg_tendsto :
    Tendsto (fun r : ℝ => putnamA3I (r + 1) / putnamA3I r) atTop (𝓝 putnamA3a) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    exact putnamA3_avg_eventually_gt l hl
  · intro u hu
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact lt_of_le_of_lt (putnamA3_avg_le hr) hu

/--
Find a real number $c$ and a positive number $L$ for which $\lim_{r \to \infty} \frac{r^c \int_0^{\pi/2} x^r\sin x\,dx}{\int_0^{\pi/2} x^r\cos x\,dx}=L$.
-/
theorem putnam_2011_a3
: putnam_2011_a3_solution.2 > 0 ∧ Tendsto (fun r : ℝ => (r ^ putnam_2011_a3_solution.1 * ∫ x in Set.Ioo 0 (Real.pi / 2), x ^ r * Real.sin x) / (∫ x in Set.Ioo 0 (Real.pi / 2), x ^ r * Real.cos x)) atTop (𝓝 putnam_2011_a3_solution.2) :=
by
  constructor
  · dsimp [putnam_2011_a3_solution]
    positivity
  · have hfactor : Tendsto (fun r : ℝ => (r + 1) / r) atTop (𝓝 1) := by
      have h :
          Tendsto (fun r : ℝ => 1 + r⁻¹) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_inv_atTop_zero
      simpa using h.congr' (by
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
        field_simp [hr])
    have hinv_avg :
        Tendsto (fun r : ℝ => putnamA3I r / putnamA3I (r + 1)) atTop (𝓝 putnamA3a⁻¹) := by
      have h := putnamA3_avg_tendsto.inv₀ putnamA3a_pos.ne'
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      have h0 : putnamA3I r ≠ 0 := (putnamA3I_pos hr).ne'
      have h1 : putnamA3I (r + 1) ≠ 0 := (putnamA3I_pos (by linarith)).ne'
      field_simp [h0, h1]
    have hprod :
        Tendsto
          (fun r : ℝ => ((r + 1) / r) * (putnamA3I r / putnamA3I (r + 1)))
          atTop (𝓝 putnamA3a⁻¹) := by
      simpa using hfactor.mul hinv_avg
    have hinterval :
        Tendsto (fun r : ℝ => (r ^ (-1 : ℝ) * putnamA3I r) / putnamA3J r)
          atTop (𝓝 putnamA3a⁻¹) := by
      refine hprod.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      have hrpos : 0 < r := by linarith
      have hrne : r ≠ 0 := hrpos.ne'
      have hr1ne : r + 1 ≠ 0 := by linarith
      have hI1 : putnamA3I (r + 1) ≠ 0 := (putnamA3I_pos (by linarith)).ne'
      rw [putnamA3J_eq (r := r) (by linarith), Real.rpow_neg_one]
      field_simp [hrne, hr1ne, hI1]
    have hinterval' :
        Tendsto
          (fun r : ℝ =>
            (r ^ (-1 : ℝ) * ∫ x in (0 : ℝ)..(Real.pi / 2), x ^ r * Real.sin x) /
              (∫ x in (0 : ℝ)..(Real.pi / 2), x ^ r * Real.cos x))
          atTop (𝓝 putnamA3a⁻¹) := by
      simpa [putnamA3I, putnamA3J, putnamA3a] using hinterval
    have hset :
        Tendsto
          (fun r : ℝ =>
            (r ^ (-1 : ℝ) * ∫ x in Ioo (0 : ℝ) (Real.pi / 2), x ^ r * Real.sin x) /
              (∫ x in Ioo (0 : ℝ) (Real.pi / 2), x ^ r * Real.cos x))
          atTop (𝓝 putnamA3a⁻¹) := by
      refine hinterval'.congr' ?_
      filter_upwards with r
      change
        (r ^ (-1 : ℝ) * ∫ x in (0 : ℝ)..putnamA3a, x ^ r * Real.sin x) /
            (∫ x in (0 : ℝ)..putnamA3a, x ^ r * Real.cos x) =
          (r ^ (-1 : ℝ) * ∫ x in Ioo (0 : ℝ) putnamA3a, x ^ r * Real.sin x) /
            (∫ x in Ioo (0 : ℝ) putnamA3a, x ^ r * Real.cos x)
      rw [putnamA3_setIntegral_eq_interval, putnamA3_setIntegral_eq_interval]
    have htarget : putnamA3a⁻¹ = 2 / Real.pi := by
      dsimp [putnamA3a]
      field_simp [Real.pi_ne_zero]
    simpa [putnam_2011_a3_solution, htarget] using hset
