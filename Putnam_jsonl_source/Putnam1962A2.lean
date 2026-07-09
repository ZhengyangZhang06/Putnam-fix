import Mathlib

open MeasureTheory Set

private lemma putnam_1962_a2_integral_rat (a c x : ℝ) (hx : 0 < x)
    (hden : ∀ t ∈ Icc (0 : ℝ) x, 1 - c * t ≠ 0) :
    ∫ t in (0 : ℝ)..x, a / (1 - c * t) ^ 2 = a * x / (1 - c * x) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun u : ℝ => a * u / (1 - c * u)) (a / (1 - c * t) ^ 2) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx.le] using ht
    have h : 1 - c * t ≠ 0 := hden t ht'
    convert (((hasDerivAt_const t a).mul (hasDerivAt_id t)).div
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_const t c).mul (hasDerivAt_id t))) h) using 1
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    field_simp [h]
    ring
  have hcont : ContinuousOn (fun t : ℝ => a / (1 - c * t) ^ 2) (uIcc (0 : ℝ) x) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx.le] using ht
    fun_prop (disch := exact pow_ne_zero 2 (hden t ht'))
  have hint : IntervalIntegrable (fun t : ℝ => a / (1 - c * t) ^ 2) volume (0 : ℝ) x := by
    exact hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

private lemma putnam_1962_a2_average_rat (a c x : ℝ) (hx : 0 < x)
    (hden : ∀ t ∈ Icc (0 : ℝ) x, 1 - c * t ≠ 0) :
    (⨍ t in Ico (0 : ℝ) x, a / (1 - c * t) ^ 2) = a / (1 - c * x) := by
  have hset : (⨍ t in Ico (0 : ℝ) x, a / (1 - c * t) ^ 2) =
      (⨍ t in Ioc (0 : ℝ) x, a / (1 - c * t) ^ 2) := by
    exact setAverage_congr (μ := volume) (f := fun t : ℝ => a / (1 - c * t) ^ 2) Ico_ae_eq_Ioc
  rw [hset]
  rw [setAverage_eq]
  rw [Real.volume_real_Ioc_of_le hx.le]
  rw [← intervalIntegral.integral_of_le hx.le]
  rw [putnam_1962_a2_integral_rat a c x hx hden]
  rw [smul_eq_mul]
  field_simp [hx.ne']
  ring

private lemma putnam_1962_a2_sqrt_rat (a d : ℝ) (ha : 0 ≤ a) (hd : 0 < d) :
    √(a * (a / d ^ 2)) = a / d := by
  have hnon : 0 ≤ a / d := div_nonneg ha hd.le
  rw [show a * (a / d ^ 2) = (a / d) ^ 2 by field_simp [hd.ne'], Real.sqrt_sq hnon]

private lemma putnam_1962_a2_rational_P
    (P : Set ℝ → (ℝ → ℝ) → Prop)
    (P_def : ∀ s f, P s f ↔ 0 ≤ f ∧ ∀ x ∈ s, ⨍ t in Ico 0 x, f t = √(f 0 * f x))
    {a c e : ℝ} (ha : 0 ≤ a)
    (hden_pos : ∀ x ∈ Ioo (0 : ℝ) e, 0 < 1 - c * x) :
    P (Ioo 0 e) (fun x : ℝ => a / (1 - c * x) ^ 2) := by
  rw [P_def]
  constructor
  · intro x
    exact div_nonneg ha (sq_nonneg _)
  · intro x hx
    have hden : ∀ t ∈ Icc (0 : ℝ) x, 1 - c * t ≠ 0 := by
      intro t ht
      have hte : t < e := lt_of_le_of_lt ht.2 hx.2
      have hpos : 0 < 1 - c * t := by
        by_cases ht0 : t = 0
        · simp [ht0]
        · exact hden_pos t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), hte⟩
      exact hpos.ne'
    rw [putnam_1962_a2_average_rat a c x hx.1 hden]
    simpa using (putnam_1962_a2_sqrt_rat a (1 - c * x) ha (hden_pos x hx)).symm

private lemma putnam_1962_a2_cutoff_P
    (P : Set ℝ → (ℝ → ℝ) → Prop)
    (P_def : ∀ s f, P s f ↔ 0 ≤ f ∧ ∀ x ∈ s, ⨍ t in Ico 0 x, f t = √(f 0 * f x))
    {a c e : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (he_inv : e ≤ 1 / c)
    (hden_pos : ∀ x ∈ Ioo (0 : ℝ) e, 0 < 1 - c * x) :
    P (Ioo 0 e) (fun x : ℝ => if x < 1 / c then a / (1 - c * x) ^ 2 else 0) := by
  rw [P_def]
  constructor
  · intro x
    change (0 : ℝ) ≤ (if x < 1 / c then a / (1 - c * x) ^ 2 else 0)
    by_cases hx : x < 1 / c
    · rw [if_pos hx]
      exact div_nonneg ha (sq_nonneg _)
    · rw [if_neg hx]
  · intro x hx
    have hxcut : x < 1 / c := lt_of_lt_of_le hx.2 he_inv
    have hden : ∀ t ∈ Icc (0 : ℝ) x, 1 - c * t ≠ 0 := by
      intro t ht
      have hte : t < e := lt_of_le_of_lt ht.2 hx.2
      have hpos : 0 < 1 - c * t := by
        by_cases ht0 : t = 0
        · simp [ht0]
        · exact hden_pos t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), hte⟩
      exact hpos.ne'
    have havg :
        (⨍ t in Ico (0 : ℝ) x, (if t < 1 / c then a / (1 - c * t) ^ 2 else 0)) =
          (⨍ t in Ico (0 : ℝ) x, a / (1 - c * t) ^ 2) := by
      refine setAverage_congr_fun (μ := volume) (s := Ico (0 : ℝ) x) measurableSet_Ico ?_
      filter_upwards [] with t ht
      have htcut : t < 1 / c := lt_trans ht.2 hxcut
      rw [if_pos htcut]
    rw [havg, putnam_1962_a2_average_rat a c x hx.1 hden]
    have h0cut : (0 : ℝ) < 1 / c := one_div_pos.mpr hc
    have h0val : (if (0 : ℝ) < 1 / c then a / (1 - c * 0) ^ 2 else 0) = a := by
      rw [if_pos h0cut]
      ring
    have hxval : (if x < 1 / c then a / (1 - c * x) ^ 2 else 0) = a / (1 - c * x) ^ 2 := by
      rw [if_pos hxcut]
    rw [h0val, hxval]
    exact (putnam_1962_a2_sqrt_rat a (1 - c * x) ha (hden_pos x hx)).symm

private lemma putnam_1962_a2_zero_on_pos_average
    {f : ℝ → ℝ} (hfzero : ∀ x : ℝ, 0 < x → f x = 0) (x : ℝ) :
    (⨍ t in Ico (0 : ℝ) x, f t) = 0 := by
  have hcongr : (⨍ t in Ico (0 : ℝ) x, f t) = (⨍ t in Ico (0 : ℝ) x, (0 : ℝ)) := by
    refine setAverage_congr_fun (μ := volume) (s := Ico (0 : ℝ) x) measurableSet_Ico ?_
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by rw [ae_iff]; simp] with t htne htmem
    exact hfzero t (lt_of_le_of_ne htmem.1 (Ne.symm htne))
  simpa using hcongr

private lemma putnam_1962_a2_zero_on_Ioo_average
    {f : ℝ → ℝ} {x : ℝ} (hfzero : ∀ t ∈ Ioo (0 : ℝ) x, f t = 0) :
    (⨍ t in Ico (0 : ℝ) x, f t) = 0 := by
  have hcongr : (⨍ t in Ico (0 : ℝ) x, f t) = (⨍ t in Ico (0 : ℝ) x, (0 : ℝ)) := by
    refine setAverage_congr_fun (μ := volume) (s := Ico (0 : ℝ) x) measurableSet_Ico ?_
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by rw [ae_iff]; simp] with t htne htmem
    exact hfzero t ⟨lt_of_le_of_ne htmem.1 (Ne.symm htne), htmem.2⟩
  simpa using hcongr

private lemma putnam_1962_a2_zero_on_pos_P
    (P : Set ℝ → (ℝ → ℝ) → Prop)
    (P_def : ∀ s f, P s f ↔ 0 ≤ f ∧ ∀ x ∈ s, ⨍ t in Ico 0 x, f t = √(f 0 * f x))
    {f : ℝ → ℝ} (hf_nonneg : 0 ≤ f) (hfzero : ∀ x : ℝ, 0 < x → f x = 0) :
    P (Ioi 0) f := by
  rw [P_def]
  refine ⟨hf_nonneg, ?_⟩
  intro x hx
  rw [putnam_1962_a2_zero_on_pos_average hfzero x, hfzero x hx]
  simp

private lemma putnam_1962_a2_point_zero_branch_mem (a : ℝ) (ha : 0 ≤ a) :
    (fun x : ℝ => if x = 0 then a else 0) ∈
      ({f | (∃ a c : ℝ, 0 ≤ a ∧ f = (fun x : ℝ ↦ a / (1 - c * x) ^ 2)) ∨
          (∃ a c : ℝ, 0 ≤ a ∧ 0 < c ∧
            f = (fun x : ℝ ↦ if x < 1 / c then a / (1 - c * x) ^ 2 else 0)) ∨
          (0 ≤ f ∧ ∀ x : ℝ, 0 < x → f x = 0) ∨
          (∃ e : ℝ, 0 < e ∧ f 0 = 0 ∧ 0 ≤ f ∧
            ∀ x ∈ Ioo (0 : ℝ) e, (⨍ t in Ico (0 : ℝ) x, f t) = 0)} :
        Set (ℝ → ℝ)) := by
  right; right; left
  constructor
  · intro x
    by_cases hx : x = 0
    · simp [hx, ha]
    · simp [hx]
  · intro x hx
    simp [hx.ne']

private lemma putnam_1962_a2_fourth_P
    (P : Set ℝ → (ℝ → ℝ) → Prop)
    (P_def : ∀ s f, P s f ↔ 0 ≤ f ∧ ∀ x ∈ s, ⨍ t in Ico 0 x, f t = √(f 0 * f x))
    {f : ℝ → ℝ} {e : ℝ} (h0 : f 0 = 0) (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) e, (⨍ t in Ico (0 : ℝ) x, f t) = 0) :
    P (Ioo 0 e) f := by
  rw [P_def]
  refine ⟨hf_nonneg, ?_⟩
  intro x hx
  rw [havg x hx]
  simp [h0]

private lemma putnam_1962_a2_integral_eq_average {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, f t) = x * (⨍ t in Ico (0 : ℝ) x, f t) := by
  have hset : (⨍ t in Ico (0 : ℝ) x, f t) = (⨍ t in Ioc (0 : ℝ) x, f t) := by
    exact setAverage_congr (μ := volume) (f := f) Ico_ae_eq_Ioc
  rw [hset, setAverage_eq, Real.volume_real_Ioc_of_le hx.le,
    ← intervalIntegral.integral_of_le hx.le]
  simp [smul_eq_mul]
  field_simp [hx.ne']

private lemma putnam_1962_a2_f_eq_primitive_sq
    {f : ℝ → ℝ} {a b u : ℝ} (ha : 0 < a) (hub : u ∈ Ioo (0 : ℝ) b)
    (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x)) :
    f u = (∫ t in (0 : ℝ)..u, f t) ^ 2 / (a * u ^ 2) := by
  have hu : 0 < u := hub.1
  have hF : (∫ t in (0 : ℝ)..u, f t) = u * √(a * f u) := by
    rw [putnam_1962_a2_integral_eq_average (f := f) hu, havg u hub]
  have hsq : (∫ t in (0 : ℝ)..u, f t) ^ 2 = u ^ 2 * (a * f u) := by
    rw [hF]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg ha.le (hf_nonneg u))]
  have hden : a * u ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  nlinarith [hsq]

private lemma putnam_1962_a2_continuousAt_of_intervalIntegrable
    {f : ℝ → ℝ} {a b t : ℝ} (ha : 0 < a) (ht : t ∈ Ioo (0 : ℝ) b)
    (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hint : IntervalIntegrable f volume (0 : ℝ) b) :
    ContinuousAt f t := by
  let F : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, f v
  have hb0 : 0 ≤ b := le_of_lt (lt_trans ht.1 ht.2)
  have hcontFOn : ContinuousOn F (Icc (0 : ℝ) b) := by
    have hac : AbsolutelyContinuousOnInterval F (0 : ℝ) b := by
      exact hint.absolutelyContinuousOnInterval_intervalIntegral (c := (0 : ℝ))
        (by
          simpa [uIcc_of_le hb0] using
            (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb0⟩))
    simpa [F, uIcc_of_le hb0] using hac.continuousOn
  have hcontF : ContinuousAt F t := hcontFOn.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have htne : t ≠ 0 := ne_of_gt ht.1
  have hane : a ≠ 0 := ne_of_gt ha
  have hden : a * t ^ 2 ≠ 0 := mul_ne_zero hane (pow_ne_zero 2 htne)
  have hcontExpr : ContinuousAt (fun u : ℝ => F u ^ 2 / (a * u ^ 2)) t := by
    exact (hcontF.pow 2).div
      ((continuousAt_const.mul ((continuousAt_id : ContinuousAt (fun u : ℝ => u) t).pow 2)))
      hden
  have hevent : f =ᶠ[nhds t] fun u : ℝ => F u ^ 2 / (a * u ^ 2) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact putnam_1962_a2_f_eq_primitive_sq (f := f) (a := a) (b := b) ha hu
      hf_nonneg havg
  exact hcontExpr.congr_of_eventuallyEq hevent

private lemma putnam_1962_a2_primitive_hasDerivAt
    {f : ℝ → ℝ} {a b t : ℝ} (ha : 0 < a) (ht : t ∈ Ioo (0 : ℝ) b)
    (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hint : IntervalIntegrable f volume (0 : ℝ) b) :
    HasDerivAt (fun u => ∫ v in (0 : ℝ)..u, f v)
      ((∫ v in (0 : ℝ)..t, f v) ^ 2 / (a * t ^ 2)) t := by
  have hb0 : 0 ≤ b := le_of_lt (lt_trans ht.1 ht.2)
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) b := by
    refine uIcc_subset_uIcc ?_ ?_
    · simpa [uIcc_of_le hb0] using
        (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb0⟩)
    · simpa [uIcc_of_le hb0] using
        (show t ∈ Icc (0 : ℝ) b from ⟨ht.1.le, ht.2.le⟩)
  have hint0t : IntervalIntegrable f volume (0 : ℝ) t := hint.mono_set hsub
  have hcont_all : ∀ y ∈ Ioo (0 : ℝ) b, ContinuousAt f y := by
    intro y hy
    exact putnam_1962_a2_continuousAt_of_intervalIntegrable (f := f) (a := a) (b := b)
      ha hy hf_nonneg havg hint
  have hmeas : StronglyMeasurableAtFilter f (nhds t) volume := by
    exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioo (0 : ℝ) b) isOpen_Ioo
      hcont_all t ht
  have hcont : ContinuousAt f t := hcont_all t ht
  have hder := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := t)
    hint0t hmeas hcont
  convert hder using 1
  exact (putnam_1962_a2_f_eq_primitive_sq (f := f) (a := a) (b := b) ha ht
    hf_nonneg havg).symm

private lemma putnam_1962_a2_lipschitz_quad
    {a p M t : ℝ} (ha : 0 < a) (hp : 0 < p) (hpt : p ≤ t) (hM : 0 ≤ M) :
    LipschitzOnWith ⟨2 * M / (a * p ^ 2), by positivity⟩
      (fun y : ℝ => y ^ 2 / (a * t ^ 2)) (Icc (0 : ℝ) M) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq]
  have htpos : 0 < t := lt_of_lt_of_le hp hpt
  have hdenpos : 0 < a * t ^ 2 := mul_pos ha (sq_pos_of_pos htpos)
  have hpdenpos : 0 < a * p ^ 2 := mul_pos ha (sq_pos_of_pos hp)
  have hxabs : |x| ≤ M := by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have hyabs : |y| ≤ M := by
    rw [abs_of_nonneg hy.1]
    exact hy.2
  have hsum : |x + y| ≤ 2 * M := by
    calc
      |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ M + M := add_le_add hxabs hyabs
      _ = 2 * M := by ring
  have hsq : x ^ 2 / (a * t ^ 2) - y ^ 2 / (a * t ^ 2) =
      (x - y) * (x + y) / (a * t ^ 2) := by
    ring
  rw [hsq]
  have hmain : |(x - y) * (x + y) / (a * t ^ 2)| ≤
      (2 * M / (a * p ^ 2)) * |x - y| := by
    rw [abs_div, abs_of_pos hdenpos, abs_mul]
    have ht2ge : p ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hp.le htpos.le).mpr hpt
    have h_inv : 1 / (a * t ^ 2) ≤ 1 / (a * p ^ 2) := by
      refine one_div_le_one_div_of_le hpdenpos ?_
      exact mul_le_mul_of_nonneg_left ht2ge ha.le
    calc
      |x - y| * |x + y| / (a * t ^ 2) =
          |x - y| * (|x + y| * (1 / (a * t ^ 2))) := by
            field_simp [hdenpos.ne']
      _ ≤ |x - y| * ((2 * M) * (1 / (a * p ^ 2))) := by
        gcongr
      _ = (2 * M / (a * p ^ 2)) * |x - y| := by
        field_simp [hpdenpos.ne']
  simpa [NNReal.coe_mk] using hmain

private lemma putnam_1962_a2_primitive_nonneg
    {f : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Ioo (0 : ℝ) b)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x)) :
    0 ≤ ∫ t in (0 : ℝ)..x, f t := by
  rw [putnam_1962_a2_integral_eq_average (f := f) hx.1, havg x hx]
  exact mul_nonneg hx.1.le (Real.sqrt_nonneg _)

private lemma putnam_1962_a2_primitive_mono_le
    {f : ℝ → ℝ} {r t : ℝ} (htr : t ≤ r) (hf_nonneg : 0 ≤ f)
    (hint0r : IntervalIntegrable f volume (0 : ℝ) r)
    (hint0t : IntervalIntegrable f volume (0 : ℝ) t) :
    (∫ u in (0 : ℝ)..t, f u) ≤ ∫ u in (0 : ℝ)..r, f u := by
  have hdiff := intervalIntegral.integral_interval_sub_left hint0r hint0t
  have hnonneg : 0 ≤ ∫ u in t..r, f u :=
    intervalIntegral.integral_nonneg htr (fun u _ => hf_nonneg u)
  nlinarith

private lemma putnam_1962_a2_intervalIntegrable_of_ne
    {f : ℝ → ℝ} {a b x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) b)
    (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hfx : f x ≠ 0) :
    IntervalIntegrable f volume (0 : ℝ) x := by
  have hfxpos : 0 < f x := lt_of_le_of_ne (hf_nonneg x) (Ne.symm hfx)
  have hFpos : 0 < ∫ t in (0 : ℝ)..x, f t := by
    rw [putnam_1962_a2_integral_eq_average (f := f) hx.1, havg x hx]
    exact mul_pos hx.1 (Real.sqrt_pos.2 (mul_pos ha hfxpos))
  exact intervalIntegral.intervalIntegrable_of_integral_ne_zero hFpos.ne'

private lemma putnam_1962_a2_exists_ne_before
    {f : ℝ → ℝ} {a b x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) b)
    (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hfx : f x ≠ 0) :
    ∃ p : ℝ, 0 < p ∧ p < x ∧ f p ≠ 0 := by
  by_contra hnone
  have hfzero : ∀ t ∈ Ioo (0 : ℝ) x, f t = 0 := by
    intro t ht
    by_contra hft
    exact hnone ⟨t, ht.1, ht.2, hft⟩
  have havg0 := putnam_1962_a2_zero_on_Ioo_average (f := f) hfzero
  have hfxpos : 0 < f x := lt_of_le_of_ne (hf_nonneg x) (Ne.symm hfx)
  have hmain := havg x hx
  rw [havg0] at hmain
  have hsqrtpos : 0 < √(a * f x) := Real.sqrt_pos.2 (mul_pos ha hfxpos)
  nlinarith

private lemma putnam_1962_a2_exists_ne_between_right
    {f : ℝ → ℝ} {a b x y : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) b)
    (hxy : x < y) (hyb : y < b) (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hfx : f x ≠ 0) :
    ∃ z : ℝ, z ∈ Ioo x y ∧ f z ≠ 0 := by
  by_contra hnone
  let m : ℝ := (x + y) / 2
  have hxm : x < m := by dsimp [m]; linarith
  have hmy : m < y := by dsimp [m]; linarith
  have hmb : m ∈ Ioo (0 : ℝ) b := ⟨lt_trans hx.1 hxm, lt_trans hmy hyb⟩
  have hfm : f m = 0 := by
    by_contra hne
    exact hnone ⟨m, ⟨hxm, hmy⟩, hne⟩
  have hint0x : IntervalIntegrable f volume (0 : ℝ) x :=
    putnam_1962_a2_intervalIntegrable_of_ne (f := f) (a := a) (b := b)
      ha hx hf_nonneg havg hfx
  have hFx_pos : 0 < ∫ t in (0 : ℝ)..x, f t := by
    rw [putnam_1962_a2_integral_eq_average (f := f) hx.1, havg x hx]
    have hfxpos : 0 < f x := lt_of_le_of_ne (hf_nonneg x) (Ne.symm hfx)
    exact mul_pos hx.1 (Real.sqrt_pos.2 (mul_pos ha hfxpos))
  have hzero_on : EqOn f (fun _ : ℝ => 0) (uIoc x m) := by
    intro t ht
    have ht' : t ∈ Ioc x m := by simpa [uIoc_of_le hxm.le] using ht
    by_contra hne
    exact hnone ⟨t, ⟨ht'.1, lt_of_le_of_lt ht'.2 hmy⟩, hne⟩
  have hintxm : IntervalIntegrable f volume x m := by
    exact (IntervalIntegrable.congr hzero_on.symm) (intervalIntegrable_const (c := (0 : ℝ)))
  have hint0m : IntervalIntegrable f volume (0 : ℝ) m := hint0x.trans hintxm
  have hIntxm : ∫ t in x..m, f t = 0 := by
    have hae : ∀ᵐ t ∂volume, t ∈ uIoc x m → f t = (fun _ : ℝ => 0) t :=
      ae_of_all volume hzero_on
    rw [intervalIntegral.integral_congr_ae hae]
    exact intervalIntegral.integral_zero
  have hsub := intervalIntegral.integral_interval_sub_left hint0m hint0x
  have hFm_eq : (∫ t in (0 : ℝ)..m, f t) = ∫ t in (0 : ℝ)..x, f t := by
    nlinarith
  have hFm_zero : (∫ t in (0 : ℝ)..m, f t) = 0 := by
    rw [putnam_1962_a2_integral_eq_average (f := f) hmb.1, havg m hmb, hfm]
    simp
  nlinarith

private lemma putnam_1962_a2_primitive_pos_of_exists_ne
    {f : ℝ → ℝ} {a b p : ℝ} (ha : 0 < a) (hp : p ∈ Ioo (0 : ℝ) b)
    (hfp : f p ≠ 0) (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hint : IntervalIntegrable f volume (0 : ℝ) b) :
    ∀ x ∈ Ioo (0 : ℝ) b, 0 < ∫ t in (0 : ℝ)..x, f t := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
  have hFp_pos : 0 < F p := by
    change 0 < ∫ t in (0 : ℝ)..p, f t
    rw [putnam_1962_a2_integral_eq_average (f := f) hp.1, havg p hp]
    have hfppos : 0 < f p := lt_of_le_of_ne (hf_nonneg p) (Ne.symm hfp)
    exact mul_pos hp.1 (Real.sqrt_pos.2 (mul_pos ha hfppos))
  intro x hx
  by_cases hpx : p ≤ x
  · have hb0 : 0 ≤ b := le_of_lt (lt_trans hx.1 hx.2)
    have hsubx : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) b := by
      refine uIcc_subset_uIcc ?_ ?_
      · simpa [uIcc_of_le hb0] using
          (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb0⟩)
      · simpa [uIcc_of_le hb0] using
          (show x ∈ Icc (0 : ℝ) b from ⟨hx.1.le, hx.2.le⟩)
    have hsubp : uIcc (0 : ℝ) p ⊆ uIcc (0 : ℝ) b := by
      refine uIcc_subset_uIcc ?_ ?_
      · simpa [uIcc_of_le hb0] using
          (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb0⟩)
      · simpa [uIcc_of_le hb0] using
          (show p ∈ Icc (0 : ℝ) b from ⟨hp.1.le, hp.2.le⟩)
    have hmono := putnam_1962_a2_primitive_mono_le (f := f) (r := x) (t := p) hpx
      hf_nonneg (hint.mono_set hsubx) (hint.mono_set hsubp)
    exact lt_of_lt_of_le hFp_pos hmono
  · have hxp : x < p := lt_of_not_ge hpx
    have hFx_nonneg : 0 ≤ F x := by
      exact putnam_1962_a2_primitive_nonneg (f := f) (a := a) (b := b) hx havg
    by_contra hxnot
    have hFx : F x = 0 := le_antisymm (le_of_not_gt hxnot) hFx_nonneg
    have hFp_nonneg : 0 ≤ F p := hFp_pos.le
    have hderivF : ∀ y ∈ Icc x p,
        HasDerivAt F (F y ^ 2 / (a * y ^ 2)) y := by
      intro y hy
      have hyb : y ∈ Ioo (0 : ℝ) b :=
        ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hp.2⟩
      simpa [F] using putnam_1962_a2_primitive_hasDerivAt (f := f) (a := a) (b := b)
        ha hyb hf_nonneg havg hint
    have hcontF : ContinuousOn F (Icc x p) := HasDerivAt.continuousOn hderivF
    have hderivZ : ∀ y ∈ Ico x p,
        HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
          (((0 : ℝ) ^ 2) / (a * y ^ 2)) (Ici y) y := by
      intro y hy
      simpa using (hasDerivAt_const y (0 : ℝ)).hasDerivWithinAt (s := Ici y)
    have hmemF : ∀ y ∈ Ico x p, F y ∈ Icc (0 : ℝ) (F p) := by
      intro y hy
      have hyb : y ∈ Ioo (0 : ℝ) b :=
        ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2.le hp.2⟩
      have hb0 : 0 ≤ b := le_of_lt (lt_trans hyb.1 hyb.2)
      have hsuby : uIcc (0 : ℝ) y ⊆ uIcc (0 : ℝ) b := by
        refine uIcc_subset_uIcc ?_ ?_
        · simpa [uIcc_of_le hb0] using
            (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb0⟩)
        · simpa [uIcc_of_le hb0] using
            (show y ∈ Icc (0 : ℝ) b from ⟨hyb.1.le, hyb.2.le⟩)
      have hsubp : uIcc (0 : ℝ) p ⊆ uIcc (0 : ℝ) b := by
        refine uIcc_subset_uIcc ?_ ?_
        · simpa [uIcc_of_le hb0] using
            (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb0⟩)
        · simpa [uIcc_of_le hb0] using
            (show p ∈ Icc (0 : ℝ) b from ⟨hp.1.le, hp.2.le⟩)
      refine ⟨putnam_1962_a2_primitive_nonneg (f := f) (a := a) (b := b) hyb havg, ?_⟩
      exact putnam_1962_a2_primitive_mono_le (f := f) (r := p) (t := y) hy.2.le
        hf_nonneg (hint.mono_set hsubp) (hint.mono_set hsuby)
    have hmemZ : ∀ y ∈ Ico x p, (fun _ : ℝ => (0 : ℝ)) y ∈ Icc (0 : ℝ) (F p) := by
      intro y hy
      exact ⟨le_rfl, hFp_nonneg⟩
    have hv : ∀ y ∈ Ico x p,
        LipschitzOnWith ⟨2 * F p / (a * x ^ 2), by positivity⟩
          (fun z : ℝ => z ^ 2 / (a * y ^ 2)) (Icc (0 : ℝ) (F p)) := by
      intro y hy
      exact putnam_1962_a2_lipschitz_quad (a := a) (p := x) (M := F p) (t := y)
        ha hx.1 hy.1 hFp_nonneg
    have heqOn := ODE_solution_unique_of_mem_Icc_right
      (v := fun y z : ℝ => z ^ 2 / (a * y ^ 2))
      (s := fun _ : ℝ => Icc (0 : ℝ) (F p))
      (K := ⟨2 * F p / (a * x ^ 2), by positivity⟩)
      hv hcontF
      (fun y hy => (hderivF y (Ico_subset_Icc_self hy)).hasDerivWithinAt)
      hmemF continuousOn_const hderivZ hmemZ hFx
    have hpzero : F p = 0 := heqOn ⟨hxp.le, le_rfl⟩
    exact hFp_pos.ne' hpzero

private lemma putnam_1962_a2_integrable_classification
    {f : ℝ → ℝ} {a b p : ℝ} (ha : 0 < a) (hp : p ∈ Ioo (0 : ℝ) b)
    (hfp : f p ≠ 0) (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hint : IntervalIntegrable f volume (0 : ℝ) b) :
    ∃ c : ℝ,
      (∀ x ∈ Ioo (0 : ℝ) b, 0 < 1 - c * x) ∧
      ∀ x ∈ Ioo (0 : ℝ) b, f x = a / (1 - c * x) ^ 2 := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
  have hFpos : ∀ x ∈ Ioo (0 : ℝ) b, 0 < F x :=
    putnam_1962_a2_primitive_pos_of_exists_ne (f := f) (a := a) (b := b) (p := p)
      ha hp hfp hf_nonneg havg hint
  let c : ℝ := a * ((a * p)⁻¹ - (F p)⁻¹)
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    have hderivF : ∀ y ∈ Ioo (0 : ℝ) b,
        HasDerivAt F (F y ^ 2 / (a * y ^ 2)) y := by
      intro y hy
      simpa [F] using putnam_1962_a2_primitive_hasDerivAt (f := f) (a := a) (b := b)
        ha hy hf_nonneg havg hint
    let Q : ℝ → ℝ := fun y => (F y)⁻¹ - (a * y)⁻¹
    have hQderivAt : ∀ y ∈ Ioo (0 : ℝ) b, HasDerivAt Q 0 y := by
      intro y hy
      have hFy : F y ≠ 0 := ne_of_gt (hFpos y hy)
      have hay : a * y ≠ 0 := mul_ne_zero ha.ne' (ne_of_gt hy.1)
      have h1 := (hderivF y hy).inv hFy
      have h2 := ((hasDerivAt_const y a).mul (hasDerivAt_id y)).inv hay
      have hsub := h1.sub h2
      convert hsub using 1
      · simp
        field_simp [ha.ne', (ne_of_gt hy.1), hFy]
        ring
    have hQdiff : DifferentiableOn ℝ Q (Ioo (0 : ℝ) b) := by
      intro y hy
      exact (hQderivAt y hy).differentiableAt.differentiableWithinAt
    have hQderiv : EqOn (deriv Q) 0 (Ioo (0 : ℝ) b) := by
      intro y hy
      exact (hQderivAt y hy).deriv
    have hQeq : Q x = Q p :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hQdiff hQderiv hx hp
    have hcp : Q p = -c / a := by
      simp [Q, c]
      field_simp [ha.ne']
      ring
    have hrec : (F x)⁻¹ - (a * x)⁻¹ = -c / a := by
      simpa [Q] using hQeq.trans hcp
    have hdeneq : 1 - c * x = a * x / F x := by
      have hane : a ≠ 0 := ne_of_gt ha
      have hxne : x ≠ 0 := ne_of_gt hx.1
      have hFxne : F x ≠ 0 := ne_of_gt (hFpos x hx)
      field_simp [hane, hxne, hFxne] at hrec ⊢
      nlinarith
    rw [hdeneq]
    exact div_pos (mul_pos ha hx.1) (hFpos x hx)
  · intro x hx
    have hderivF : ∀ y ∈ Ioo (0 : ℝ) b,
        HasDerivAt F (F y ^ 2 / (a * y ^ 2)) y := by
      intro y hy
      simpa [F] using putnam_1962_a2_primitive_hasDerivAt (f := f) (a := a) (b := b)
        ha hy hf_nonneg havg hint
    let Q : ℝ → ℝ := fun y => (F y)⁻¹ - (a * y)⁻¹
    have hQderivAt : ∀ y ∈ Ioo (0 : ℝ) b, HasDerivAt Q 0 y := by
      intro y hy
      have hFy : F y ≠ 0 := ne_of_gt (hFpos y hy)
      have hay : a * y ≠ 0 := mul_ne_zero ha.ne' (ne_of_gt hy.1)
      have h1 := (hderivF y hy).inv hFy
      have h2 := ((hasDerivAt_const y a).mul (hasDerivAt_id y)).inv hay
      have hsub := h1.sub h2
      convert hsub using 1
      · simp
        field_simp [ha.ne', (ne_of_gt hy.1), hFy]
        ring
    have hQdiff : DifferentiableOn ℝ Q (Ioo (0 : ℝ) b) := by
      intro y hy
      exact (hQderivAt y hy).differentiableAt.differentiableWithinAt
    have hQderiv : EqOn (deriv Q) 0 (Ioo (0 : ℝ) b) := by
      intro y hy
      exact (hQderivAt y hy).deriv
    have hQeq : Q x = Q p :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hQdiff hQderiv hx hp
    have hcp : Q p = -c / a := by
      simp [Q, c]
      field_simp [ha.ne']
      ring
    have hrec : (F x)⁻¹ - (a * x)⁻¹ = -c / a := by
      simpa [Q] using hQeq.trans hcp
    have hF_eq : F x = a * x / (1 - c * x) := by
      have hdeneq : 1 - c * x = a * x / F x := by
        have hane : a ≠ 0 := ne_of_gt ha
        have hxne : x ≠ 0 := ne_of_gt hx.1
        have hFxne : F x ≠ 0 := ne_of_gt (hFpos x hx)
        field_simp [hane, hxne, hFxne] at hrec ⊢
        nlinarith
      rw [hdeneq]
      field_simp [ne_of_gt (hFpos x hx), ha.ne', (ne_of_gt hx.1)]
    have hf_eq := putnam_1962_a2_f_eq_primitive_sq (f := f) (a := a) (b := b)
      ha hx hf_nonneg havg
    rw [hf_eq]
    change F x ^ 2 / (a * x ^ 2) = a / (1 - c * x) ^ 2
    rw [hF_eq]
    field_simp [ha.ne', (ne_of_gt hx.1)]

private lemma putnam_1962_a2_integrable_classification_explicit
    {f : ℝ → ℝ} {a b p : ℝ} (ha : 0 < a) (hp : p ∈ Ioo (0 : ℝ) b)
    (hfp : f p ≠ 0) (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hint : IntervalIntegrable f volume (0 : ℝ) b) :
    let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
    let c : ℝ := a * ((a * p)⁻¹ - (F p)⁻¹)
    (∀ x ∈ Ioo (0 : ℝ) b, 0 < 1 - c * x) ∧
      ∀ x ∈ Ioo (0 : ℝ) b, f x = a / (1 - c * x) ^ 2 := by
  intro F c
  have hFpos : 0 < F p := by
    change 0 < ∫ t in (0 : ℝ)..p, f t
    rw [putnam_1962_a2_integral_eq_average (f := f) hp.1, havg p hp]
    have hfppos : 0 < f p := lt_of_le_of_ne (hf_nonneg p) (Ne.symm hfp)
    exact mul_pos hp.1 (Real.sqrt_pos.2 (mul_pos ha hfppos))
  rcases putnam_1962_a2_integrable_classification (f := f) (a := a) (b := b) (p := p)
      ha hp hfp hf_nonneg havg hint with ⟨d, hdpos, hdeq⟩
  have hFp_eq : F p = a * p / (1 - d * p) := by
    change ∫ t in (0 : ℝ)..p, f t = a * p / (1 - d * p)
    rw [putnam_1962_a2_integral_eq_average (f := f) hp.1, havg p hp, hdeq p hp]
    rw [putnam_1962_a2_sqrt_rat a (1 - d * p) ha.le (hdpos p hp)]
    ring
  have hdc : d = c := by
    dsimp [c]
    rw [hFp_eq]
    field_simp [ha.ne', (ne_of_gt hp.1), (hdpos p hp).ne']
    ring
  constructor
  · intro x hx
    simpa [← hdc] using hdpos x hx
  · intro x hx
    simpa [← hdc] using hdeq x hx

private lemma putnam_1962_a2_formula_of_ne_in_interval
    {f : ℝ → ℝ} {a b p y0 : ℝ} (ha : 0 < a)
    (hp_pos : 0 < p) (hpy0 : p < y0) (hy0b : y0 < b)
    (hfp : f p ≠ 0) (hfy0 : f y0 ≠ 0) (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x)) :
    let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
    let c : ℝ := a * ((a * p)⁻¹ - (F p)⁻¹)
    ∀ x ∈ Ioo (0 : ℝ) b, f x ≠ 0 →
      0 < 1 - c * x ∧ f x = a / (1 - c * x) ^ 2 := by
  intro F c x hx hfx
  let w : ℝ := max x y0
  let u : ℝ := (w + b) / 2
  have hw_pos : 0 < w := lt_of_lt_of_le hx.1 (le_max_left x y0)
  have hw_b : w < b := max_lt hx.2 hy0b
  have hw_ne : f w ≠ 0 := by
    by_cases hxy : x ≤ y0
    · have hw : w = y0 := by simp [w, max_eq_right hxy]
      simpa [hw] using hfy0
    · have hyx : y0 ≤ x := le_of_not_ge hxy
      have hw : w = x := by simp [w, max_eq_left hyx]
      simpa [hw] using hfx
  have hwu : w < u := by dsimp [u]; linarith
  have hub : u < b := by dsimp [u]; linarith
  rcases putnam_1962_a2_exists_ne_between_right (f := f) (a := a) (b := b)
      ha ⟨hw_pos, hw_b⟩ hwu hub hf_nonneg havg hw_ne with ⟨z, hz, hfz⟩
  have hz_mem : z ∈ Ioo (0 : ℝ) b := ⟨lt_trans hw_pos hz.1, lt_trans hz.2 hub⟩
  have hpz : p ∈ Ioo (0 : ℝ) z := by
    refine ⟨hp_pos, ?_⟩
    exact lt_of_lt_of_le hpy0 (le_max_right x y0) |>.trans hz.1
  have hxz : x ∈ Ioo (0 : ℝ) z := ⟨hx.1, lt_of_le_of_lt (le_max_left x y0) hz.1⟩
  have hint0z : IntervalIntegrable f volume (0 : ℝ) z :=
    putnam_1962_a2_intervalIntegrable_of_ne (f := f) (a := a) (b := b)
      ha hz_mem hf_nonneg havg hfz
  have hclass := putnam_1962_a2_integrable_classification_explicit
    (f := f) (a := a) (b := z) (p := p) ha hpz hfp hf_nonneg
    (fun t ht => havg t ⟨ht.1, lt_trans ht.2 hz_mem.2⟩) hint0z
  exact ⟨hclass.1 x hxz, hclass.2 x hxz⟩

private lemma putnam_1962_a2_ne_of_lt_ne
    {f : ℝ → ℝ} {a b x y : ℝ} (ha : 0 < a) (hy : y ∈ Ioo (0 : ℝ) b)
    (hx0 : 0 < x) (hxy : x < y) (hf_nonneg : 0 ≤ f)
    (havg : ∀ x ∈ Ioo (0 : ℝ) b, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x))
    (hfy : f y ≠ 0) :
    f x ≠ 0 := by
  rcases putnam_1962_a2_exists_ne_before (f := f) (a := a) (b := b)
      ha hy hf_nonneg havg hfy with ⟨p, hp0, hpy, hfp⟩
  have hint0y : IntervalIntegrable f volume (0 : ℝ) y :=
    putnam_1962_a2_intervalIntegrable_of_ne (f := f) (a := a) (b := b)
      ha hy hf_nonneg havg hfy
  have hp : p ∈ Ioo (0 : ℝ) y := ⟨hp0, hpy⟩
  rcases putnam_1962_a2_integrable_classification (f := f) (a := a) (b := y) (p := p)
      ha hp hfp hf_nonneg (fun t ht => havg t ⟨ht.1, lt_trans ht.2 hy.2⟩) hint0y
    with ⟨c, hden, hrat⟩
  have hx : x ∈ Ioo (0 : ℝ) y := ⟨hx0, hxy⟩
  rw [hrat x hx]
  exact div_ne_zero ha.ne' (pow_ne_zero 2 (hden x hx).ne')

private lemma putnam_1962_a2_no_stop_before_pole
    {f : ℝ → ℝ} {a c e r : ℝ} (ha : 0 < a) (hrpos : 0 < r) (hre : r < e)
    (hden_left : ∀ x : ℝ, 0 < x → x < r → 0 < 1 - c * x)
    (hleft : ∀ x : ℝ, 0 < x → x < r → f x = a / (1 - c * x) ^ 2)
    (hright : ∀ x : ℝ, r ≤ x → x < e → f x = 0)
    (hdenr : 0 < 1 - c * r)
    (havg : ∀ x ∈ Ioo (0 : ℝ) e, (⨍ t in Ico (0 : ℝ) x, f t) = √(a * f x)) :
    False := by
  let m : ℝ := (r + e) / 2
  have hrm : r < m := by dsimp [m]; linarith
  have hme : m < e := by dsimp [m]; linarith
  have hmpos : 0 < m := lt_trans hrpos hrm
  let rat : ℝ → ℝ := fun x => a / (1 - c * x) ^ 2
  have hdenIcc : ∀ t ∈ Icc (0 : ℝ) r, 1 - c * t ≠ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | htpos
    · norm_num
    rcases lt_or_eq_of_le ht.2 with htr | rfl
    · exact (hden_left t htpos htr).ne'
    · exact hdenr.ne'
  have hrat_int_val : ∫ t in (0 : ℝ)..r, rat t = a * r / (1 - c * r) := by
    simpa [rat] using putnam_1962_a2_integral_rat a c r hrpos hdenIcc
  have hrat_int : IntervalIntegrable rat volume (0 : ℝ) r := by
    refine intervalIntegral.intervalIntegrable_of_integral_ne_zero ?_
    rw [hrat_int_val]
    exact (div_pos (mul_pos ha hrpos) hdenr).ne'
  have hae_rat_f : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) r → rat t = f t := by
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ r by rw [ae_iff]; simp] with t htrne ht
    have ht' : t ∈ Ioc (0 : ℝ) r := by simpa [uIoc_of_le hrpos.le] using ht
    have hlt : t < r := lt_of_le_of_ne ht'.2 htrne
    exact (hleft t ht'.1 hlt).symm
  have hf_int0r : IntervalIntegrable f volume (0 : ℝ) r :=
    hrat_int.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_rat_f)
  have hzero_rm : EqOn f (fun _ : ℝ => 0) (uIoc r m) := by
    intro t ht
    have ht' : t ∈ Ioc r m := by simpa [uIoc_of_le hrm.le] using ht
    exact hright t ht'.1.le (lt_of_le_of_lt ht'.2 hme)
  have hf_intrm : IntervalIntegrable f volume r m := by
    exact (IntervalIntegrable.congr hzero_rm.symm) (intervalIntegrable_const (c := (0 : ℝ)))
  have hf_int0m : IntervalIntegrable f volume (0 : ℝ) m := hf_int0r.trans hf_intrm
  have hInt0r : ∫ t in (0 : ℝ)..r, f t = a * r / (1 - c * r) := by
    rw [← hrat_int_val]
    exact (intervalIntegral.integral_congr_ae
      (Filter.Eventually.mono hae_rat_f fun t ht hmem => (ht hmem).symm))
  have hIntrm : ∫ t in r..m, f t = 0 := by
    have hae : ∀ᵐ t ∂volume, t ∈ uIoc r m → f t = (fun _ : ℝ => 0) t :=
      ae_of_all volume hzero_rm
    rw [intervalIntegral.integral_congr_ae hae]
    exact intervalIntegral.integral_zero
  have hsub := intervalIntegral.integral_interval_sub_left hf_int0m hf_int0r
  have hInt0m : ∫ t in (0 : ℝ)..m, f t = a * r / (1 - c * r) := by
    nlinarith
  have hfm : f m = 0 := hright m hrm.le hme
  have hInt0m_zero : ∫ t in (0 : ℝ)..m, f t = 0 := by
    rw [putnam_1962_a2_integral_eq_average (f := f) hmpos, havg m ⟨hmpos, hme⟩, hfm]
    simp
  have hpos : 0 < a * r / (1 - c * r) := div_pos (mul_pos ha hrpos) hdenr
  nlinarith

-- {f | (∃ a c : ℝ, 0 ≤ a ∧ f = (fun x : ℝ ↦ a / (1 - c * x) ^ 2)) ∨ (∃ a c : ℝ, 0 ≤ a ∧ 0 < c ∧ f = (fun x : ℝ ↦ if x < 1 / c then a / (1 - c * x) ^ 2 else 0)) ∨ (0 ≤ f ∧ ∀ x : ℝ, 0 < x → f x = 0) ∨ (∃ e : ℝ, 0 < e ∧ f 0 = 0 ∧ 0 ≤ f ∧ ∀ x ∈ Ioo (0 : ℝ) e, (⨍ t in Ico (0 : ℝ) x, f t) = 0)}
/--
Find every real-valued function $f$ whose domain is an interval $I$ (finite or infinite) having 0 as a left-hand endpoint, such that for every positive member $x$ of $I$ the average of $f$ over the closed interval $[0, x]$ is equal to the geometric mean of the numbers $f(0)$ and $f(x)$.
-/
theorem putnam_1962_a2
    (P : Set ℝ → (ℝ → ℝ) → Prop)
    (P_def : ∀ s f, P s f ↔ 0 ≤ f ∧ ∀ x ∈ s, ⨍ t in Ico 0 x, f t = √(f 0 * f x)) :
    (∀ f,
      (P (Ioi 0) f → ∃ g ∈ (({f | (∃ a c : ℝ, 0 ≤ a ∧ f = (fun x : ℝ ↦ a / (1 - c * x) ^ 2)) ∨ (∃ a c : ℝ, 0 ≤ a ∧ 0 < c ∧ f = (fun x : ℝ ↦ if x < 1 / c then a / (1 - c * x) ^ 2 else 0)) ∨ (0 ≤ f ∧ ∀ x : ℝ, 0 < x → f x = 0) ∨ (∃ e : ℝ, 0 < e ∧ f 0 = 0 ∧ 0 ≤ f ∧ ∀ x ∈ Ioo (0 : ℝ) e, (⨍ t in Ico (0 : ℝ) x, f t) = 0)}) : Set (ℝ → ℝ) ), EqOn f g (Ici 0)) ∧
      (∀ e > 0, P (Ioo 0 e) f → ∃ g ∈ (({f | (∃ a c : ℝ, 0 ≤ a ∧ f = (fun x : ℝ ↦ a / (1 - c * x) ^ 2)) ∨ (∃ a c : ℝ, 0 ≤ a ∧ 0 < c ∧ f = (fun x : ℝ ↦ if x < 1 / c then a / (1 - c * x) ^ 2 else 0)) ∨ (0 ≤ f ∧ ∀ x : ℝ, 0 < x → f x = 0) ∨ (∃ e : ℝ, 0 < e ∧ f 0 = 0 ∧ 0 ≤ f ∧ ∀ x ∈ Ioo (0 : ℝ) e, (⨍ t in Ico (0 : ℝ) x, f t) = 0)}) : Set (ℝ → ℝ) ), EqOn f g (Ico 0 e))) ∧
    ∀ f ∈ (({f | (∃ a c : ℝ, 0 ≤ a ∧ f = (fun x : ℝ ↦ a / (1 - c * x) ^ 2)) ∨ (∃ a c : ℝ, 0 ≤ a ∧ 0 < c ∧ f = (fun x : ℝ ↦ if x < 1 / c then a / (1 - c * x) ^ 2 else 0)) ∨ (0 ≤ f ∧ ∀ x : ℝ, 0 < x → f x = 0) ∨ (∃ e : ℝ, 0 < e ∧ f 0 = 0 ∧ 0 ≤ f ∧ ∀ x ∈ Ioo (0 : ℝ) e, (⨍ t in Ico (0 : ℝ) x, f t) = 0)}) : Set (ℝ → ℝ) ), P (Ioi 0) f ∨ (∃ e > 0, P (Ioo 0 e) f) := by
  classical
  constructor
  · intro f
    constructor
    · intro hf
      by_cases h0 : f 0 = 0
      · refine ⟨f, ?_, ?_⟩
        · right; right; right
          refine ⟨1, by norm_num, h0, ((P_def (Ioi 0) f).mp hf).1, ?_⟩
          intro x hx
          have h := ((P_def (Ioi 0) f).mp hf).2 x hx.1
          simpa [h0] using h
        · intro x hx
          rfl
      · have hfdata := ((P_def (Ioi 0) f).mp hf)
        by_cases hpos : ∃ x : ℝ, 0 < x ∧ f x ≠ 0
        · have ha : 0 < f 0 := lt_of_le_of_ne (hfdata.1 0) (Ne.symm h0)
          rcases hpos with ⟨x1, hx1pos, hfx1⟩
          let B1 : ℝ := x1 + 1
          have hx1B1 : x1 ∈ Ioo (0 : ℝ) B1 := ⟨hx1pos, by dsimp [B1]; linarith⟩
          rcases putnam_1962_a2_exists_ne_before (f := f) (a := f 0) (b := B1)
              ha hx1B1 hfdata.1 (fun x hx => hfdata.2 x hx.1) hfx1 with
            ⟨p, hp0, hpx1, hfp⟩
          let B2 : ℝ := x1 + 2
          let u1 : ℝ := x1 + 1
          have hx1B2 : x1 ∈ Ioo (0 : ℝ) B2 := ⟨hx1pos, by dsimp [B2]; linarith⟩
          have hx1u1 : x1 < u1 := by dsimp [u1]; linarith
          have hu1B2 : u1 < B2 := by dsimp [u1, B2]; linarith
          rcases putnam_1962_a2_exists_ne_between_right (f := f) (a := f 0) (b := B2)
              ha hx1B2 hx1u1 hu1B2 hfdata.1 (fun x hx => hfdata.2 x hx.1) hfx1 with
            ⟨y0, hy0, hfy0⟩
          have hpy0 : p < y0 := lt_trans hpx1 hy0.1
          let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
          let c : ℝ := f 0 * ((f 0 * p)⁻¹ - (F p)⁻¹)
          have hformula_ne : ∀ x : ℝ, 0 < x → f x ≠ 0 →
              0 < 1 - c * x ∧ f x = f 0 / (1 - c * x) ^ 2 := by
            intro x hx0 hfx
            let B : ℝ := max x y0 + 1
            have hy0B : y0 < B := by dsimp [B]; linarith [le_max_right x y0]
            have hxB : x ∈ Ioo (0 : ℝ) B := ⟨hx0, by dsimp [B]; linarith [le_max_left x y0]⟩
            have h := putnam_1962_a2_formula_of_ne_in_interval (f := f) (a := f 0)
              (b := B) (p := p) (y0 := y0) ha hp0 hpy0 hy0B hfp hfy0 hfdata.1
              (fun t ht => hfdata.2 t ht.1)
            simpa [F, c] using h x hxB hfx
          have hne_of_lt_ne_global : ∀ x y : ℝ, 0 < x → x < y → f y ≠ 0 → f x ≠ 0 := by
            intro x y hx0 hxy hfy
            let B : ℝ := y + 1
            have hyB : y ∈ Ioo (0 : ℝ) B := by
              have hy0 : 0 < y := lt_trans hx0 hxy
              exact ⟨hy0, by dsimp [B]; linarith⟩
            exact putnam_1962_a2_ne_of_lt_ne (f := f) (a := f 0) (b := B)
              ha hyB hx0 hxy hfdata.1 (fun t ht => hfdata.2 t ht.1) hfy
          let S : Set ℝ := {x | 0 < x ∧ f x ≠ 0}
          have hS_nonempty : S.Nonempty := ⟨y0, ⟨lt_trans hx1pos hy0.1, hfy0⟩⟩
          by_cases hS_bdd : BddAbove S
          · let r : ℝ := sSup S
            have hy0_le_r : y0 ≤ r := le_csSup hS_bdd ⟨lt_trans hx1pos hy0.1, hfy0⟩
            have hrpos : 0 < r := lt_of_lt_of_le (lt_trans hx1pos hy0.1) hy0_le_r
            have hne_of_lt_r : ∀ x : ℝ, 0 < x → x < r → f x ≠ 0 := by
              intro x hx0 hxr
              rcases exists_lt_of_lt_csSup hS_nonempty hxr with ⟨y, hyS, hxy⟩
              exact hne_of_lt_ne_global x y hx0 hxy hyS.2
            have hden_left : ∀ x : ℝ, 0 < x → x < r → 0 < 1 - c * x := by
              intro x hx0 hxr
              exact (hformula_ne x hx0 (hne_of_lt_r x hx0 hxr)).1
            have hleft : ∀ x : ℝ, 0 < x → x < r → f x = f 0 / (1 - c * x) ^ 2 := by
              intro x hx0 hxr
              exact (hformula_ne x hx0 (hne_of_lt_r x hx0 hxr)).2
            have hzero_of_r_lt : ∀ x : ℝ, r < x → f x = 0 := by
              intro x hrx
              by_contra hfx
              have hxS : x ∈ S := ⟨lt_trans hrpos hrx, hfx⟩
              have hxle : x ≤ r := le_csSup hS_bdd hxS
              linarith
            have hzero_of_r_le : ∀ x : ℝ, r ≤ x → f x = 0 := by
              intro x hrx
              rcases lt_or_eq_of_le hrx with hrx' | rfl
              · exact hzero_of_r_lt x hrx'
              · by_contra hfr
                let B : ℝ := r + 2
                let u : ℝ := r + 1
                have hrB : r ∈ Ioo (0 : ℝ) B := ⟨hrpos, by dsimp [B]; linarith⟩
                have hru : r < u := by dsimp [u]; linarith
                have huB : u < B := by dsimp [u, B]; linarith
                rcases putnam_1962_a2_exists_ne_between_right (f := f) (a := f 0) (b := B)
                    ha hrB hru huB hfdata.1 (fun t ht => hfdata.2 t ht.1) hfr with
                  ⟨z, hz, hfz⟩
                have hzS : z ∈ S := ⟨lt_trans hrpos hz.1, hfz⟩
                have hzle : z ≤ r := le_csSup hS_bdd hzS
                exact (not_lt_of_ge hzle) hz.1
            have hdenr_nonneg : 0 ≤ 1 - c * r := by
              by_contra hnot
              have hneg : 1 - c * r < 0 := lt_of_not_ge hnot
              have hcpos : 0 < c := by nlinarith [hrpos]
              let x : ℝ := (r + 1 / c) / 2
              have hinv_lt_r : 1 / c < r := by
                field_simp [hcpos.ne']
                nlinarith
              have hx0 : 0 < x := by
                dsimp [x]
                positivity
              have hxr : x < r := by dsimp [x]; linarith
              have hxdenneg : 1 - c * x < 0 := by
                dsimp [x]
                field_simp [hcpos.ne']
                nlinarith
              have hxdenpos := hden_left x hx0 hxr
              linarith
            have hdenr_notpos : ¬ 0 < 1 - c * r := by
              intro hdenrpos
              exact putnam_1962_a2_no_stop_before_pole (f := f) (a := f 0) (c := c)
                (e := r + 1) (r := r) ha hrpos (by linarith) hden_left hleft
                (fun x hrx hxlt => hzero_of_r_le x hrx) hdenrpos
                (fun x hx => hfdata.2 x hx.1)
            have hdenr_eq : 1 - c * r = 0 := le_antisymm (le_of_not_gt hdenr_notpos) hdenr_nonneg
            have hcr : c * r = 1 := by nlinarith
            have hcpos : 0 < c := by nlinarith [hrpos, hcr]
            have hr_eq : r = 1 / c := by
              field_simp [hcpos.ne']
              nlinarith
            refine ⟨(fun x : ℝ => if x < 1 / c then f 0 / (1 - c * x) ^ 2 else 0), ?_, ?_⟩
            · right; left
              exact ⟨f 0, c, ha.le, hcpos, rfl⟩
            · intro x hx
              rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x by simpa using hx) with rfl | hx0
              · have h0cut : (0 : ℝ) < 1 / c := one_div_pos.mpr hcpos
                change f 0 = (if (0 : ℝ) < 1 / c then f 0 / (1 - c * 0) ^ 2 else 0)
                rw [if_pos h0cut]
                ring
              · by_cases hxr : x < r
                · have hxcut : x < 1 / c := by rwa [← hr_eq]
                  change f x = (if x < 1 / c then f 0 / (1 - c * x) ^ 2 else 0)
                  rw [if_pos hxcut]
                  exact hleft x hx0 hxr
                · have hrx : r ≤ x := le_of_not_gt hxr
                  have hxcut : ¬ x < 1 / c := by rwa [← hr_eq]
                  change f x = (if x < 1 / c then f 0 / (1 - c * x) ^ 2 else 0)
                  rw [if_neg hxcut, hzero_of_r_le x hrx]
          · refine ⟨(fun x : ℝ => f 0 / (1 - c * x) ^ 2), ?_, ?_⟩
            · left
              exact ⟨f 0, c, ha.le, rfl⟩
            · intro x hx
              rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x by simpa using hx) with rfl | hx0
              · ring
              · have hnot_bound : ¬ ∀ z ∈ S, z ≤ max x y0 := by
                  intro hb
                  exact hS_bdd ⟨max x y0, hb⟩
                push_neg at hnot_bound
                rcases hnot_bound with ⟨z, hzS, hzgt⟩
                have hxz : x < z := lt_of_le_of_lt (le_max_left x y0) hzgt
                have hfx : f x ≠ 0 := hne_of_lt_ne_global x z hx0 hxz hzS.2
                exact (hformula_ne x hx0 hfx).2
        · refine ⟨(fun x : ℝ => if x = 0 then f 0 else 0), ?_, ?_⟩
          · exact putnam_1962_a2_point_zero_branch_mem (f 0) (hfdata.1 0)
          · intro x hx
            rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x by simpa using hx) with rfl | hxpos
            · simp
            · have hfx : f x = 0 := by
                by_contra hne
                exact hpos ⟨x, hxpos, hne⟩
              simp [hxpos.ne', hfx]
    · intro e he hf
      by_cases h0 : f 0 = 0
      · refine ⟨f, ?_, ?_⟩
        · right; right; right
          refine ⟨e, he, h0, ((P_def (Ioo 0 e) f).mp hf).1, ?_⟩
          intro x hx
          have h := ((P_def (Ioo 0 e) f).mp hf).2 x hx
          simpa [h0] using h
        · intro x hx
          rfl
      · have hfdata := ((P_def (Ioo 0 e) f).mp hf)
        by_cases hpos : ∃ x ∈ Ioo (0 : ℝ) e, f x ≠ 0
        · have ha : 0 < f 0 := lt_of_le_of_ne (hfdata.1 0) (Ne.symm h0)
          rcases hpos with ⟨x1, hx1, hfx1⟩
          rcases putnam_1962_a2_exists_ne_before (f := f) (a := f 0) (b := e)
              ha hx1 hfdata.1 hfdata.2 hfx1 with ⟨p, hp0, hpx1, hfp⟩
          let u1 : ℝ := (x1 + e) / 2
          have hx1u1 : x1 < u1 := by dsimp [u1]; linarith [hx1.2]
          have hu1e : u1 < e := by dsimp [u1]; linarith [hx1.2]
          rcases putnam_1962_a2_exists_ne_between_right (f := f) (a := f 0) (b := e)
              ha hx1 hx1u1 hu1e hfdata.1 hfdata.2 hfx1 with ⟨y0, hy0, hfy0⟩
          have hy0e : y0 < e := lt_trans hy0.2 hu1e
          have hpy0 : p < y0 := lt_trans hpx1 hy0.1
          let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
          let c : ℝ := f 0 * ((f 0 * p)⁻¹ - (F p)⁻¹)
          have hformula_ne :
              ∀ x ∈ Ioo (0 : ℝ) e, f x ≠ 0 →
                0 < 1 - c * x ∧ f x = f 0 / (1 - c * x) ^ 2 := by
            simpa [F, c] using
              putnam_1962_a2_formula_of_ne_in_interval (f := f) (a := f 0) (b := e)
                (p := p) (y0 := y0) ha hp0 hpy0 hy0e hfp hfy0 hfdata.1 hfdata.2
          let S : Set ℝ := {x | x ∈ Ioo (0 : ℝ) e ∧ f x ≠ 0}
          have hS_nonempty : S.Nonempty := ⟨y0, ⟨⟨lt_trans hx1.1 hy0.1, hy0e⟩, hfy0⟩⟩
          have hS_bdd : BddAbove S := ⟨e, by intro x hx; exact hx.1.2.le⟩
          let r : ℝ := sSup S
          have hy0_le_r : y0 ≤ r := le_csSup hS_bdd ⟨⟨lt_trans hx1.1 hy0.1, hy0e⟩, hfy0⟩
          have hrpos : 0 < r := lt_of_lt_of_le (lt_trans hx1.1 hy0.1) hy0_le_r
          have hre_le : r ≤ e := csSup_le hS_nonempty (by intro x hx; exact hx.1.2.le)
          have hne_of_lt_r : ∀ x : ℝ, 0 < x → x < r → f x ≠ 0 := by
            intro x hx0 hxr
            rcases exists_lt_of_lt_csSup hS_nonempty hxr with ⟨y, hyS, hxy⟩
            exact putnam_1962_a2_ne_of_lt_ne (f := f) (a := f 0) (b := e)
              ha hyS.1 hx0 hxy hfdata.1 hfdata.2 hyS.2
          have hden_left : ∀ x : ℝ, 0 < x → x < r → 0 < 1 - c * x := by
            intro x hx0 hxr
            exact (hformula_ne x ⟨hx0, lt_of_lt_of_le hxr hre_le⟩
              (hne_of_lt_r x hx0 hxr)).1
          have hleft : ∀ x : ℝ, 0 < x → x < r → f x = f 0 / (1 - c * x) ^ 2 := by
            intro x hx0 hxr
            exact (hformula_ne x ⟨hx0, lt_of_lt_of_le hxr hre_le⟩
              (hne_of_lt_r x hx0 hxr)).2
          have hzero_of_r_lt : ∀ x : ℝ, r < x → x < e → f x = 0 := by
            intro x hrx hxe
            by_contra hfx
            have hxS : x ∈ S := ⟨⟨lt_trans hrpos hrx, hxe⟩, hfx⟩
            have hxle : x ≤ r := le_csSup hS_bdd hxS
            linarith
          have hzero_of_r_le : ∀ x : ℝ, r ≤ x → x < e → f x = 0 := by
            intro x hrx hxe
            rcases lt_or_eq_of_le hrx with hrx' | rfl
            · exact hzero_of_r_lt x hrx' hxe
            · by_contra hfr
              let u : ℝ := (r + e) / 2
              have hru : r < u := by dsimp [u]; linarith
              have hue : u < e := by dsimp [u]; linarith
              rcases putnam_1962_a2_exists_ne_between_right (f := f) (a := f 0) (b := e)
                  ha ⟨hrpos, hxe⟩ hru hue hfdata.1 hfdata.2 hfr with ⟨z, hz, hfz⟩
              have hzS : z ∈ S := ⟨⟨lt_trans hrpos hz.1, lt_trans hz.2 hue⟩, hfz⟩
              have hzle : z ≤ r := le_csSup hS_bdd hzS
              exact (not_lt_of_ge hzle) hz.1
          have hdenr_nonneg : 0 ≤ 1 - c * r := by
            by_contra hnot
            have hneg : 1 - c * r < 0 := lt_of_not_ge hnot
            have hcpos : 0 < c := by nlinarith [hrpos]
            let x : ℝ := (r + 1 / c) / 2
            have hinv_lt_r : 1 / c < r := by
              field_simp [hcpos.ne']
              nlinarith
            have hx0 : 0 < x := by
              dsimp [x]
              positivity
            have hxr : x < r := by dsimp [x]; linarith
            have hxdenneg : 1 - c * x < 0 := by
              dsimp [x]
              field_simp [hcpos.ne']
              nlinarith
            have hxdenpos := hden_left x hx0 hxr
            linarith
          by_cases hre : r < e
          · have hdenr_notpos : ¬ 0 < 1 - c * r := by
              intro hdenrpos
              exact putnam_1962_a2_no_stop_before_pole (f := f) (a := f 0) (c := c)
                (e := e) (r := r) ha hrpos hre hden_left hleft hzero_of_r_le hdenrpos
                hfdata.2
            have hdenr_eq : 1 - c * r = 0 := le_antisymm (le_of_not_gt hdenr_notpos) hdenr_nonneg
            have hcr : c * r = 1 := by nlinarith
            have hcpos : 0 < c := by nlinarith [hrpos, hcr]
            have hr_eq : r = 1 / c := by
              field_simp [hcpos.ne']
              nlinarith
            refine ⟨(fun x : ℝ => if x < 1 / c then f 0 / (1 - c * x) ^ 2 else 0), ?_, ?_⟩
            · right; left
              exact ⟨f 0, c, ha.le, hcpos, rfl⟩
            · intro x hx
              rcases eq_or_lt_of_le hx.1 with rfl | hx0
              · have h0cut : (0 : ℝ) < 1 / c := one_div_pos.mpr hcpos
                change f 0 = (if (0 : ℝ) < 1 / c then f 0 / (1 - c * 0) ^ 2 else 0)
                rw [if_pos h0cut]
                ring
              · by_cases hxr : x < r
                · have hxcut : x < 1 / c := by rwa [← hr_eq]
                  change f x = (if x < 1 / c then f 0 / (1 - c * x) ^ 2 else 0)
                  rw [if_pos hxcut]
                  exact hleft x hx0 hxr
                · have hrx : r ≤ x := le_of_not_gt hxr
                  have hxcut : ¬ x < 1 / c := by rwa [← hr_eq]
                  change f x = (if x < 1 / c then f 0 / (1 - c * x) ^ 2 else 0)
                  rw [if_neg hxcut, hzero_of_r_le x hrx hx.2]
          · have hre_eq : r = e := le_antisymm hre_le (le_of_not_gt hre)
            refine ⟨(fun x : ℝ => f 0 / (1 - c * x) ^ 2), ?_, ?_⟩
            · left
              exact ⟨f 0, c, ha.le, rfl⟩
            · intro x hx
              rcases eq_or_lt_of_le hx.1 with rfl | hx0
              · ring
              · have hxr : x < r := by
                  rw [hre_eq]
                  exact hx.2
                exact hleft x hx0 hxr
        · refine ⟨(fun x : ℝ => if x = 0 then f 0 else 0), ?_, ?_⟩
          · exact putnam_1962_a2_point_zero_branch_mem (f 0) (hfdata.1 0)
          · intro x hx
            rcases eq_or_lt_of_le hx.1 with rfl | hxpos
            · simp
            · have hfx : f x = 0 := by
                by_contra hne
                exact hpos ⟨x, ⟨hxpos, hx.2⟩, hne⟩
              simp [hxpos.ne', hfx]
  · intro f hf
    rcases hf with hrat | hcut | hzero | hfourth
    · rcases hrat with ⟨a, c, ha, rfl⟩
      right
      by_cases hc : 0 < c
      · refine ⟨1 / (2 * c), by positivity, ?_⟩
        refine putnam_1962_a2_rational_P P P_def ha ?_
        intro x hx
        have hcx : c * x < c * (1 / (2 * c)) := mul_lt_mul_of_pos_left hx.2 hc
        have hcne : c ≠ 0 := ne_of_gt hc
        have hcval : c * (1 / (2 * c)) = 1 / 2 := by
          field_simp [hcne]
        nlinarith
      · refine ⟨1, zero_lt_one, ?_⟩
        refine putnam_1962_a2_rational_P P P_def ha ?_
        intro x hx
        have hc_le : c ≤ 0 := le_of_not_gt hc
        have hcx_nonpos : c * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_le hx.1.le
        nlinarith
    · rcases hcut with ⟨a, c, ha, hc, rfl⟩
      right
      refine ⟨1 / (2 * c), by positivity, ?_⟩
      refine putnam_1962_a2_cutoff_P P P_def ha hc ?_ ?_
      · have hcne : c ≠ 0 := ne_of_gt hc
        field_simp [hcne]
        nlinarith
      · intro x hx
        have hcx : c * x < c * (1 / (2 * c)) := mul_lt_mul_of_pos_left hx.2 hc
        have hcne : c ≠ 0 := ne_of_gt hc
        have hcval : c * (1 / (2 * c)) = 1 / 2 := by
          field_simp [hcne]
        nlinarith
    · rcases hzero with ⟨hf_nonneg, hfzero⟩
      left
      exact putnam_1962_a2_zero_on_pos_P P P_def hf_nonneg hfzero
    · rcases hfourth with ⟨e, he, h0, hf_nonneg, havg⟩
      right
      exact ⟨e, he, putnam_1962_a2_fourth_P P P_def h0 hf_nonneg havg⟩
