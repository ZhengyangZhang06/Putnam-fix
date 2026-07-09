import Mathlib

open Filter Topology Metric MeasureTheory

private theorem putnam_2021_a4_euclidean_to_prod
    (R : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) R, f (p 0) (p 1)) =
      ∫ z : ℝ × ℝ in {z | √(z.1 ^ 2 + z.2 ^ 2) < R}, f z.1 z.2 := by
  let e : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) := fun q => WithLp.toLp 2 q
  have h₁ :
      (∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) R, f (p 0) (p 1)) =
        ∫ x : Fin 2 → ℝ in e ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) R,
          f (x 0) (x 1) := by
    rw [← (PiLp.volume_preserving_toLp (Fin 2)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding]
  have h₂ :
      (∫ x : Fin 2 → ℝ in e ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) R, f (x 0) (x 1)) =
        ∫ z : ℝ × ℝ in
          MeasurableEquiv.finTwoArrow '' (e ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) R),
          f z.1 z.2 := by
    rw [(MeasureTheory.volume_preserving_finTwoArrow ℝ).setIntegral_image_emb
      MeasurableEquiv.finTwoArrow.measurableEmbedding]
    simp [MeasurableEquiv.finTwoArrow]
  have hset :
      MeasurableEquiv.finTwoArrow '' (e ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) R) =
        {z : ℝ × ℝ | √(z.1 ^ 2 + z.2 ^ 2) < R} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [e, MeasurableEquiv.finTwoArrow, Metric.mem_ball, dist_eq_norm,
        EuclideanSpace.norm_eq, Fin.sum_univ_two] using hx
    · intro hz
      refine ⟨MeasurableEquiv.finTwoArrow.symm z, ?_, by simp⟩
      simpa [e, MeasurableEquiv.finTwoArrow, Metric.mem_ball, dist_eq_norm,
        EuclideanSpace.norm_eq, Fin.sum_univ_two] using hz
  rw [h₁, h₂, hset]

private lemma putnam_2021_a4_sin_sq_den_pos
    (a b x : ℝ) (ha : 0 < a) (hab : 0 < a + b) :
    0 < a + b * Real.sin x ^ 2 := by
  have hs0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have hs1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  by_cases hb : 0 ≤ b
  · nlinarith [mul_nonneg hb hs0]
  · have hb' : b < 0 := lt_of_not_ge hb
    have hmul : b ≤ b * Real.sin x ^ 2 := by
      nlinarith [mul_le_mul_of_nonpos_left hs1 hb'.le]
    nlinarith

private lemma putnam_2021_a4_tan_pointwise
    (a b θ : ℝ) (hcospos : 0 < Real.cos θ) :
    |1 / Real.cos θ ^ 2| * (a + (a + b) * Real.tan θ ^ 2)⁻¹ =
      (a + b * Real.sin θ ^ 2)⁻¹ := by
  have hcos : Real.cos θ ≠ 0 := hcospos.ne'
  have hcos2 : Real.cos θ ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  rw [abs_of_pos]
  · rw [Real.tan_eq_sin_div_cos]
    have hD :
        a + (a + b) * (Real.sin θ / Real.cos θ) ^ 2 =
          (a + b * Real.sin θ ^ 2) / Real.cos θ ^ 2 := by
      rw [eq_div_iff hcos2]
      have hs :
          (Real.sin θ / Real.cos θ) ^ 2 * Real.cos θ ^ 2 =
            Real.sin θ ^ 2 := by
        rw [div_pow]
        exact div_mul_cancel₀ _ hcos2
      calc
        (a + (a + b) * (Real.sin θ / Real.cos θ) ^ 2) * Real.cos θ ^ 2
            = a * Real.cos θ ^ 2 +
                (a + b) * ((Real.sin θ / Real.cos θ) ^ 2 * Real.cos θ ^ 2) := by
                ring
        _ = a * Real.cos θ ^ 2 + (a + b) * Real.sin θ ^ 2 := by rw [hs]
        _ = a + b * Real.sin θ ^ 2 := by
          conv_rhs => rw [← mul_one a, ← Real.sin_sq_add_cos_sq θ]
          ring
    rw [hD]
    by_cases hE : a + b * Real.sin θ ^ 2 = 0
    · simp [hE]
    · field_simp [hE, hcos2]
  · positivity

private lemma putnam_2021_a4_tan_change (a b : ℝ) :
    (∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
        (a + b * Real.sin θ ^ 2)⁻¹) =
      ∫ t : ℝ, (a + (a + b) * t ^ 2)⁻¹ := by
  let s : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let g : ℝ → ℝ := fun t => (a + (a + b) * t ^ 2)⁻¹
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := s) (f := Real.tan) (f' := fun θ => 1 / Real.cos θ ^ 2)
    (F := ℝ) measurableSet_Ioo
    (fun θ hθ => (Real.hasDerivAt_tan
      (Real.cos_pos_of_mem_Ioo hθ).ne').hasDerivWithinAt)
    (by simpa [s, Real.tanPartialHomeomorph] using Real.tanPartialHomeomorph.injOn)
    g
  have himage : Real.tan '' s = (Set.univ : Set ℝ) := by
    simpa [s, Real.tanPartialHomeomorph] using
      (PartialEquiv.image_source_eq_target Real.tanPartialHomeomorph.toPartialEquiv)
  rw [himage, setIntegral_univ] at hcov
  rw [hcov]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  exact (by
    simpa [g, smul_eq_mul] using
      (putnam_2021_a4_tan_pointwise a b θ (Real.cos_pos_of_mem_Ioo hθ)).symm)

private lemma putnam_2021_a4_integral_univ_inv_add_mul_sq
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ t : ℝ, (a + c * t ^ 2)⁻¹) = Real.pi / Real.sqrt (a * c) := by
  let k : ℝ := Real.sqrt (c / a)
  have hk_pos : 0 < k := by
    dsimp [k]
    positivity
  have hk_ne : k ≠ 0 := hk_pos.ne'
  have hk_sq : k ^ 2 = c / a := by
    dsimp [k]
    rw [Real.sq_sqrt]
    positivity
  have hpoint : (fun t : ℝ => (a + c * t ^ 2)⁻¹) =
      fun t : ℝ => a⁻¹ * (1 + (k * t) ^ 2)⁻¹ := by
    funext t
    have hden : a + c * t ^ 2 = a * (1 + (k * t) ^ 2) := by
      rw [mul_pow, hk_sq]
      field_simp [ha.ne']
    rw [hden]
    field_simp [ha.ne']
  rw [hpoint]
  rw [integral_const_mul]
  have hscale := MeasureTheory.Measure.integral_comp_mul_left
    (g := fun y : ℝ => (1 + y ^ 2)⁻¹) k
  simp only [smul_eq_mul] at hscale
  rw [hscale]
  rw [integral_univ_inv_one_add_sq]
  have habs : |k⁻¹| = k⁻¹ := abs_of_pos (inv_pos.mpr hk_pos)
  rw [habs]
  have hsqrt : Real.sqrt (a * c) = a * k := by
    rw [Real.sqrt_eq_cases]
    left
    constructor
    · rw [mul_assoc, ← mul_assoc k a k]
      ring_nf
      rw [hk_sq]
      field_simp [ha.ne']
    · positivity
  rw [hsqrt]
  field_simp [ha.ne', hk_ne]

private lemma putnam_2021_a4_integral_Ioo_inv_add_mul_sin_sq
    (a b : ℝ) (ha : 0 < a) (hab : 0 < a + b) :
    (∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
        (a + b * Real.sin θ ^ 2)⁻¹) =
      Real.pi / Real.sqrt (a * (a + b)) := by
  rw [putnam_2021_a4_tan_change]
  exact putnam_2021_a4_integral_univ_inv_add_mul_sq a (a + b) ha hab

private lemma putnam_2021_a4_integral_Ioo_neg_pi_pi_inv_add_mul_sin_two_sq
    (a b : ℝ) (ha : 0 < a) (hab : 0 < a + b) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (a + b * Real.sin (2 * θ) ^ 2)⁻¹) =
      2 * Real.pi / Real.sqrt (a * (a + b)) := by
  let f : ℝ → ℝ := fun φ => (a + b * Real.sin φ ^ 2)⁻¹
  have hfper : Function.Periodic f Real.pi := by
    intro x
    simp [f, sq]
  have hfcont : Continuous f := by
    dsimp [f]
    apply Continuous.inv₀
    · fun_prop
    · intro x hx
      exact (putnam_2021_a4_sin_sq_den_pos a b x ha hab).ne' hx
  have hfint : ∀ t₁ t₂, IntervalIntegrable f volume t₁ t₂ := fun t₁ t₂ =>
    hfcont.intervalIntegrable t₁ t₂
  have hhalf_set :
      (∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), f θ) =
        Real.pi / Real.sqrt (a * (a + b)) := by
    simpa [f] using putnam_2021_a4_integral_Ioo_inv_add_mul_sin_sq a b ha hab
  have hhalf_interval :
      (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), f θ) =
        Real.pi / Real.sqrt (a * (a + b)) := by
    rw [← hhalf_set]
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le]
    linarith [Real.pi_pos]
  have hfour :
      (∫ φ in (-(Real.pi / 2))..(-(Real.pi / 2) + (4 : ℤ) • Real.pi), f φ) =
        (4 : ℤ) • (∫ φ in (-(Real.pi / 2))..(Real.pi / 2), f φ) := by
    have h := hfper.intervalIntegral_add_zsmul_eq (4 : ℤ) (-(Real.pi / 2)) hfint
    convert h using 2
    ring_nf
  have hshift :
      (∫ φ in (-(2 * Real.pi))..(2 * Real.pi), f φ) =
        ∫ φ in (-(Real.pi / 2))..(-(Real.pi / 2) + (4 : ℤ) • Real.pi), f φ := by
    have h := (hfper.zsmul (4 : ℤ)).intervalIntegral_add_eq
      (-(2 * Real.pi)) (-(Real.pi / 2))
    convert h using 2
    norm_num [zsmul_eq_mul]
    ring_nf
  have hbig :
      (∫ φ in (-(2 * Real.pi))..(2 * Real.pi), f φ) =
        4 * (Real.pi / Real.sqrt (a * (a + b))) := by
    rw [hshift, hfour, hhalf_interval]
    norm_num [zsmul_eq_mul]
  have hscale :
      (∫ θ in (-Real.pi)..Real.pi, f (2 * θ)) =
        (2 : ℝ)⁻¹ * (∫ φ in (-(2 * Real.pi))..(2 * Real.pi), f φ) := by
    have h := intervalIntegral.integral_comp_mul_left
      (a := -Real.pi) (b := Real.pi) (c := (2 : ℝ)) f
      (by norm_num : (2 : ℝ) ≠ 0)
    convert h using 2
    ring_nf
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le]
  · change (∫ θ in (-Real.pi)..Real.pi, f (2 * θ)) =
      2 * Real.pi / Real.sqrt (a * (a + b))
    rw [hscale, hbig]
    ring
  · linarith [Real.pi_pos]

private lemma putnam_2021_a4_quartic_angular_integral (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (1 + 2 * r ^ 4 - r ^ 4 * Real.sin (2 * θ) ^ 2)⁻¹) =
      2 * Real.pi / Real.sqrt ((1 + 2 * r ^ 4) * (1 + r ^ 4)) := by
  have ha : 0 < 1 + 2 * r ^ 4 := by positivity
  have hab : 0 < (1 + 2 * r ^ 4) + (-r ^ 4) := by
    nlinarith [sq_nonneg (r ^ 2)]
  have h := putnam_2021_a4_integral_Ioo_neg_pi_pi_inv_add_mul_sin_two_sq
    (1 + 2 * r ^ 4) (-r ^ 4) ha hab
  convert h using 3 <;> ring

private theorem putnam_2021_a4_prod_disk_to_polar
    (R : ℝ) (g : ℝ → ℝ → ℝ) :
    (∫ z in {z : ℝ × ℝ | √(z.1 ^ 2 + z.2 ^ 2) < R}, g z.1 z.2) =
      ∫ p in Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * g (p.1 * Real.cos p.2) (p.1 * Real.sin p.2) := by
  let s : Set (ℝ × ℝ) := {z : ℝ × ℝ | √(z.1 ^ 2 + z.2 ^ 2) < R}
  let t : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
  let G : ℝ × ℝ → ℝ := fun z => g z.1 z.2
  let H : ℝ × ℝ → ℝ := fun p => p.1 * g (p.1 * Real.cos p.2) (p.1 * Real.sin p.2)
  have hs : MeasurableSet s := by
    dsimp [s]
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have ht : MeasurableSet t := by
    dsimp [t]
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : t ⊆ polarCoord.target := by
    intro p hp
    rw [polarCoord_target]
    exact ⟨hp.1.1, hp.2⟩
  have hpol := integral_comp_polarCoord_symm (fun z : ℝ × ℝ => s.indicator G z)
  rw [integral_indicator hs] at hpol
  rw [← hpol]
  have hfun : Set.EqOn
      (fun p : ℝ × ℝ => p.1 • s.indicator G (polarCoord.symm p))
      (t.indicator H) polarCoord.target := by
    intro p hp
    change p.1 • s.indicator G (polarCoord.symm p) = t.indicator H p
    have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
      simpa [polarCoord_target] using hp
    have hsq :
        (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      calc
        (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2
            = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
        _ = p.1 ^ 2 := by
          rw [add_comm, Real.sin_sq_add_cos_sq]
          ring_nf
    have hradius :
        √((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) = p.1 := by
      rw [hsq, Real.sqrt_sq hp'.1.le]
    have hs_iff : (polarCoord.symm p : ℝ × ℝ) ∈ s ↔ p.1 < R := by
      simp [s, polarCoord_symm_apply, hradius]
    have hmem : (polarCoord.symm p : ℝ × ℝ) ∈ s ↔ p ∈ t := by
      constructor
      · intro hps
        exact ⟨⟨hp'.1, hs_iff.mp hps⟩, hp'.2⟩
      · intro hpt
        exact hs_iff.mpr hpt.1.2
    by_cases hpt : p ∈ t
    · have hps : (polarCoord.symm p : ℝ × ℝ) ∈ s := hmem.mpr hpt
      rw [Set.indicator_of_mem hps, Set.indicator_of_mem hpt]
      simp [G, H, polarCoord_symm_apply, smul_eq_mul]
    · have hps : (polarCoord.symm p : ℝ × ℝ) ∉ s := by
        intro hs'
        exact hpt (hmem.mp hs')
      rw [Set.indicator_of_notMem hps, Set.indicator_of_notMem hpt]
      simp
  calc
    (∫ p in polarCoord.target, p.1 • s.indicator G (polarCoord.symm p))
        = ∫ p in polarCoord.target, t.indicator H p := by
          exact setIntegral_congr_fun polarCoord.open_target.measurableSet hfun
    _ = ∫ p, (polarCoord.target).indicator (t.indicator H) p := by
          rw [integral_indicator polarCoord.open_target.measurableSet]
    _ = ∫ p, t.indicator H p := by
          apply integral_congr_ae
          filter_upwards with p
          by_cases hpt : p ∈ t
          · rw [Set.indicator_of_mem (hsub hpt), Set.indicator_of_mem hpt]
          · by_cases hpT : p ∈ polarCoord.target
            · rw [Set.indicator_of_mem hpT, Set.indicator_of_notMem hpt]
            · rw [Set.indicator_of_notMem hpT, Set.indicator_of_notMem hpt]
    _ = ∫ p in t, H p := by rw [integral_indicator ht]
    _ = ∫ p in Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * g (p.1 * Real.cos p.2) (p.1 * Real.sin p.2) := rfl

private lemma putnam_2021_a4_cos_sq_integral_eq_sin_sq
    (ψ : ℝ → ℝ) (hper : Function.Periodic ψ (Real.pi / 2)) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, Real.cos θ ^ 2 * ψ θ) =
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, Real.sin θ ^ 2 * ψ θ := by
  let f : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * ψ θ
  have hconv : (fun θ => Real.cos θ ^ 2 * ψ θ) = fun θ => f (θ + Real.pi / 2) := by
    funext θ
    dsimp [f]
    rw [hper θ]
    simp [Real.sin_add_pi_div_two]
  have hfper_pi : Function.Periodic f Real.pi := by
    intro θ
    dsimp [f]
    have hψ : ψ (θ + Real.pi) = ψ θ := by
      have h := hper.nat_mul 2 θ
      convert h using 2
      ring
    rw [hψ]
    simp [Real.sin_add_pi]
  have hfper_two : Function.Periodic f (2 * Real.pi) := by
    exact hfper_pi.nat_mul 2
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, Real.cos θ ^ 2 * ψ θ)
        = ∫ θ in (-Real.pi)..Real.pi, Real.cos θ ^ 2 * ψ θ := by
          rw [← integral_Ioc_eq_integral_Ioo]
          rw [← intervalIntegral.integral_of_le hle]
    _ = ∫ θ in (-Real.pi)..Real.pi, f (θ + Real.pi / 2) := by rw [hconv]
    _ = ∫ θ in (-Real.pi + Real.pi / 2)..(Real.pi + Real.pi / 2), f θ := by
          rw [intervalIntegral.integral_comp_add_right]
    _ = ∫ θ in (-Real.pi)..Real.pi, f θ := by
          have hshift := hfper_two.intervalIntegral_add_eq (-Real.pi / 2) (-Real.pi)
          convert hshift using 2 <;> ring
    _ = ∫ θ in Set.Ioo (-Real.pi) Real.pi, Real.sin θ ^ 2 * ψ θ := by
          rw [← integral_Ioc_eq_integral_Ioo]
          rw [← intervalIntegral.integral_of_le hle]

private lemma putnam_2021_a4_cos_sq_integral_half
    (ψ : ℝ → ℝ) (hper : Function.Periodic ψ (Real.pi / 2))
    (hcont : Continuous ψ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, Real.cos θ ^ 2 * ψ θ) =
      (1 / 2 : ℝ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ := by
  let s : Set ℝ := Set.Ioo (-Real.pi) Real.pi
  have hs : MeasurableSet s := measurableSet_Ioo
  have hcoscont : Continuous (fun θ => Real.cos θ ^ 2 * ψ θ) := by fun_prop
  have hsincont : Continuous (fun θ => Real.sin θ ^ 2 * ψ θ) := by fun_prop
  have hcosint : IntegrableOn (fun θ => Real.cos θ ^ 2 * ψ θ) s := by
    exact (hcoscont.integrableOn_Icc : IntegrableOn (fun θ => Real.cos θ ^ 2 * ψ θ)
      (Set.Icc (-Real.pi) Real.pi)).mono_set Set.Ioo_subset_Icc_self
  have hsinint : IntegrableOn (fun θ => Real.sin θ ^ 2 * ψ θ) s := by
    exact (hsincont.integrableOn_Icc : IntegrableOn (fun θ => Real.sin θ ^ 2 * ψ θ)
      (Set.Icc (-Real.pi) Real.pi)).mono_set Set.Ioo_subset_Icc_self
  have hsum :
      (∫ θ in s, Real.cos θ ^ 2 * ψ θ) + (∫ θ in s, Real.sin θ ^ 2 * ψ θ) =
        ∫ θ in s, ψ θ := by
    rw [← integral_add hcosint hsinint]
    exact setIntegral_congr_fun hs (by
      intro θ hθ
      calc
        Real.cos θ ^ 2 * ψ θ + Real.sin θ ^ 2 * ψ θ
            = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * ψ θ := by ring
        _ = ψ θ := by
          rw [add_comm, Real.sin_sq_add_cos_sq]
          ring)
  have hcs := putnam_2021_a4_cos_sq_integral_eq_sin_sq ψ hper
  dsimp [s] at hsum ⊢
  linarith

private lemma putnam_2021_a4_sin_sq_integral_half
    (ψ : ℝ → ℝ) (hper : Function.Periodic ψ (Real.pi / 2))
    (hcont : Continuous ψ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, Real.sin θ ^ 2 * ψ θ) =
      (1 / 2 : ℝ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ := by
  rw [← putnam_2021_a4_cos_sq_integral_eq_sin_sq ψ hper]
  exact putnam_2021_a4_cos_sq_integral_half ψ hper hcont

private noncomputable def putnam_2021_a4_kernel (t : ℝ) : ℝ :=
  (1 + t) / (Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + 2 * t ^ 2))

private lemma putnam_2021_a4_kernel_cont : Continuous putnam_2021_a4_kernel := by
  unfold putnam_2021_a4_kernel
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

private lemma putnam_2021_a4_first_kernel_form (t : ℝ) :
    (1 + t) * (2 * Real.pi / Real.sqrt ((1 + t ^ 2) * (1 + 2 * t ^ 2))) =
      2 * Real.pi * putnam_2021_a4_kernel t := by
  unfold putnam_2021_a4_kernel
  rw [Real.sqrt_mul]
  · ring
  · positivity

private lemma putnam_2021_a4_second_kernel_form (t : ℝ) :
    (1 + t / 2) * (2 * Real.pi / Real.sqrt ((2 + t ^ 2) * (2 + t ^ 2 / 2))) =
      Real.pi * putnam_2021_a4_kernel (t / 2) := by
  unfold putnam_2021_a4_kernel
  have h1 : 1 + (t / 2) ^ 2 = (4 + t ^ 2) / 4 := by ring
  have h2 : 1 + 2 * (t / 2) ^ 2 = (2 + t ^ 2) / 2 := by ring
  rw [h1, h2]
  have hsqrt1 : Real.sqrt ((4 + t ^ 2) / 4) = Real.sqrt (4 + t ^ 2) / 2 := by
    rw [Real.sqrt_div]
    · norm_num
    · positivity
  have hsqrt2 : Real.sqrt ((2 + t ^ 2) / 2) =
      Real.sqrt (2 + t ^ 2) / Real.sqrt 2 := by
    rw [Real.sqrt_div]
    positivity
  rw [hsqrt1, hsqrt2]
  rw [Real.sqrt_mul]
  · have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have hsrel : Real.sqrt (4 + t ^ 2) =
        Real.sqrt (2 + t ^ 2 / 2) * Real.sqrt 2 := by
      rw [← Real.sqrt_mul]
      · congr 1
        ring_nf
      · positivity
    field_simp [Real.pi_ne_zero, hs2]
    rw [hsrel]
    ring_nf
  · positivity

private lemma putnam_2021_a4_kernel_upper {t : ℝ} (ht : 1 ≤ t) :
    putnam_2021_a4_kernel t ≤ (Real.sqrt 2)⁻¹ * (t⁻¹ + t⁻¹ ^ 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hApos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg t])
  have hBpos : 0 < Real.sqrt (1 + 2 * t ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg t])
  have hA : t ≤ Real.sqrt (1 + t ^ 2) := by
    rw [Real.le_sqrt ht0.le (by nlinarith [sq_nonneg t])]
    nlinarith
  have hB : Real.sqrt 2 * t ≤ Real.sqrt (1 + 2 * t ^ 2) := by
    rw [Real.le_sqrt (mul_nonneg (Real.sqrt_nonneg _) ht0.le)
      (by nlinarith [sq_nonneg t])]
    have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg t]
  have hden : Real.sqrt 2 * t ^ 2 ≤
      Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + 2 * t ^ 2) := by
    calc
      Real.sqrt 2 * t ^ 2 = t * (Real.sqrt 2 * t) := by ring
      _ ≤ Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + 2 * t ^ 2) := by
        exact mul_le_mul hA hB (mul_nonneg (Real.sqrt_nonneg _) ht0.le) hApos.le
  have hdiv := div_le_div_of_nonneg_left (by nlinarith : 0 ≤ 1 + t)
    (mul_pos hs2pos (sq_pos_of_pos ht0)) hden
  unfold putnam_2021_a4_kernel
  calc
    (1 + t) / (Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + 2 * t ^ 2))
        ≤ (1 + t) / (Real.sqrt 2 * t ^ 2) := hdiv
    _ = (Real.sqrt 2)⁻¹ * (t⁻¹ + t⁻¹ ^ 2) := by
      field_simp [ht0.ne', hs2pos.ne']
      ring

private lemma putnam_2021_a4_kernel_lower {t : ℝ} (ht : 1 ≤ t) :
    (Real.sqrt 2)⁻¹ * (t⁻¹ - t⁻¹ ^ 2) ≤ putnam_2021_a4_kernel t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht1pos : 0 < t + 1 := by linarith
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hApos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg t])
  have hBpos : 0 < Real.sqrt (1 + 2 * t ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg t])
  have hA : Real.sqrt (1 + t ^ 2) ≤ t + 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hB : Real.sqrt (1 + 2 * t ^ 2) ≤ Real.sqrt 2 * (t + 1) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith [sq_nonneg (t + 1)]
  have hden : Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + 2 * t ^ 2) ≤
      Real.sqrt 2 * (t + 1) ^ 2 := by
    calc
      Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + 2 * t ^ 2)
          ≤ (t + 1) * (Real.sqrt 2 * (t + 1)) := by
            exact mul_le_mul hA hB (Real.sqrt_nonneg _) (by linarith : 0 ≤ t + 1)
      _ = Real.sqrt 2 * (t + 1) ^ 2 := by ring
  have hdenpos : 0 < Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + 2 * t ^ 2) :=
    mul_pos hApos hBpos
  have hdiv := div_le_div_of_nonneg_left (by nlinarith : 0 ≤ 1 + t) hdenpos hden
  have hbase : (Real.sqrt 2)⁻¹ * (t⁻¹ - t⁻¹ ^ 2) ≤
      (1 + t) / (Real.sqrt 2 * (t + 1) ^ 2) := by
    have hineq : t⁻¹ - t⁻¹ ^ 2 ≤ (t + 1)⁻¹ := by
      field_simp [ht0.ne', ht1pos.ne']
      nlinarith
    calc
      (Real.sqrt 2)⁻¹ * (t⁻¹ - t⁻¹ ^ 2) ≤ (Real.sqrt 2)⁻¹ * (t + 1)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hineq (inv_nonneg.mpr hs2pos.le)
      _ = (1 + t) / (Real.sqrt 2 * (t + 1) ^ 2) := by
        field_simp [hs2pos.ne', ht1pos.ne']
        ring
  unfold putnam_2021_a4_kernel
  exact hbase.trans hdiv

private lemma putnam_2021_a4_inv_sq_interval_bound {X : ℝ} (hX : 2 ≤ X) :
    (∫ t in X / 2..X, t⁻¹ ^ 2) ≤ 2 / X := by
  have hX0 : 0 < X := by linarith
  have hhalfpos : 0 < X / 2 := by linarith
  have hle : X / 2 ≤ X := by linarith
  let s : Set ℝ := Set.uIcc (X / 2) X
  have hne : ∀ t ∈ s, t ≠ 0 := by
    intro t ht
    have htI : t ∈ Set.Icc (X / 2) X := by
      simpa [s, Set.uIcc_of_le hle] using ht
    have htlow : X / 2 ≤ t := htI.1
    have : 0 < t := by linarith
    exact this.ne'
  have hcont_inv : ContinuousOn (fun t : ℝ => t⁻¹) s := by
    exact continuousOn_id.inv₀ hne
  have hfint : IntervalIntegrable (fun t : ℝ => t⁻¹ ^ 2) volume (X / 2) X := by
    exact (hcont_inv.pow 2).intervalIntegrable
  have hcint : IntervalIntegrable (fun _ : ℝ => 4 / X ^ 2) volume (X / 2) X :=
    intervalIntegrable_const
  have hpoint : ∀ t ∈ Set.Icc (X / 2) X, t⁻¹ ^ 2 ≤ 4 / X ^ 2 := by
    intro t ht
    have htlow : X / 2 ≤ t := ht.1
    have htpos : 0 < t := by linarith
    have hsq : (X / 2) ^ 2 ≤ t ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg hhalfpos.le, abs_of_nonneg htpos.le]
        exact htlow)
    have hden : X ^ 2 / 4 ≤ t ^ 2 := by nlinarith
    have hposden : 0 < X ^ 2 / 4 := by positivity
    have h := one_div_le_one_div_of_le hposden hden
    calc
      t⁻¹ ^ 2 = 1 / t ^ 2 := by field_simp [htpos.ne']
      _ ≤ 1 / (X ^ 2 / 4) := h
      _ = 4 / X ^ 2 := by field_simp [hX0.ne']
  have hmono := intervalIntegral.integral_mono_on hle hfint hcint hpoint
  calc
    (∫ t in X / 2..X, t⁻¹ ^ 2) ≤ ∫ _t in X / 2..X, 4 / X ^ 2 := hmono
    _ = 2 / X := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
      field_simp [hX0.ne']
      ring

private lemma putnam_2021_a4_inv_interval_eq_log_two {X : ℝ} (hX : 0 < X) :
    (∫ t in X / 2..X, t⁻¹) = Real.log 2 := by
  have hhalf : 0 < X / 2 := by positivity
  rw [integral_inv_of_pos hhalf hX]
  congr 1
  field_simp [hX.ne']

private lemma putnam_2021_a4_kernel_interval_error_bound {X : ℝ} (hX : 2 ≤ X) :
    |(∫ t in X / 2..X, putnam_2021_a4_kernel t) -
        (Real.sqrt 2)⁻¹ * Real.log 2| ≤
      (Real.sqrt 2)⁻¹ * (2 / X) := by
  have hX0 : 0 < X := by linarith
  have hle : X / 2 ≤ X := by linarith
  let c : ℝ := (Real.sqrt 2)⁻¹
  let s : Set ℝ := Set.uIcc (X / 2) X
  have hc_nonneg : 0 ≤ c := by positivity
  have hne : ∀ t ∈ s, t ≠ 0 := by
    intro t ht
    have htI : t ∈ Set.Icc (X / 2) X := by
      simpa [s, Set.uIcc_of_le hle] using ht
    have htlow : X / 2 ≤ t := htI.1
    have : 0 < t := by linarith
    exact this.ne'
  have hinvcont : ContinuousOn (fun t : ℝ => t⁻¹) s := continuousOn_id.inv₀ hne
  have hinvint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (X / 2) X :=
    hinvcont.intervalIntegrable
  have hinvsqint : IntervalIntegrable (fun t : ℝ => t⁻¹ ^ 2) volume (X / 2) X :=
    (hinvcont.pow 2).intervalIntegrable
  have hlowint :
      IntervalIntegrable (fun t : ℝ => c * (t⁻¹ - t⁻¹ ^ 2)) volume (X / 2) X :=
    (hinvint.sub hinvsqint).const_mul c
  have hupint :
      IntervalIntegrable (fun t : ℝ => c * (t⁻¹ + t⁻¹ ^ 2)) volume (X / 2) X :=
    (hinvint.add hinvsqint).const_mul c
  have hKint : IntervalIntegrable putnam_2021_a4_kernel volume (X / 2) X :=
    putnam_2021_a4_kernel_cont.intervalIntegrable _ _
  have hlow_mono :
      ∫ t in X / 2..X, c * (t⁻¹ - t⁻¹ ^ 2) ≤
        ∫ t in X / 2..X, putnam_2021_a4_kernel t := by
    refine intervalIntegral.integral_mono_on hle hlowint hKint ?_
    intro t ht
    have htlow : X / 2 ≤ t := ht.1
    have ht1 : 1 ≤ t := by linarith
    simpa [c] using putnam_2021_a4_kernel_lower ht1
  have hup_mono :
      ∫ t in X / 2..X, putnam_2021_a4_kernel t ≤
        ∫ t in X / 2..X, c * (t⁻¹ + t⁻¹ ^ 2) := by
    refine intervalIntegral.integral_mono_on hle hKint hupint ?_
    intro t ht
    have htlow : X / 2 ≤ t := ht.1
    have ht1 : 1 ≤ t := by linarith
    simpa [c] using putnam_2021_a4_kernel_upper ht1
  have hJle : (∫ t in X / 2..X, t⁻¹ ^ 2) ≤ 2 / X :=
    putnam_2021_a4_inv_sq_interval_bound hX
  have hlow_eval :
      (∫ t in X / 2..X, c * (t⁻¹ - t⁻¹ ^ 2)) =
        c * Real.log 2 - c * (∫ t in X / 2..X, t⁻¹ ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hinvint hinvsqint,
      putnam_2021_a4_inv_interval_eq_log_two hX0]
    ring
  have hup_eval :
      (∫ t in X / 2..X, c * (t⁻¹ + t⁻¹ ^ 2)) =
        c * Real.log 2 + c * (∫ t in X / 2..X, t⁻¹ ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hinvint hinvsqint,
      putnam_2021_a4_inv_interval_eq_log_two hX0]
    ring
  have h_upper :
      (∫ t in X / 2..X, putnam_2021_a4_kernel t) - c * Real.log 2 ≤ c * (2 / X) := by
    have htmp :
        (∫ t in X / 2..X, putnam_2021_a4_kernel t) ≤
          c * Real.log 2 + c * (∫ t in X / 2..X, t⁻¹ ^ 2) := by
      exact hup_mono.trans_eq hup_eval
    have htmp2 : c * (∫ t in X / 2..X, t⁻¹ ^ 2) ≤ c * (2 / X) :=
      mul_le_mul_of_nonneg_left hJle hc_nonneg
    linarith
  have h_lower :
      c * Real.log 2 - (∫ t in X / 2..X, putnam_2021_a4_kernel t) ≤ c * (2 / X) := by
    have htmp :
        c * Real.log 2 - c * (∫ t in X / 2..X, t⁻¹ ^ 2) ≤
          (∫ t in X / 2..X, putnam_2021_a4_kernel t) := by
      exact hlow_eval.symm.trans_le hlow_mono
    have htmp2 : c * (∫ t in X / 2..X, t⁻¹ ^ 2) ≤ c * (2 / X) :=
      mul_le_mul_of_nonneg_left hJle hc_nonneg
    linarith
  simpa [c] using (abs_sub_le_iff.mpr ⟨h_upper, h_lower⟩)

private lemma putnam_2021_a4_kernel_interval_tendsto :
    Tendsto (fun X : ℝ => ∫ t in X / 2..X, putnam_2021_a4_kernel t) atTop
      (𝓝 ((Real.sqrt 2)⁻¹ * Real.log 2)) := by
  have hbound : Tendsto (fun X : ℝ => (Real.sqrt 2)⁻¹ * (2 / X)) atTop (𝓝 0) := by
    have h : Tendsto (fun X : ℝ => (2 : ℝ) / X) atTop (𝓝 0) := by
      simpa [id] using
        (tendsto_const_nhds.div_atTop
          (tendsto_id : Tendsto (fun X : ℝ => X) atTop atTop) (a := (2 : ℝ)))
    simpa using (Tendsto.const_mul (Real.sqrt 2)⁻¹ h)
  have habs :
      Tendsto
        (fun X : ℝ =>
          |(∫ t in X / 2..X, putnam_2021_a4_kernel t) -
            (Real.sqrt 2)⁻¹ * Real.log 2|)
        atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun X => abs_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    exact putnam_2021_a4_kernel_interval_error_bound hX
  exact (tendsto_iff_norm_sub_tendsto_zero).2 (by
    simpa [Real.norm_eq_abs] using habs)

private noncomputable def putnam_2021_a4_integrand (x y : ℝ) : ℝ :=
  (1 + 2 * x ^ 2) / (1 + x ^ 4 + 6 * x ^ 2 * y ^ 2 + y ^ 4) -
    (1 + y ^ 2) / (2 + x ^ 4 + y ^ 4)

private lemma putnam_2021_a4_sin_two_sq_shift (θ : ℝ) :
    Real.sin (2 * (θ + Real.pi / 2)) ^ 2 = Real.sin (2 * θ) ^ 2 := by
  have harg : 2 * (θ + Real.pi / 2) = 2 * θ + Real.pi := by ring
  rw [harg, Real.sin_add_pi]
  ring

private lemma putnam_2021_a4_first_angular_integral (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (1 + 2 * r ^ 2 * Real.cos θ ^ 2) /
          (1 + r ^ 4 + r ^ 4 * Real.sin (2 * θ) ^ 2)) =
      2 * Real.pi * putnam_2021_a4_kernel (r ^ 2) := by
  let ψ : ℝ → ℝ := fun θ => (1 + r ^ 4 + r ^ 4 * Real.sin (2 * θ) ^ 2)⁻¹
  have hper : Function.Periodic ψ (Real.pi / 2) := by
    intro θ
    change (1 + r ^ 4 + r ^ 4 * Real.sin (2 * (θ + Real.pi / 2)) ^ 2)⁻¹ =
      (1 + r ^ 4 + r ^ 4 * Real.sin (2 * θ) ^ 2)⁻¹
    rw [putnam_2021_a4_sin_two_sq_shift θ]
  have hcont : Continuous ψ := by
    dsimp [ψ]
    apply Continuous.inv₀
    · fun_prop
    · intro θ
      positivity
  have hψint : IntegrableOn ψ (Set.Ioo (-Real.pi) Real.pi) := by
    exact (ContinuousOn.integrableOn_compact isCompact_Icc hcont.continuousOn).mono_set
      Set.Ioo_subset_Icc_self
  have hcosint : IntegrableOn (fun θ => Real.cos θ ^ 2 * ψ θ)
      (Set.Ioo (-Real.pi) Real.pi) := by
    have hc : Continuous (fun θ => Real.cos θ ^ 2 * ψ θ) := by fun_prop
    exact (ContinuousOn.integrableOn_compact isCompact_Icc hc.continuousOn).mono_set
      Set.Ioo_subset_Icc_self
  have hJ : (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) =
      2 * Real.pi / Real.sqrt ((1 + r ^ 4) * (1 + 2 * r ^ 4)) := by
    have ha : 0 < 1 + r ^ 4 := by positivity
    have hab : 0 < (1 + r ^ 4) + r ^ 4 := by positivity
    simpa [ψ, add_assoc, two_mul] using
      putnam_2021_a4_integral_Ioo_neg_pi_pi_inv_add_mul_sin_two_sq
        (1 + r ^ 4) (r ^ 4) ha hab
  calc
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (1 + 2 * r ^ 2 * Real.cos θ ^ 2) /
          (1 + r ^ 4 + r ^ 4 * Real.sin (2 * θ) ^ 2))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ψ θ + (2 * r ^ 2) * (Real.cos θ ^ 2 * ψ θ) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          dsimp [ψ]
          ring
    _ = (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) +
          ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            (2 * r ^ 2) * (Real.cos θ ^ 2 * ψ θ) := by
          rw [integral_add hψint (hcosint.const_mul (2 * r ^ 2))]
    _ = (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) +
          (2 * r ^ 2) * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
            Real.cos θ ^ 2 * ψ θ) := by
          rw [integral_const_mul]
    _ = (1 + r ^ 2) * (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) := by
          rw [putnam_2021_a4_cos_sq_integral_half ψ hper hcont]
          ring
    _ = (1 + r ^ 2) * (2 * Real.pi / Real.sqrt ((1 + r ^ 4) * (1 + 2 * r ^ 4))) := by
          rw [hJ]
    _ = 2 * Real.pi * putnam_2021_a4_kernel (r ^ 2) := by
          convert putnam_2021_a4_first_kernel_form (r ^ 2) using 2
          all_goals ring_nf

private lemma putnam_2021_a4_second_angular_integral (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (1 + r ^ 2 * Real.sin θ ^ 2) /
          (2 + r ^ 4 - (r ^ 4 / 2) * Real.sin (2 * θ) ^ 2)) =
      Real.pi * putnam_2021_a4_kernel (r ^ 2 / 2) := by
  let ψ : ℝ → ℝ := fun θ =>
    (2 + r ^ 4 - r ^ 4 / 2 * Real.sin (2 * θ) ^ 2)⁻¹
  have hdenpos : ∀ θ : ℝ, 0 < 2 + r ^ 4 - r ^ 4 / 2 * Real.sin (2 * θ) ^ 2 := by
    intro θ
    have hs : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
    have hmul : r ^ 4 / 2 * Real.sin (2 * θ) ^ 2 ≤ r ^ 4 / 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have hr4 : 0 ≤ r ^ 4 := by positivity
    nlinarith
  have hper : Function.Periodic ψ (Real.pi / 2) := by
    intro θ
    change (2 + r ^ 4 - r ^ 4 / 2 * Real.sin (2 * (θ + Real.pi / 2)) ^ 2)⁻¹ =
      (2 + r ^ 4 - r ^ 4 / 2 * Real.sin (2 * θ) ^ 2)⁻¹
    rw [putnam_2021_a4_sin_two_sq_shift θ]
  have hcont : Continuous ψ := by
    dsimp [ψ]
    apply Continuous.inv₀
    · fun_prop
    · intro θ
      exact (hdenpos θ).ne'
  have hψint : IntegrableOn ψ (Set.Ioo (-Real.pi) Real.pi) := by
    exact (ContinuousOn.integrableOn_compact isCompact_Icc hcont.continuousOn).mono_set
      Set.Ioo_subset_Icc_self
  have hsinint : IntegrableOn (fun θ => Real.sin θ ^ 2 * ψ θ)
      (Set.Ioo (-Real.pi) Real.pi) := by
    have hc : Continuous (fun θ => Real.sin θ ^ 2 * ψ θ) := by fun_prop
    exact (ContinuousOn.integrableOn_compact isCompact_Icc hc.continuousOn).mono_set
      Set.Ioo_subset_Icc_self
  have hJ : (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) =
      2 * Real.pi / Real.sqrt ((2 + r ^ 4) * (2 + r ^ 4 / 2)) := by
    have ha : 0 < 2 + r ^ 4 := by positivity
    have hab : 0 < (2 + r ^ 4) + (-(r ^ 4 / 2)) := by
      nlinarith [sq_nonneg (r ^ 2)]
    have h := putnam_2021_a4_integral_Ioo_neg_pi_pi_inv_add_mul_sin_two_sq
        (2 + r ^ 4) (-(r ^ 4 / 2)) ha hab
    convert h using 3
    all_goals ring
  calc
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (1 + r ^ 2 * Real.sin θ ^ 2) /
          (2 + r ^ 4 - (r ^ 4 / 2) * Real.sin (2 * θ) ^ 2))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ψ θ + r ^ 2 * (Real.sin θ ^ 2 * ψ θ) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          dsimp [ψ]
          ring
    _ = (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) +
          ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            r ^ 2 * (Real.sin θ ^ 2 * ψ θ) := by
          rw [integral_add hψint (hsinint.const_mul (r ^ 2))]
    _ = (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) +
          r ^ 2 * (∫ θ in Set.Ioo (-Real.pi) Real.pi,
            Real.sin θ ^ 2 * ψ θ) := by
          rw [integral_const_mul]
    _ = (1 + r ^ 2 / 2) * (∫ θ in Set.Ioo (-Real.pi) Real.pi, ψ θ) := by
          rw [putnam_2021_a4_sin_sq_integral_half ψ hper hcont]
          ring
    _ = (1 + r ^ 2 / 2) * (2 * Real.pi / Real.sqrt ((2 + r ^ 4) * (2 + r ^ 4 / 2))) := by
          rw [hJ]
    _ = Real.pi * putnam_2021_a4_kernel (r ^ 2 / 2) := by
          convert putnam_2021_a4_second_kernel_form (r ^ 2) using 2
          all_goals ring_nf

private lemma putnam_2021_a4_integrand_polar_form (r θ : ℝ) :
    putnam_2021_a4_integrand (r * Real.cos θ) (r * Real.sin θ) =
      ((1 + 2 * r ^ 2 * Real.cos θ ^ 2) /
          (1 + r ^ 4 + r ^ 4 * Real.sin (2 * θ) ^ 2) -
        (1 + r ^ 2 * Real.sin θ ^ 2) /
          (2 + r ^ 4 - (r ^ 4 / 2) * Real.sin (2 * θ) ^ 2)) := by
  unfold putnam_2021_a4_integrand
  have hD1 :
      1 + (r * Real.cos θ) ^ 4 + 6 * (r * Real.cos θ) ^ 2 * (r * Real.sin θ) ^ 2 +
          (r * Real.sin θ) ^ 4 =
        1 + r ^ 4 + r ^ 4 * Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]
    have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    calc
      1 + (r * Real.cos θ) ^ 4 + 6 * (r * Real.cos θ) ^ 2 * (r * Real.sin θ) ^ 2 +
          (r * Real.sin θ) ^ 4 =
          1 + r ^ 4 * ((Real.cos θ ^ 2 + Real.sin θ ^ 2) ^ 2 +
            4 * Real.cos θ ^ 2 * Real.sin θ ^ 2) := by ring
      _ = 1 + r ^ 4 + r ^ 4 * (2 * Real.sin θ * Real.cos θ) ^ 2 := by
        rw [h]
        ring
  have hD2 :
      2 + (r * Real.cos θ) ^ 4 + (r * Real.sin θ) ^ 4 =
        2 + r ^ 4 - (r ^ 4 / 2) * Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]
    have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    calc
      2 + (r * Real.cos θ) ^ 4 + (r * Real.sin θ) ^ 4 =
          2 + r ^ 4 * ((Real.cos θ ^ 2 + Real.sin θ ^ 2) ^ 2 -
            2 * Real.cos θ ^ 2 * Real.sin θ ^ 2) := by ring
      _ = 2 + r ^ 4 - (r ^ 4 / 2) * (2 * Real.sin θ * Real.cos θ) ^ 2 := by
        rw [h]
        ring
  rw [hD1, hD2]
  ring

private lemma putnam_2021_a4_angular_integral (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_integrand (r * Real.cos θ) (r * Real.sin θ)) =
      2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
        (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2)) := by
  let A : ℝ → ℝ := fun θ =>
    (1 + 2 * r ^ 2 * Real.cos θ ^ 2) /
      (1 + r ^ 4 + r ^ 4 * Real.sin (2 * θ) ^ 2)
  let B : ℝ → ℝ := fun θ =>
    (1 + r ^ 2 * Real.sin θ ^ 2) /
      (2 + r ^ 4 - (r ^ 4 / 2) * Real.sin (2 * θ) ^ 2)
  have hBdenpos : ∀ θ : ℝ, 0 < 2 + r ^ 4 - r ^ 4 / 2 * Real.sin (2 * θ) ^ 2 := by
    intro θ
    have hs : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
    have hmul : r ^ 4 / 2 * Real.sin (2 * θ) ^ 2 ≤ r ^ 4 / 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have hr4 : 0 ≤ r ^ 4 := by positivity
    nlinarith
  have hAcont : Continuous A := by
    dsimp [A]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ
      positivity
  have hBcont : Continuous B := by
    dsimp [B]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ
      exact (hBdenpos θ).ne'
  have hAint : IntegrableOn A (Set.Ioo (-Real.pi) Real.pi) := by
    exact (ContinuousOn.integrableOn_compact isCompact_Icc hAcont.continuousOn).mono_set
      Set.Ioo_subset_Icc_self
  have hBint : IntegrableOn B (Set.Ioo (-Real.pi) Real.pi) := by
    exact (ContinuousOn.integrableOn_compact isCompact_Icc hBcont.continuousOn).mono_set
      Set.Ioo_subset_Icc_self
  calc
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      putnam_2021_a4_integrand (r * Real.cos θ) (r * Real.sin θ))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi, A θ - B θ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          dsimp [A, B]
          exact putnam_2021_a4_integrand_polar_form r θ
    _ = (∫ θ in Set.Ioo (-Real.pi) Real.pi, A θ) -
          ∫ θ in Set.Ioo (-Real.pi) Real.pi, B θ := by
          rw [integral_sub hAint hBint]
    _ = 2 * Real.pi * putnam_2021_a4_kernel (r ^ 2) -
          Real.pi * putnam_2021_a4_kernel (r ^ 2 / 2) := by
          rw [putnam_2021_a4_first_angular_integral r,
            putnam_2021_a4_second_angular_integral r]
    _ = 2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
        (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2)) := by ring

private lemma putnam_2021_a4_kernel_interval_decomp (X : ℝ) :
    (∫ t in (0 : ℝ)..X,
        Real.pi * (putnam_2021_a4_kernel t -
          (1 / 2) * putnam_2021_a4_kernel (t / 2))) =
      Real.pi * (∫ t in X / 2..X, putnam_2021_a4_kernel t) := by
  let K : ℝ → ℝ := putnam_2021_a4_kernel
  have hKcont : Continuous K := putnam_2021_a4_kernel_cont
  have hK0X : IntervalIntegrable K volume (0 : ℝ) X := hKcont.intervalIntegrable _ _
  have hK0half : IntervalIntegrable K volume (0 : ℝ) (X / 2) := hKcont.intervalIntegrable _ _
  have hKhalfarg : IntervalIntegrable (fun t : ℝ => K (t / 2)) volume (0 : ℝ) X := by
    exact (hKcont.comp (by fun_prop)).intervalIntegrable _ _
  have hscale :
      (∫ t in (0 : ℝ)..X, (1 / 2) * K (t / 2)) =
        ∫ t in (0 : ℝ)..(X / 2), K t := by
    have hcomp := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := X) (c := (1 / 2 : ℝ)) K (by norm_num)
    rw [intervalIntegral.integral_const_mul]
    calc
      (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..X, K (t / 2))
          = (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..X, K ((1 / 2 : ℝ) * t)) := by ring_nf
      _ = (1 / 2 : ℝ) * ((1 / 2 : ℝ)⁻¹ *
            (∫ t in (1 / 2 : ℝ) * 0..(1 / 2 : ℝ) * X, K t)) := by
          rw [hcomp]
          rfl
      _ = ∫ t in (0 : ℝ)..(X / 2), K t := by
          norm_num
          ring_nf
  calc
    (∫ t in (0 : ℝ)..X,
        Real.pi * (putnam_2021_a4_kernel t -
          (1 / 2) * putnam_2021_a4_kernel (t / 2)))
        = Real.pi * (∫ t in (0 : ℝ)..X,
            K t - (1 / 2) * K (t / 2)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = Real.pi * ((∫ t in (0 : ℝ)..X, K t) -
          ∫ t in (0 : ℝ)..X, (1 / 2) * K (t / 2)) := by
          rw [intervalIntegral.integral_sub hK0X (hKhalfarg.const_mul (1 / 2))]
    _ = Real.pi * ((∫ t in (0 : ℝ)..X, K t) -
          ∫ t in (0 : ℝ)..(X / 2), K t) := by
          rw [hscale]
    _ = Real.pi * (∫ t in X / 2..X, K t) := by
          rw [intervalIntegral.integral_interval_sub_left hK0X hK0half]

private lemma putnam_2021_a4_radial_kernel_identity {R : ℝ} (hR : 0 < R) :
    (∫ r in Set.Ioo (0 : ℝ) R,
        r * (2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
          (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2)))) =
      Real.pi * (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t) := by
  let G : ℝ → ℝ := fun t => Real.pi * (putnam_2021_a4_kernel t -
    (1 / 2) * putnam_2021_a4_kernel (t / 2))
  have hGcont : Continuous G := by
    have hcomp : Continuous fun t : ℝ => putnam_2021_a4_kernel (t / 2) :=
      putnam_2021_a4_kernel_cont.comp (by fun_prop)
    dsimp [G]
    exact continuous_const.mul (putnam_2021_a4_kernel_cont.sub (continuous_const.mul hcomp))
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) R, HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x hx
    simpa using (hasDerivAt_pow 2 x : HasDerivAt (fun y : ℝ => y ^ 2) ((2 : ℝ) * x ^ (2 - 1)) x)
  have hf'cont : ContinuousOn (fun x : ℝ => 2 * x) (Set.uIcc (0 : ℝ) R) := by fun_prop
  have hchange := intervalIntegral.integral_comp_smul_deriv
    (a := (0 : ℝ)) (b := R) (f := fun y : ℝ => y ^ 2) (f' := fun x : ℝ => 2 * x)
    (g := G) hderiv hf'cont hGcont
  have hset_to_interval :
      (∫ r in Set.Ioo (0 : ℝ) R,
        r * (2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
          (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2)))) =
        ∫ r in (0 : ℝ)..R,
          r * (2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
            (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2))) := by
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hR.le]
  calc
    (∫ r in Set.Ioo (0 : ℝ) R,
        r * (2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
          (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2))))
        = ∫ r in (0 : ℝ)..R,
          r * (2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
            (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2))) := hset_to_interval
    _ = ∫ t in (0 : ℝ)..R ^ 2, G t := by
          convert hchange using 1
          · apply intervalIntegral.integral_congr
            intro r hr
            dsimp [G]
            change r * (2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) - 1 / 2 *
                putnam_2021_a4_kernel (r ^ 2 / 2))) =
              (2 * r) * (Real.pi * (putnam_2021_a4_kernel (r ^ 2) - 1 / 2 *
                putnam_2021_a4_kernel (r ^ 2 / 2)))
            ring
          · change (∫ t in (0 : ℝ)..R ^ 2, G t) = ∫ x in (0 : ℝ) ^ 2..R ^ 2, G x
            norm_num
    _ = Real.pi * (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t) := by
          simpa [G] using putnam_2021_a4_kernel_interval_decomp (R ^ 2)

private lemma putnam_2021_a4_disk_integral_identity {R : ℝ} (hR : 0 < R) :
    (∫ z in {z : ℝ × ℝ | √(z.1 ^ 2 + z.2 ^ 2) < R},
        putnam_2021_a4_integrand z.1 z.2) =
      Real.pi * (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t) := by
  let rect : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) R ×ˢ Set.Ioo (-Real.pi) Real.pi
  let H : ℝ × ℝ → ℝ := fun p =>
    p.1 * putnam_2021_a4_integrand (p.1 * Real.cos p.2) (p.1 * Real.sin p.2)
  have hHcont : Continuous H := by
    dsimp [H, putnam_2021_a4_integrand]
    apply Continuous.mul
    · fun_prop
    · apply Continuous.sub
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro p
          positivity
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro p
          positivity
  have hHint_volume : IntegrableOn H rect := by
    have hcompact : IsCompact (Set.Icc (0 : ℝ) R ×ˢ Set.Icc (-Real.pi) Real.pi) :=
      isCompact_Icc.prod isCompact_Icc
    have hIcc : IntegrableOn H (Set.Icc (0 : ℝ) R ×ˢ Set.Icc (-Real.pi) Real.pi) :=
      ContinuousOn.integrableOn_compact hcompact hHcont.continuousOn
    exact hIcc.mono_set (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  have hHint_prod : IntegrableOn H rect ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod ℝ ℝ]
  have hpolar :
      (∫ z in {z : ℝ × ℝ | √(z.1 ^ 2 + z.2 ^ 2) < R},
          putnam_2021_a4_integrand z.1 z.2) = ∫ p in rect, H p := by
    simpa [rect, H] using putnam_2021_a4_prod_disk_to_polar R putnam_2021_a4_integrand
  calc
    (∫ z in {z : ℝ × ℝ | √(z.1 ^ 2 + z.2 ^ 2) < R},
        putnam_2021_a4_integrand z.1 z.2)
        = ∫ p in rect, H p := hpolar
    _ = ∫ r in Set.Ioo (0 : ℝ) R, ∫ θ in Set.Ioo (-Real.pi) Real.pi, H (r, θ) := by
          rw [Measure.volume_eq_prod ℝ ℝ]
          simpa [rect] using (setIntegral_prod H hHint_prod)
    _ = ∫ r in Set.Ioo (0 : ℝ) R,
          r * (2 * Real.pi * (putnam_2021_a4_kernel (r ^ 2) -
            (1 / 2) * putnam_2021_a4_kernel (r ^ 2 / 2))) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro r hr
          dsimp [H]
          rw [integral_const_mul]
          rw [putnam_2021_a4_angular_integral r]
    _ = Real.pi * (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t) :=
          putnam_2021_a4_radial_kernel_identity hR

-- ((Real.sqrt 2) / 2) * Real.pi * Real.log 2
/--
Let
\[
I(R) = \iint_{x^2+y^2 \leq R^2} \left( \frac{1+2x^2}{1+x^4+6x^2y^2+y^4} - \frac{1+y^2}{2+x^4+y^4} \right)\,dx\,dy.
\]
Find
\[
\lim_{R \to \infty} I(R),
\]
or show that this limit does not exist.
-/
theorem putnam_2021_a4
  (S : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
  (hS : S = fun R => ball (0 : EuclideanSpace ℝ (Fin 2)) R)
  (I : ℝ → ℝ)
  (hI : I = fun R => ∫ p in S R,
    (1 + 2*(p 0)^2)/(1 + (p 0)^4 + 6*(p 0)^2*(p 1)^2 + (p 1)^4) - (1 + (p 1)^2)/(2 + (p 0)^4 + (p 1)^4)) :
  Tendsto I atTop (𝓝 ((((Real.sqrt 2) / 2) * Real.pi * Real.log 2) : ℝ )) := by
  rw [hI, hS]
  change Tendsto
    (fun R : ℝ => ∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) R,
      putnam_2021_a4_integrand (p 0) (p 1)) atTop
    (𝓝 ((((Real.sqrt 2) / 2) * Real.pi * Real.log 2) : ℝ))
  have hevent :
      (fun R : ℝ => ∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) R,
        putnam_2021_a4_integrand (p 0) (p 1)) =ᶠ[atTop]
        (fun R : ℝ => Real.pi *
          (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    calc
      (∫ p in ball (0 : EuclideanSpace ℝ (Fin 2)) R,
        putnam_2021_a4_integrand (p 0) (p 1))
          = ∫ z : ℝ × ℝ in {z | √(z.1 ^ 2 + z.2 ^ 2) < R},
              putnam_2021_a4_integrand z.1 z.2 :=
            putnam_2021_a4_euclidean_to_prod R putnam_2021_a4_integrand
      _ = Real.pi * (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t) :=
            putnam_2021_a4_disk_integral_identity hR
  have hsq : Tendsto (fun R : ℝ => R ^ (2 : ℕ)) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hK : Tendsto
      (fun R : ℝ => ∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t) atTop
      (𝓝 ((Real.sqrt 2)⁻¹ * Real.log 2)) := by
    simpa [Function.comp_def] using putnam_2021_a4_kernel_interval_tendsto.comp hsq
  have hpi : Tendsto
      (fun R : ℝ => Real.pi *
        (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t)) atTop
      (𝓝 (Real.pi * ((Real.sqrt 2)⁻¹ * Real.log 2))) :=
    hK.const_mul Real.pi
  have hconst : Real.pi * ((Real.sqrt 2)⁻¹ * Real.log 2) =
      (Real.sqrt 2 / 2) * Real.pi * Real.log 2 := by
    have hs : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      have hs0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
      field_simp [hs0]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hs]
    ring
  have hpi' : Tendsto
      (fun R : ℝ => Real.pi *
        (∫ t in R ^ 2 / 2..R ^ 2, putnam_2021_a4_kernel t)) atTop
      (𝓝 ((((Real.sqrt 2) / 2) * Real.pi * Real.log 2) : ℝ)) := by
    simpa [hconst] using hpi
  exact hpi'.congr' hevent.symm
