import Mathlib

open Nat Topology Filter

open MeasureTheory Set
open scoped ENNReal

private lemma putnam_1967_a5_reflected_sqrt_intervalIntegrable (m M : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sqrt (1 - (x - (m + M - x)) ^ 2)) volume m M := by
  have hcont : Continuous (fun x : ℝ => Real.sqrt (1 - (x - (m + M - x)) ^ 2)) := by
    continuity
  exact hcont.intervalIntegrable m M

private lemma putnam_1967_a5_sqrt_one_sub_sq_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.sqrt (1 - u ^ 2)) volume a b := by
  have hcont : Continuous (fun u : ℝ => Real.sqrt (1 - u ^ 2)) := by
    continuity
  exact hcont.intervalIntegrable a b

private lemma putnam_1967_a5_reflected_semicircle_integral (m M : ℝ) :
    (∫ x in m..M, Real.sqrt (1 - (x - (m + M - x)) ^ 2)) =
      (2 : ℝ)⁻¹ * ∫ u in (m - M)..(M - m), Real.sqrt (1 - u ^ 2) := by
  let H : ℝ → ℝ := fun u => Real.sqrt (1 - u ^ 2)
  calc
    (∫ x in m..M, Real.sqrt (1 - (x - (m + M - x)) ^ 2)) =
        ∫ x in m..M, H (2 * x - (m + M)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [H]
      congr 1
      ring
    _ = (2 : ℝ)⁻¹ • ∫ u in (2 * m - (m + M))..(2 * M - (m + M)), H u := by
      exact intervalIntegral.integral_comp_mul_sub (f := H) (a := m) (b := M)
        (c := 2) (d := m + M) (by norm_num)
    _ = (2 : ℝ)⁻¹ * ∫ u in (2 * m - (m + M))..(2 * M - (m + M)), H u := by
      rfl
    _ = (2 : ℝ)⁻¹ * ∫ u in (m - M)..(M - m), H u := by
      congr 1
      ring_nf

private lemma putnam_1967_a5_section_compact_of_compact
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (x : ℝ) :
    IsCompact {y : ℝ | (x, y) ∈ K} := by
  let L : Set (ℝ × ℝ) := K ∩ {p | p.1 = x}
  have hL : IsCompact L := hKc.inter_right (isClosed_eq continuous_fst continuous_const)
  have himg : Prod.snd '' L = {y : ℝ | (x, y) ∈ K} := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp_eq : (x, p.2) = p := by
        ext
        · exact hp.2.symm
        · rfl
      simpa [hp_eq] using hp.1
    · intro hy
      refine ⟨(x, y), ?_, rfl⟩
      exact ⟨hy, rfl⟩
  simpa [himg] using hL.image continuous_snd

private lemma putnam_1967_a5_compact_sections_measure_add_le
    {A B : Set ℝ} (hAc : IsCompact A) (hBc : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) {c : ℝ}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, |a - b| ≤ c) :
    (volume A).toReal + (volume B).toReal ≤ 2 * c := by
  obtain ⟨loA, hloA⟩ := hAc.exists_isLeast hAne
  obtain ⟨hiA, hhiA⟩ := hAc.exists_isGreatest hAne
  obtain ⟨loB, hloB⟩ := hBc.exists_isLeast hBne
  obtain ⟨hiB, hhiB⟩ := hBc.exists_isGreatest hBne
  have hloA_le_hiA : loA ≤ hiA := hhiA.2 hloA.1
  have hloB_le_hiB : loB ≤ hiB := hhiB.2 hloB.1
  have hvolA : (volume A).toReal ≤ hiA - loA := by
    have hsub : A ⊆ Icc loA hiA := fun y hy => ⟨hloA.2 hy, hhiA.2 hy⟩
    have hle : volume A ≤ volume (Icc loA hiA) := measure_mono hsub
    rw [Real.volume_Icc] at hle
    exact ENNReal.toReal_le_of_le_ofReal (sub_nonneg.mpr hloA_le_hiA) hle
  have hvolB : (volume B).toReal ≤ hiB - loB := by
    have hsub : B ⊆ Icc loB hiB := fun y hy => ⟨hloB.2 hy, hhiB.2 hy⟩
    have hle : volume B ≤ volume (Icc loB hiB) := measure_mono hsub
    rw [Real.volume_Icc] at hle
    exact ENNReal.toReal_le_of_le_ofReal (sub_nonneg.mpr hloB_le_hiB) hle
  have h1 : hiA - loB ≤ c := (abs_le.mp (hcross hiA hhiA.1 loB hloB.1)).2
  have h2 : hiB - loA ≤ c := by
    have hneg : -c ≤ loA - hiB := (abs_le.mp (hcross loA hloA.1 hiB hhiB.1)).1
    linarith
  linarith

private theorem putnam_1967_a5_convex_compact_prod_area_le_pi_div_four
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (hconv : Convex ℝ K)
    (hdist : ∀ p ∈ K, ∀ q ∈ K, (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 1) :
    (volume K).toReal ≤ Real.pi / 4 := by
  classical
  by_cases hne : K.Nonempty
  · have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
    have hKfinite : volume K ≠ ∞ := (hKc.measure_lt_top (μ := volume)).ne
    obtain ⟨pmin, hpmin, hmin⟩ := hKc.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨pmax, hpmax, hmax⟩ := hKc.exists_isMaxOn hne continuous_fst.continuousOn
    let m : ℝ := pmin.1
    let M : ℝ := pmax.1
    have hm_le_M : m ≤ M := hmax hpmin
    let F : ℝ → ℝ := fun x => (volume {y : ℝ | (x, y) ∈ K}).toReal
    have hsec_compact : ∀ x, IsCompact {y : ℝ | (x, y) ∈ K} :=
      putnam_1967_a5_section_compact_of_compact hKc
    have hsec_empty_of_lt {x : ℝ} (hx : x < m ∨ M < x) : {y : ℝ | (x, y) ∈ K} = ∅ := by
      ext y
      constructor
      · intro hy
        have hxK : (x, y) ∈ K := hy
        rcases hx with hx | hx
        · exact (not_lt_of_ge (hmin hxK)) hx
        · exact (not_lt_of_ge (hmax hxK)) hx
      · intro hy
        exact False.elim hy
    have hF_zero_out : ∀ x, x ∉ Icc m M → F x = 0 := by
      intro x hx
      have hxlt : x < m ∨ M < x := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hx
        exact hx
      simp [F, hsec_empty_of_lt hxlt]
    have hprod_finite : (volume.prod volume) K ≠ ∞ := by
      simpa [Measure.volume_eq_prod ℝ ℝ] using hKfinite
    have hF_integrable : Integrable F := by
      simpa [F, Measure.real, measureReal_def] using
        (Measure.integrable_measure_prodMk_left (μ := volume) (ν := volume) hKmeas hprod_finite)
    have hvol_eq_global : (volume K).toReal = ∫ x, F x := by
      have h_ae_lt : ∀ᵐ x ∂volume, volume (Prod.mk x ⁻¹' K) < ∞ :=
        Measure.ae_measure_lt_top (μ := volume) (ν := volume) hKmeas hprod_finite
      have h_toReal := integral_toReal (measurable_measure_prodMk_left hKmeas).aemeasurable h_ae_lt
      calc
        (volume K).toReal = ((volume.prod volume) K).toReal := by
          rw [Measure.volume_eq_prod ℝ ℝ]
        _ = (∫⁻ x, volume (Prod.mk x ⁻¹' K) ∂volume).toReal := by
          rw [Measure.prod_apply hKmeas]
        _ = ∫ x, F x := by
          rw [← h_toReal]
          rfl
    have hglobal_eq_set : ∫ x, F x = ∫ x in Icc m M, F x := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Icc m M
      · simp [hx]
      · simp [hx, hF_zero_out x hx]
    have hglobal_eq_interval : ∫ x, F x = ∫ x in m..M, F x := by
      rw [hglobal_eq_set, intervalIntegral.integral_of_le hm_le_M]
      exact setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (α := ℝ) (μ := volume)).symm
    have hsection_nonempty : ∀ x ∈ Icc m M, ({y : ℝ | (x, y) ∈ K}).Nonempty := by
      intro x hx
      by_cases hlt : m < M
      · let t : ℝ := (x - m) / (M - m)
        have ht0 : 0 ≤ t := by
          dsimp [t]
          exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hlt.le)
        have ht1 : t ≤ 1 := by
          dsimp [t]
          have hden : 0 < M - m := sub_pos.mpr hlt
          have hxsub : x - m ≤ M - m := sub_le_sub_right hx.2 m
          calc
            (x - m) / (M - m) ≤ (M - m) / (M - m) :=
              div_le_div_of_nonneg_right hxsub hden.le
            _ = 1 := div_self (ne_of_gt hden)
        let z := AffineMap.lineMap pmin pmax t
        have hzK : z ∈ K := hconv.lineMap_mem hpmin hpmax ⟨ht0, ht1⟩
        have hz1 : z.1 = x := by
          have hlt' : pmin.1 < pmax.1 := by simpa [m, M] using hlt
          have hden : pmax.1 - pmin.1 ≠ 0 := sub_ne_zero.mpr hlt'.ne'
          have hcoord : z.1 = t * (pmax.1 - pmin.1) + pmin.1 := by
            simp [z, AffineMap.lineMap_apply]
          calc
            z.1 = t * (pmax.1 - pmin.1) + pmin.1 := hcoord
            _ = x := by
              dsimp [t, m, M]
              field_simp [hden]
              ring
        exact ⟨z.2, by
          have hz_eq : (x, z.2) = z := by
            ext
            · exact hz1.symm
            · rfl
          simpa [hz_eq] using hzK⟩
      · have hEq : m = M := le_antisymm hm_le_M (le_of_not_gt hlt)
        have hx_eq : x = m := by linarith [hx.1, hx.2, hEq]
        exact ⟨pmin.2, by simpa [hx_eq, m] using hpmin⟩
    have hpair : ∀ x ∈ Icc m M,
        F x + F (m + M - x) ≤ 2 * Real.sqrt (1 - (x - (m + M - x)) ^ 2) := by
      intro x hx
      have hxr : m + M - x ∈ Icc m M := by
        constructor <;> linarith [hx.1, hx.2]
      have hAne := hsection_nonempty x hx
      have hBne := hsection_nonempty (m + M - x) hxr
      have hcross : ∀ a ∈ {y : ℝ | (x, y) ∈ K}, ∀ b ∈ {y : ℝ | (m + M - x, y) ∈ K},
          |a - b| ≤ Real.sqrt (1 - (x - (m + M - x)) ^ 2) := by
        intro a ha b hb
        have hsq := hdist (x, a) ha (m + M - x, b) hb
        have hsq' : (x - (m + M - x)) ^ 2 + (a - b) ^ 2 ≤ 1 := by
          simpa using hsq
        have hle : (a - b) ^ 2 ≤ 1 - (x - (m + M - x)) ^ 2 := by linarith
        exact Real.abs_le_sqrt hle
      change (volume {y : ℝ | (x, y) ∈ K}).toReal +
          (volume {y : ℝ | (m + M - x, y) ∈ K}).toReal ≤
          2 * Real.sqrt (1 - (x - (m + M - x)) ^ 2)
      exact putnam_1967_a5_compact_sections_measure_add_le
        (hsec_compact x) (hsec_compact (m + M - x)) hAne hBne hcross
    have hG_int : IntervalIntegrable (fun x => Real.sqrt (1 - (x - (m + M - x)) ^ 2)) volume m M :=
      putnam_1967_a5_reflected_sqrt_intervalIntegrable m M
    have hF_int : IntervalIntegrable F volume m M := hF_integrable.intervalIntegrable
    have hF_ref_int : IntervalIntegrable (fun x => F (m + M - x)) volume m M := by
      convert (hF_int.comp_sub_left (m + M)).symm using 1 <;> ring
    have hsum_int : IntervalIntegrable (fun x => F x + F (m + M - x)) volume m M :=
      hF_int.add hF_ref_int
    have h_two_int : ∫ x in m..M, (F x + F (m + M - x)) = 2 * ∫ x in m..M, F x := by
      rw [intervalIntegral.integral_add hF_int hF_ref_int]
      have hreflect : ∫ x in m..M, F (m + M - x) = ∫ x in m..M, F x := by
        rw [intervalIntegral.integral_comp_sub_left F (m + M)]
        congr 2 <;> ring
      rw [hreflect]
      ring
    have h_int_pair : ∫ x in m..M, F x ≤
        ∫ x in m..M, Real.sqrt (1 - (x - (m + M - x)) ^ 2) := by
      have hmono : ∫ x in m..M, (fun x => F x + F (m + M - x)) x ≤
          ∫ x in m..M, (fun x => 2 * Real.sqrt (1 - (x - (m + M - x)) ^ 2)) x := by
        apply intervalIntegral.integral_mono_on hm_le_M hsum_int
        · exact hG_int.const_mul 2
        · intro x hx
          exact hpair x hx
      have hnonnegF : 0 ≤ ∫ x in m..M, F x := by
        apply intervalIntegral.integral_nonneg hm_le_M
        intro x hx
        exact ENNReal.toReal_nonneg
      rw [h_two_int] at hmono
      rw [intervalIntegral.integral_const_mul] at hmono
      nlinarith
    have hwidth_sq : (M - m) ^ 2 ≤ 1 := by
      have h := hdist pmax hpmax pmin hpmin
      have h' : (M - m) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (pmax.2 - pmin.2)]
      exact h'
    have hwidth_le_one : M - m ≤ 1 := by
      have hwidth_sq' : (M - m) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using hwidth_sq
      have habs : |M - m| ≤ |(1 : ℝ)| := (sq_le_sq.mp hwidth_sq')
      simpa [abs_of_nonneg (sub_nonneg.mpr hm_le_M)] using habs
    have hsmall_left : -1 ≤ m - M := by linarith
    have hsmall_right : M - m ≤ 1 := hwidth_le_one
    have hH_int_big : IntervalIntegrable (fun u : ℝ => Real.sqrt (1 - u ^ 2)) volume (-1) 1 :=
      putnam_1967_a5_sqrt_one_sub_sq_intervalIntegrable (-1) 1
    have hH_nonneg : 0 ≤ᵐ[volume.restrict (Ioc (-1 : ℝ) 1)]
        (fun u : ℝ => Real.sqrt (1 - u ^ 2)) := by
      filter_upwards with u
      exact Real.sqrt_nonneg _
    have hsemi : ∫ u in (m - M)..(M - m), Real.sqrt (1 - u ^ 2) ≤ Real.pi / 2 := by
      have hle := intervalIntegral.integral_mono_interval hsmall_left
        (by linarith : m - M ≤ M - m) hsmall_right hH_nonneg hH_int_big
      simpa [integral_sqrt_one_sub_sq] using hle
    have hG_le : ∫ x in m..M, Real.sqrt (1 - (x - (m + M - x)) ^ 2) ≤ Real.pi / 4 := by
      rw [putnam_1967_a5_reflected_semicircle_integral m M]
      nlinarith [hsemi]
    calc
      (volume K).toReal = ∫ x, F x := hvol_eq_global
      _ = ∫ x in m..M, F x := hglobal_eq_interval
      _ ≤ ∫ x in m..M, Real.sqrt (1 - (x - (m + M - x)) ^ 2) := h_int_pair
      _ ≤ Real.pi / 4 := hG_le
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hKempty]
    simp
    positivity

private theorem putnam_1967_a5_convex_euclidean_area_le_pi_div_four_of_dist_le_one
    {R : Set (EuclideanSpace ℝ (Fin 2))} (hconv : Convex ℝ R)
    (hdist : ∀ P ∈ R, ∀ Q ∈ R, dist P Q ≤ 1) :
    (volume R).toReal ≤ Real.pi / 4 := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨P0, hP0⟩ := hne
    have hR_subset_ball : R ⊆ Metric.closedBall P0 1 := by
      intro Q hQ
      rw [Metric.mem_closedBall, _root_.dist_comm]
      exact hdist P0 hP0 Q hQ
    have hclosure_subset_ball : closure R ⊆ Metric.closedBall P0 1 :=
      closure_minimal hR_subset_ball Metric.isClosed_closedBall
    have hclosure_compact : IsCompact (closure R) :=
      (ProperSpace.isCompact_closedBall P0 1).of_isClosed_subset isClosed_closure hclosure_subset_ball
    let phi : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun x =>
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) (WithLp.ofLp x)
    let K : Set (ℝ × ℝ) := phi '' closure R
    have hphicont : Continuous phi := by
      dsimp [phi]
      exact (Homeomorph.piFinTwo (fun _ : Fin 2 => ℝ)).continuous.comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
    have hKc : IsCompact K := hclosure_compact.image hphicont
    have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
    have hconvK : Convex ℝ K := by
      let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ × ℝ :=
        ((LinearEquiv.piFinTwo ℝ (fun _ : Fin 2 => ℝ)).toLinearMap.comp
          (EuclideanSpace.equiv (Fin 2) ℝ).toLinearMap)
      change Convex ℝ (L '' closure R)
      exact hconv.closure.linear_image L
    have hdist_closure : ∀ P ∈ closure R, ∀ Q ∈ closure R, dist P Q ≤ 1 := by
      intro P hP Q hQ
      have hP_to_R : ∀ Q ∈ R, dist P Q ≤ 1 := by
        intro Q hQ
        have hclosed : IsClosed {X : EuclideanSpace ℝ (Fin 2) | dist X Q ≤ 1} :=
          isClosed_le (continuous_id.dist continuous_const) continuous_const
        exact closure_minimal (fun X hX => hdist X hX Q hQ) hclosed hP
      have hclosed : IsClosed {Y : EuclideanSpace ℝ (Fin 2) | dist P Y ≤ 1} :=
        isClosed_le (continuous_const.dist continuous_id) continuous_const
      exact closure_minimal (fun Y hY => hP_to_R Y hY) hclosed hQ
    have hdistK : ∀ p ∈ K, ∀ q ∈ K, (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 1 := by
      rintro p ⟨P, hP, rfl⟩ q ⟨Q, hQ, rfl⟩
      have hPQ : dist P Q ≤ 1 := hdist_closure P hP Q hQ
      have hcoord :
          (((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) (WithLp.ofLp P)).1 -
            ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) (WithLp.ofLp Q)).1) ^ 2 +
          (((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) (WithLp.ofLp P)).2 -
            ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) (WithLp.ofLp Q)).2) ^ 2 =
          dist P Q ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq]
        simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
      rw [hcoord]
      nlinarith [(dist_nonneg : 0 ≤ dist P Q), hPQ]
    have hK_area : (volume K).toReal ≤ Real.pi / 4 :=
      putnam_1967_a5_convex_compact_prod_area_le_pi_div_four hKc hconvK hdistK
    have hphimp : MeasurePreserving phi volume volume :=
      (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))
    have hpre : phi ⁻¹' K = closure R := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hp := congrArg
          (fun p : ℝ × ℝ => (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm p) hxy
        have : y = x := by
          ext i
          fin_cases i
          · simpa [phi] using congrArg (fun f : Fin 2 → ℝ => f 0) hp
          · simpa [phi] using congrArg (fun f : Fin 2 → ℝ => f 1) hp
        simpa [this] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hvolK : volume K = volume (closure R) := by
      calc
        volume K = (Measure.map phi volume) K := by rw [hphimp.map_eq]
        _ = volume (phi ⁻¹' K) := by rw [Measure.map_apply hphimp.measurable hKmeas]
        _ = volume (closure R) := by rw [hpre]
    have hclosure_finite : volume (closure R) ≠ ∞ :=
      (hclosure_compact.measure_lt_top (μ := volume)).ne
    calc
      (volume R).toReal ≤ (volume (closure R)).toReal :=
        ENNReal.toReal_mono hclosure_finite (measure_mono subset_closure)
      _ = (volume K).toReal := by rw [hvolK]
      _ ≤ Real.pi / 4 := hK_area
  · have hRempty : R = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hRempty]
    simp
    positivity

/--
Prove that any convex region in the Euclidean plane with area greater than $\pi/4$ contains a pair of points exactly $1$ unit apart.
-/
theorem putnam_1967_a5
(R : Set (EuclideanSpace ℝ (Fin 2)))
(hR : Convex ℝ R ∧ (MeasureTheory.volume R).toReal > Real.pi / 4)
: ∃ P ∈ R, ∃ Q ∈ R, dist P Q = 1 := by
  classical
  by_contra hno
  have hdist_le : ∀ P ∈ R, ∀ Q ∈ R, dist P Q ≤ 1 := by
    intro P hP Q hQ
    by_contra hle
    have hgt : 1 < dist P Q := lt_of_not_ge hle
    let t : ℝ := (dist P Q)⁻¹
    have hdist_pos : 0 < dist P Q := zero_lt_one.trans hgt
    have ht_pos : 0 < t := inv_pos.mpr hdist_pos
    have ht_le_one : t ≤ 1 := by
      dsimp [t]
      exact inv_le_one_of_one_le₀ hgt.le
    have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_pos.le, ht_le_one⟩
    let S := AffineMap.lineMap P Q t
    have hS : S ∈ R := hR.1.lineMap_mem hP hQ ht_mem
    have hdist : dist P S = 1 := by
      dsimp [S, t]
      rw [_root_.dist_comm, dist_lineMap_left]
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdist_pos)]
      exact inv_mul_cancel₀ (ne_of_gt hdist_pos)
    exact hno ⟨P, hP, S, hS, hdist⟩
  have harea_le : (MeasureTheory.volume R).toReal ≤ Real.pi / 4 := by
    exact putnam_1967_a5_convex_euclidean_area_le_pi_div_four_of_dist_le_one hR.1 hdist_le
  exact (not_lt_of_ge harea_le) hR.2
