import Mathlib

open Nat Topology Filter
open MeasureTheory
open scoped ENNReal

private lemma integral_sqrt_one_sub_sq_left :
    ∫ x in (-1 : ℝ)..0, √(1 - x ^ 2) = Real.pi / 4 := by
  let f : ℝ → ℝ := fun x => √(1 - x ^ 2)
  have h_even : ∀ x, f (-x) = f x := by
    intro x
    simp [f]
  have h_left_eq_right : ∫ x in (-1 : ℝ)..0, f x = ∫ x in (0 : ℝ)..1, f x := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := 1)
    simpa [h_even] using h.symm
  have hsum :
      (∫ x in (-1 : ℝ)..0, f x) + (∫ x in (0 : ℝ)..1, f x) =
        ∫ x in (-1 : ℝ)..1, f x := by
    refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
    · exact (by fun_prop : Continuous f).intervalIntegrable _ _
    · exact (by fun_prop : Continuous f).intervalIntegrable _ _
  have hfull : ∫ x in (-1 : ℝ)..1, f x = Real.pi / 2 := by
    simpa [f] using integral_sqrt_one_sub_sq
  nlinarith [hsum, h_left_eq_right, hfull]

private lemma real_volume_add_le_two_mul_of_forall_abs_sub_le
    {A B : Set ℝ} {C : ℝ}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, |a - b| ≤ C) :
    (volume A).toReal + (volume B).toReal ≤ 2 * C := by
  rcases hAne with ⟨a0, ha0⟩
  rcases hBne with ⟨b0, hb0⟩
  have hAne' : A.Nonempty := ⟨a0, ha0⟩
  have hBne' : B.Nonempty := ⟨b0, hb0⟩
  have hAbdd : Bornology.IsBounded A := by
    refine (Metric.isBounded_iff_subset_closedBall b0).2 ?_
    refine ⟨C, fun a ha => ?_⟩
    simpa [Real.dist_eq] using hAB a ha b0 hb0
  have hBbdd : Bornology.IsBounded B := by
    refine (Metric.isBounded_iff_subset_closedBall a0).2 ?_
    refine ⟨C, fun b hb => ?_⟩
    simpa [Real.dist_eq, abs_sub_comm] using hAB a0 ha0 b hb
  have hwidthA_nonneg : 0 ≤ sSup A - sInf A :=
    sub_nonneg.mpr (Real.sInf_le_sSup A hAbdd.bddBelow hAbdd.bddAbove)
  have hwidthB_nonneg : 0 ≤ sSup B - sInf B :=
    sub_nonneg.mpr (Real.sInf_le_sSup B hBbdd.bddBelow hBbdd.bddAbove)
  have hvolA : (volume A).toReal ≤ sSup A - sInf A := by
    have hle : volume A ≤ ENNReal.ofReal (sSup A - sInf A) := by
      simpa [Real.ediam_eq hAbdd] using Real.volume_le_diam A
    calc
      (volume A).toReal ≤ (ENNReal.ofReal (sSup A - sInf A)).toReal :=
        ENNReal.toReal_mono (by simp) hle
      _ = sSup A - sInf A := ENNReal.toReal_ofReal hwidthA_nonneg
  have hvolB : (volume B).toReal ≤ sSup B - sInf B := by
    have hle : volume B ≤ ENNReal.ofReal (sSup B - sInf B) := by
      simpa [Real.ediam_eq hBbdd] using Real.volume_le_diam B
    calc
      (volume B).toReal ≤ (ENNReal.ofReal (sSup B - sInf B)).toReal :=
        ENNReal.toReal_mono (by simp) hle
      _ = sSup B - sInf B := ENNReal.toReal_ofReal hwidthB_nonneg
  have hsupA_le : sSup A - sInf B ≤ C := by
    have hs : sSup A ≤ sInf B + C := by
      refine csSup_le hAne' ?_
      intro a ha
      have hb : a - C ≤ sInf B := by
        refine le_csInf hBne' ?_
        intro b hb
        have h := hAB a ha b hb
        rw [abs_le] at h
        linarith
      linarith
    linarith
  have hsupB_le : sSup B - sInf A ≤ C := by
    have hs : sSup B ≤ sInf A + C := by
      refine csSup_le hBne' ?_
      intro b hb
      have ha : b - C ≤ sInf A := by
        refine le_csInf hAne' ?_
        intro a ha
        have h := hAB a ha b hb
        rw [abs_le] at h
        linarith
      linarith
    linarith
  linarith

private def verticalSlice (K : Set (ℝ × ℝ)) (x : ℝ) : Set ℝ :=
  {y | (x, y) ∈ K}

private lemma compact_prod_volume_eq_lintegral_verticalSlice
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) :
    let m : ℝ → ℝ≥0∞ := fun x => volume (verticalSlice K x)
    volume K = ∫⁻ x, m x := by
  intro m
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply hKmeas]
  apply lintegral_congr
  intro x
  rfl

private lemma verticalSlice_volume_lt_top
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (x : ℝ) :
    volume (verticalSlice K x) < ⊤ := by
  have hYbdd : Bornology.IsBounded (Prod.snd '' K) :=
    (hKc.image continuous_snd).isBounded
  have hslice_bdd : Bornology.IsBounded (verticalSlice K x) := by
    refine hYbdd.subset ?_
    intro y hy
    exact ⟨(x, y), hy, rfl⟩
  exact hslice_bdd.measure_lt_top

private lemma verticalSlice_volume_aemeasurable
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) :
    let m : ℝ → ℝ≥0∞ := fun x => volume (verticalSlice K x)
    AEMeasurable m volume := by
  intro m
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  have hm : Measurable fun x : ℝ => volume (Prod.mk x ⁻¹' K) :=
    measurable_measure_prodMk_left hKmeas
  refine hm.aemeasurable.congr ?_
  exact Eventually.of_forall fun _ => rfl

private lemma verticalSlice_volume_toReal_integrable
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) :
    let m : ℝ → ℝ≥0∞ := fun x => volume (verticalSlice K x)
    Integrable (fun x => (m x).toReal) := by
  intro m
  have hm : AEMeasurable m volume := verticalSlice_volume_aemeasurable hKc
  have hmne : ∀ᵐ x : ℝ, m x ≠ ∞ :=
    Eventually.of_forall fun x => ne_of_lt (verticalSlice_volume_lt_top hKc x)
  rw [integrable_toReal_iff hm hmne]
  have hvol_lt : volume K < ⊤ := hKc.measure_lt_top
  have hvol_eq : volume K = ∫⁻ x, m x :=
    compact_prod_volume_eq_lintegral_verticalSlice hKc
  rw [← hvol_eq]
  exact ne_of_lt hvol_lt

private lemma integral_verticalSlice_eq_integral_projection_interval
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) :
    let X : Set ℝ := Prod.fst '' K
    let a : ℝ := sInf X
    let b : ℝ := sSup X
    let m : ℝ → ℝ≥0∞ := fun x => volume (verticalSlice K x)
    let mr : ℝ → ℝ := fun x => (m x).toReal
    Integrable mr → ∫ x, mr x = ∫ x in Set.Icc a b, mr x := by
  intro X a b m mr hint
  have hXc : IsCompact X := hKc.image continuous_fst
  have hXbdd : Bornology.IsBounded X := hXc.isBounded
  have hcomp_zero : ∫ x in (Set.Icc a b)ᶜ, mr x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    have hslice_empty : verticalSlice K x = ∅ := by
      ext y
      constructor
      · intro hy
        have hxX : x ∈ X := ⟨(x, y), hy, rfl⟩
        have hxI : x ∈ Set.Icc a b := by
          constructor
          · exact csInf_le hXbdd.bddBelow hxX
          · exact le_csSup hXbdd.bddAbove hxX
        exact False.elim (hx hxI)
      · intro hy
        cases hy
    simp [mr, m, hslice_empty]
  have hsum := integral_add_compl (s := Set.Icc a b) measurableSet_Icc hint
  rw [hcomp_zero, add_zero] at hsum
  exact hsum.symm

private lemma verticalSlice_nonempty_of_mem_projection_interval
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) :
    let X : Set ℝ := Prod.fst '' K
    ∀ x ∈ Set.Icc (sInf X) (sSup X), (verticalSlice K x).Nonempty := by
  intro X x hx
  have hXc : IsCompact X := hKc.image continuous_fst
  have hXne : X.Nonempty := hne.image _
  have hXbdd : Bornology.IsBounded X := hXc.isBounded
  have haX : sInf X ∈ X := hXc.isClosed.csInf_mem hXne hXbdd.bddBelow
  have hbX : sSup X ∈ X := hXc.isClosed.csSup_mem hXne hXbdd.bddAbove
  rcases haX with ⟨pa, hpa, hpa1⟩
  rcases hbX with ⟨pb, hpb, hpb1⟩
  by_cases habeq : sSup X = sInf X
  · refine ⟨pa.2, ?_⟩
    have hxeq : x = pa.1 := by
      rw [hpa1]
      exact le_antisymm (by simpa [habeq] using hx.2) hx.1
    simpa [verticalSlice, hxeq]
  · have hablt : sInf X < sSup X := lt_of_le_of_ne ?_ (Ne.symm habeq)
    · let t : ℝ := (x - sInf X) / (sSup X - sInf X)
      have ht0 : 0 ≤ t := by
        dsimp [t]
        exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hablt.le)
      have ht1 : t ≤ 1 := by
        dsimp [t]
        rw [div_le_one (sub_pos.mpr hablt)]
        linarith [hx.2]
      let p : ℝ × ℝ := (1 - t) • pa + t • pb
      have hpK : p ∈ K := by
        refine hconv hpa hpb (sub_nonneg.mpr ht1) ht0 ?_
        ring
      refine ⟨p.2, ?_⟩
      have hp1 : p.1 = x := by
        dsimp [p, t]
        rw [hpa1, hpb1]
        field_simp [sub_ne_zero.mpr (ne_of_gt hablt)]
        ring
      change (x, p.2) ∈ K
      convert hpK using 1
      ext <;> simp [hp1]
    · exact Real.sInf_le_sSup X hXbdd.bddBelow hXbdd.bddAbove

private lemma verticalSlice_reflection_volume_le
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty)
    (hle : ∀ p ∈ K, ∀ q ∈ K,
      √((p.1 - q.1)^2 + (p.2 - q.2)^2) ≤ (1 : ℝ)) :
    let X : Set ℝ := Prod.fst '' K
    let a : ℝ := sInf X
    let b : ℝ := sSup X
    let c : ℝ := (a + b) / 2
    ∀ x ∈ Set.Icc a c,
      (volume (verticalSlice K x)).toReal +
        (volume (verticalSlice K (a + b - x))).toReal ≤
          2 * √(1 - (x - (a + b - x))^2) := by
  intro X a b c x hx
  have hXc : IsCompact X := hKc.image continuous_fst
  have hXne : X.Nonempty := hne.image _
  have hXbdd : Bornology.IsBounded X := hXc.isBounded
  have hab : a ≤ b := Real.sInf_le_sSup X hXbdd.bddBelow hXbdd.bddAbove
  have hxI : x ∈ Set.Icc a b := ⟨hx.1, le_trans hx.2 (by dsimp [c]; linarith)⟩
  have hx'I : a + b - x ∈ Set.Icc a b := by
    constructor
    · linarith [hxI.2]
    · linarith [hx.1]
  have hsne := verticalSlice_nonempty_of_mem_projection_interval hKc hconv hne
  have hAne : (verticalSlice K x).Nonempty := hsne x hxI
  have hBne : (verticalSlice K (a + b - x)).Nonempty := hsne (a + b - x) hx'I
  refine real_volume_add_le_two_mul_of_forall_abs_sub_le hAne hBne ?_
  intro y hy z hz
  have hp : (x, y) ∈ K := hy
  have hq : (a + b - x, z) ∈ K := hz
  have hdist := hle (x, y) hp (a + b - x, z) hq
  have hsum_le : (x - (a + b - x)) ^ 2 + (y - z) ^ 2 ≤ 1 := by
    have := (Real.sqrt_le_left zero_le_one).1 hdist
    simpa using this
  have hy_sq : (y - z) ^ 2 ≤ 1 - (x - (a + b - x)) ^ 2 := by linarith
  calc
    |y - z| = √((y - z) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ √(1 - (x - (a + b - x)) ^ 2) := Real.sqrt_le_sqrt hy_sq

private lemma reflected_semicircle_integral_le_pi_quarter
    {a b c : ℝ} (hc : c = (a + b) / 2) (hab : a ≤ b)
    (hwidth : b - a ≤ 1) :
    (∫ x in a..c, 2 * √(1 - (x - (a + b - x)) ^ 2)) ≤ Real.pi / 4 := by
  let f : ℝ → ℝ := fun t => √(1 - t ^ 2)
  have hfun :
      (fun x : ℝ => 2 * √(1 - (x - (a + b - x)) ^ 2)) =
        fun x : ℝ => 2 * f (2 * x - (a + b)) := by
    funext x
    simp [f]
    ring_nf
  have hsubst :
      (∫ x in a..c, 2 * f (2 * x - (a + b))) =
        ∫ t in (a - b)..0, f t := by
    calc
      (∫ x in a..c, 2 * f (2 * x - (a + b))) =
          2 * ∫ x in a..c, f (2 * x - (a + b)) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ t in (2 * a - (a + b))..(2 * c - (a + b)), f t := by
            have h := intervalIntegral.smul_integral_comp_mul_sub (f := f)
              (a := a) (b := c) (c := (2 : ℝ)) (d := a + b)
            exact h
      _ = ∫ t in (a - b)..0, f t := by
            have hlow : 2 * a - (a + b) = a - b := by ring
            have hhigh : 2 * c - (a + b) = 0 := by linarith
            rw [hlow, hhigh]
  have hleft : (-1 : ℝ) ≤ a - b := by linarith
  have hab0 : a - b ≤ 0 := by linarith
  have hmono : (∫ t in (a - b)..0, f t) ≤ ∫ t in (-1 : ℝ)..0, f t := by
    have hf_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 0)] f :=
      Eventually.of_forall fun _ => Real.sqrt_nonneg _
    have hf_int : IntervalIntegrable f volume (-1 : ℝ) 0 :=
      (by fun_prop : Continuous f).intervalIntegrable _ _
    exact intervalIntegral.integral_mono_interval (a := a - b) (b := 0)
      (c := (-1 : ℝ)) (d := 0) hleft hab0 le_rfl hf_nonneg hf_int
  rw [hfun, hsubst]
  exact hmono.trans_eq integral_sqrt_one_sub_sq_left

private lemma compact_convex_prod_volume_le_pi_quarter
    (K : Set (ℝ × ℝ)) (hKc : IsCompact K) (hconv : Convex ℝ K)
    (hle : ∀ p ∈ K, ∀ q ∈ K,
      √((p.1 - q.1)^2 + (p.2 - q.2)^2) ≤ (1 : ℝ)) :
    (volume K).toReal ≤ Real.pi / 4 := by
  by_cases hne : K.Nonempty
  · let X : Set ℝ := Prod.fst '' K
    let a : ℝ := sInf X
    let b : ℝ := sSup X
    let c : ℝ := (a + b) / 2
    let m : ℝ → ℝ≥0∞ := fun x => volume (verticalSlice K x)
    let mr : ℝ → ℝ := fun x => (m x).toReal
    let g : ℝ → ℝ := fun x => 2 * √(1 - (x - (a + b - x)) ^ 2)
    have hXc : IsCompact X := hKc.image continuous_fst
    have hXne : X.Nonempty := hne.image _
    have hXbdd : Bornology.IsBounded X := hXc.isBounded
    have hab : a ≤ b := Real.sInf_le_sSup X hXbdd.bddBelow hXbdd.bddAbove
    have hac : a ≤ c := by dsimp [c]; linarith
    have hcb : c ≤ b := by dsimp [c]; linarith
    have haX : a ∈ X := hXc.isClosed.csInf_mem hXne hXbdd.bddBelow
    have hbX : b ∈ X := hXc.isClosed.csSup_mem hXne hXbdd.bddAbove
    rcases haX with ⟨pa, hpa, hpa1⟩
    rcases hbX with ⟨pb, hpb, hpb1⟩
    have hsum_le : (pa.1 - pb.1) ^ 2 + (pa.2 - pb.2) ^ 2 ≤ 1 := by
      have hdist := hle pa hpa pb hpb
      simpa using (Real.sqrt_le_left zero_le_one).1 hdist
    have hx_sq_le : (pa.1 - pb.1) ^ 2 ≤ 1 := by
      nlinarith [hsum_le, sq_nonneg (pa.2 - pb.2)]
    have habs : |pa.1 - pb.1| ≤ 1 := by
      calc
        |pa.1 - pb.1| = √((pa.1 - pb.1) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ √(1 : ℝ) := Real.sqrt_le_sqrt hx_sq_le
        _ = 1 := by simp
    have hwidth : b - a ≤ 1 := by
      have hba_abs : |b - a| ≤ 1 := by
        simpa [hpa1, hpb1, abs_sub_comm] using habs
      simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using hba_abs
    have hm_ae : AEMeasurable m volume := verticalSlice_volume_aemeasurable hKc
    have hm_finite : ∀ᵐ x : ℝ, m x < ⊤ :=
      Eventually.of_forall fun x => verticalSlice_volume_lt_top hKc x
    have hmr_int : Integrable mr := verticalSlice_volume_toReal_integrable hKc
    have hvol_real_eq : (volume K).toReal = ∫ x, mr x := by
      have hvol_eq : volume K = ∫⁻ x, m x :=
        compact_prod_volume_eq_lintegral_verticalSlice hKc
      rw [hvol_eq]
      exact (integral_toReal hm_ae hm_finite).symm
    have hglobal_interval :
        ∫ x, mr x = ∫ x in Set.Icc a b, mr x :=
      integral_verticalSlice_eq_integral_projection_interval hKc hmr_int
    have hset_interval :
        ∫ x in Set.Icc a b, mr x = ∫ x in a..b, mr x := by
      rw [intervalIntegral.integral_of_le hab]
      exact integral_Icc_eq_integral_Ioc
    have hmr_ac : IntervalIntegrable mr volume a c := hmr_int.intervalIntegrable
    have hmr_cb : IntervalIntegrable mr volume c b := hmr_int.intervalIntegrable
    have hmr_bc : IntervalIntegrable mr volume b c := hmr_int.intervalIntegrable
    have href_int : IntervalIntegrable (fun x => mr (a + b - x)) volume a c := by
      have h := hmr_bc.comp_sub_left (a + b)
      convert h using 1
      · ring
      · dsimp [c]
        linarith
    have hsplit :
        (∫ x in a..c, mr x) + ∫ x in c..b, mr x = ∫ x in a..b, mr x :=
      intervalIntegral.integral_add_adjacent_intervals hmr_ac hmr_cb
    have hreflect :
        ∫ x in c..b, mr x = ∫ x in a..c, mr (a + b - x) := by
      have h := intervalIntegral.integral_comp_sub_left (f := mr)
        (a := a) (b := c) (d := a + b)
      have hlow : a + b - c = c := by dsimp [c]; linarith
      have hhigh : a + b - a = b := by ring
      rw [hlow, hhigh] at h
      exact h.symm
    have hinterval_pair :
        ∫ x in a..b, mr x =
          ∫ x in a..c, (fun x => mr x + mr (a + b - x)) x := by
      rw [← hsplit, hreflect, intervalIntegral.integral_add hmr_ac href_int]
    have hpair_int :
        IntervalIntegrable (fun x => mr x + mr (a + b - x)) volume a c :=
      hmr_ac.add href_int
    have hg_int : IntervalIntegrable g volume a c :=
      (by fun_prop : Continuous g).intervalIntegrable _ _
    have hslice_le :
        ∀ x ∈ Set.Icc a c, mr x + mr (a + b - x) ≤ g x := by
      intro x hx
      have hpair := verticalSlice_reflection_volume_le hKc hconv hne hle
      simpa [X, a, b, c, m, mr, g] using hpair x hx
    have hpair_integral_le :
        (∫ x in a..c, (fun x => mr x + mr (a + b - x)) x) ≤
          ∫ x in a..c, g x :=
      intervalIntegral.integral_mono_on hac hpair_int hg_int hslice_le
    have hupper : (∫ x in a..c, g x) ≤ Real.pi / 4 := by
      simpa [g, c] using
        reflected_semicircle_integral_le_pi_quarter (a := a) (b := b) (c := c) rfl hab hwidth
    calc
      (volume K).toReal = ∫ x, mr x := hvol_real_eq
      _ = ∫ x in Set.Icc a b, mr x := hglobal_interval
      _ = ∫ x in a..b, mr x := hset_interval
      _ = ∫ x in a..c, (fun x => mr x + mr (a + b - x)) x := hinterval_pair
      _ ≤ ∫ x in a..c, g x := hpair_integral_le
      _ ≤ Real.pi / 4 := hupper
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hKempty]
    simp
    exact div_nonneg Real.pi_pos.le (by norm_num)

private lemma convex_volume_le_pi_quarter_of_pairwise_dist_le
    (R : Set (EuclideanSpace ℝ (Fin 2)))
    (hconv : Convex ℝ R)
    (hle : ∀ P ∈ R, ∀ Q ∈ R, dist P Q ≤ (1 : ℝ)) :
    (volume R).toReal ≤ Real.pi / 4 := by
  by_cases hne : R.Nonempty
  · let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    let K : Set (ℝ × ℝ) := e '' closure R
    rcases hne with ⟨P0, hP0⟩
    have hRbdd : Bornology.IsBounded R := by
      refine (Metric.isBounded_iff_subset_closedBall P0).2 ?_
      refine ⟨1, fun Q hQ => ?_⟩
      simpa using hle Q hQ P0 hP0
    have hcl_comp : IsCompact (closure R) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hRbdd.closure
    have hcl_conv : Convex ℝ (closure R) := hconv.closure
    have hKc : IsCompact K := hcl_comp.image e.continuous
    have hKconv : Convex ℝ K := hcl_conv.linear_image e.toLinearMap
    have hle_closure :
        ∀ P ∈ closure R, ∀ Q ∈ closure R, dist P Q ≤ (1 : ℝ) := by
      intro P hP Q hQ
      have hleft : ∀ P ∈ closure R, ∀ Q ∈ R, dist P Q ≤ (1 : ℝ) := by
        intro P hP Q hQ
        have hclosed : IsClosed {P : EuclideanSpace ℝ (Fin 2) | dist P Q ≤ (1 : ℝ)} :=
          isClosed_le (continuous_id.dist continuous_const) continuous_const
        exact (closure_minimal (fun P hP => hle P hP Q hQ) hclosed) hP
      have hclosedQ : IsClosed {Q : EuclideanSpace ℝ (Fin 2) | dist P Q ≤ (1 : ℝ)} :=
        isClosed_le (continuous_const.dist continuous_id) continuous_const
      exact (closure_minimal (fun Q hQ => hleft P hP Q hQ) hclosedQ) hQ
    have hKle :
        ∀ p ∈ K, ∀ q ∈ K,
          √((p.1 - q.1)^2 + (p.2 - q.2)^2) ≤ (1 : ℝ) := by
      intro p hp q hq
      rcases hp with ⟨P, hP, rfl⟩
      rcases hq with ⟨Q, hQ, rfl⟩
      have hd := hle_closure P hP Q hQ
      have hdist :
          √((((e P).1 - (e Q).1)^2) + (((e P).2 - (e Q).2)^2)) = dist P Q := by
        rw [EuclideanSpace.dist_eq]
        simp [e, Fin.sum_univ_two, Real.dist_eq, sq_abs]
      exact hdist.trans_le hd
    have hprod_le : (volume K).toReal ≤ Real.pi / 4 :=
      compact_convex_prod_volume_le_pi_quarter K hKc hKconv hKle
    have hemp : MeasurePreserving (e : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) := by
      dsimp [e]
      exact (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
    have hKvol : volume K = volume (closure R) := by
      have hmeas : MeasurableSet (e '' closure R) :=
        e.toHomeomorph.measurableEmbedding.measurableSet_image' isClosed_closure.measurableSet
      change volume (e '' closure R) = volume (closure R)
      rw [← hemp.map_eq]
      rw [Measure.map_apply e.continuous.measurable hmeas]
      congr 1
      exact e.toEquiv.preimage_image (closure R)
    have hcl_vol : volume (closure R) = volume R :=
      measure_closure_of_null_frontier (hconv.addHaar_frontier volume)
    calc
      (volume R).toReal = (volume (closure R)).toReal := by rw [hcl_vol]
      _ = (volume K).toReal := by rw [hKvol]
      _ ≤ Real.pi / 4 := hprod_le
  · have hRempty : R = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hRempty]
    simp
    exact div_nonneg Real.pi_pos.le (by norm_num)

/--
Prove that any convex region in the Euclidean plane with area greater than $\pi/4$ contains a pair of points exactly $1$ unit apart.
-/
theorem putnam_1967_a5
(R : Set (EuclideanSpace ℝ (Fin 2)))
(hR : Convex ℝ R ∧ (MeasureTheory.volume R).toReal > Real.pi / 4)
: ∃ P ∈ R, ∃ Q ∈ R, dist P Q = 1 := by
  classical
  by_contra h
  push_neg at h
  have hle : ∀ P ∈ R, ∀ Q ∈ R, dist P Q ≤ 1 := by
    intro P hP Q hQ
    by_contra hle
    have hgt : 1 < dist P Q := lt_of_not_ge hle
    let t : ℝ := (dist P Q)⁻¹
    let Z : EuclideanSpace ℝ (Fin 2) := (1 - t) • P + t • Q
    have hdist_pos : 0 < dist P Q := lt_trans zero_lt_one hgt
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact inv_nonneg.mpr dist_nonneg
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact inv_le_one_of_one_le₀ hgt.le
    have hsum : (1 - t) + t = 1 := by ring
    have hZ : Z ∈ R := by
      exact hR.1 hP hQ (sub_nonneg.mpr ht1) ht0 hsum
    have hsub : Z - P = t • (Q - P) := by
      dsimp [Z]
      module
    have hdist : dist P Z = 1 := by
      rw [dist_eq_norm]
      have hnorm : ‖P - Z‖ = ‖t • (Q - P)‖ := by
        rw [← norm_neg, neg_sub, hsub]
      rw [hnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      have hmul : t * dist P Q = 1 := by
        dsimp [t]
        exact inv_mul_cancel₀ hdist_pos.ne'
      rw [← dist_eq_norm Q P, dist_comm Q P]
      exact hmul
    exact (h P hP Z hZ) hdist
  exact not_lt_of_ge
    (convex_volume_le_pi_quarter_of_pairwise_dist_le R hR.1 hle)
    hR.2
