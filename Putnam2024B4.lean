import Mathlib

open MeasureTheory
open scoped ProbabilityTheory
open scoped Topology
open scoped Real

private def putnamStep (x y : ℤ) : ℤ :=
  if y > x then x + 1 else if y = x then x else x - 1

private def putnamWalk : (k : ℕ) → (Fin k → ℤ) → ℤ
  | 0, _ => 1
  | k + 1, xs =>
      let prev := putnamWalk k (fun i => xs i.castSucc)
      putnamStep prev (xs (Fin.last k))

private def delta (r y : ℤ) : ℝ :=
  if y > r then 1 else if y = r then 0 else -1

private def pointMass (r x : ℤ) : ℝ := if x = r then 1 else 0

private lemma integrableOn_finset_int (s : Finset ℤ) (f : ℤ → ℝ) :
    IntegrableOn f (s : Set ℤ) Measure.count := by
  classical
  refine Measure.integrableOn_of_bounded ?_
    (by exact (measurable_of_countable f).aestronglyMeasurable)
    (M := (↑(s.sup fun x => ‖f x‖₊) : ℝ)) ?_
  · rw [Measure.count_apply_finite]
    · exact ENNReal.natCast_ne_top _
    · exact Finset.finite_toSet s
  · filter_upwards [MeasureTheory.ae_restrict_mem (MeasurableSet.of_discrete (α := ℤ))] with x hx
    rw [← coe_nnnorm (f x)]
    exact (NNReal.coe_le_coe.2 (Finset.le_sup (s := s) (f := fun x => ‖f x‖₊) hx))

private lemma integral_uniformOn_int_finite (s : Set ℤ) (hs : s.Finite) (f : ℤ → ℝ) :
    ∫ x, f x ∂ (ProbabilityTheory.uniformOn s) =
      ((s.ncard : ℝ)⁻¹) * (∑ x ∈ hs.toFinset, f x) := by
  classical
  rw [ProbabilityTheory.uniformOn, ProbabilityTheory.cond, integral_smul_measure]
  have hcount : Measure.count s = (hs.toFinset.card : ENNReal) := by
    simpa using Measure.count_apply_finite s hs
  rw [hcount]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hint : (∫ x, f x ∂ Measure.count.restrict s) =
      ∫ x in (hs.toFinset : Set ℤ), f x ∂ Measure.count := by
    rw [hs.coe_toFinset]
  rw [hint]
  rw [integral_finset hs.toFinset f (integrableOn_finset_int hs.toFinset f)]
  simp [Set.ncard_eq_toFinset_card s hs, smul_eq_mul]

private lemma sum_delta (S : Finset ℤ) (r : ℤ) :
    (∑ y ∈ S, delta r y) =
      ((S.filter fun y => y > r).card : ℝ) -
        ((S.filter fun y => y < r).card : ℝ) := by
  classical
  have hpoint :
      ∀ y, delta r y =
        (if y > r then (1 : ℝ) else 0) - (if y < r then (1 : ℝ) else 0) := by
    intro y
    by_cases hgt : y > r
    · have hnlt : ¬ y < r := not_lt_of_gt hgt
      simp [delta, hgt, hnlt]
    · by_cases heq : y = r
      · simp [delta, heq]
      · have hlt : y < r := lt_of_le_of_ne (le_of_not_gt hgt) heq
        simp [delta, hgt, heq, hlt]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp [Finset.sum_boole, sub_eq_add_neg]

private lemma card_Icc_one_int (n : ℕ) (hn : 0 < n) :
    ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℝ) = (n : ℝ) := by
  rw [Int.card_Icc]
  have hnonneg : 0 ≤ (n : ℤ) + 1 - (1 : ℤ) := by omega
  norm_num [Int.toNat_of_nonneg hnonneg]

private lemma card_filter_gt (n : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    (((Finset.Icc (1 : ℤ) (n : ℤ)).filter fun y => y > r).card : ℝ) =
      (n : ℝ) - (r : ℝ) := by
  classical
  have hr1 : (1 : ℤ) ≤ r := (Finset.mem_Icc.mp hr).1
  have hrn : r ≤ (n : ℤ) := (Finset.mem_Icc.mp hr).2
  have hfilter :
      ((Finset.Icc (1 : ℤ) (n : ℤ)).filter fun y => y > r) =
        Finset.Icc (r + 1) (n : ℤ) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor <;> intro h <;> omega
  rw [hfilter, Int.card_Icc]
  have hnonneg : 0 ≤ (n : ℤ) + 1 - (r + 1) := by omega
  norm_num [Int.toNat_of_nonneg hnonneg]
  have hnonneg2 : 0 ≤ (n : ℤ) - r := by omega
  exact_mod_cast (Int.toNat_of_nonneg hnonneg2)

private lemma card_filter_lt (n : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    (((Finset.Icc (1 : ℤ) (n : ℤ)).filter fun y => y < r).card : ℝ) =
      (r : ℝ) - 1 := by
  classical
  have hr1 : (1 : ℤ) ≤ r := (Finset.mem_Icc.mp hr).1
  have hrn : r ≤ (n : ℤ) := (Finset.mem_Icc.mp hr).2
  have hfilter :
      ((Finset.Icc (1 : ℤ) (n : ℤ)).filter fun y => y < r) =
        Finset.Icc (1 : ℤ) (r - 1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor <;> intro h <;> omega
  rw [hfilter, Int.card_Icc]
  have hnonneg : 0 ≤ (r - 1) + 1 - (1 : ℤ) := by omega
  norm_num [Int.toNat_of_nonneg hnonneg]
  have hnat : r.toNat - 1 = (r - 1).toNat := by omega
  rw [hnat]
  have hnonneg2 : 0 ≤ r - 1 := by omega
  exact_mod_cast (Int.toNat_of_nonneg hnonneg2)

private lemma sum_step_Icc (n : ℕ) (hn : 0 < n) (r : ℤ)
    (hr : r ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    (∑ y ∈ Finset.Icc (1 : ℤ) (n : ℤ), (putnamStep r y : ℝ)) =
      (n : ℝ) * (r : ℝ) + ((n : ℝ) + 1 - 2 * (r : ℝ)) := by
  classical
  have hstep : ∀ y, (putnamStep r y : ℝ) = (r : ℝ) + delta r y := by
    intro y
    unfold putnamStep delta
    split_ifs <;> simp [Int.cast_add, Int.cast_sub]; try ring
  simp_rw [hstep]
  rw [Finset.sum_add_distrib]
  rw [sum_delta]
  rw [Finset.sum_const, nsmul_eq_mul, card_Icc_one_int n hn,
    card_filter_gt n r hr, card_filter_lt n r hr]
  ring

private lemma integral_step_uniform (n : ℕ) (hn : 0 < n) (r : ℤ)
    (hr : r ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    ∫ y, (putnamStep r y : ℝ) ∂ (ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ))) =
      (r : ℝ) + (((n : ℝ) + 1 - 2 * (r : ℝ)) / (n : ℝ)) := by
  classical
  have hs : (Set.Icc (1 : ℤ) (n : ℤ)).Finite := Set.finite_Icc _ _
  rw [integral_uniformOn_int_finite (Set.Icc (1 : ℤ) (n : ℤ)) hs]
  have hto : hs.toFinset = Finset.Icc (1 : ℤ) (n : ℤ) := by
    ext x
    rw [hs.mem_toFinset]
    simp
  have hncard : (Set.Icc (1 : ℤ) (n : ℤ)).ncard = n := by
    rw [Set.ncard_eq_toFinset_card _ hs, hto, Int.card_Icc]
    have hnonneg : 0 ≤ (n : ℤ) + 1 - (1 : ℤ) := by omega
    norm_num [Int.toNat_of_nonneg hnonneg]
  rw [hto, hncard, sum_step_Icc n hn r hr]
  field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hn)]

private lemma putnamStep_mem_Icc (n : ℕ) {x y : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) (n : ℤ))
    (hy : y ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    putnamStep x y ∈ Finset.Icc (1 : ℤ) (n : ℤ) := by
  unfold putnamStep
  simp only [Finset.mem_Icc] at hx hy ⊢
  split_ifs <;> omega

private lemma putnamWalk_mem_Icc (n k : ℕ) (hn : 0 < n) {xs : Fin k → ℤ}
    (hxs : ∀ i, xs i ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    putnamWalk k xs ∈ Finset.Icc (1 : ℤ) (n : ℤ) := by
  induction k with
  | zero =>
      simp [putnamWalk, Finset.mem_Icc]
      omega
  | succ k ih =>
      change putnamStep (putnamWalk k (fun i : Fin k => xs i.castSucc)) (xs (Fin.last k)) ∈
        Finset.Icc (1 : ℤ) (n : ℤ)
      apply putnamStep_mem_Icc n
      · exact ih (fun i => hxs i.castSucc)
      · exact hxs (Fin.last k)

private lemma norm_cast_le_of_mem_Icc (n : ℕ) {x : ℤ}
    (hx : x ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    ‖(x : ℝ)‖ ≤ (n : ℝ) := by
  have hx0 : (0 : ℤ) ≤ x := by
    have hx1 : (1 : ℤ) ≤ x := (Finset.mem_Icc.mp hx).1
    omega
  rw [Real.norm_of_nonneg (by exact_mod_cast hx0)]
  exact_mod_cast (Finset.mem_Icc.mp hx).2

private lemma pointMass_norm_le_one (r x : ℤ) : ‖pointMass r x‖ ≤ (1 : ℝ) := by
  unfold pointMass
  split_ifs <;> norm_num

private lemma aemeasurable_cast_int {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℤ}
    (hX : AEMeasurable X μ) : AEMeasurable (fun ω => (X ω : ℝ)) μ := by
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).aemeasurable.comp_aemeasurable hX

private lemma integrable_pointMass {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℤ} (hX : AEMeasurable X μ) (r : ℤ) :
    Integrable (fun ω => pointMass r (X ω)) μ := by
  have haem : AEMeasurable (fun ω => pointMass r (X ω)) μ :=
    (measurable_of_countable (pointMass r)).aemeasurable.comp_aemeasurable hX
  refine Integrable.of_bound haem.aestronglyMeasurable 1 ?_
  filter_upwards with ω
  exact pointMass_norm_le_one r (X ω)

private lemma integrable_pointMass_mul_step {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℤ} (n : ℕ) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ)
    (hYmem : ∀ᵐ ω ∂μ, Y ω ∈ Finset.Icc (1 : ℤ) (n : ℤ))
    {r : ℤ} (hr : r ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    Integrable (fun ω => pointMass r (X ω) * (putnamStep r (Y ω) : ℝ)) μ := by
  have hpm : AEMeasurable (fun ω => pointMass r (X ω)) μ :=
    (measurable_of_countable (pointMass r)).aemeasurable.comp_aemeasurable hX
  have hst : AEMeasurable (fun ω => (putnamStep r (Y ω) : ℝ)) μ :=
    (measurable_of_countable (fun y : ℤ => (putnamStep r y : ℝ))).aemeasurable.comp_aemeasurable hY
  refine Integrable.of_bound (hpm.aestronglyMeasurable.mul hst.aestronglyMeasurable) (n : ℝ) ?_
  filter_upwards [hYmem] with ω hy
  by_cases hx : X ω = r
  · simpa [pointMass, hx] using norm_cast_le_of_mem_Icc n (putnamStep_mem_Icc n hr hy)
  · simp [pointMass, hx]

private lemma sum_pointMass_eq_one (S : Finset ℤ) {x : ℤ} (hx : x ∈ S) :
    (∑ r ∈ S, pointMass r x) = 1 := by
  classical
  rw [Finset.sum_eq_single x]
  · simp [pointMass]
  · intro b hb hbne
    simp [pointMass, hbne.symm]
  · intro hnot
    exact (hnot hx).elim

private lemma sum_pointMass_mul_eq (S : Finset ℤ) {x : ℤ} (hx : x ∈ S) :
    (∑ r ∈ S, pointMass r x * (r : ℝ)) = (x : ℝ) := by
  classical
  rw [Finset.sum_eq_single x]
  · simp [pointMass]
  · intro b hb hbne
    simp [pointMass, hbne.symm]
  · intro hnot
    exact (hnot hx).elim

private lemma step_expand (S : Finset ℤ) {x : ℤ} (hx : x ∈ S) (y : ℤ) :
    (putnamStep x y : ℝ) = ∑ r ∈ S, pointMass r x * (putnamStep r y : ℝ) := by
  classical
  rw [Finset.sum_eq_single x]
  · simp [pointMass]
  · intro b hb hbne
    simp [pointMass, hbne.symm]
  · intro hnot
    exact (hnot hx).elim

private lemma integral_pointMass_sum_eq_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] [IsProbabilityMeasure μ] {X : Ω → ℤ} (S : Finset ℤ)
    (hX : AEMeasurable X μ) (hmem : ∀ᵐ ω ∂μ, X ω ∈ S) :
    (∑ r ∈ S, ∫ ω, pointMass r (X ω) ∂μ) = 1 := by
  rw [← integral_finset_sum S (fun r _ => integrable_pointMass hX r)]
  have hsum : (fun ω => ∑ r ∈ S, pointMass r (X ω)) =ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [hmem] with ω hω
    exact sum_pointMass_eq_one S hω
  rw [integral_congr_ae hsum]
  simp [integral_const]

private lemma integral_pointMass_weighted_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℤ} (n : ℕ) (hX : AEMeasurable X μ)
    (hmem : ∀ᵐ ω ∂μ, X ω ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    (∑ r ∈ Finset.Icc (1 : ℤ) (n : ℤ), (∫ ω, pointMass r (X ω) ∂μ) * (r : ℝ)) =
      ∫ ω, (X ω : ℝ) ∂μ := by
  simp_rw [← integral_mul_const]
  rw [← integral_finset_sum (Finset.Icc (1 : ℤ) (n : ℤ))
    (fun r _ => (integrable_pointMass hX r).mul_const (r : ℝ))]
  have hsum : (fun ω => ∑ r ∈ Finset.Icc (1 : ℤ) (n : ℤ), pointMass r (X ω) * (r : ℝ))
      =ᵐ[μ] fun ω => (X ω : ℝ) := by
    filter_upwards [hmem] with ω hω
    exact sum_pointMass_mul_eq (Finset.Icc (1 : ℤ) (n : ℤ)) hω
  rw [integral_congr_ae hsum]

private lemma uniformOn_cond_self_eq {s : Set ℤ} (hs : s.Finite) (hne : s.Nonempty) :
    ProbabilityTheory.cond (ProbabilityTheory.uniformOn s) s = ProbabilityTheory.uniformOn s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.uniformOn_self hs hne]
  simp only [inv_one, one_smul]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  rw [ProbabilityTheory.uniformOn_eq_zero_iff hs]
  ext x
  simp

private lemma map_eq_uniformOn_of_isUniform_uniformOn {Ω : Type*} [MeasurableSpace Ω]
    {Y : Ω → ℤ} {μ : Measure Ω} {s : Set ℤ} (hs : s.Finite) (hne : s.Nonempty)
    (hY : pdf.IsUniform Y s μ (ProbabilityTheory.uniformOn s)) :
    Measure.map Y μ = ProbabilityTheory.uniformOn s := by
  rw [hY, uniformOn_cond_self_eq hs hne]

private lemma Icc_one_natCast_nonempty (n : ℕ) (hn : 0 < n) :
    (Set.Icc (1 : ℤ) (n : ℤ)).Nonempty := by
  refine ⟨1, ?_⟩
  simp [Set.mem_Icc]
  omega

private lemma uniform_Icc_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {Y : Ω → ℤ} {μ : Measure Ω} {n : ℕ} (hn : 0 < n)
    (hY : pdf.IsUniform Y (Set.Icc (1 : ℤ) (n : ℤ)) μ
      (ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)))) :
    AEMeasurable Y μ := by
  have hs : (Set.Icc (1 : ℤ) (n : ℤ)).Finite := Set.finite_Icc _ _
  have hne : (Set.Icc (1 : ℤ) (n : ℤ)).Nonempty := Icc_one_natCast_nonempty n hn
  have hself := ProbabilityTheory.uniformOn_self hs hne
  exact hY.aemeasurable (by rw [hself]; simp) (by rw [hself]; simp)

private lemma uniform_Icc_map {Ω : Type*} [MeasurableSpace Ω]
    {Y : Ω → ℤ} {μ : Measure Ω} {n : ℕ} (hn : 0 < n)
    (hY : pdf.IsUniform Y (Set.Icc (1 : ℤ) (n : ℤ)) μ
      (ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)))) :
    Measure.map Y μ = ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)) := by
  exact map_eq_uniformOn_of_isUniform_uniformOn (Set.finite_Icc _ _) (Icc_one_natCast_nonempty n hn) hY

private lemma uniform_Icc_ae_mem_finset {Ω : Type*} [MeasurableSpace Ω]
    {Y : Ω → ℤ} {μ : Measure Ω} {n : ℕ} (hn : 0 < n)
    (hY : pdf.IsUniform Y (Set.Icc (1 : ℤ) (n : ℤ)) μ
      (ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)))) :
    ∀ᵐ ω ∂μ, Y ω ∈ Finset.Icc (1 : ℤ) (n : ℤ) := by
  have hs : (Set.Icc (1 : ℤ) (n : ℤ)).Finite := Set.finite_Icc _ _
  have hYaem := uniform_Icc_aemeasurable (Y := Y) (μ := μ) hn hY
  have hYmap := uniform_Icc_map (Y := Y) (μ := μ) hn hY
  have hset : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
    rw [ae_iff]
    change μ (Y ⁻¹' (Set.Icc (1 : ℤ) (n : ℤ))ᶜ) = 0
    rw [← Measure.map_apply_of_aemeasurable hYaem hs.measurableSet.compl]
    rw [hYmap]
    rw [ProbabilityTheory.uniformOn_eq_zero_iff hs]
    ext x
    simp
  filter_upwards [hset] with ω hω
  simpa using hω

private lemma integral_step_of_indep_uniform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    {X Y : Ω → ℤ} (n : ℕ) (hn : 0 < n)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXmem : ∀ᵐ ω ∂μ, X ω ∈ Finset.Icc (1 : ℤ) (n : ℤ))
    (hYmem : ∀ᵐ ω ∂μ, Y ω ∈ Finset.Icc (1 : ℤ) (n : ℤ))
    (hYmap : Measure.map Y μ = ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)))
    (hind : X ⟂ᵢ[μ] Y) :
    ∫ ω, (putnamStep (X ω) (Y ω) : ℝ) ∂μ =
      (((n : ℝ) - 2) / (n : ℝ)) * (∫ ω, (X ω : ℝ) ∂μ) + (((n : ℝ) + 1) / (n : ℝ)) := by
  classical
  let S : Finset ℤ := Finset.Icc (1 : ℤ) (n : ℤ)
  have hstepae : (fun ω => (putnamStep (X ω) (Y ω) : ℝ)) =ᵐ[μ]
      fun ω => ∑ r ∈ S, pointMass r (X ω) * (putnamStep r (Y ω) : ℝ) := by
    filter_upwards [hXmem] with ω hx
    exact step_expand S hx (Y ω)
  rw [integral_congr_ae hstepae]
  rw [integral_finset_sum S (fun r hr => integrable_pointMass_mul_step n hX hY hYmem hr)]
  have hfactor : ∀ r ∈ S,
      ∫ ω, pointMass r (X ω) * (putnamStep r (Y ω) : ℝ) ∂μ =
        (∫ ω, pointMass r (X ω) ∂μ) *
          ((r : ℝ) + (((n : ℝ) + 1 - 2 * (r : ℝ)) / (n : ℝ))) := by
    intro r hr
    have hpm : AEStronglyMeasurable (pointMass r) (Measure.map X μ) :=
      (measurable_of_countable (pointMass r)).aestronglyMeasurable
    have hst : AEStronglyMeasurable (fun y : ℤ => (putnamStep r y : ℝ)) (Measure.map Y μ) :=
      (measurable_of_countable (fun y : ℤ => (putnamStep r y : ℝ))).aestronglyMeasurable
    rw [hind.integral_fun_comp_mul_comp hX hY hpm hst]
    congr 1
    rw [← integral_map hY hst, hYmap]
    exact integral_step_uniform n hn r hr
  calc
    (∑ r ∈ S, ∫ ω, pointMass r (X ω) * (putnamStep r (Y ω) : ℝ) ∂μ)
        = ∑ r ∈ S, (∫ ω, pointMass r (X ω) ∂μ) *
          ((r : ℝ) + (((n : ℝ) + 1 - 2 * (r : ℝ)) / (n : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hfactor r hr
    _ = (((n : ℝ) - 2) / (n : ℝ)) * (∫ ω, (X ω : ℝ) ∂μ) + (((n : ℝ) + 1) / (n : ℝ)) := by
      have hsumone := integral_pointMass_sum_eq_one S hX (by simpa [S] using hXmem)
      have hweighted := integral_pointMass_weighted_eq n hX hXmem
      have hdecomp :
          (∑ r ∈ S, (∫ ω, pointMass r (X ω) ∂μ) *
            ((r : ℝ) + (((n : ℝ) + 1 - 2 * (r : ℝ)) / (n : ℝ)))) =
            (∑ r ∈ S, (∫ ω, pointMass r (X ω) ∂μ) * (r : ℝ)) +
              (((n : ℝ) + 1) / (n : ℝ)) * (∑ r ∈ S, ∫ ω, pointMass r (X ω) ∂μ) -
                (2 / (n : ℝ)) * (∑ r ∈ S, (∫ ω, pointMass r (X ω) ∂μ) * (r : ℝ)) := by
        have hpoint : ∀ r, (∫ ω, pointMass r (X ω) ∂μ) *
            ((r : ℝ) + (((n : ℝ) + 1 - 2 * (r : ℝ)) / (n : ℝ))) =
            (∫ ω, pointMass r (X ω) ∂μ) * (r : ℝ) +
              (((n : ℝ) + 1) / (n : ℝ)) * (∫ ω, pointMass r (X ω) ∂μ) -
                (2 / (n : ℝ)) * ((∫ ω, pointMass r (X ω) ∂μ) * (r : ℝ)) := by
          intro r
          ring
        simp_rw [hpoint]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        rw [Finset.mul_sum, Finset.mul_sum]
      rw [hdecomp]
      rw [hweighted, hsumone]
      field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hn)]
      ring

private lemma a_eq_putnamWalk {Ω : Type*} (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (n k : ℕ) (hn : 0 < n) :
    a n k = fun ω => putnamWalk k (fun i : Fin k => m n i.1 ω) := by
  funext ω
  induction k with
  | zero =>
      simpa [putnamWalk] using congrFun (h₀ n hn) ω
  | succ k ih =>
      rw [h₂ n k ω hn, ih]
      simp [putnamWalk, putnamStep]

private def prevCurrIndex (n k : ℕ) : Option (Fin k) → ℕ × ℕ
  | none => (n, k)
  | some i => (n, i.1)

private lemma prevCurrIndex_injective (n k : ℕ) : Function.Injective (prevCurrIndex n k) := by
  intro a b h
  cases a <;> cases b <;> simp [prevCurrIndex] at h ⊢
  · omega
  · omega
  · exact Fin.ext h

private lemma indep_walk_current {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : ℕ → ℕ → Ω → ℤ) (h₃ : ProbabilityTheory.iIndepFun m.uncurry μ)
    (n k : ℕ) (hm : ∀ j, AEMeasurable (m n j) μ) :
    (fun ω => putnamWalk k (fun i : Fin k => m n i.1 ω)) ⟂ᵢ[μ] (m n k) := by
  classical
  let f : Option (Fin k) → Ω → ℤ :=
    fun o ω => m (prevCurrIndex n k o).1 (prevCurrIndex n k o).2 ω
  have hi : ProbabilityTheory.iIndepFun f μ := by
    simpa [f, Function.uncurry] using h₃.precomp (prevCurrIndex_injective n k)
  let S : Finset (Option (Fin k)) := Finset.univ.filter (fun o => o.isSome)
  let T : Finset (Option (Fin k)) := {none}
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hnone
    simp [T] at hnone
    subst x
    simp [S] at hx
  have hfmeas : ∀ o, AEMeasurable (f o) μ := by
    intro o
    cases o with
    | none => simpa [f, prevCurrIndex] using hm k
    | some i => simpa [f, prevCurrIndex] using hm i.1
  have htuple := hi.indepFun_finset₀ S T hST hfmeas
  let φ : (S → ℤ) → ℤ := fun v => putnamWalk k (fun i : Fin k => v ⟨some i, by simp [S]⟩)
  let ψ : (T → ℤ) → ℤ := fun v => v ⟨none, by simp [T]⟩
  have hcomp := htuple.comp (measurable_of_countable φ) (measurable_of_countable ψ)
  simpa [φ, ψ, f, S, T, prevCurrIndex, Function.comp_def] using hcomp

private lemma integral_a_succ
    {Ω : Type*}
    [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (h₃ : ProbabilityTheory.iIndepFun m.uncurry ℙ)
    (n k : ℕ) (hn : 0 < n) :
    ∫ ω, (a n (k + 1) ω : ℝ) =
      (((n : ℝ) - 2) / (n : ℝ)) * (∫ ω, (a n k ω : ℝ)) + (((n : ℝ) + 1) / (n : ℝ)) := by
  classical
  have hm : ∀ j, AEMeasurable (m n j) ℙ := by
    intro j
    exact uniform_Icc_aemeasurable (Y := m n j) (μ := ℙ) hn (h₁ n j hn)
  have hY := hm k
  have hYmem : ∀ᵐ ω ∂ℙ, m n k ω ∈ Finset.Icc (1 : ℤ) (n : ℤ) :=
    uniform_Icc_ae_mem_finset (Y := m n k) (μ := ℙ) hn (h₁ n k hn)
  have hYmap : Measure.map (m n k) ℙ =
      ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)) :=
    uniform_Icc_map (Y := m n k) (μ := ℙ) hn (h₁ n k hn)
  have ha := a_eq_putnamWalk m a h₀ h₂ n k hn
  have hvec : AEMeasurable (fun ω => fun i : Fin k => m n i.1 ω) ℙ := by
    exact aemeasurable_pi_lambda _ (fun i => hm i.1)
  have hwalk_meas : AEMeasurable (fun ω => putnamWalk k (fun i : Fin k => m n i.1 ω)) ℙ := by
    have hw : AEMeasurable (putnamWalk k)
        (Measure.map (fun ω => fun i : Fin k => m n i.1 ω) ℙ) :=
      (measurable_of_countable (putnamWalk k)).aemeasurable
    simpa [Function.comp_def] using hw.comp_aemeasurable hvec
  have hX : AEMeasurable (a n k) ℙ := by
    simpa [ha] using hwalk_meas
  have hall : ∀ᵐ ω ∂ℙ, ∀ i : Fin k, m n i.1 ω ∈ Finset.Icc (1 : ℤ) (n : ℤ) := by
    exact (Filter.eventually_all).2 (fun i => uniform_Icc_ae_mem_finset (Y := m n i.1) (μ := ℙ) hn (h₁ n i.1 hn))
  have hwalk_mem :
      ∀ᵐ ω ∂ℙ, putnamWalk k (fun i : Fin k => m n i.1 ω) ∈ Finset.Icc (1 : ℤ) (n : ℤ) := by
    filter_upwards [hall] with ω hω
    exact putnamWalk_mem_Icc n k hn hω
  have hXmem : ∀ᵐ ω ∂ℙ, a n k ω ∈ Finset.Icc (1 : ℤ) (n : ℤ) := by
    simpa [ha] using hwalk_mem
  have hind_walk := indep_walk_current (ℙ : Measure Ω) m h₃ n k hm
  have hind : (a n k) ⟂ᵢ[ℙ] (m n k) := by
    simpa [ha] using hind_walk
  have hstep :
      (fun ω => (a n (k + 1) ω : ℝ)) =
        fun ω => (putnamStep (a n k ω) (m n k ω) : ℝ) := by
    funext ω
    rw [h₂ n k ω hn]
    unfold putnamStep
    split_ifs <;> simp [Int.cast_add, Int.cast_sub]
  rw [hstep]
  exact integral_step_of_indep_uniform n hn hX hY hXmem hYmem hYmap hind

private lemma tendsto_factor_plus :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (2 * (n : ℝ))) Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  have hbase : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) Filter.atTop (𝓝 ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  have h := hbase.div_const 2
  have hev : (fun n : ℕ => ((1 : ℝ) + 1 / (n : ℝ)) / 2) =ᶠ[Filter.atTop]
      fun n : ℕ => ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    field_simp [hn0]
  simpa using h.congr' hev

private lemma tendsto_factor_minus :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 1) / (2 * (n : ℝ))) Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  have hbase : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ)) Filter.atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  have h := hbase.div_const 2
  have hev : (fun n : ℕ => ((1 : ℝ) - 1 / (n : ℝ)) / 2) =ᶠ[Filter.atTop]
      fun n : ℕ => ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    field_simp [hn0]
  simpa using h.congr' hev

private lemma tendsto_pow_part :
    Filter.Tendsto (fun n : ℕ => (((n : ℝ) - 2) / (n : ℝ)) ^ n) Filter.atTop (𝓝 (Real.exp (-2))) := by
  refine (Real.tendsto_one_add_div_pow_exp (-2)).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  congr 1
  field_simp [hn0]
  ring

private lemma tendsto_final_expr :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (2 * (n : ℝ)) -
      (((n : ℝ) - 1) / (2 * (n : ℝ))) * ((((n : ℝ) - 2) / (n : ℝ)) ^ n))
      Filter.atTop (𝓝 ((1 - Real.exp (-2)) / 2 : ℝ)) := by
  have h := tendsto_factor_plus.sub (tendsto_factor_minus.mul tendsto_pow_part)
  convert h using 1
  ring_nf

noncomputable abbrev putnam_2024_b4_solution : ℝ := (1 - Real.exp (-2)) / 2

/--
Let $n$ be a positive integer. Set $a_{n, 0} = 1$. For $k \geq 0$
choose an integer $m_{n, k}$ uniformly at random from the set
$\{1, 2, \ldots, n\}$, and let
$$a_{n, k+1} = \begin{cases}
a_{n, k} + 1 & \text{if } m_{n, k} > a_{n, k} \\
a_{n, k} & \text{ if } m_{n, k} = a_{n, k} \\
a_{n, k} -1 & \text{if } m_{n, k} < a_{n, k} \end{cases}$$.
Let $E(n)$ be the expected value of $a_{n, n}$. Determine
$\lim_{n \to \infty} E(n)/n$.
-/
theorem putnam_2024_b4
    {Ω : Type*}
    [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (h₃ : ProbabilityTheory.iIndepFun m.uncurry ℙ) :
    Filter.Tendsto (fun n => (∫ ω, a n n ω : ℝ) / n) Filter.atTop (𝓝 putnam_2024_b4_solution) :=
  by
  classical
  have hclosed : ∀ n > 0, ∀ k,
      ∫ ω, (a n k ω : ℝ) =
        (((n : ℝ) + 1) / 2) -
          (((n : ℝ) - 1) / 2) * ((((n : ℝ) - 2) / (n : ℝ)) ^ k) := by
    intro n hn k
    induction k with
    | zero =>
        rw [h₀ n hn]
        simp [integral_const]
        field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hn)]
        ring
    | succ k ih =>
        rw [integral_a_succ m a h₀ h₁ h₂ h₃ n k hn, ih]
        rw [pow_succ]
        field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hn)]
        ring
  have heq : (fun n => (∫ ω, a n n ω : ℝ) / n) =ᶠ[Filter.atTop]
      fun n : ℕ => ((n : ℝ) + 1) / (2 * (n : ℝ)) -
        (((n : ℝ) - 1) / (2 * (n : ℝ))) * ((((n : ℝ) - 2) / (n : ℝ)) ^ n) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    rw [hclosed n hn n]
    field_simp [hn0]
  exact tendsto_final_expr.congr' heq.symm
