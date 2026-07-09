import Mathlib

open MeasureTheory
open scoped BigOperators
open scoped ProbabilityTheory
open scoped Topology
open scoped Real

private def putnamB4Step (x y : ℤ) : ℤ :=
  if y > x then
    x + 1
  else if y = x then
    x
  else
    x - 1

private def putnamB4State : (k : ℕ) → (Fin k → ℤ) → ℤ
  | 0, _ => 1
  | k + 1, xs =>
      putnamB4Step (putnamB4State k (fun i => xs i.castSucc)) (xs ⟨k, Nat.lt_succ_self k⟩)

private def putnamB4EqInd (j x : ℤ) : ℝ :=
  if x = j then 1 else 0

private def putnamB4GtInd (j x : ℤ) : ℝ :=
  if j < x then 1 else 0

private def putnamB4LtInd (j x : ℤ) : ℝ :=
  if x < j then 1 else 0

private lemma putnamB4State_measurable (k : ℕ) :
    Measurable (putnamB4State k) := by
  exact measurable_of_countable _

private lemma putnamB4_indicator_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (f : Ω → ℝ)
    (hf : AEMeasurable f (ℙ : Measure Ω)) (hbound : ∀ ω, ‖f ω‖ ≤ 1) :
    Integrable f (ℙ : Measure Ω) := by
  exact Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)

private lemma putnamB4_eq_ind_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Ω → ℤ) (j : ℤ)
    (hX : AEMeasurable X (ℙ : Measure Ω)) :
    Integrable (fun ω => putnamB4EqInd j (X ω)) (ℙ : Measure Ω) := by
  refine putnamB4_indicator_integrable _ ((measurable_of_countable
    (putnamB4EqInd j)).comp_aemeasurable hX) ?_
  intro ω
  by_cases h : X ω = j <;> simp [putnamB4EqInd, h]

private lemma putnamB4_gt_ind_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Ω → ℤ) (j : ℤ)
    (hX : AEMeasurable X (ℙ : Measure Ω)) :
    Integrable (fun ω => putnamB4GtInd j (X ω)) (ℙ : Measure Ω) := by
  refine putnamB4_indicator_integrable _ ((measurable_of_countable
    (putnamB4GtInd j)).comp_aemeasurable hX) ?_
  intro ω
  by_cases h : j < X ω <;> simp [putnamB4GtInd, h]

private lemma putnamB4_lt_ind_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Ω → ℤ) (j : ℤ)
    (hX : AEMeasurable X (ℙ : Measure Ω)) :
    Integrable (fun ω => putnamB4LtInd j (X ω)) (ℙ : Measure Ω) := by
  refine putnamB4_indicator_integrable _ ((measurable_of_countable
    (putnamB4LtInd j)).comp_aemeasurable hX) ?_
  intro ω
  by_cases h : X ω < j <;> simp [putnamB4LtInd, h]

private lemma putnamB4_prod_ind_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X Y : Ω → ℤ) (j : ℤ)
    (hX : AEMeasurable X (ℙ : Measure Ω)) (hY : AEMeasurable Y (ℙ : Measure Ω)) :
    Integrable (fun ω => putnamB4EqInd j (X ω) * putnamB4GtInd j (Y ω))
      (ℙ : Measure Ω) ∧
    Integrable (fun ω => putnamB4EqInd j (X ω) * putnamB4LtInd j (Y ω))
      (ℙ : Measure Ω) := by
  constructor
  · refine putnamB4_indicator_integrable _ ?_ ?_
    · exact ((measurable_of_countable (fun p : ℤ × ℤ =>
        putnamB4EqInd j p.1 * putnamB4GtInd j p.2)).comp_aemeasurable
        (hX.prodMk hY))
    · intro ω
      by_cases h₁ : X ω = j <;> by_cases h₂ : j < Y ω <;>
        simp [putnamB4EqInd, putnamB4GtInd, h₁, h₂]
  · refine putnamB4_indicator_integrable _ ?_ ?_
    · exact ((measurable_of_countable (fun p : ℤ × ℤ =>
        putnamB4EqInd j p.1 * putnamB4LtInd j p.2)).comp_aemeasurable
        (hX.prodMk hY))
    · intro ω
      by_cases h₁ : X ω = j <;> by_cases h₂ : Y ω < j <;>
        simp [putnamB4EqInd, putnamB4LtInd, h₁, h₂]

private lemma putnamB4_sum_eqInd {n : ℕ} {x : ℤ}
    (hx : x ∈ Set.Icc (1 : ℤ) (n : ℤ)) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), putnamB4EqInd j x) = 1 := by
  rw [Finset.sum_eq_single_of_mem x]
  · simp [putnamB4EqInd]
  · simp only [Finset.mem_Icc]
    exact hx
  · intro j hj hne
    simp [putnamB4EqInd, hne.symm]

private lemma putnamB4_sum_weighted_eqInd {n : ℕ} {x : ℤ}
    (hx : x ∈ Set.Icc (1 : ℤ) (n : ℤ)) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), (j : ℝ) * putnamB4EqInd j x) = x := by
  rw [Finset.sum_eq_single_of_mem x]
  · simp [putnamB4EqInd]
  · simp only [Finset.mem_Icc]
    exact hx
  · intro j hj hne
    simp [putnamB4EqInd, hne.symm]

private lemma putnamB4_gt_sum_eq {n : ℕ} {x y : ℤ}
    (hx : x ∈ Set.Icc (1 : ℤ) (n : ℤ)) :
    putnamB4GtInd x y =
      ∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), putnamB4EqInd j x * putnamB4GtInd j y := by
  rw [Finset.sum_eq_single_of_mem x]
  · simp [putnamB4EqInd]
  · simp only [Finset.mem_Icc]
    exact hx
  · intro j hj hne
    simp [putnamB4EqInd, hne.symm]

private lemma putnamB4_lt_sum_eq {n : ℕ} {x y : ℤ}
    (hx : x ∈ Set.Icc (1 : ℤ) (n : ℤ)) :
    putnamB4LtInd x y =
      ∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), putnamB4EqInd j x * putnamB4LtInd j y := by
  rw [Finset.sum_eq_single_of_mem x]
  · simp [putnamB4EqInd]
  · simp only [Finset.mem_Icc]
    exact hx
  · intro j hj hne
    simp [putnamB4EqInd, hne.symm]

private lemma putnamB4Step_real (x y : ℤ) :
    (putnamB4Step x y : ℝ) =
      (x : ℝ) + putnamB4GtInd x y - putnamB4LtInd x y := by
  dsimp [putnamB4Step, putnamB4GtInd, putnamB4LtInd]
  split_ifs with hgt heq hlt <;> norm_num at * <;> omega

private lemma putnamB4_sum_algebra (n : ℕ) (p : ℤ → ℝ) (hn : 0 < n) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ),
        p j * (((n : ℝ) - (j : ℝ)) / (n : ℝ))) -
      (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ),
        p j * (((j : ℝ) - 1) / (n : ℝ))) =
    (((n : ℝ) + 1) / (n : ℝ)) *
        (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), p j) -
      (2 / (n : ℝ)) *
        (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), (j : ℝ) * p j) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let S : Finset ℤ := Finset.Icc (1 : ℤ) (n : ℤ)
  change
      (∑ j ∈ S, p j * (((n : ℝ) - (j : ℝ)) / (n : ℝ))) -
        (∑ j ∈ S, p j * (((j : ℝ) - 1) / (n : ℝ))) =
      (((n : ℝ) + 1) / (n : ℝ)) * (∑ j ∈ S, p j) -
        (2 / (n : ℝ)) * (∑ j ∈ S, (j : ℝ) * p j)
  rw [← Finset.sum_sub_distrib]
  trans
      (∑ j ∈ S,
        ((((n : ℝ) + 1) / (n : ℝ)) * p j -
          (2 / (n : ℝ)) * ((j : ℝ) * p j)))
  · apply Finset.sum_congr rfl
    intro j hj
    field_simp [hn0]
    ring
  · rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]

private lemma uniformOn_finite_apply {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {s t : Set α} (hs : s.Finite) :
    ProbabilityTheory.uniformOn s t =
      (↑((hs.inter_of_left t).toFinset.card) : ENNReal) / (↑(hs.toFinset.card) : ENNReal) := by
  rw [ProbabilityTheory.uniformOn, ProbabilityTheory.cond_apply hs.measurableSet]
  rw [Measure.count_apply_finite _ hs, Measure.count_apply_finite _ (hs.inter_of_left t)]
  rw [ENNReal.div_eq_inv_mul]

private lemma uniformOn_Icc_Ioi_real (n : ℕ) (j : ℤ)
    (hj₁ : (1 : ℤ) ≤ j) (hjn : j ≤ (n : ℤ)) :
    (ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ))).real (Set.Ioi j) =
      ((n : ℝ) - (j : ℝ)) / (n : ℝ) := by
  let S : Set ℤ := Set.Icc (1 : ℤ) (n : ℤ)
  have hSfin : S.Finite := Set.finite_Icc _ _
  rw [Measure.real, uniformOn_finite_apply hSfin]
  have hnum : (hSfin.inter_of_left (Set.Ioi j)).toFinset = Finset.Ioc j (n : ℤ) := by
    ext x
    simp [S]
    omega
  have hden : hSfin.toFinset = Finset.Icc (1 : ℤ) (n : ℤ) := by
    ext x
    simp [S]
  rw [hnum, hden]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [Int.card_Ioc]
  have hnonneg : 0 ≤ (n : ℤ) - j := by omega
  have hnum_real : ((((n : ℤ) - j).toNat : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonneg)
  have hden_int : ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℤ) = (n : ℤ) := by
    have := Int.card_Icc_of_le (1 : ℤ) (n : ℤ) (by omega)
    omega
  have hden_real : ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℝ) = (n : ℝ) := by
    exact_mod_cast hden_int
  rw [hnum_real, hden_real]

private lemma uniformOn_Icc_Iio_real (n : ℕ) (j : ℤ)
    (hj₁ : (1 : ℤ) ≤ j) (hjn : j ≤ (n : ℤ)) :
    (ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ))).real (Set.Iio j) =
      ((j : ℝ) - 1) / (n : ℝ) := by
  let S : Set ℤ := Set.Icc (1 : ℤ) (n : ℤ)
  have hSfin : S.Finite := Set.finite_Icc _ _
  rw [Measure.real, uniformOn_finite_apply hSfin]
  have hnum : (hSfin.inter_of_left (Set.Iio j)).toFinset = Finset.Ico (1 : ℤ) j := by
    ext x
    simp [S]
    omega
  have hden : hSfin.toFinset = Finset.Icc (1 : ℤ) (n : ℤ) := by
    ext x
    simp [S]
  rw [hnum, hden]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [Int.card_Ico]
  have hnonneg : 0 ≤ j - (1 : ℤ) := by omega
  have hnum_real : (((j - (1 : ℤ)).toNat : ℕ) : ℝ) = (j : ℝ) - 1 := by
    exact_mod_cast (Int.toNat_of_nonneg hnonneg)
  have hden_int : ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℤ) = (n : ℤ) := by
    have := Int.card_Icc_of_le (1 : ℤ) (n : ℤ) (by omega)
    omega
  have hden_real : ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℝ) = (n : ℝ) := by
    exact_mod_cast hden_int
  rw [hnum_real, hden_real]

private lemma putnamB4_state_eq {Ω : Type*}
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    a n k = fun ω => putnamB4State k (fun i => m n i ω) := by
  induction k with
  | zero =>
      simpa [putnamB4State] using h₀ n hn
  | succ k ih =>
      funext ω
      rw [h₂ n k ω hn, ih]
      simp [putnamB4State, putnamB4Step]

private lemma putnamB4Step_mem_Icc {n : ℕ} {x y : ℤ}
    (hx : x ∈ Set.Icc (1 : ℤ) (n : ℤ))
    (hy : y ∈ Set.Icc (1 : ℤ) (n : ℤ)) :
    putnamB4Step x y ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  dsimp [putnamB4Step]
  split_ifs with hgt heq
  · constructor <;> omega
  · constructor <;> omega
  · constructor <;> omega

private lemma putnamB4State_mem_Icc {n k : ℕ} (hn : 0 < n) (xs : Fin k → ℤ)
    (hxs : ∀ i, xs i ∈ Set.Icc (1 : ℤ) (n : ℤ)) :
    putnamB4State k xs ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
  induction k with
  | zero =>
      constructor <;> simp [putnamB4State] <;> omega
  | succ k ih =>
      simp only [putnamB4State]
      exact putnamB4Step_mem_Icc (ih _ fun i => hxs i.castSucc)
        (hxs ⟨k, Nat.lt_succ_self k⟩)

private lemma putnamB4_m_mem_ae {Ω : Type*} [MeasureSpace Ω]
    (m : ℕ → ℕ → Ω → ℤ)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    {n k : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), m n k ω ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
  let S : Set ℤ := Set.Icc (1 : ℤ) (n : ℤ)
  have hSfin : S.Finite := Set.finite_Icc _ _
  have hSnon : S.Nonempty := ⟨1, by constructor <;> omega⟩
  have hμS : ProbabilityTheory.uniformOn S S = 1 :=
    ProbabilityTheory.uniformOn_self hSfin hSnon
  have hμS_ne_zero : ProbabilityTheory.uniformOn S S ≠ 0 := by simp [hμS]
  have hμS_ne_top : ProbabilityTheory.uniformOn S S ≠ (⊤ : ENNReal) := by simp [hμS]
  have hpre := (h₁ n k hn).measure_preimage hμS_ne_zero hμS_ne_top
    (A := Sᶜ) hSfin.measurableSet.compl
  rw [ae_iff]
  change (ℙ : Measure Ω) ((m n k) ⁻¹' Sᶜ) = 0
  rw [hpre, Set.inter_compl_self]
  simp

private lemma putnamB4_m_aemeasurable {Ω : Type*} [MeasureSpace Ω]
    (m : ℕ → ℕ → Ω → ℤ)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    {n k : ℕ} (hn : 0 < n) :
    AEMeasurable (m n k) (ℙ : Measure Ω) := by
  let S : Set ℤ := Set.Icc (1 : ℤ) (n : ℤ)
  have hSfin : S.Finite := Set.finite_Icc _ _
  have hSnon : S.Nonempty := ⟨1, by constructor <;> omega⟩
  have hμS : ProbabilityTheory.uniformOn S S = 1 :=
    ProbabilityTheory.uniformOn_self hSfin hSnon
  have hμS_ne_zero : ProbabilityTheory.uniformOn S S ≠ 0 := by simp [hμS]
  have hμS_ne_top : ProbabilityTheory.uniformOn S S ≠ (⊤ : ENNReal) := by simp [hμS]
  exact (h₁ n k hn).aemeasurable hμS_ne_zero hμS_ne_top

private lemma putnamB4_cond_uniformOn_Icc (n : ℕ) (hn : 0 < n) :
    ProbabilityTheory.cond
        (ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)))
        (Set.Icc (1 : ℤ) (n : ℤ)) =
      ProbabilityTheory.uniformOn (Set.Icc (1 : ℤ) (n : ℤ)) := by
  let S : Set ℤ := Set.Icc (1 : ℤ) (n : ℤ)
  have hSfin : S.Finite := Set.finite_Icc _ _
  have hSnon : S.Nonempty := ⟨1, by constructor <;> omega⟩
  change ProbabilityTheory.cond (ProbabilityTheory.uniformOn S) S =
    ProbabilityTheory.uniformOn S
  ext t
  rw [ProbabilityTheory.cond_apply hSfin.measurableSet]
  rw [ProbabilityTheory.uniformOn_inter_self hSfin, ProbabilityTheory.uniformOn_self hSfin hSnon]
  simp

private lemma putnamB4_integral_gt_m {Ω : Type*} [MeasureSpace Ω]
    (m : ℕ → ℕ → Ω → ℤ)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    {n k : ℕ} (hn : 0 < n) {j : ℤ}
    (hj₁ : (1 : ℤ) ≤ j) (hjn : j ≤ (n : ℤ)) :
    (∫ ω, putnamB4GtInd j (m n k ω) ∂(ℙ : Measure Ω)) =
      ((n : ℝ) - (j : ℝ)) / (n : ℝ) := by
  let S : Set ℤ := Set.Icc (1 : ℤ) (n : ℤ)
  have hf : AEStronglyMeasurable (putnamB4GtInd j)
      (Measure.map (m n k) (ℙ : Measure Ω)) :=
    (measurable_of_countable (putnamB4GtInd j)).aestronglyMeasurable
  calc
    (∫ ω, putnamB4GtInd j (m n k ω) ∂(ℙ : Measure Ω)) =
        ∫ x, putnamB4GtInd j x ∂Measure.map (m n k) (ℙ : Measure Ω) := by
          exact (integral_map (putnamB4_m_aemeasurable m h₁ hn) hf).symm
    _ = ∫ x, putnamB4GtInd j x ∂ProbabilityTheory.uniformOn S := by
          rw [(h₁ n k hn), putnamB4_cond_uniformOn_Icc n hn]
    _ = (ProbabilityTheory.uniformOn S).real (Set.Ioi j) := by
          have hfun :
              putnamB4GtInd j =
                (Set.Ioi j).indicator (fun _ : ℤ => (1 : ℝ)) := by
            funext x
            by_cases h : j < x <;> simp [putnamB4GtInd, Set.indicator, h]
          rw [hfun]
          simpa using
            (integral_indicator_one
              (μ := ProbabilityTheory.uniformOn S)
              (hs := (measurableSet_Ioi : MeasurableSet (Set.Ioi j))))
    _ = ((n : ℝ) - (j : ℝ)) / (n : ℝ) := by
          exact uniformOn_Icc_Ioi_real n j hj₁ hjn

private lemma putnamB4_integral_lt_m {Ω : Type*} [MeasureSpace Ω]
    (m : ℕ → ℕ → Ω → ℤ)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    {n k : ℕ} (hn : 0 < n) {j : ℤ}
    (hj₁ : (1 : ℤ) ≤ j) (hjn : j ≤ (n : ℤ)) :
    (∫ ω, putnamB4LtInd j (m n k ω) ∂(ℙ : Measure Ω)) =
      ((j : ℝ) - 1) / (n : ℝ) := by
  let S : Set ℤ := Set.Icc (1 : ℤ) (n : ℤ)
  have hf : AEStronglyMeasurable (putnamB4LtInd j)
      (Measure.map (m n k) (ℙ : Measure Ω)) :=
    (measurable_of_countable (putnamB4LtInd j)).aestronglyMeasurable
  calc
    (∫ ω, putnamB4LtInd j (m n k ω) ∂(ℙ : Measure Ω)) =
        ∫ x, putnamB4LtInd j x ∂Measure.map (m n k) (ℙ : Measure Ω) := by
          exact (integral_map (putnamB4_m_aemeasurable m h₁ hn) hf).symm
    _ = ∫ x, putnamB4LtInd j x ∂ProbabilityTheory.uniformOn S := by
          rw [(h₁ n k hn), putnamB4_cond_uniformOn_Icc n hn]
    _ = (ProbabilityTheory.uniformOn S).real (Set.Iio j) := by
          have hfun :
              putnamB4LtInd j =
                (Set.Iio j).indicator (fun _ : ℤ => (1 : ℝ)) := by
            funext x
            by_cases h : x < j <;> simp [putnamB4LtInd, Set.indicator, h]
          rw [hfun]
          simpa using
            (integral_indicator_one
              (μ := ProbabilityTheory.uniformOn S)
              (hs := (measurableSet_Iio : MeasurableSet (Set.Iio j))))
    _ = ((j : ℝ) - 1) / (n : ℝ) := by
          exact uniformOn_Icc_Iio_real n j hj₁ hjn

private lemma putnamB4_a_mem_ae {Ω : Type*} [MeasureSpace Ω]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), a n k ω ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
  rw [putnamB4_state_eq m a h₀ h₂ hn]
  have hm_all :
      ∀ᵐ ω ∂(ℙ : Measure Ω),
        ∀ i : Fin k, m n i ω ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
    exact Filter.eventually_all.2 fun i => putnamB4_m_mem_ae m h₁ hn
  filter_upwards [hm_all] with ω hω
  exact putnamB4State_mem_Icc hn (fun i => m n i ω) hω

private lemma putnamB4_a_aemeasurable_int {Ω : Type*} [MeasureSpace Ω]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    AEMeasurable (a n k) (ℙ : Measure Ω) := by
  rw [putnamB4_state_eq m a h₀ h₂ hn]
  exact (putnamB4State_measurable k).comp_aemeasurable
    (aemeasurable_pi_lambda _ fun i => putnamB4_m_aemeasurable m h₁ hn)

private lemma putnamB4_a_aemeasurable_real {Ω : Type*} [MeasureSpace Ω]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    AEMeasurable (fun ω => (a n k ω : ℝ)) (ℙ : Measure Ω) := by
  exact (measurable_of_countable fun z : ℤ => (z : ℝ)).comp_aemeasurable
    (putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn)

private lemma putnamB4_a_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    Integrable (fun ω => (a n k ω : ℝ)) (ℙ : Measure Ω) := by
  refine Integrable.of_mem_Icc (1 : ℝ) (n : ℝ)
    (putnamB4_a_aemeasurable_real m a h₀ h₁ h₂ hn) ?_
  filter_upwards [putnamB4_a_mem_ae m a h₀ h₁ h₂ hn] with ω hω
  exact ⟨by exact_mod_cast hω.1, by exact_mod_cast hω.2⟩

private lemma putnamB4_a_indep_m {Ω : Type*} [MeasureSpace Ω]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (h₃ : ProbabilityTheory.iIndepFun m.uncurry ℙ)
    {n k : ℕ} (hn : 0 < n) :
    ProbabilityTheory.IndepFun (a n k) (m n k) (ℙ : Measure Ω) := by
  classical
  let row : ℕ → ℕ × ℕ := fun j => (n, j)
  have hrow_inj : Function.Injective row := by
    intro i j hij
    exact Prod.ext_iff.mp hij |>.2
  have hrow : ProbabilityTheory.iIndepFun (fun j => m n j) (ℙ : Measure Ω) := by
    simpa [row, Function.comp_def, Function.uncurry] using h₃.precomp hrow_inj
  have hprev :
      ProbabilityTheory.IndepFun
        (fun ω (i : (Finset.range k : Finset ℕ)) => m n i ω)
        (fun ω (i : ({k} : Finset ℕ)) => m n i ω)
        (ℙ : Measure Ω) := by
    refine ProbabilityTheory.iIndepFun.indepFun_finset₀
      (Finset.range k) ({k} : Finset ℕ) ?_ hrow ?_
    · rw [Finset.disjoint_singleton_right]
      exact Finset.notMem_range_self
    · intro j
      exact putnamB4_m_aemeasurable m h₁ hn
  let toState : (((i : (Finset.range k : Finset ℕ)) → ℤ) → ℤ) :=
    fun xs => putnamB4State k fun i => xs ⟨i, Finset.mem_range.mpr i.2⟩
  let fromSingleton : (((i : ({k} : Finset ℕ)) → ℤ) → ℤ) :=
    fun xs => xs ⟨k, by simp⟩
  have hcomp :
      ProbabilityTheory.IndepFun
        (toState ∘ fun ω (i : (Finset.range k : Finset ℕ)) => m n i ω)
        (fromSingleton ∘ fun ω (i : ({k} : Finset ℕ)) => m n i ω)
        (ℙ : Measure Ω) := by
    exact hprev.comp (measurable_of_countable toState) (measurable_of_countable fromSingleton)
  refine hcomp.congr ?_ ?_
  · filter_upwards with ω
    rw [putnamB4_state_eq m a h₀ h₂ hn]
    rfl
  · filter_upwards with ω
    rfl

private lemma putnamB4_integral_eqInd_sum_one {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ),
        ∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) = 1 := by
  let Sfin : Finset ℤ := Finset.Icc (1 : ℤ) (n : ℤ)
  have hmem := putnamB4_a_mem_ae m a h₀ h₁ h₂ hn (k := k)
  have hsum :
      (fun _ : Ω => (1 : ℝ)) =ᵐ[(ℙ : Measure Ω)]
        fun ω => ∑ j ∈ Sfin, putnamB4EqInd j (a n k ω) := by
    filter_upwards [hmem] with ω hω
    symm
    simpa [Sfin] using putnamB4_sum_eqInd (n := n) (x := a n k ω) hω
  calc
    (∑ j ∈ Sfin, ∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) =
        ∫ ω, (∑ j ∈ Sfin, putnamB4EqInd j (a n k ω)) ∂(ℙ : Measure Ω) := by
          exact (integral_finset_sum Sfin fun j hj =>
            putnamB4_eq_ind_integrable (a n k) j
              (putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn)).symm
    _ = ∫ _ : Ω, (1 : ℝ) ∂(ℙ : Measure Ω) := by
          exact (integral_congr_ae hsum.symm)
    _ = 1 := by
          simp

private lemma putnamB4_integral_eqInd_weighted {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ),
        (j : ℝ) * ∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) =
      ∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω) := by
  let Sfin : Finset ℤ := Finset.Icc (1 : ℤ) (n : ℤ)
  have hmem := putnamB4_a_mem_ae m a h₀ h₁ h₂ hn (k := k)
  have hsum :
      (fun ω => (a n k ω : ℝ)) =ᵐ[(ℙ : Measure Ω)]
        fun ω => ∑ j ∈ Sfin, (j : ℝ) * putnamB4EqInd j (a n k ω) := by
    filter_upwards [hmem] with ω hω
    symm
    simpa [Sfin] using putnamB4_sum_weighted_eqInd (n := n) (x := a n k ω) hω
  calc
    (∑ j ∈ Sfin, (j : ℝ) * ∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) =
        (∑ j ∈ Sfin, ∫ ω, (j : ℝ) * putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) := by
          simp_rw [integral_const_mul]
    _ =
        ∫ ω, (∑ j ∈ Sfin, (j : ℝ) * putnamB4EqInd j (a n k ω)) ∂(ℙ : Measure Ω) := by
          exact (integral_finset_sum Sfin fun j hj =>
            (putnamB4_eq_ind_integrable (a n k) j
              (putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn)).const_mul (j : ℝ)).symm
    _ = ∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω) := by
          exact (integral_congr_ae hsum.symm)

private lemma putnamB4_integral_prod_gt_factor {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (h₃ : ProbabilityTheory.iIndepFun m.uncurry ℙ)
    {n k : ℕ} (hn : 0 < n) {j : ℤ}
    (hj₁ : (1 : ℤ) ≤ j) (hjn : j ≤ (n : ℤ)) :
    (∫ ω, putnamB4EqInd j (a n k ω) * putnamB4GtInd j (m n k ω)
        ∂(ℙ : Measure Ω)) =
      (∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) *
        (((n : ℝ) - (j : ℝ)) / (n : ℝ)) := by
  have hXY := putnamB4_a_indep_m m a h₀ h₁ h₂ h₃ hn (k := k)
  have hX := putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn (k := k)
  have hY := putnamB4_m_aemeasurable m h₁ hn (k := k)
  have hf : AEStronglyMeasurable (putnamB4EqInd j)
      (Measure.map (a n k) (ℙ : Measure Ω)) :=
    (measurable_of_countable (putnamB4EqInd j)).aestronglyMeasurable
  have hg : AEStronglyMeasurable (putnamB4GtInd j)
      (Measure.map (m n k) (ℙ : Measure Ω)) :=
    (measurable_of_countable (putnamB4GtInd j)).aestronglyMeasurable
  calc
    (∫ ω, putnamB4EqInd j (a n k ω) * putnamB4GtInd j (m n k ω)
        ∂(ℙ : Measure Ω)) =
        (∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) *
          (∫ ω, putnamB4GtInd j (m n k ω) ∂(ℙ : Measure Ω)) := by
            simpa [Function.comp_def] using hXY.integral_comp_mul_comp hX hY hf hg
    _ = (∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) *
        (((n : ℝ) - (j : ℝ)) / (n : ℝ)) := by
          rw [putnamB4_integral_gt_m m h₁ hn hj₁ hjn]

private lemma putnamB4_integral_prod_lt_factor {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (h₃ : ProbabilityTheory.iIndepFun m.uncurry ℙ)
    {n k : ℕ} (hn : 0 < n) {j : ℤ}
    (hj₁ : (1 : ℤ) ≤ j) (hjn : j ≤ (n : ℤ)) :
    (∫ ω, putnamB4EqInd j (a n k ω) * putnamB4LtInd j (m n k ω)
        ∂(ℙ : Measure Ω)) =
      (∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) *
        (((j : ℝ) - 1) / (n : ℝ)) := by
  have hXY := putnamB4_a_indep_m m a h₀ h₁ h₂ h₃ hn (k := k)
  have hX := putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn (k := k)
  have hY := putnamB4_m_aemeasurable m h₁ hn (k := k)
  have hf : AEStronglyMeasurable (putnamB4EqInd j)
      (Measure.map (a n k) (ℙ : Measure Ω)) :=
    (measurable_of_countable (putnamB4EqInd j)).aestronglyMeasurable
  have hg : AEStronglyMeasurable (putnamB4LtInd j)
      (Measure.map (m n k) (ℙ : Measure Ω)) :=
    (measurable_of_countable (putnamB4LtInd j)).aestronglyMeasurable
  calc
    (∫ ω, putnamB4EqInd j (a n k ω) * putnamB4LtInd j (m n k ω)
        ∂(ℙ : Measure Ω)) =
        (∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) *
          (∫ ω, putnamB4LtInd j (m n k ω) ∂(ℙ : Measure Ω)) := by
            simpa [Function.comp_def] using hXY.integral_comp_mul_comp hX hY hf hg
    _ = (∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)) *
        (((j : ℝ) - 1) / (n : ℝ)) := by
          rw [putnamB4_integral_lt_m m h₁ hn hj₁ hjn]

private lemma putnamB4_gt_current_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    Integrable (fun ω => putnamB4GtInd (a n k ω) (m n k ω))
      (ℙ : Measure Ω) := by
  have hX := putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn (k := k)
  have hY := putnamB4_m_aemeasurable m h₁ hn (k := k)
  refine putnamB4_indicator_integrable _ ?_ ?_
  · exact (measurable_of_countable
      (fun p : ℤ × ℤ => putnamB4GtInd p.1 p.2)).comp_aemeasurable (hX.prodMk hY)
  · intro ω
    by_cases h : a n k ω < m n k ω <;> simp [putnamB4GtInd, h]

private lemma putnamB4_lt_current_integrable {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    {n k : ℕ} (hn : 0 < n) :
    Integrable (fun ω => putnamB4LtInd (a n k ω) (m n k ω))
      (ℙ : Measure Ω) := by
  have hX := putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn (k := k)
  have hY := putnamB4_m_aemeasurable m h₁ hn (k := k)
  refine putnamB4_indicator_integrable _ ?_ ?_
  · exact (measurable_of_countable
      (fun p : ℤ × ℤ => putnamB4LtInd p.1 p.2)).comp_aemeasurable (hX.prodMk hY)
  · intro ω
    by_cases h : m n k ω < a n k ω <;> simp [putnamB4LtInd, h]

private lemma putnamB4_expectation_recurrence {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (h₃ : ProbabilityTheory.iIndepFun m.uncurry ℙ)
    {n k : ℕ} (hn : 0 < n) :
    (∫ ω, (a n (k + 1) ω : ℝ) ∂(ℙ : Measure Ω)) =
      (1 - 2 / (n : ℝ)) * (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω)) +
        ((n : ℝ) + 1) / (n : ℝ) := by
  let Sfin : Finset ℤ := Finset.Icc (1 : ℤ) (n : ℤ)
  let p : ℤ → ℝ := fun j => ∫ ω, putnamB4EqInd j (a n k ω) ∂(ℙ : Measure Ω)
  have hAint := putnamB4_a_integrable m a h₀ h₁ h₂ hn (k := k)
  have hGTint := putnamB4_gt_current_integrable m a h₀ h₁ h₂ hn (k := k)
  have hLTint := putnamB4_lt_current_integrable m a h₀ h₁ h₂ hn (k := k)
  have hmem := putnamB4_a_mem_ae m a h₀ h₁ h₂ hn (k := k)
  have hstep :
      (fun ω => (a n (k + 1) ω : ℝ)) =ᵐ[(ℙ : Measure Ω)]
        fun ω => (a n k ω : ℝ) +
          putnamB4GtInd (a n k ω) (m n k ω) -
          putnamB4LtInd (a n k ω) (m n k ω) := by
    filter_upwards with ω
    rw [h₂ n k ω hn]
    exact putnamB4Step_real (a n k ω) (m n k ω)
  have hgt_sum :
      (fun ω => putnamB4GtInd (a n k ω) (m n k ω)) =ᵐ[(ℙ : Measure Ω)]
        fun ω => ∑ j ∈ Sfin,
          putnamB4EqInd j (a n k ω) * putnamB4GtInd j (m n k ω) := by
    filter_upwards [hmem] with ω hω
    simpa [Sfin] using putnamB4_gt_sum_eq (n := n) (x := a n k ω) (y := m n k ω) hω
  have hlt_sum :
      (fun ω => putnamB4LtInd (a n k ω) (m n k ω)) =ᵐ[(ℙ : Measure Ω)]
        fun ω => ∑ j ∈ Sfin,
          putnamB4EqInd j (a n k ω) * putnamB4LtInd j (m n k ω) := by
    filter_upwards [hmem] with ω hω
    simpa [Sfin] using putnamB4_lt_sum_eq (n := n) (x := a n k ω) (y := m n k ω) hω
  have hGT :
      (∫ ω, putnamB4GtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) =
        ∑ j ∈ Sfin, p j * (((n : ℝ) - (j : ℝ)) / (n : ℝ)) := by
    calc
      (∫ ω, putnamB4GtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) =
          ∫ ω, (∑ j ∈ Sfin,
            putnamB4EqInd j (a n k ω) * putnamB4GtInd j (m n k ω))
              ∂(ℙ : Measure Ω) := by
            exact integral_congr_ae hgt_sum
      _ = ∑ j ∈ Sfin,
            ∫ ω, putnamB4EqInd j (a n k ω) * putnamB4GtInd j (m n k ω)
              ∂(ℙ : Measure Ω) := by
            exact integral_finset_sum Sfin fun j hj =>
              (putnamB4_prod_ind_integrable (a n k) (m n k) j
                (putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn)
                (putnamB4_m_aemeasurable m h₁ hn)).1
      _ = ∑ j ∈ Sfin, p j * (((n : ℝ) - (j : ℝ)) / (n : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj₁ : (1 : ℤ) ≤ j := (Finset.mem_Icc.mp hj).1
            have hjn : j ≤ (n : ℤ) := (Finset.mem_Icc.mp hj).2
            simpa [p] using
              putnamB4_integral_prod_gt_factor m a h₀ h₁ h₂ h₃ hn hj₁ hjn (k := k)
  have hLT :
      (∫ ω, putnamB4LtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) =
        ∑ j ∈ Sfin, p j * (((j : ℝ) - 1) / (n : ℝ)) := by
    calc
      (∫ ω, putnamB4LtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) =
          ∫ ω, (∑ j ∈ Sfin,
            putnamB4EqInd j (a n k ω) * putnamB4LtInd j (m n k ω))
              ∂(ℙ : Measure Ω) := by
            exact integral_congr_ae hlt_sum
      _ = ∑ j ∈ Sfin,
            ∫ ω, putnamB4EqInd j (a n k ω) * putnamB4LtInd j (m n k ω)
              ∂(ℙ : Measure Ω) := by
            exact integral_finset_sum Sfin fun j hj =>
              (putnamB4_prod_ind_integrable (a n k) (m n k) j
                (putnamB4_a_aemeasurable_int m a h₀ h₁ h₂ hn)
                (putnamB4_m_aemeasurable m h₁ hn)).2
      _ = ∑ j ∈ Sfin, p j * (((j : ℝ) - 1) / (n : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj₁ : (1 : ℤ) ≤ j := (Finset.mem_Icc.mp hj).1
            have hjn : j ≤ (n : ℤ) := (Finset.mem_Icc.mp hj).2
            simpa [p] using
              putnamB4_integral_prod_lt_factor m a h₀ h₁ h₂ h₃ hn hj₁ hjn (k := k)
  have hP : (∑ j ∈ Sfin, p j) = 1 := by
    simpa [Sfin, p] using putnamB4_integral_eqInd_sum_one m a h₀ h₁ h₂ hn (k := k)
  have hE :
      (∑ j ∈ Sfin, (j : ℝ) * p j) =
        ∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω) := by
    simpa [Sfin, p] using putnamB4_integral_eqInd_weighted m a h₀ h₁ h₂ hn (k := k)
  have hDelta :
      (∫ ω, putnamB4GtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) -
        (∫ ω, putnamB4LtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) =
      ((n : ℝ) + 1) / (n : ℝ) -
        (2 / (n : ℝ)) * (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω)) := by
    rw [hGT, hLT]
    change
      (∑ j ∈ Sfin, p j * (((n : ℝ) - (j : ℝ)) / (n : ℝ))) -
        (∑ j ∈ Sfin, p j * (((j : ℝ) - 1) / (n : ℝ))) =
      ((n : ℝ) + 1) / (n : ℝ) -
        (2 / (n : ℝ)) * (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω))
    rw [putnamB4_sum_algebra n p hn, hP, hE]
    ring
  calc
    (∫ ω, (a n (k + 1) ω : ℝ) ∂(ℙ : Measure Ω)) =
        ∫ ω, ((a n k ω : ℝ) +
          putnamB4GtInd (a n k ω) (m n k ω) -
          putnamB4LtInd (a n k ω) (m n k ω)) ∂(ℙ : Measure Ω) := by
          exact integral_congr_ae hstep
    _ = (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω)) +
        (∫ ω, putnamB4GtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) -
        (∫ ω, putnamB4LtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) := by
          calc
            (∫ ω, ((a n k ω : ℝ) +
              putnamB4GtInd (a n k ω) (m n k ω) -
              putnamB4LtInd (a n k ω) (m n k ω)) ∂(ℙ : Measure Ω)) =
                (∫ ω, (a n k ω : ℝ) +
                  putnamB4GtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) -
                (∫ ω, putnamB4LtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) := by
                  simpa only using
                    (integral_sub
                      (f := fun ω => (a n k ω : ℝ) +
                        putnamB4GtInd (a n k ω) (m n k ω))
                      (g := fun ω => putnamB4LtInd (a n k ω) (m n k ω))
                      (μ := (ℙ : Measure Ω)) (hAint.add hGTint) hLTint)
            _ = (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω)) +
                (∫ ω, putnamB4GtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) -
                (∫ ω, putnamB4LtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) := by
                  rw [integral_add hAint hGTint]
    _ = (1 - 2 / (n : ℝ)) * (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω)) +
        ((n : ℝ) + 1) / (n : ℝ) := by
          trans
              (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω)) +
                ((∫ ω, putnamB4GtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)) -
                  (∫ ω, putnamB4LtInd (a n k ω) (m n k ω) ∂(ℙ : Measure Ω)))
          · ring
          rw [hDelta]
          ring

private lemma putnamB4_expectation_formula {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (m a : ℕ → ℕ → Ω → ℤ)
    (h₀ : ∀ n > 0, a n 0 = 1)
    (h₁ : ∀ n k, 0 < n → pdf.IsUniform (m n k) (Set.Icc 1 n) ℙ
      (ProbabilityTheory.uniformOn <| Set.Icc 1 n))
    (h₂ : ∀ n k ω, 0 < n →
      a n (k + 1) ω =
        if m n k ω > a n k ω then
          a n k ω + 1
        else if m n k ω = a n k ω then
          a n k ω
        else
          a n k ω - 1)
    (h₃ : ProbabilityTheory.iIndepFun m.uncurry ℙ)
    {n k : ℕ} (hn : 0 < n) :
    (∫ ω, (a n k ω : ℝ) ∂(ℙ : Measure Ω)) =
      ((n : ℝ) + 1) / 2 +
        (1 - ((n : ℝ) + 1) / 2) * (1 - 2 / (n : ℝ)) ^ k := by
  induction k with
  | zero =>
      have hinit :
          (fun ω => (a n 0 ω : ℝ)) = fun _ : Ω => (1 : ℝ) := by
        funext ω
        rw [h₀ n hn]
        norm_num
      rw [hinit]
      simp
  | succ k ih =>
      rw [putnamB4_expectation_recurrence m a h₀ h₁ h₂ h₃ hn, ih]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      let A : ℝ := ((n : ℝ) + 1) / 2
      let r : ℝ := 1 - 2 / (n : ℝ)
      have hc : ((n : ℝ) + 1) / (n : ℝ) = (1 - r) * A := by
        subst A
        subst r
        field_simp [hn0]
        ring
      change r * (A + (1 - A) * r ^ k) + ((n : ℝ) + 1) / (n : ℝ) =
        A + (1 - A) * r ^ (k + 1)
      rw [hc, pow_succ]
      ring

--(1 - rexp (- 2))/2
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
    Filter.Tendsto (fun n => (∫ ω, a n n ω : ℝ) / n) Filter.atTop (𝓝 (((1 - rexp (- 2))/2) : ℝ )) := by
  have hlim_expr :
      Filter.Tendsto
        (fun n : ℕ =>
          (((n : ℝ) + 1) / (2 * (n : ℝ)) -
            (((n : ℝ) - 1) / (2 * (n : ℝ))) * (1 - 2 / (n : ℝ)) ^ n))
        Filter.atTop (𝓝 (((1 - rexp (-2)) / 2) : ℝ)) := by
    have hden :
        Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ))
          Filter.atTop Filter.atTop := by
      exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    have hsmall :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ)))
          Filter.atTop (𝓝 (0 : ℝ)) := by
      exact Filter.Tendsto.const_div_atTop hden (1 : ℝ)
    have hcoef₁ :
        Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (2 * (n : ℝ))))
          Filter.atTop (𝓝 ((1 : ℝ) / 2)) := by
      have heq :
          (fun n : ℕ => (((n : ℝ) + 1) / (2 * (n : ℝ)))) =ᶠ[Filter.atTop]
            fun n : ℕ => (1 : ℝ) / 2 + (1 : ℝ) / (2 * (n : ℝ)) := by
        exact Filter.eventually_atTop.2 ⟨1, fun n hn => by
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
          field_simp [hn0]⟩
      have hbase :
          Filter.Tendsto
            (fun n : ℕ => (1 : ℝ) / 2 + (1 : ℝ) / (2 * (n : ℝ)))
            Filter.atTop (𝓝 ((1 : ℝ) / 2)) := by
        simpa using ((tendsto_const_nhds (x := (1 : ℝ) / 2)).add hsmall)
      exact hbase.congr' heq.symm
    have hcoef₂ :
        Filter.Tendsto (fun n : ℕ => (((n : ℝ) - 1) / (2 * (n : ℝ))))
          Filter.atTop (𝓝 ((1 : ℝ) / 2)) := by
      have heq :
          (fun n : ℕ => (((n : ℝ) - 1) / (2 * (n : ℝ)))) =ᶠ[Filter.atTop]
            fun n : ℕ => (1 : ℝ) / 2 - (1 : ℝ) / (2 * (n : ℝ)) := by
        exact Filter.eventually_atTop.2 ⟨1, fun n hn => by
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
          field_simp [hn0]⟩
      have hbase :
          Filter.Tendsto
            (fun n : ℕ => (1 : ℝ) / 2 - (1 : ℝ) / (2 * (n : ℝ)))
            Filter.atTop (𝓝 ((1 : ℝ) / 2)) := by
        simpa using ((tendsto_const_nhds (x := (1 : ℝ) / 2)).sub hsmall)
      exact hbase.congr' heq.symm
    have hpow :
        Filter.Tendsto (fun n : ℕ => (1 - 2 / (n : ℝ)) ^ n)
          Filter.atTop (𝓝 (rexp (-2))) := by
      simpa [sub_eq_add_neg, neg_div] using Real.tendsto_one_add_div_pow_exp (-2)
    convert hcoef₁.sub (hcoef₂.mul hpow) using 1
    ring_nf
  have hseq :
      (fun n => (∫ ω, a n n ω : ℝ) / n) =ᶠ[Filter.atTop]
        (fun n : ℕ =>
          (((n : ℝ) + 1) / (2 * (n : ℝ)) -
            (((n : ℝ) - 1) / (2 * (n : ℝ))) * (1 - 2 / (n : ℝ)) ^ n)) := by
    exact Filter.eventually_atTop.2 ⟨1, fun n hn => by
      have hnpos : 0 < n := hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
      change (∫ ω, (a n n ω : ℝ) ∂(ℙ : Measure Ω)) / (n : ℝ) =
        (((n : ℝ) + 1) / (2 * (n : ℝ)) -
          (((n : ℝ) - 1) / (2 * (n : ℝ))) * (1 - 2 / (n : ℝ)) ^ n)
      rw [putnamB4_expectation_formula m a h₀ h₁ h₂ h₃ hnpos (k := n)]
      field_simp [hn0]
      ring_nf⟩
  exact (Filter.tendsto_congr' hseq).2 hlim_expr
