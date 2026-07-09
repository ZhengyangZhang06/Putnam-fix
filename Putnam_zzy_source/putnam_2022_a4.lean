import Mathlib

open MeasureTheory ProbabilityTheory Classical

noncomputable section

abbrev putnam_2022_a4_solution : ℝ :=
  -3 + 2 * Real.exp (1 / 2)

private lemma putnam_2022_a4_mem_prefix
    (x : ℕ → ℝ) (n : ℕ) :
    n ∈ sSup { s : Set ℕ |
      ∃ m, s = Set.Iic m ∧ ∀ l, l < m → x l > x (l + 1) } ↔
      ∀ l, l < n → x l > x (l + 1) := by
  constructor
  · intro hn l hln
    rcases (by simpa [Set.sSup_eq_sUnion] using hn) with ⟨m, hm, hnm⟩
    exact hm l (lt_of_lt_of_le hln hnm)
  · intro hn
    simpa [Set.sSup_eq_sUnion] using ⟨n, hn, le_rfl⟩

private abbrev putnam_2022_a4_U : Measure ℝ :=
  ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1)

private lemma putnam_2022_a4_U_prob :
    IsProbabilityMeasure putnam_2022_a4_U := by
  unfold putnam_2022_a4_U
  exact cond_isProbabilityMeasure_of_finite
    (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    (by norm_num [Real.volume_Icc]) (by norm_num [Real.volume_Icc])

private lemma putnam_2022_a4_U_fin :
    IsFiniteMeasure putnam_2022_a4_U := by
  unfold putnam_2022_a4_U ProbabilityTheory.cond
  constructor
  simp [Real.volume_Icc]

private lemma putnam_2022_a4_U_mem :
    ∀ᵐ x ∂putnam_2022_a4_U, x ∈ Set.Icc (0 : ℝ) 1 := by
  haveI := putnam_2022_a4_U_prob
  exact (mem_ae_iff_prob_eq_one measurableSet_Icc).2
    (by unfold putnam_2022_a4_U ProbabilityTheory.cond; simp [Real.volume_Icc])

private def putnam_2022_a4_pref (n : ℕ) (x : Fin (n + 1) → ℝ) : Prop :=
  ∀ l : Fin n, x (Fin.castSucc l) > x (Fin.succ l)

private def putnam_2022_a4_term (n p : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  if putnam_2022_a4_pref n x then x (Fin.last n) ^ p else 0

private def putnam_2022_a4_summand {Ω : Type*}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  putnam_2022_a4_term n 1 (fun i : Fin (n + 1) => X i.val ω) /
    (2 : ℝ) ^ (n + 1)

private lemma putnam_2022_a4_pref_vector_iff
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    putnam_2022_a4_pref n (fun i : Fin (n + 1) => X i.val ω) ↔
      ∀ l, l < n → X l ω > X (l + 1) ω := by
  unfold putnam_2022_a4_pref
  constructor
  · intro h l hl
    have := h ⟨l, hl⟩
    simpa [Fin.val_castSucc, Fin.val_succ] using this
  · intro h l
    simpa [Fin.val_castSucc, Fin.val_succ] using h l.val l.isLt

private lemma putnam_2022_a4_term_measurable (n p : ℕ) :
    Measurable (putnam_2022_a4_term n p) := by
  unfold putnam_2022_a4_term putnam_2022_a4_pref
  have hset :
      MeasurableSet
        {x : Fin (n + 1) → ℝ |
          ∀ l : Fin n, x (Fin.castSucc l) > x (Fin.succ l)} := by
    simp_rw [gt_iff_lt]
    simpa [Set.setOf_forall] using
      (MeasurableSet.iInter fun l : Fin n =>
        measurableSet_lt
          (show Measurable (fun x : Fin (n + 1) → ℝ => x (Fin.succ l)) from
            measurable_pi_apply _)
          (show Measurable (fun x : Fin (n + 1) → ℝ => x (Fin.castSucc l)) from
            measurable_pi_apply _))
  exact Measurable.ite hset
    ((measurable_pi_apply (Fin.last n)).pow_const p) measurable_const

private lemma putnam_2022_a4_summand_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (putnam_2022_a4_summand X n) := by
  unfold putnam_2022_a4_summand
  exact ((putnam_2022_a4_term_measurable n 1).comp
    (measurable_pi_lambda _ fun i => hX i.val)).div_const _

private lemma putnam_2022_a4_term_abs_le_one
    {n p : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    ‖putnam_2022_a4_term n p x‖ ≤ (1 : ℝ) := by
  unfold putnam_2022_a4_term
  by_cases h : putnam_2022_a4_pref n x
  · simp only [h, if_true, Real.norm_eq_abs]
    have hx0 : 0 ≤ x (Fin.last n) := (hx (Fin.last n)).1
    have hx1 : x (Fin.last n) ≤ 1 := (hx (Fin.last n)).2
    have hpow0 : 0 ≤ x (Fin.last n) ^ p := pow_nonneg hx0 p
    have hpow1 : x (Fin.last n) ^ p ≤ (1 : ℝ) := by
      exact pow_le_one₀ (n := p) hx0 hx1
    simpa [abs_of_nonneg hpow0] using hpow1
  · simp [h]

private lemma putnam_2022_a4_term_integrable (n p : ℕ) :
    Integrable (putnam_2022_a4_term n p)
      (Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U)) := by
  haveI := putnam_2022_a4_U_prob
  haveI := putnam_2022_a4_U_fin
  have hsupp :
      ∀ᵐ x ∂(Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U)),
        ∀ i, x i ∈ Set.Icc (0 : ℝ) 1 := by
    exact ae_all_iff.2 fun i =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin (n + 1) => putnam_2022_a4_U) (i := i)).eventually
        putnam_2022_a4_U_mem
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (putnam_2022_a4_term_measurable n p).aestronglyMeasurable ?_
  exact hsupp.mono fun _ hx =>
    putnam_2022_a4_term_abs_le_one (n := n) (p := p) hx

private lemma putnam_2022_a4_pref_snoc
    (n : ℕ) (z : Fin (n + 1) → ℝ) (y : ℝ) :
    putnam_2022_a4_pref (n + 1)
      (Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y) ↔
    putnam_2022_a4_pref n z ∧ z (Fin.last n) > y := by
  unfold putnam_2022_a4_pref
  constructor
  · intro h
    constructor
    · intro l
      have := h (Fin.castSucc l)
      rw [show Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y
          (Fin.succ (Fin.castSucc l)) = z (Fin.succ l) by
        change Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y
          ((Fin.succ l).castSucc) = z (Fin.succ l)
        exact Fin.snoc_castSucc (n := n + 1) (α := fun _ => ℝ) y z (Fin.succ l)] at this
      simpa [Fin.snoc_castSucc] using this
    · have := h (Fin.last n)
      simpa using this
  · intro h l
    refine Fin.lastCases ?last ?cast l
    · simpa using h.2
    · intro i
      have := h.1 i
      rw [show Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y
          (Fin.succ (Fin.castSucc i)) = z (Fin.succ i) by
        change Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y
          ((Fin.succ i).castSucc) = z (Fin.succ i)
        exact Fin.snoc_castSucc (n := n + 1) (α := fun _ => ℝ) y z (Fin.succ i)]
      simpa [Fin.snoc_castSucc] using this

private lemma putnam_2022_a4_term_snoc
    (n p : ℕ) (z : Fin (n + 1) → ℝ) (y : ℝ) :
    putnam_2022_a4_term (n + 1) p
      (Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y) =
    if putnam_2022_a4_pref n z then
      (Set.Iio (z (Fin.last n))).indicator (fun t : ℝ => t ^ p) y
    else 0 := by
  unfold putnam_2022_a4_term
  rw [putnam_2022_a4_pref_snoc]
  by_cases hpref : putnam_2022_a4_pref n z
  · simp [hpref, Set.indicator, gt_iff_lt]
  · simp [hpref]

private lemma putnam_2022_a4_uniform_moment (m : ℕ) :
    ∫ x : ℝ, x ^ m ∂putnam_2022_a4_U = (1 : ℝ) / (m + 1) := by
  rw [putnam_2022_a4_U, ProbabilityTheory.cond, integral_smul_measure]
  simp [Real.volume_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [integral_pow]
  norm_num

private lemma putnam_2022_a4_threshold_integral
    (p : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ y : ℝ, (Set.Iio a).indicator (fun y => y ^ p) y
      ∂putnam_2022_a4_U = a ^ (p + 1) / (p + 1) := by
  rw [putnam_2022_a4_U, ProbabilityTheory.cond, integral_smul_measure]
  simp [Real.volume_Icc]
  rw [integral_indicator measurableSet_Iio]
  rw [Measure.restrict_restrict measurableSet_Iio]
  rw [show Set.Iio a ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 a by
    ext y
    constructor <;> intro hy
    · exact ⟨hy.2.1, hy.1⟩
    · exact ⟨hy.2, ⟨hy.1, le_of_lt (lt_of_lt_of_le hy.2 ha1)⟩⟩]
  rw [← integral_Icc_eq_integral_Ico]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le ha0]
  rw [integral_pow]
  simp

private lemma putnam_2022_a4_term_inner
    (n p : ℕ) (z : Fin (n + 1) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) :
    ∫ y : ℝ,
      putnam_2022_a4_term (n + 1) p
        (Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y)
      ∂putnam_2022_a4_U =
    (1 / (p + 1 : ℝ)) * putnam_2022_a4_term n (p + 1) z := by
  rw [show
      (fun y : ℝ =>
        putnam_2022_a4_term (n + 1) p
          (Fin.snoc (n := n + 1) (α := fun _ => ℝ) z y)) =
      (fun y : ℝ =>
        if putnam_2022_a4_pref n z then
          (Set.Iio (z (Fin.last n))).indicator (fun t : ℝ => t ^ p) y
        else 0) by
    funext y
    exact putnam_2022_a4_term_snoc n p z y]
  by_cases hpref : putnam_2022_a4_pref n z
  · simp [hpref, putnam_2022_a4_term,
      putnam_2022_a4_threshold_integral p (hz (Fin.last n)).1 (hz (Fin.last n)).2]
    ring
  · simp [hpref, putnam_2022_a4_term]

private lemma putnam_2022_a4_term_split (n p : ℕ) :
    ∫ x : Fin (n + 2) → ℝ, putnam_2022_a4_term (n + 1) p x
      ∂(Measure.pi (fun _ : Fin (n + 2) => putnam_2022_a4_U)) =
    ∫ yz : ℝ × (Fin (n + 1) → ℝ),
      putnam_2022_a4_term (n + 1) p
        (Fin.snoc (n := n + 1) (α := fun _ => ℝ) yz.2 yz.1)
      ∂(putnam_2022_a4_U.prod
        (Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U))) := by
  haveI := putnam_2022_a4_U_fin
  let μ : Fin (n + 2) → Measure ℝ := fun _ => putnam_2022_a4_U
  have hsymm := (measurePreserving_piFinSuccAbove μ (Fin.last (n + 1))).symm
  rw [← hsymm.integral_comp' (putnam_2022_a4_term (n + 1) p)]
  simp only [μ]
  apply integral_congr_ae
  filter_upwards with yz
  congr 1
  funext i
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
  exact Fin.snocEquiv_apply (fun _ : Fin (n + 2) => ℝ) yz i

private lemma putnam_2022_a4_term_recurrence (n p : ℕ) :
    ∫ x : Fin (n + 2) → ℝ, putnam_2022_a4_term (n + 1) p x
      ∂(Measure.pi (fun _ : Fin (n + 2) => putnam_2022_a4_U)) =
    (1 / (p + 1 : ℝ)) *
      ∫ z : Fin (n + 1) → ℝ, putnam_2022_a4_term n (p + 1) z
        ∂(Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U)) := by
  haveI := putnam_2022_a4_U_prob
  haveI := putnam_2022_a4_U_fin
  rw [putnam_2022_a4_term_split n p]
  have hsymm_int :
      Integrable
        (fun yz : ℝ × (Fin (n + 1) → ℝ) =>
          putnam_2022_a4_term (n + 1) p
            (Fin.snoc (n := n + 1) (α := fun _ => ℝ) yz.2 yz.1))
        (putnam_2022_a4_U.prod
          (Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U))) := by
    let μ : Fin (n + 2) → Measure ℝ := fun _ => putnam_2022_a4_U
    have hsymm := (measurePreserving_piFinSuccAbove μ (Fin.last (n + 1))).symm
    have hcomp :
        Integrable
          (fun yz : ℝ × (Fin (n + 1) → ℝ) =>
            putnam_2022_a4_term (n + 1) p
              ((MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))).symm yz))
          (putnam_2022_a4_U.prod
            (Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U))) := by
      simpa [μ] using
        (hsymm.integrable_comp
          (putnam_2022_a4_term_measurable (n + 1) p).aestronglyMeasurable).2
          (putnam_2022_a4_term_integrable (n + 1) p)
    refine hcomp.congr ?_
    filter_upwards with yz
    congr 1
    funext i
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
    exact Fin.snocEquiv_apply (fun _ : Fin (n + 2) => ℝ) yz i
  rw [integral_prod_symm _ hsymm_int]
  have hsupp :
      ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U)),
        ∀ i, z i ∈ Set.Icc (0 : ℝ) 1 := by
    exact ae_all_iff.2 fun i =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin (n + 1) => putnam_2022_a4_U) (i := i)).eventually
        putnam_2022_a4_U_mem
  rw [integral_congr_ae (hsupp.mono fun z hz =>
    putnam_2022_a4_term_inner n p z hz)]
  rw [integral_const_mul]

private lemma putnam_2022_a4_term_integral_formula (n p : ℕ) :
    ∫ x : Fin (n + 1) → ℝ, putnam_2022_a4_term n p x
      ∂(Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U)) =
    (Nat.factorial p : ℝ) / Nat.factorial (p + n + 1) := by
  induction n generalizing p with
  | zero =>
      haveI := putnam_2022_a4_U_prob
      have heval :=
        measurePreserving_eval (μ := fun _ : Fin 1 => putnam_2022_a4_U) (0 : Fin 1)
      have hfun :
          (fun x : Fin 1 → ℝ => putnam_2022_a4_term 0 p x) =
          fun x => (x (0 : Fin 1)) ^ p := by
        funext x
        unfold putnam_2022_a4_term putnam_2022_a4_pref
        simp
      rw [hfun]
      have hmap := integral_map
        (μ := Measure.pi (fun _ : Fin 1 => putnam_2022_a4_U))
        (φ := Function.eval (0 : Fin 1)) heval.measurable.aemeasurable
        (f := fun y : ℝ => y ^ p) (by fun_prop)
      rw [← hmap, heval.map_eq]
      rw [putnam_2022_a4_uniform_moment]
      rw [Nat.factorial_succ]
      norm_num [Nat.cast_mul, Nat.cast_add]
      have hfac : ((Nat.factorial p : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero p)
      have hp : (↑p + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hfac, hp]
  | succ n ih =>
      rw [putnam_2022_a4_term_recurrence n p]
      rw [ih (p + 1)]
      rw [Nat.factorial_succ]
      norm_num [Nat.cast_mul, Nat.cast_add]
      have hsucc : ((p + 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero p)
      have hden : ((Nat.factorial (p + 1 + n + 1) : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero (p + 1 + n + 1))
      field_simp [hsucc, hden]
      ring_nf

private lemma putnam_2022_a4_uniform_mem_Icc_ae
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → ℝ) (hX : Measurable X)
    (hX' : MeasureTheory.pdf.IsUniform X (Set.Icc (0 : ℝ) 1) ℙ) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), X ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hpre := hX'.measure_preimage
    (μ := (volume : Measure ℝ))
    (A := Set.Icc (0 : ℝ) 1)
    (by norm_num [Real.volume_Icc]) (by norm_num [Real.volume_Icc]) measurableSet_Icc
  rw [Set.inter_self, ENNReal.div_self] at hpre
  · exact (mem_ae_iff_prob_eq_one (hX measurableSet_Icc)).2 hpre
  · norm_num [Real.volume_Icc]
  · norm_num [Real.volume_Icc]

private lemma putnam_2022_a4_vector_law
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (hX'' : iIndepFun X) (n : ℕ) :
    Measure.map (fun ω (i : Fin (n + 1)) => X i.val ω) (ℙ : Measure Ω) =
      Measure.pi (fun _ : Fin (n + 1) => putnam_2022_a4_U) := by
  have hind_fin :
      iIndepFun (fun i : Fin (n + 1) => X i.val) (ℙ : Measure Ω) := by
    exact hX''.precomp (fun i j hij => Fin.ext hij)
  have hind := (iIndepFun_iff_map_fun_eq_pi_map (μ := (ℙ : Measure Ω))
    (f := fun i : Fin (n + 1) => X i.val)
    (by intro i; exact (hX i.val).aemeasurable)).mp hind_fin
  rw [hind]
  apply congrArg Measure.pi
  funext i
  simpa [MeasureTheory.pdf.IsUniform, putnam_2022_a4_U] using hX' i.val

private lemma putnam_2022_a4_random_term_integral
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (hX'' : iIndepFun X) (n : ℕ) :
    ∫ ω, putnam_2022_a4_term n 1
        (fun i : Fin (n + 1) => X i.val ω)
      ∂(ℙ : Measure Ω) =
    (1 : ℝ) / Nat.factorial (n + 2) := by
  let φ : Ω → (Fin (n + 1) → ℝ) := fun ω i => X i.val ω
  have hφ_meas : Measurable φ := by
    exact measurable_pi_lambda _ fun i => hX i.val
  have hmap := integral_map (μ := (ℙ : Measure Ω)) (φ := φ)
    hφ_meas.aemeasurable
    (f := putnam_2022_a4_term n 1)
    (putnam_2022_a4_term_measurable n 1).aestronglyMeasurable
  rw [← hmap]
  rw [putnam_2022_a4_vector_law X hX hX' hX'' n]
  rw [putnam_2022_a4_term_integral_formula n 1]
  norm_num only [Nat.factorial_one, Nat.cast_one, one_div]
  rw [show 1 + n + 1 = n + 2 by omega]

private lemma putnam_2022_a4_summand_norm_le
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) {ω : Ω}
    (hω : ∀ m, X m ω ∈ Set.Icc (0 : ℝ) 1) :
    ‖putnam_2022_a4_summand X n ω‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  unfold putnam_2022_a4_summand
  have hx :
      ∀ i : Fin (n + 1),
        (fun i : Fin (n + 1) => X i.val ω) i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => hω i.val
  have hterm := putnam_2022_a4_term_abs_le_one (n := n) (p := 1) hx
  have hpos : 0 < (2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  calc
    ‖putnam_2022_a4_term n 1 (fun i : Fin (n + 1) => X i.val ω) /
        (2 : ℝ) ^ (n + 1)‖
        = ‖putnam_2022_a4_term n 1
            (fun i : Fin (n + 1) => X i.val ω)‖ / ((2 : ℝ) ^ (n + 1)) := by
          rw [norm_div, Real.norm_of_nonneg hpos.le]
    _ ≤ 1 / ((2 : ℝ) ^ (n + 1)) := by
          exact div_le_div_of_nonneg_right hterm hpos.le
    _ = (1 / 2 : ℝ) ^ (n + 1) := by
          simp [one_div]

private lemma putnam_2022_a4_summand_integrable
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hsupp : ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ n, X n ω ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (putnam_2022_a4_summand X n) (ℙ : Measure Ω) := by
  refine Integrable.mono' (integrable_const ((1 / 2 : ℝ) ^ (n + 1)))
    (putnam_2022_a4_summand_measurable X hX n).aestronglyMeasurable ?_
  exact hsupp.mono fun _ hω => putnam_2022_a4_summand_norm_le X n hω

private lemma putnam_2022_a4_summable_integral_norm
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hsupp : ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ n, X n ω ∈ Set.Icc (0 : ℝ) 1) :
    Summable fun n : ℕ =>
      ∫ ω, ‖putnam_2022_a4_summand X n ω‖ ∂(ℙ : Measure Ω) := by
  have hInt : ∀ n, Integrable (putnam_2022_a4_summand X n) (ℙ : Measure Ω) :=
    fun n => putnam_2022_a4_summand_integrable X hX hsupp n
  have hle :
      ∀ n,
        ∫ ω, ‖putnam_2022_a4_summand X n ω‖ ∂(ℙ : Measure Ω) ≤
          (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    have hnorm_int :
        Integrable (fun ω => ‖putnam_2022_a4_summand X n ω‖)
          (ℙ : Measure Ω) := (hInt n).norm
    have hconst_int :
        Integrable (fun _ : Ω => (1 / 2 : ℝ) ^ (n + 1))
          (ℙ : Measure Ω) := integrable_const _
    have hmono := integral_mono_ae hnorm_int hconst_int
      (hsupp.mono fun _ hω => putnam_2022_a4_summand_norm_le X n hω)
    simpa using hmono
  have hnonneg :
      ∀ n, 0 ≤ ∫ ω, ‖putnam_2022_a4_summand X n ω‖ ∂(ℙ : Measure Ω) := by
    intro n
    exact integral_nonneg fun _ => norm_nonneg _
  have hgeo : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) := by
    simpa [Nat.add_comm] using
      ((summable_nat_add_iff
        (G := ℝ) (f := fun n : ℕ => (1 / 2 : ℝ) ^ n) 1).2
        summable_geometric_two)
  exact Summable.of_nonneg_of_le hnonneg hle hgeo

private lemma putnam_2022_a4_summand_integral
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (hX'' : iIndepFun X) (n : ℕ) :
    ∫ ω, putnam_2022_a4_summand X n ω ∂(ℙ : Measure Ω) =
    (1 : ℝ) / ((2 : ℝ) ^ (n + 1) * (Nat.factorial (n + 2) : ℝ)) := by
  unfold putnam_2022_a4_summand
  rw [show
      (fun ω : Ω =>
        putnam_2022_a4_term n 1 (fun i : Fin (n + 1) => X i.val ω) /
          (2 : ℝ) ^ (n + 1)) =
      (fun ω : Ω =>
        (1 / (2 : ℝ) ^ (n + 1)) *
          putnam_2022_a4_term n 1 (fun i : Fin (n + 1) => X i.val ω)) by
    funext ω
    rw [div_eq_inv_mul, one_div]]
  rw [integral_const_mul]
  rw [putnam_2022_a4_random_term_integral X hX hX' hX'' n]
  have hpow : (2 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (Nat.factorial (n + 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (n + 2))
  field_simp [hpow, hfac]

private lemma putnam_2022_a4_pointwise_sum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (k : Ω → Set ℕ)
    (hk : ∀ ω, k ω = sSup { s : Set ℕ |
      ∃ m, s = Set.Iic m ∧ ∀ l, l < m → X l ω > X (l + 1) ω })
    (S : Ω → ℝ)
    (hS : ∀ ω, S ω = ∑' (i : k ω), (X i ω) / (2 ^ (i.val + 1)))
    (ω : Ω) :
    S ω = ∑' n : ℕ, putnam_2022_a4_summand X n ω := by
  calc
    S ω = ∑' (i : k ω), (X i ω) / (2 ^ (i.val + 1)) := hS ω
    _ = ∑' n : ℕ,
        (k ω).indicator (fun i : ℕ => X i ω / (2 : ℝ) ^ (i + 1)) n := by
      exact tsum_subtype (k ω) (fun i : ℕ => X i ω / (2 : ℝ) ^ (i + 1))
    _ = ∑' n : ℕ, putnam_2022_a4_summand X n ω := by
      apply tsum_congr
      intro n
      have hmem :
          n ∈ k ω ↔ ∀ l, l < n → X l ω > X (l + 1) ω := by
        rw [hk ω]
        exact putnam_2022_a4_mem_prefix (fun l => X l ω) n
      by_cases hn : n ∈ k ω
      · have hp : ∀ l, l < n → X l ω > X (l + 1) ω := hmem.1 hn
        have hpref :
            putnam_2022_a4_pref n
              (fun i : Fin (n + 1) => X i.val ω) :=
          (putnam_2022_a4_pref_vector_iff X n ω).2 hp
        simp [Set.indicator_of_mem hn, putnam_2022_a4_summand,
          putnam_2022_a4_term, hpref, Fin.val_last]
      · have hnp : ¬ ∀ l, l < n → X l ω > X (l + 1) ω := by
          exact mt hmem.2 hn
        have hnpref :
            ¬ putnam_2022_a4_pref n
              (fun i : Fin (n + 1) => X i.val ω) := by
          intro hpref
          exact hnp ((putnam_2022_a4_pref_vector_iff X n ω).1 hpref)
        simp [Set.indicator_of_notMem hn, putnam_2022_a4_summand,
          putnam_2022_a4_term, hnpref]

private lemma putnam_2022_a4_scalar_series :
    (∑' n : ℕ,
      (1 : ℝ) / ((2 : ℝ) ^ (n + 1) * (Nat.factorial (n + 2) : ℝ))) =
    -3 + 2 * Real.exp (1 / 2) := by
  let b : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ m / (Nat.factorial m : ℝ)
  have hb : HasSum b (Real.exp (1 / 2)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (1 / 2 : ℝ)
    simpa [b, Real.exp_eq_exp_ℝ] using h
  have htail :
      HasSum (fun n : ℕ => b (n + 2)) (Real.exp (1 / 2) - (b 0 + b 1)) := by
    simpa [Finset.sum_range_succ, b] using
      ((hasSum_nat_add_iff' (f := b) (g := Real.exp (1 / 2)) 2).2 hb)
  have hterm :
      (fun n : ℕ =>
        (1 : ℝ) / ((2 : ℝ) ^ (n + 1) * (Nat.factorial (n + 2) : ℝ))) =
      fun n : ℕ => 2 * b (n + 2) := by
    funext n
    simp [b]
    field_simp
      [pow_ne_zero (n := n + 1) (by norm_num : (2 : ℝ) ≠ 0),
       Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 2))]
    ring
  rw [hterm]
  rw [tsum_mul_left]
  rw [htail.tsum_eq]
  simp [b]
  ring_nf

/--
Suppose $X_1, X_2, ...$ real numbers between 0 and 1 that are chosen independently and uniformly at random. Let $S = \sum_{i=1}^k X_i / 2^i $ where $k$ is the least positive integer such that $X_k < X_{k+1}$ or $k = \infty$ if there is no such integer. Find the expected value of $S$
-/
theorem putnam_2022_a4
    {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (hX'' : iIndepFun X)
    (k : Ω → Set ℕ)

    (hk : ∀ ω, k ω = sSup { s : Set ℕ |
      ∃ m, s = Set.Iic m ∧ ∀ l, l < m → X l ω > X (l + 1) ω })
    (S : Ω → ℝ)
    (hS : ∀ ω, S ω = ∑' (i : k ω), (X i ω) / (2 ^ (i.val + 1))) :
    ∫ ω, S ω ∂(ℙ : Measure Ω) = putnam_2022_a4_solution := by
  have hsupp :
      ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ n, X n ω ∈ Set.Icc (0 : ℝ) 1 := by
    exact ae_all_iff.2 fun n =>
      putnam_2022_a4_uniform_mem_Icc_ae (X n) (hX n) (hX' n)
  have hInt :
      ∀ n, Integrable (putnam_2022_a4_summand X n) (ℙ : Measure Ω) :=
    fun n => putnam_2022_a4_summand_integrable X hX hsupp n
  have hSumNorm :
      Summable fun n : ℕ =>
        ∫ ω, ‖putnam_2022_a4_summand X n ω‖ ∂(ℙ : Measure Ω) :=
    putnam_2022_a4_summable_integral_norm X hX hsupp
  calc
    ∫ ω, S ω ∂(ℙ : Measure Ω)
        = ∫ ω, ∑' n : ℕ, putnam_2022_a4_summand X n ω
            ∂(ℙ : Measure Ω) := by
          exact integral_congr_ae
            (ae_of_all _ fun ω => putnam_2022_a4_pointwise_sum X k hk S hS ω)
    _ = ∑' n : ℕ,
          ∫ ω, putnam_2022_a4_summand X n ω ∂(ℙ : Measure Ω) := by
          exact (integral_tsum_of_summable_integral_norm hInt hSumNorm).symm
    _ = ∑' n : ℕ,
          (1 : ℝ) / ((2 : ℝ) ^ (n + 1) * (Nat.factorial (n + 2) : ℝ)) := by
          exact tsum_congr fun n =>
            putnam_2022_a4_summand_integral X hX hX' hX'' n
    _ = putnam_2022_a4_solution := by
          rw [putnam_2022_a4_scalar_series]
